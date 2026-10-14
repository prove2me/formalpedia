-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2803
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:47:09.107344+00:00
-- url     : https://prove2.me/submissions/40c989d6-f55b-4e41-bbe0-c2e5375e111c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 503956834 ≤ n < 504136690 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 503958084 1250 503956834 503956847
    0xa050a090806040506040b13080d0f0207020307060c0501060f06021f020f070f0611070b2d010305010f05070810171203040b160201110306010c020a05030105070314010b0f19 76
    0x40300e03202c0d02040006005000800c0340c00369004500121254999040c6184251810140640041420891610211200d41c410703060080009001400c1c10050b0340028242a15039000c4000607c800301024148407085c0304540017081c40c1000c7e801400c1c907188001c1c0d00e520b83c0c014000078844c0f80d0408009940c00c1030301103840030f2551850181c3d50b603840c0d2510124807a400c500a0707551615000c41042081c600d0004c40300c0c2c880e08264410442da48500e80c000315200782003001d0025903407840c10706141107101105c80303029501c50130002c1541c10304e01b05003204440c2d00030304080400058900f4402c4212494038048180c80001109110029462102514155001d41090350380c0000104010070307c41207503203c9008012000011024448000f4101e0030380f60850a149089202000810741540c090501c0310b100b00e1002d40400300c4a540c40340002d084890440c0c188021a0701d510705100509010201340e805019516100c074140070781c0400d40b500500848040d40304420421445260381c2e80501c9 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 503959334 1250 503958084 503958089
    0x1090b010e07181e0e0106020601050904050a08181009050603010b1305030604050c1903020105040e040303090b04060b010905120318061c0204060306090e0c04050a0e01240b0f0a050a09 81
    0x9280c3c120075a0b500a009440307070140c86103507800c443e4210701141c041c8682c074a0b5030490700a03500420581e4207040c20800c801c0e034060021105407040c0051300c00000d11a00145c0403820803c619403200422036070a112881d542ca007074000801400c8802804035907039030010303641134070028490240c40e0320000d107840c00a442c482c1c1100758148140820042000800a242c420b640025603080c10300b42603118401480c80394600000f4040748051100f40030003030740c403103086074000d00900e80032402d21503d4941c450b0040b0240c40c00e4a059483e004800350558000300e100c4001d01040d10400300b80240c481c455130701c0b40a02040e105040504500b00b441568890f0b080d6100400741c16207114102c0520122000298441c0c802d500100c1d00b08040003501956a206650705074600300301800d1a072403208104002008003c0c40094601d55682c03185903140824406d0180c80d5040c840c0442444000340405040030030744c1e52001c40f034000300b0800c19101c0307442c1d0310594001c0c0c40b280c01c00315107500410100341c4d4500c80c1078 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 503960584 1250 503959334 503959367
    0x120b0f0a09020322080306040c05031504020a120212010305070b090d2a08011a1e010809100f050402030f030304120c02030a0230030a0912020f040e03031801090b010e07 74
    0x1144800d0170f00001500071805034408940400528a00000030703502c0340006c50308101c82841100202220b0300b001e400a107800e08041c50000394000c0c15221480c1203801c0441d22070f14100d6804014030820004201b054080c088290100e03050180c03c1d4000f501d10381402c800100302c0d9440b0f010305041003148010858a840703241908865041d203d401c160b000b041d008103554925413002511a10a08040300404403200162544414050000c8015106c40f04058682140e0344a41c040758044104c16200358440e4010881d008074107410070b4010585032882c01424401e441d00b00700240400035105c034640149441031070038401524480c40c0002800c00d9030558001e500f1120000c1d81e250306200d41e503079074000c03030031030f54030407000c1ea40b4800c111513403401440d403003a000c42c0000c0c03001e000d041044c514035180701d80b0042405c640401c800000c0340a4a540c840d04055584c8040207001001c0800c009480d140700740d20008003d1103034581c03507811b10017806201317100709182420080307645188100303600700d55105031 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 503961834 1250 503960584 503960641
    0x705060d06030b0f100501090b030705210a0c1101140412051e0705010c0906022e0c030c080a090203061b0d05042a1503020f040e07120b0f0a090203 65
    0x2151300d0103008800c8600d4900c49424110100c0c5644c02491110709131054a005603003150b5852070150703141da00002c503109116424440301c80c03800480410442c8100c08180000c9140f008041010340910000e0303880080c10790610b64001580050048506d5025030056440e841504444034242c80510030040e0811200000d42c0d40e0706040c542c0036000b461a00d22820080154034650b50089800107411700414006803c541c102d04658110005d901c520000450180038039035210311100021203001c05482c00210341c40d4901c0c0342c5200d4200c442c140d4051a41078050181055542c006612481c0040c100c4080d0081c0f400d090301c0c883c1820f41a40c90390030150304200203a06281c1000b071500c90321100040703941c626041d00c1d13000e120b2401504108544003406060010510540c06030083c0d004144480b1a81d10203000004400451f22a003e00840c00c644078200b100d00310b1182ca070140c0f2581d02c1d400d409403a0b402441003640e120303242060100d45050200503242d032100056641c00340002c5464114246a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 503963084 1250 503961834 503961841
    0x60d0203010b090a080a0b1801060f090504050f060103080409091e0f0c0b09010c0f050c0a1403010f0204030201020a02210f1e0c0117041b090e070b0306030705060d06030b 75
    0x18010300300e040080364074243c03480d610b1752251b40c0d85407800ca004044048000c0481c140040c07210001030088844400402d00c25201d40007400303580c585a0015400720f40b02c000340307c1849001d01021000c110808061301c17880d81107840e00740c0c040c400c610929003807a6589075002d080c880d40a00c044140d0500c000c080b0b52852450a1a0400000c000d070180d50041a0142c0000c0c500161004c5400d82041a110515460210384880d0341e0442c9107001540c00d4051041d50b12400d079592242d000c06400002611800c0e482910181400c5580584948551030710402040c00541e0300010b11035882a81110410482c0c002084c0000b0032241900e06031103030348111200c1e2629030101040b0003181050710300313070001806000d9110f15928260022224086404604800e65030102d40006960042c015072076202d10240070480c101c40846551b020a103940c0d0f45d540035002c0c08e0028020b5400070042d16002c01e0840c141400000e449154074410300707115030000515001a01d4180d0400b00c0155000002d080d030394913 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 503964334 1250 503963084 503963099
    0xa0510121703041203050106021b091305030a11010501060206040201120c0201110a030906050c04051c030c0b010e1e0f06060d0f020a020d110d02060403052802240108030901030b060d020301 83
    0x2c07000142e40000c17078117160004c244548005600c0340c4420050381c1c21303a40d800070b600600c810f801e400703804104416154102c10340481d10401c0204140441c03030b500d141041d1480c1c049a030854406070031420864200c8000e020150b030f070040e0b203850303499005500018007450118043c0c0c010411504510140c081c086009200b840c1c2680c003031002d00b4020041403107141c4d900c00d10b440f4180701e140145175100c00301d000e2002c030070403040c40540c040382d10070b0409208145803a1110300078940309138082d6025000c1c1000308103601c485c11202013a0840c0d5400c045015041c26100c6d603880d108010301050080314082605007000321960403145820302048000c540d0340c141140000d41351868103004002244007001880442c8400150880c85242207a01510060b05c40790b0b4211030562144c00985500c11501c2201d12138a07500030080560306140d50020a41e101c0c0c212940f1a550303003407184440d2601655001048941c1001c011108180d8003440c000440c0c0805000040b40c5003c2c249528402d00c0c404800070a581 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 503965584 1250 503964334 503964353
    0x80906161b0819050d050c1207080403060e010c17060307321203070204020a09051f02011508071a1210080106091107060504060b031f050a051012170304 67
    0x9840d40c80a03183d82c81007902c00b003503210760240c0c4014120b40c40442d040200c80c0c0714001030b18000340d1350701c1034403401000d61022100030341007664241c9070020005810820045944150103900c05c0b200002e00814001000c01750102e00301115040c11560703200000b860aa42c20f200740806003000440f4083c0d2980444d1184400310a003244030007142620701300c90f4440340b03400e0892821425506000710720b441603a9081c00041d411240d00c5a09000b02e40c072012800f0b50794140c0c0e01c241d180030540820100740d031a00c002400e68004a40085280e04060b4081c0082e100100f55001929003c020700880310f003180d81501424401d100600004d09940c1090000c610440f00154007101c0e000c02c0240482c2d52120400030844100c00c95100f030744a0100b0541d0006403070354002552090040784000f421044043c042800d040703000c02c8a002e0020711458011300040d0300d01c1800d40003040c540e400c00003032078058000500c200003405185000c0354a90b0040c42042071ba0550f00d80b00c0032483c10529101d060620f0b141d040d8 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 503966834 1250 503965584 503965589
    0x480203030f0606030112060b0a09090302030a0e1504030b09100c170f1509060409020915090c1312060b030a08040620030306010c050c04050c03090d0c080906161b 71
    0x980d801403010452900e800400d07a41030316401b02c2d209650460303e58440c001000744035242500918000d81c0000c1d5088240301c0c16014034007980246988004118004000c1e54000d41040c3c0702d03002102c06210000e44460070b0750282c0c1c0e1300c070384a5400f50311b4440c0380300c0c9000341842248010606061408150030f500c10a0012001800c5e1400b404540f18807981c4540c503542200c424208070405403200005161a04503507400410141c000920005641c02082d00510101c941d5000090000326070501400d042e0b42080c0e000c0810324005003420842414000008500d00c1202d0350134240082da502031080a0b0300901e41400000c1c1211032600b450700e40b14007075411034402e03040070030100c9054141c0c1c5a5940141081d0701c80c80001385d131031076071043e005607407011000c0000d4400b44600341202c80c0310303100d902c1014001d81c040c14409413a0710f03111480c64507001d88528140d0401c9504442d050014901100780c50103050b00300c4949031194081a64142d404010010141544522044520310010100c045409 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 503968084 1250 503966834 503966851
    0x405030615030604030f2c12030f0316090f0f140913170c010608030405032803200a0605040303060911041203030209060708091348020303 61
    0x400d40d0350003010222105076420a942642059001400083c032560a0b00102e04003030402d52040880c03420001c49281228103402c007070500c2e5100305496880c011001941c5a120000250703c0c2002242c0c805200e0700025000c600c41e07181c0703504a4040c00340600990405400d4901840b590695a4102089602c61521030102e01c8080c1481c69426400c1040855120703449600c5203510310000d90b41c952000ca0341101c4000000e0030700b8846460317680000c0c040d101c01031544030000c540b100e080c54201030414180741a41c099000094444001014052030742005868150030016a030980d4510b000d60004c05940d481c7c0d0b164003d01d244a0100030040d032041d8000c0340669001c100c0c0c40e807103109020442e0f403403c2003807000300d4082c001008401e4201100188840c443e1801504150000000c64900e81114004461814011541d000241041305180805000f4144240500d005007101050387c1003107580d0762014914140b4540c000300380c4000c0d4904e03000c00369141704a840e000018000303441e60810380760004e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 503969334 1250 503968084 503968093
    0x7050c040b04020702030c100513080a021002060106230702150a0e0a060c0213060504060b04170312070333031527050a0f0803070201200d0b0f1203040503 68
    0x1c80e01c1c201032082c1d921456000d40140410080f90040005008016000c4400c000d420040082c906003403c1004008000150051510b080c1c103204001340703058110f02c1760702154040c40041142c0c070b030b001d00200300d912000c1c51412035020100055104a21034100082c2d00320003000c03003060030680301e6402071000b5900d0307541c0da01c40151004200661080b09109010002d0809902103000d46080c0c045403d02d000b03000320014000d640d80f030108041e030300720754002044001c1c0070504101c01112800b214480164210203903140140c0ca0a03400440207024200c5401c0540d5018646080007003200b00b2211035044020b0700c8040c0070140d681800700016804100c07005110ba88a04002e20307028000c0c0c40d80c5100301204c8007614103102179144280c0941c40400d030340b02d101c0d0f6003602c0b01041c81c140e10000c40701c0c007039400a5528549000701900755440c070210050490f03c144100d0340b035561804142d07064074419480100303620503a10001401c41d8a254940d41d4042650743d80d803102d0300400002042100e07000c2d010764 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 503970584 1250 503969334 503969351
    0x40b040618030308071b05010e071707081b0409140105101706010302041503080711090601020f060406150504060b0403060b0108011212121b0305160c0b13020607050c04 74
    0x1001403079600e01c4000c1c0403030100c1300490030701c45c0100600b400c0f85903c41329031085a00140c03030346400d40312000441000398002c1c4038203002c141044010422030800440041c074005d8a495a52a030712042c00c42000c1051544421503540c41da42c4d500464401c81e0424002091603070091900d9000b483c09880c07211001c481c000740050031011201d014602c81003c10040c26a03a80303540c0134403000e002c0c0c1000401981044840101c0010310b008040c10545014014044145950b181807000010b0040d20180c1994409404c462400c034000904c00da00070303449030000c84c11400036034810400c03281c15001150700034282240032484008010140c01103900031030041c000c60701c9100064402400030300403914034000d6a8862170101c0c2100302030044000c01d500d400c20400c0909c2d40540308a8010303086092001c92502c881405140c2e050041319000f10306010010408121180050f0141d80140302c020803ca00d09000680c8072801990711030303a51034014180d00d80d07411540c03400c0d544039481003410500c0750f0300e0134141c03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 503971834 1250 503970584 503970617
    0x20f07140d1403010e0402010507081809010506090d12090f1e0b1321080318010606020705010e01080604060807151e0f110c1c05150402010e0123040b0406 68
    0x200d1004210ba407500c1450359003040c640c0c2c21000380040050b07041c01320800020700010036160040c4101d0100030a141540b20482c0d040100c90131040c0d00c082d205107010b2214031807695595030740c01c240c151b200315003030400f0700084401e0768242c801d9840007221600c80780340003d0307588004410801c8a00105101c03e80a40c070307180c20000340e0080441030040c500400c2c40c140f00d00d00b041d1142e1080d114010354800440072659440d60110352003100d800089100008000c40b0410090042401401090000c0d2110a003004002400031082c031942d10b04110841d40411072645495120710b000c0c01460041ea840c60b511000d00c411103c00c3c01c2c05400004581001c0040d12800c00919010b1000443c0e44840247c0566201203900070502d0021110601515140e0059950b8080c0b0146102c2c01801c044100004070381022400c01081852600110f10319008100041c0c0c0d00a202121011090a01001944001404004503e14402d0320902c081c80010701207003c0b43c10708080c20450700250750302464250420070 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 503973084 1250 503971834 503971847
    0x5100b0415181d09120d0c18082d060a050603071707060c1109040309080c0d17030405120c07030c050102030c0718020d0f050a230f0406020f07140d 65
    0x41c1c40009100c59401c0c0a081042e83c1580303030030558007401c84020329001e0f225000c3da03038800d0700750044e45a620007208003440e0304405e441e00e2104c40d40445000b424640508640c4032200e41c1c52600d600340c80048200242c50060342030041c612a000102d07401880d00758a200300804c410359003240b003403046a00004541e40791070313601e4a204035000301600500e031030a83c0a40d194a80518215a02261315501e400789403110003038148940d0080d40d80d8001c0c60710340040b5604001d01c4440c01801056000310900110340403980b11442c4080050000e5900d03512801c045080c481c6041503651540000111402c00c0f58001074210280c85c002e502c151703109a40c440041e03a0320b2141b01c0c5100c0310f07508041001c000b10700002d002c000c41d00305107400251400b80c91070711400031250a805e080204030340c0c89040c8500c01006114203500c900d0000340d0070342d00d1008861100c1d50301100408241606114600250030040f0b184c041c1c4403403a401181e00e5440b50914034001081014222404041d803190030104130317480c1d10855 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 503974334 1250 503973084 503973089
    0x91d060c07061d1c03050108160b0f040503070e0406050f0f0a09021f09090501140d081e0d0e1c0f1b0227010506041805100b041518 58
    0x81403600c05155280006098010340c040780403200f541000d076034000c05100d0448144102134084c0b440561000c3c0c094211003060b00662015409100500002044641100f081e0b8110080c001e464810380305c40390b101d5208580005405000e2075800213840301f0410300700c1d03000700e02c0742c1c0b014071440e5203141e0800d4010500f01e0f04955002480d00c08246072042c80d50022807145d00240503991095510322310841800419220070002a40030442049003c9880c8903244c05041882110300c440d44038040054204082d08101400c41080014900344541568983c41520030640c259a51204504c0b005480100801007004030f85000e52840ca003245d8507110504844000b8503107800d041192041c6088818176000300800d2140c2c4100c2401c0d40c00b41c0c0d100719140000c502c03070b0340c00444100c0038202c05404031f420603070100e809054107110902180b00c609a101031640c00000001415550b01d1010072521462a44003090710039001902061107590141111201150703030b00d482c41001295842d00d841c003800391 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 503975584 1250 503974334 503974351
    0x2030c0f0303060a170106080d11010f09050a0b070908010507050c01420b0d150b0f041403160306050a0c1d061c05090c0f19090209030f07091d06 64
    0x603052101ca24040c1c0c0001744004e070700c400014025224440c040c64070f0121624070010a0005480004c4c04c0000d0182d03440b0344140c45c2060041d000716984507543d41d21041c0c0024113442d500c1c0c2c00941d00700e01c41d821010091041500a02940c24208009805075010304c2071359416500304410700b502009189141002c2050b030054400008140243c12041903c240b02c940c000e4020030840050156040006414031840b410f000103400641d041000c4030480045c0e10074215000144403103840c20b41008107460132140b0203412a903d411684000a0910b216100203922190024102005210140e0300a5100c1c200d100401c02a44101d29415105e00c0c040c074894807085008841c5c0300c07019080040140102110071107440a80015002154080c0c4004640c02e034400da0010090f010340e031a009071101c8020800390313130049550610030100961030301e56020301c011054000a0080340f6440820840004812580544420580384c80040001d0403056501002c0701e200d404141120308004140c0f05c0c0150040c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 503976834 1250 503975584 503975599
    0xc06091c0f21091403010905070e060a0608070c0206090d050a0f050118020f1c08191209030e040c0e040204080c120309130c0c020901030f020411131703040305030a02030c0f030306 79
    0x1082c85814620401131401d6425540381c010180015804002a10203020030700e03039000d000c3c41c003902442800c1103c2d03400501006001c0003400400e9801907800000703a038040e1000f07582c2c0d91481012070820404c0403002009449220304c12810300005090340d1020501c40c50007400180152001e505c00c0c0540000040c0d441650501c0e80505d03494210b0344c06001148490f01022000d40a4940408641101c65052100d8030740e42c8107801c909030b10950310408444442c0c0c0070004170f1140d403002071140c1c5050080c0381c0160703500d08040d50300c00c0c001c1180f0700384868000c2040d0f50301c3d40c84850154076005010b500c103016003e411078400c80e004000c41030324030503c0054500340074112000c09030400791008540d00b2080c0f1800c071281d80f0241c1c132a0310309140a9402a81c07940f0400c03000b8418441140c0645507007580400c410f00c880e140080240078100100e079600407032000109010080385003144110b6100070001d110010355942d080f60040040e00d00890040280c50002d1050407040703891b41f10490703205612240 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 503978084 1250 503976834 503976839
    0x150417031e090906221d190c050a121202010e0d09031103060f0f070e0a0e04020f04090b060d05010f090f020918030f030702010e060a0506120109050c06091c0f2109 72
    0x2060b500c07054020400e8200c40c0c00d0841c9620a1a082c6050821080d140411110102c002e0055410410000349014ad84001d03200303250010704010341c040340c0300081c8801c03e8010041d80061003508110508891441030328039040410002501c40880e80c0b0040340c20100c54030544050b8a008207400b842281701b80020300300d65071103600c001003100c0028a80030a02041c3d081000d215141c01c0d002501070410100000c2d541e05190040000c0343c001c000480344501d0910381071400040032140b0b02d6030868402d40d250000d51302d030343c90a103001d0500900c212401c40d182035070a5090000c042c1488084900903642c06240340c0328182c02e00840c41c450007041c500c651040101041c21080d6000655000d002c41c800050f450450300d0f170b1507082c5102030301d500c14415151001e2000500c0c01410300a9958501c80c003c010403061a40c1d26a1a40c594069940c451440442e90100d140c84000c119028540002164030b241d02c480d281110f040030b440c00c019104110404480c10080c020009400050340d02d946032100c0452 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 503979334 1250 503978084 503978149
    0x60906090109080708010c12021306030c05071505010501080601050c0304061d03010c0e011101180803060604080706030c1704020d0b0402030102190c05010b150417031e090906 77
    0x14400000c0300e040109101002404007401e220f0781c0003070103445c1d0010448100800001b8903140502c13a4400e00244100302c4560742705140c02050301180c520341000710780305007400416100b0780188040078003c035180e40c1c030b0300150140c1944a24140c0d0002d032250728807501c50318011250f0740200c40d43c030001c0d50300420081c00a01d024034041c4a1507403460030502c1d0b0740d80094003c03d09561300c901914021803030b07803020ba8000f50703004000f9001c4002d003200200508414802940d10311380003580d01400000b000001306400761a03000c2181c02514940045410320b9030340340c6005000b40002006400022404004c814844001d841139030b0249400400780c040781001502c03200350000c005032040744e03d990708104c580d04000c40c281a4015140781c584500c0e140e0012030a04900f941c0c65421580e11406000703480c1400304007034401b0f85094031540d80c4840e4021200744180d074070b14400d10001c850029854401400c054072688000c04050100303071a0040107440c0d042c00c2c080020300e641d440c500140c00c00440c0c4010305 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 503980584 1250 503979334 503979337
    0x9110d05040519030e09060f010507030503100305030a0503070305011e17101d1c08130c0f0b030105040f150902180a0f030201110706020c040b012c0f060306060906 72
    0x24028000c0d5241e410f60701c551442009000030084010444040100d08540b600401c8550301c5482a605030718204c1c80140002e10610074000c004040c481c0c0400402d1108002000d0000603540c44811a59220f10700c00c0c01411581007210074100080c00d2100200c0c43c041c114507586140044002150201c6082a240c0e100c0350001c08a0041070f4441e403200070ad20ba00301805003024460144091500602c07659094a080405040c2c50700443e89a21b10781d03040159005003420707880044004640d070017002914050503032000a901031007503605044004205050548011412100119010405500c0c811400c009990600f014000449800141004a040c4030380003014030400303510100c10241001c0c0c00044030000c2507003003c000c000303050205100310350700300c500100c1c503840e9100144206803404200940c4e411078405424010b9844420305610b41c2d000e006444640071303c1844105595a032a00d01039500b0800c603d20381e00c42c8451070b8601d00c8905080c0f049070302942024140902d428401c8040c440346 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 503981834 1250 503980584 503980591
    0xf0c1903020f13090203070e030606031005070c080f0d0b2e0302070501110d05061e0f0a03390e060f0f0a0b030907140d0201200d0201060f09110d05 65
    0x940003c010903165803203800b185001a0440020042c0c42e400d0056005007000c0700442c140780203910890034003005540000f0805119980b0580205442d81e582d2800c40e0b6494545034010900e24010030941c400801d05001380148140e150700070070141040300100901c46c000507103c2c40c41102c40404001a800c02400310000424007824007519050380caa48960071644041040200e966000ca0101e802407410b01074260000300480b0004152140010079500c0c804003a591584940418000407000c1c0c1c072a401d51900a64102d4900100c008131054000301c7c8150800720300c041c5030740d00d0300c000140c51605800f25081e00d01000c01080380ba507908042c0051f00607001c10040d4030014001901c0960b03502d04014901602c01c648480d502c80c140000460302e410403540000002002445100381c080d151016807555043c0c0901e0142030042e1184012014a20b0300750101030070740130340101201d4260f015048881140c40c10340008000565600000040703d2030010300c1000e020f41040750a8a207141d50304070982 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 503983084 1250 503981834 503981857
    0x206010915230303160c0504180c0b071b0620010501060905090402031005040515010803070b0601030f14011401080c0c0703030c240614010806030c0d0609020d0b0f0c190302 76
    0x140c85d140102c3c2071001240b0503821200e003020380100748070a05141c001c00c80f084121040080003054070b44e132402c03001d03801401191810400403601e0010700400c101300002440c0060036000e00c240d10703103c0c01410380302809a203040608014050b000c1c40001481054101e482d1a0780382c1c12943d080c58204003d0050281081c0d03410b103d035206681c10a11140300d200c1c0158410320060840c000d0b540000e00c56401c050b400344826400038842c0c040450601458564010340c00d10300020b54860b4072580034000d1801050380e22982441d0700009c6010f18004a003180040d80989070345400c2d0356105c5a21040307206080c0d0590554110f58010400240550072580090f8031903030702d01c10f188003800d6002c94072898903034442504580341c0344200040d00b003408201005480038a001c045518140000c02c0c1e69407541c0c0e113450701030702e613031081b140501003e98056001568010320608540b0440d0a01c0300b641e03c0280c0da880740e6484650007060004070a0404c880400740d956002d4240d0b0041094140c000f9009201c0144 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 503984334 1250 503983084 503983087
    0x105090718051903050304080724050d020f0c010c0206091009020f100c15061a07050a0321020d0e0c090702060c0a140307120f14061903020306070206010915230303 72
    0x4c00910b05201400140c0352440061079910b15203c1c440c190385200c40385a92051000c554584100c66000048540a000d04080582d4410200090b4001449203003a40100c81d4a0310117106201640030501078020641d10045038080f03400c240400003159603c000080d840140d20494400a0a2940d0040390284843c20020082c203241c0c1c403440a101d525050032541995507100902201104c988031614000380215041d040298598034160f94002c1c908001d02403000e8200700850103401c0340441242070b0308502003592600c1701288000c020b001c1080c00c6901c10b0040000440c203900300354050710f20440541d8010300740754403a01f07030080785c3d944161512070030070078080303082241d0042150086010310483d0740d031000c214818001c0107040320750b83d40c0314400050074000c401c0340c003c890400c081c0c0c20000449110075503c131020410010109550700007505405400f0400c041c1507000b05051f412102050014401005801c041c3c000040460040c1005030707074600320444440b01e0040c00c0f040403860140459 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 503985584 1250 503984334 503984339
    0x40b1c08070f0c050910140f0a0b040303020303100e1b18090403080703050a020906090616022805030307150b0a0f320a06120906050f01050907180519 66
    0x200c40342015403054803c0c200c8188100242d04105260581c03082a03000301ca50710710b0604800c207803a03648001c2007a205481c0d80082c5c15483c1e03194511130300207000840801d07940d9a81e900d40a9100c0d001121807009200d02000009a110500b0071454424007815070318a0500c0c4070f801e031104064000440800b0481070808042100380c50701c0c00514055402a103886541d8a4500d0300201a03131002800c2d140080c1c010700032800760b5158601130302c02800044034202e4480c04c501e6481416000714400c042d51041141ca000f29820080c0e03a01328001691314400251032544810074142e85e0302c07078660f004029801800c0b4011124526070700522094000504440e04030b03503611003500c3c4900c1e19400c4141d00c0c4d01043d0f4503868640c4d1820803400f101c9180329009001400441c00110311407101d100d403100b880110601404100303110b60046040ba540003404200c14100058201c44a240901072113025121000c0030a504c94050b82c81300c00c01c1c001d000f03019081641004e062000b004200d0030010710703003400703444007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 503986834 1250 503985584 503985593
    0x3121d0301060b1801020106030b19090501020d0b010f05070b2e0602030a0908150105010f20100506040924060302120312180703120c02060a090311040b1c0807 70
    0x300300040426216858540030011244d0300d00000d1100042d040d6854800d082001640841405901c100600700441c0031310380c0720b40385002038481418000c003c0e500c00100c4da100110700d903104143d00c00d070a07618421035425004058034075119900b4080c2080504900090f8542d140071108586107402030700a00c4090002c43d00e0302e81c1140c80d030b0041d40140e08046402030110740c0c41068040102003060041c10785540036040190000342c18091127040107190050092030602541c1010040d9010101c40c40694251041c040c0d1030794519450100c0c85410034020802d140340c18054a4105904299038000d0309002007010a10340c1d02c1c103204041021348072003000015a540808161050315200b01035079440c0441c180300320075810001c10b8190b25174a24402d500000d9070001d402d4044e44d034010f0005102590b007030410783d00e1200480c0b000303500500000e02251800d0b8032102c0305080328407d40054800039004010081500e9082050680001c54107a4540c505494144440d01590103504440c0c40e2034055144c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 503988084 1250 503986834 503986841
    0xf0308070203181e182e05040b03012007200108071119060203040506010909080f0d0b09041401110a0509010e042309100506130c11010f060801060b0403121d0301 71
    0x40c2e800c0520b07174200720340416141080069218285000e465000e428988001c129115010b0303180541d40d00d0301c100f070030b0341ca00b540241c0e1005680014500a02880c0c1049130241c2c2c0701c1c80b0112800749840300c82c204400c031703441100317158414161142c00d95965820404c03249002500f03440c2e07400303101d901c00c101e40ca0400d60301600c000c1d9005000160766481c0c28184140340c60b806038403000d038462400541170701080f400029540300c21400c80c078982d65103021511082c007500e02941101c0d441500003040c00b0410169810a025401c0c0d150f000748030784500d00405c6402d50003002c1c03c950116400b0810350f101e40d0310900208100080080c8001203180c010015144082c004104040d180c081e0340c0306103d503506041043c0f44030341e00c00d01d1041c046c62400c0b80118260744251401c00001c107891740454102940100c0c0140415851407008004031580803181c0030140403907128141984d464030300e0204109200404450070789402c4010800342d5003448008880c000030380005044150700d042189016a0340038013 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 503989334 1250 503988084 503988109
    0x3080d1d010e0c1c08030c0f0325020714040c02030f070503040e010f06090b0c010b030d080711060105100e13020c01020d18231005040f0308070203181e 67
    0x4000054a02e814142a807521411079110380c4a500e210130b880585001d40c0b800c14a103158040c105e40d442e5124140c02910038012410383c000201ca02000f0401400102200d078440b1003458282c1c255012811030b0203903242c24050041d10101800e103401d0650a00b080c0c0c0201c1e40303040c1c4510480e40b400b0079003075000302c02d5001070000300d54603000080c8c20400040c03034140700c0e17024115011031b0644d811b00d05000940112540e02c55480d03400380106507401c0514080d4403029043c400030b82134585008003000300516242c82250079a0224411000301d5820000001d00c1030705130b075406880302001030703440d950543d0404502594194808580e090b40020891180003403c8490b08940c0003684480119a18000b0303030b01a803000c4031045406121240c04500e0080c02400700e00400c1d00300300400c00c01100c2c43c50900c55114a0400340f40e0506007804200594101201ca14034040e070303214280c51311681012a141d120707100054450344000c00c0240c1507407404c00e442d803440450b00d0b5201c1505c810044045000c00c042e84 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 503990584 1250 503989334 503989391
    0x6091302090108031908090316060e0a150501080d0e040905160801090606050d020d141e0a050105011a18182e0b250c2301020d0903080d 60
    0x10034061145c0c2821291264441668103040ca002d190164421360f076402641c01c8841c42041c040001c3c0c5c103110203079001c0c40c602400c2005030740307c00f10b0300e0038036401c004007803401d41c58014900400040e54200120790300000c000c481c0da0300a00c02800c1c104200250280200940d014090781d001840f00c0508030203040028880c54001043c1d1900c0f07424081c0860301283e000e06e001c0c207800041c1c2401aa2800b00d00d000890b0702800700b20801c400c0007000d03031419403440f10308c400c500c80c40003d5100c0c01c4800219075082a1194000340303e20f0ba00d84e1541c0280ca1000d0803496100c000c140104692401e0001c0c40b180483e5001e0081c41a1961150400700c034441d00f03481060a16100400f0f100c409140e00c0801c5d4a01103a041d6150203c52a0001c03850852142c0038180f0050740c1444080317032407403080d015094407254100b4400201a610b42000e034440d030707040310010001c4841203038904072554000728407000d00c8a07640d203689000d1840c40c0c88000b500e5200300080031a80da40d480b10548400d2711748440c410040720b071 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 503991834 1250 503990584 503990587
    0x120513141005160806030a0308010627180b04063b0406022d030106050a030914010e0714030703020405090307061505010906020a1709360a0c080609130209010803 71
    0x1400640784034130103402503009821a81c0700d40e000ca50000c50160440b0100d240100c090b0104e480928402d05400c0e00750650409142000100e6038299110f90a4011809200b000010070301340411045840074840c10503105140241d042040082000b1040081541030206c026860540d12160403050119800c40c0c0c1d0b50740c0842d1421802d400c401e00610802041c0c0316101c100100c0701c01e5203031240014407860003080300029103880124800d400640c24607500050703540b400c150000d40300b8040c1210b6040804103106401001440b141c0304d441c1007801000140282589071300315001e100180000500c03040c3d007480304100351740c00a030007482000c9080c44641668180c450405000601c698a1903204500b194402038914000c81c0155801c59550388020800d19914502c50010581b0040300c01b041c150100d00120f0a480e04000d100400300095a03400110a015552503a00204680000c65003030700191480c00068890704106e010950401c074411554420a0029400940030000c00d03004907905410 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 503993084 1250 503991834 503991871
    0x106230a080316141f02090f09161103031905100518060102120a12200a020102040608070507051f0f020f040504050f0f16050403080a0201050601120513141005 70
    0x1c031300c510196210b840e07501034140c000003507a81c050761013076840c4800d1050b54006601200d40d0b880c8541303c507603a40c001d41851541d1400204090004403a55603210109000c019056143e45010049a200304410f103c0c1100503d005202a4018000100046182003040303034045055980c400c1899442d900c440980c0d401450a08002030800041d01c18407141144240903126040e9085240c42500c1c171008074000070000100e010b840810700340701e04c100a8510b8002103503031901c1d50640007041030703a10310344844003030f52108902141c4500c145c6c3c0015246411500d6a0304042c80c0c40712418944116a0501040e45030300501c00404036403106c01e00034410240002d08000908050094035486140c00d2410200c0e40b0f06026000401c0c07000a0418501850106044030082d000f8000c5d580515009006141c4030580302e00068004c28081e19281d012070043da840140081e010b02031244509004401c1b061604417990b914103d000d002d0b251480c036405001400e68121005214541c4903040d0000148940740 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 503994334 1250 503993084 503993093
    0x80c07230a0605040f210f0b01060e06040303173105060a1802011103070c1202010809060412030b030106030b0c0a080109090b0411120f0f0f0106230a080316 69
    0x3607a0390100060107428401004442507902209049a204150603140d0114180c048441221403920041031044800301c0b40b820b0005010f8440d040e10200e0312000d02a040301010441d2a000e54400240001c070303005145450031100c201655000462000d44420140011001c00000d819000003001030f544901c8600781409020040c40303800c01e030042000c008000b03089502c0044481c2c04000a0b05000c41724083d004030714020011102c0c459005100c2c952255210380580c02c01c0c00c02d41c1c034140d00241010000c902c000350046906070090340d110b400514034003ca0141034000c1c00c04589466450356a13000f00101050002e081c85100711449030300c03280c0e0349038285006804000185c200c8503149107840085030024150302c0015070095005410307a09414030303141c006200b20300c881c000d4564901880600240f100000146564200201c1d402d44448640150307a20b402c80c0c0182c800e030703103540192010400b01c40c1104201c00505c40700141050550b151500006455035024524040d21100d03030048100900 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 503995584 1250 503994334 503994349
    0x30303020d2a0f0203041701090b0603030c101a1201020307020f0d020601030201030b0a0b18120a0b270f0a02040c030902211903031d0f0604080c0723 66
    0x20048080b008009080c0c0d80700081105084801d05001c4078400c40b9068900820a540041c2040d0880200154003290300ba07000e48000c0400300e4001c44007001180303044c47e0110540308010548401000c042c10f2610b03c12015040410240515041c050018031540c0c807034a071f802414441c41130001d84d0781d00b00200002c0c900708565001c0821504008200b48040343d0200740941160f40900e00481d0f401c400d1400501e10092581c00343d940c91100144140d105d07048003041d921004803c41c0d40d5031110700c1d00f455890b254400044010514030030040003e03004260b110f8520301c1d0301d014800c42c461550440140038500601c0c4643c59050341d1204d001c0304210b140500556440004518003030003060740e16400300e2130a001740c100440954280b90402c1050310000c01000c120744814072150143c81e812410050001d280072105030074482d03034208800314903e5000074244103090000b0014410359685450301001a00208000754260150720700004d40e00031083d400d01d44014400c0c2c482002d45c54100c0030070042 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 503996834 1250 503995584 503995601
    0x3110a02160b070f2a14030c01051c050a09050313211a0702010908030c07110d020607080a0302040510110d0f020d0311090307030b0415050118020c0a0507030303020d 73
    0x4215240010b80f1801d1101c2486170f20098880b5081132402c12200e015403200790003a10007000042c0082c18400c1c1212001e1080420b6066448480c80900111900d100f4140c603042035460031403507019441e045074015a03106904520010b03080f0041d54525046510401c04032a2800c16914180320800d104c85000b2843d03c0c07100d00c1c030200a44e082c0d840070713030544c0243d41c000c0021001c2000100070034001c0d0046101260703c1200940d59243c200d0964071240c00c1f112040d141a1224005000c25040c008080d10100340c000708007501303000d010b65584c40194001e00ea20002c0607000c1c000000c107621001a080604025511100d08102005144d80e251290380100c0c1c008000e0715540d4a810a500070502400100c0c0ba4500462910b44590011380144208160b10b41c15105010f00001030100030300040340190f10800c2c1c2070702609403000100060310401c0c080c10341c00328808a0b40d450b80242c40d90041041c080f840c01500c03116001600c0710b5003800715950095010030340001d078000459000d441207900 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 503998084 1250 503996834 503996849
    0x70e010e040309060f170c0a030b010504050310050408070c08030d0b03010506090606130e090a05010e0303041a0a06120b15031623210d090b0909040303110a0216 71
    0x1071900d910028030440c001d00c1604103201c80004813009091140c0d00c0f8020b0500065a16003003800d18400380342c1c00340e00200c0c026001071b1400181c83d19940c490800c0b00c00b110300c001e006052503c440c4008078000c1c5006401250200c1040100c100000c5052024000411030039001d0340c1c403242c000c0205003e480283c0065442079142404000321903440c070706003d8105c0000d481d05502c0d600d8201030142c450b001900030b0031402c511041007100c072010000e081c15a9a00c100300901a00c42ca00c100c465490000360ac0c02401e01e00040201442281c62100050f403121b10040007194640d41c8403505640c2c603000550070345209082d041044a804040b03500e6802c1d11000381c0090602c0c1c42e04260705a00f000c90b40c041c000011f040440c0104c81c1c2c090f16125020403200042542022001c200c014181120340c410302d40c60580101070140d08114040e61501c02100d001c1d0003401d15000c51042001200140108100e044c503944001c002017004c5002c0c0500f204001c241c00400341e08101e0009480d901b001d82d4040325 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 503999334 1250 503998084 503998109
    0xc1302040503100b0d0b06011101060311181b0c03091203030411270a1515080705090105030106030b01020f01021303020a08060105010f2604200904050d111608070e01 73
    0x859130301d0b560502c000d21030f0070050306281368550304012140c49e01d414120540790340c00c046000c0244029200c1040c0c5400c811204200c41d44000c101c03484000174211043c42001d41401448440303502000c0c020103102403200c06482c50003281c140020340b405160408440194000b004110401800800102c001e02d0100d072148405110307410032004030794810181a454990180204071524850f8000b901292001c10081e042c1c035488050416031049400088000907071a0400300d01154003032070440c0c0c01c2c200d06a4855285a09200d010750141c412034441c18114810507100c40007040c003c0c03010300105603560080048862950041009849154021003902d40004004020680e044480c00c1150749150038049080d009010104090f44042d4840981402d2010108820042e0328040041c149803080b4400088508450034848032480c12503000b001c56020489a03041c070b502900c0d8001d0040c1c1c00008442441c0003124250f010122503600c10100f503405950248044a42d407141c02c0e01402e2542d0412 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 504000584 1250 503999334 503999351
    0xc0e07030f0b030c0103090c0e160219020a0b0f1209030d0609020906040306090c1203080a141006080c090a0b070c06020613081e030f250804060b030c130204050310 72
    0x40c0e150058004085e052507038035100c40c5c0c100880c010301350300280040c880d00032251614002441e03a05034450500c8006016011010000701c03400400d030030750b464025190300040c2d818401d00307841541c0031002d0045800001d01c2106280002c02480f1407250780c4c108051900c0b0103040c2d110741d060350405d41060780d2040c018070503049180c440006a17130440c0d80080d000702c0c0802d10340c101101044001e4004004103001400108180341c0c0060056000b414910340030401800300b000b1050141c030054401440c271001169081001610410b00782b5000110400f507980392a8200c0001200c0080c0c0e83c0c0151104480881d001050019075100301004050300c0c0060001403500c1c4074010f14031120040020901c4502181456800c1100c0c405140303800c0c003254010380eaa09101c181c0702520201111a1890102c40900000c136182c2042596807822034140c0350001641c9503943da210290007122940341e094401d1545803001681d82c410743e042c0341061000c8c0140c0e100c1c1000145414a41d1084c1401103003802c0c5180c8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 504001834 1250 504000584 504000589
    0xb04061a010c05033c0306011205011508060f1e031204210c0306050c090a0603060803250206070b18030415050702040f06150e0f030d1b0c0e07030f0b 66
    0x880759100d4000c2d01c06005800516403031222242011031041000c8410300d4017190181d41c0100641c0262001d032103512105000050040030f4070424060034110078500c1442038029170003004442d40104004120300c4208c015480400c1c0e414001c140740620a280e41c0590300303094241805480d07000d12140900d249424103090b0300c41c0403401c0020712911100242c404240500050b404004c0c003035540a8410b00c100d09080725149265040034040ba445448070b46030000348180648036210407180260082e40c14148810325283c2446910020045c40b1181c5441003801641c4c3c0c4001804840c0c4a02c0550310301d42444a41d21800006003140d207a0390b5801044103114440101d41136400109061501903600c801341e20114001d007458807804004c0c50f040020100c2d03150b62282d005400c448099581c0000b100d240ca00b0007920b20040c0d08425013503003060141209161240c1000f5080c480c0c590503280c000c903500d0342da13222101c100741e0103009c01c40c0000c01402546541401100c0c0c0da41e020715800c3c0050842e0400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 504003084 1250 504001834 504001837
    0x10c200a0302060106080a14181606211d0307030f0305040803010306020f12160e010302040f0308031b0c01020a03110a021b2101021201051c031b0b04061a010c0503 72
    0x80c4170a21102d400003c0229110380c21840c070100041c0034203456400c00410000c0c1a1780003140401d401d004842184040a40c02e8041d80111002c0c0d81d1400802e50302840c1020101001c20406c03840c4585606484003031480c50441c45103291444001140c0d00c0d581420002c001d4040e80b010320041504000038000490141e0b001e072030550b60820401a070700c400c401080c001e58447c02402c0b1070258000700411a141844d805841e00290b06030b02c6141c0044919401102244a50b02414050381445141403021818980195a2100501900a012503500383c0c0402d2180c0100341091042c3c0e40000b9004681070b0300d4080c1c02103004c2c1148203541031502102020351140e001c0040090f42844241c0b07400300b07036a6002085a03501c69001003011200d140405124045e600c4007060b1288403811030000035040c209100703074042404000c01c030305042420301d9400701e401441c80c07045c085c00c1030720198204001ca80f0042c403003409244200c01c001401340ba50080c0940041e5a00c24031030500c000360803c4804a41e0100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 504004334 1250 504003084 504003089
    0x405100b1c090b100305011b02031801051c020d0b0a03050a0f0303180309031103030906040320060c060405070911041e09020a050c07050d030903030c020111010c200a03020601 77
    0xca078010400580c000d401814203034000f5082500e0b500c184106420105103030000c3c2c07030040c4001d001026094102841d000004266903005900801800045481c070340488107001c03105240003468001c1c610f4030840750352800e02d07000040740e50000d001d841d07001403846440c2605400f030301d9091501d4610b8407559150030801c0300240950a024204408140c0b090707000b582c00c070f240d41a1007400d442c070034100109101c1c10f5001c01c440d80700043e80034100619002040e80c01e00c00000349002d24181c155134403100c080c4484002c1040c03040c6c1124481d0382c90741c0c8100141011920400c01400145005e0030441d2616216601840d0242e2502a10f5000030050b034007142e007a104103091030021404c45d03403901c0350140125400070f07007000e1000ca00e0300c0e0074079440030043c280c6503d070400311002d01380c84204102e05010030388002000700355911001c000080c098801c201e070840c0141050203181c0c00ca031541c6401d581d045004600001c401d05a101501c41990300d01c06c0d01901c00754000c0c81c044515540296980f001030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 504005584 1250 504004334 504004357
    0x81c0806010e03010605040e0a020a0905010f2c15031501060519091d04030807020c03070e07050903010606090824070c140a031e0f1d0d0813050405100b 67
    0x140c40b40c030b01034801350880001070102400400041d50032101140d00c8403186802207205054102e40000d0520175801600c1c181e40c00202c42d0b01180e850028040401c0e01711510048910600c48040000610200300440c803030300044c50ba0f48102d441e01410181465119003880020f0f41450780144800f65221007070310003000a44105000040b024681900c080b01290301003100c8a011201c0000301d21054098180180d12a449202c2f264031107403816600c2e00198500c40e901a400b154003003102d00d0114038a0b90b00640c603410a01d02e0035100c2c2000c80e00b90f624170780012010450409041101103010001840c41c0c104403401c0300d242d54003511000d03030000005042c4008004100d1048030074081900f41c0c1c000c840e580b800444d642d4401030701c2d0240081c082c201c0381012000c04148080b0740240109030307802100c0103d545030300e12124009621200c4007000b100058010f800010104002030040d40200b0b601e04170501032440080c80c0c030b000c02080d640001d20011007441703c403030100319a950a2f401da48444280 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 504006834 1250 504005584 504005597
    0x629090303090a1e0e0f04060b010309021009030507050a030c0314070b07050a0213050702030d0c2003280203031911030403030506030d09140909010615020304081c080601 75
    0x2800060700d140228480c26612807074101d800101c107401c11442010480c80c6102c04800203a0790384454884d0001201c81050184158000800140c81981324903058801414000303980c1089801107050010002412001f0074250242401031050820103840140012241c4104a50541c1c0d2140440c0b180c6101c0101030049900c00070400e494280199005030500813a25130306d4483d00d0404036520340c1c0d50501640141403201c0410400f208030b00840c0e12800da1130300114642078002c40300c10000d02e00d65002004114403040e402000310428052417800ea4031480c011602c608a40380c2c280700454100707990521000c404030104240310340100650f913100c0c400d4041c00d840d5140401c80340c0040d1080000e0284059400000c000400d40c02d03902141c042d0741f09030202c80f0001401e001c26124243da500030f0142d1541000300c0c81e2650b03e01254415402078001e0004202c860ba10324090000e0707110640000056000824240804001000401e100303140c4521600c940c02c03040103010b0b000082c040e00315810440d8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 504008084 1250 504006834 504006847
    0x80705030903011b0f020c0a120f0b07050c1b030715020a0503070b011e0b090409050f01020409061d0c12040218070e150c07060507050f011b030629 65
    0xd106071030151801500070b0026407911494407035a600080e43d5040800c10701145003000b107100003170400c02d01c0c0000d08400c61807030614030030340c81541c080742c1c044407224503407007a040c006000001510b01812030342d202d1326159410f14074042d0810260541e1060a01c10540d417040241d80c0020b00c40040310300032011118102c06403c01241440b00304080580a403000081d440200811010302e80d04940c0c11200d1002c03030f000210b9076182202402e100300c1e01460720a00120b5840c4c5060b5002801d031600c502c08072000450350b648900d081e6005680000251903035890104130042010020500c42100014281c0407450801000c0c01c1900405200e409407269600024046442c0e8810b00c2c141c94001c80c8040381d0b2403404140041400148581c02402030b22100031580380c42c01082c00f5500022100806410194102202250950003498040c0c925200b01003000c000c00308e0070321441d407034010a62070048880c60501030107000e4520560104244a692684c040f03000031031040e030707102103000c4607440565410 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 504009334 1250 504008084 504008093
    0x5270c09031923010b030c060307050702040e01091a090a0f03050721020f03040f0e0a1404051b010503060f0907030e100b0f040204051c050a0c08160f120807 69
    0x30a051050b51031660a4803050501c40302d00d02e518031204100005150b0a0b000600c1036003030b140c0d8044407035051750000c210b48865240100103580d0000462410a041a450b07400107001d60b00c036002d90a8940c1d41d1000c03401c05111000d5201c403880d282c1e55040c5d880e14205140c4255948040c0b81c0080d00c1800b0b110a010304141c4208100c61005070001558810890000c4940004000840c503d1015109070100c54072100c00c00720681d41211003400c243e03002245403400b503c80b0440000d000b0940b0980d200303014090b03540d082d004940910b0145c0000d00084601544260035030b6a003a84081c14045d0034070410001e9aa83c41c0c1044402d0015110100399403103010040c1c02400d2251f8000855019a40f01504038003a5a0701c082c0031040115004031036203403040c0620040b0320a40c02125006076105001d50f515890740c942181580b4401c000721290035800da112000b24608036000741c0c005d600506004a2031114603066071004c0c0581002c074400c0945403280c05940482124001441c1a50200303944080c0b1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 504010584 1250 504009334 504009343
    0x31b050d150905100c031418030a03110c0f0703052e200301151403272a040e010e0c0d0f050d0f020f010b0306150613060302030105270c0903 62
    0xc0004007805d00c01c52200320005406411f5848094660410344000209411400c0010460b030a0000000d1480e080000301d044000d4400240d00e050b18030800c00c10940c1200d401c022b0301100200002c0a40122400c522703256040c5800d03112951440c68060f4281d42e46494115030b84c000100e003007000001d4100300c00200d44800400f0741d0201c0b1081310003000008a405000900b8041c08c030080e80c400350b054005a00c1000359010659510842c3c0d161140214040c0090005070101400800100c41d05200704140008203844100381c8000340e011250085501030510b40262058141403900034403e00b111100c05070f03070714003e038481180300da44201c9583c800d0009105550510300d402c90700340c848190a004020340b0410440f52404014810804440307a5075106101f00e424240f0000c01a000c55101c1d01401d140c030424100e5180d03400402049544d2046c0e84610040c0010060f6032400b60f101c1d89403008200034a00481700b00009890342c00d031901262850b2a00d22a800030319044040e441d982d513440842d140 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 504011834 1250 504010584 504010603
    0xa120c030c0f0b01090f050405100b01020a08030a140114010f0509060d0204171e070e04080c03030a050402010207090905070315020903030c031c0b091602010b0a031b050d150905 78
    0x507941c040108600340210400001d058175a6400240300c1d07a0194a0b0480407035600322005000e81d00119684103441110790030040d4003000520445003400f500f41c0380c0092650061b01c044280e15924844410495500d196481c010215990144910284200081d111020034203802c000c10400080344a125520041580c03410880300004541300e0f91034400c4004222240000014284130310003050100c031081c2241c1d1580c411012029241041c940702c600d800d2100081c100712010f11090142c01c010704010400b41d88104030381030001c10f8500340307800003a00703140036500240d11050415111601007500012054100d0ba40917003c0c417511102010090002d004d000c0c0200d07414003000450f1580c9500c0000900f0321500450034101c50f0b64003c0d0900b80480d605400640d4000b441c0100150321511805508504090240004680c018501d40014014001504110750458460748040a80809000a03e024200669000c0b80c2c07040d9a4503440c0c1e099003201280003996840310340441c200041402107105 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 504013084 1250 504011834 504011843
    0x50735041404050c0702060a030506011b0f0c060f02030a05090604090c0203040911030112030503060f150a03060e09070b07140304060804110a0e06040b0a030c090203010807080a120c030c 82
    0x22901d49460994480d440e0460841d4466810300c2c001c1104050360710211903401d9402002d583c40c00303030715040a50140c08000e0602d030502c0745403441000880c100030440c03d42c880c450110602c0c0a10b0910f85040c000e006600f0103010412620300820300260000f00304d400880d614100035444200c81d200140c10b40c41503800c01460b10381420b80201d405030300000900256201c24100744907828070035076087e0940c00244075440f03580020000703450100340204015908120080d2108006400c12404204002c0e1b45600124800c04005031600c24141c0c1071048102805541c09441c1e890b0400c039031015912403282c010001503000000304030041268000e10b40c0701010440c0203803074507150754802c090013400c0122810b07148136440c1c0d4400c1002c0c0c83c00c241154140c0e02c0244908e10940c584d44c040c04010442a6001c40d048403141c400400030400d0303031200c8001092032600260f41c940c101054981055040d40c040c40e6185d22121844001078608440c09400084d14501401c0c450740f1800c0440344c1c190700c004040c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 504014334 1250 504013084 504013087
    0x31902031204060f091509230316061d0d08030c040e01060503040614060a0b030c0d1a120d0e130f0f0c090501020d140306010c1e02090601050735 64
    0x2102c1d6040500c642c2100d19030f483c0c1700401c9545929014200090b900c0740d05c002140c0380e8007400601c1500d0000080000300480f130010580020021034074148520003003d4140e0525201046002d80c40085c0203280d400300395020712140000b401142607c0c00b4004010b00f0386901200240c0038900301c0081d540104514805091103580d6110f001d00790394030544081e1420790a280080300f007600f0141045000b544040d104000103868010400c0d000d030006440c100d49250108241801480a80510001d4640401807041c540b5040342c100129000000101101d40d08443d9861054980101c000c580d05802910040c0c0390385500c507142001031211545024145240280c8181ca40300a0790042818000c00d8441c002c11680f182d0040e6640d0f00600071160006a405c094043c8484001000d541c02080c1818030030700c803080f035070746401c112003184031507880c00d1030007014090551034000e141c0f0750011003c0c2400351074a0b840d900c03440c04c03020100006807170b0942c0e244c80d20081800c0c1106100e003040c56030003030103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 504015584 1250 504014334 504014339
    0xd0609020117070e0a0e0108060712181112010e0d0c030c140c120318061806160c05040b0609010305340212161b052707020c031902031204 61
    0x284ca46000080038502611481d0f0b4080741c01900344030801e060b54048001800140e845280898900c040404603009598495209517800c1010300c90880310284031f0044030100346058001d0010f49003a14000203016810007012841d100d03000b081d066600905031904450301565810240e902d80a192001031203450f09240b0710260050104458284080c21200e14051541e18201580e0705d008865861041c1030034440c00000301e00e0700b040101a6a8100c0c400c0c448030100460004045820000c0400f6040203c0003a0f4010480b480840e1005040c040380c04104d02401100468030a0259031250350605a40b42c001c644000d42c01218509000c628400c940e0014811200d40710354070402440340000751007644210700740310400d0010795507e03500c07402d00100a0b40700350304c0301c1c00c0c9070184190031030280640800103e521f40b10340c100d096074401daa0104039070b20703c255008598402c0340107008004640004001150396640410502212014041c41007148034587c00041d081c0070003010500006040000c00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 504016834 1250 504015584 504015587
    0x3130f03030218030601060906121b020604020a08120301050108090109050105070e030d211d0303091609140c090102030c0114100f081f0e030a030b090a09020d060902011707 76
    0x14680490a160500c40043c842d1090560300c013400e00494010458040080c0300e140c0c0b080320b4034010081c4440d00400c0020840102d40c02c02c00741e1303002c00001170304100304000a504156032031100621040313009102d88141e140e01c621040c0010b000d618100b011240219a541000b500881d070030a0300f04001b003280381032010014218070458140ca50280c05130000c0302c00c0250244448000184601031840343d1006001c00c0d9400624500d942e146840303002e07074482d200c1480100080c620035403c035001490b50a045c244803041e072072607942c0701400480c101035402c90044d60790800c0c10381001c050303030705983c45480c1107006030308600036101030508562a01501030071940c0c50a6001d4000d01c02102c806000c69200c0000c44850385050040402c56445003001200c00c45507040e040605e0b07130300c140300090081c2e8040c3c080c0d070a56003c101050300003a2625502881c51500d1290313950490703101c46003004552102e0780030a14501950001820070340c3c0d03903440c000c00e590148106440300d007101c40c01d001a51a05440 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 504018084 1250 504016834 504016837
    0x70204050a0b19060c0b0709150806092203030e071a2206051b0c06040e090721020105090f04090507031103060408180a050307080f01200405010503130f030302 70
    0x501d80c03040e5007000060315411140610701c82502c0744da42e10416041c01640b40c1e207001902c007034681b0041000c82c00000419030700554465001802d540c1c0d4000c2942000410040310340c2001e00744108481445080301c0381d00c254201d40c20b24899040c00d0100b050001d4101081c00d182c000d034032814803030601041008000362010014941c2e84100d2014800b003400208503062001b0060080a010940c10803810324124010841c40c00a403444108070b440a034070751320210700140c02c41e82c403001c40c40b900340c014441c8031841072260354098400c00d90f003c4011a0352055042404408400181c180200050101c16a49a2140d402030104001d8418040c41c102c5250507950b4080c903102c141d61aa400c0345c7d01488030302d808602d2500854000b0041d90520b0780400344007048503124501154803954543c0001201d44003480f82000500240024216108540f441e80e420b442042d0b04151030300d00d14842c4125140351031707020740d0291242841e180384c80c1c0c0d6494150a6282d01990303000350800c044c18111a007010351640 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 504019334 1250 504018084 504018101
    0xf05120c0c0406120804030803181207060e0f031b01020f19140a0806041d0a0b061203130b090a0b120103110603102907050a05070509010308190302070204050a 70
    0x11410051182e503280c0d0304c60000b0328000002e001c158100000c0001c122160043d503046904034100307c0380c0005519041d8a40038116101000711440850b4000500c0020312030320001d0036000d03018150310702001c49030689a00c070390001034440c161601c141000f40d40d802d6040e644480c1c041c40031160354000818901d2042c1d80c00381d10030800030307111442880c0c0105140050321074484e00e544440c81203440c0c190411000d41039681c1c42c045450318030351031502c204078108503081516009101018140c1002424800580303902ca1001c589a4010041034803079010f02905c0208a541100141d501e0341520b40004004824a40c071507859003030041240e80052202d5440b45040300d125041a5403100685800e00005010880e200702481d480081c042152a17241403d0311014082c00100c0105071a0f90340451210381c010325002d903100d6010b051301400f004410800c8101070402120555055859550b030b00f41188034401d00c0d41c00486e141d200740501c290181e015650072a82c0100701340302d546080306a9200800440 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 504020584 1250 504019334 504019339
    0x11407020307181113060c03110a0c03060b060f030a0e160605030703050703060503100e070b0c010518010e10091104050117010f180f020a05090702030c060a06050d0f05120c0c 77
    0x1002c01300c151903601d080355883c008001c0c0e03400071035140100035103400e0031600c2c040c1d06000941002d441031107018482500e40501c1407510100c9603040d070a114040750358a541c446e0007005c0400401c00c2105401e000e59500425401001c0307010822003143c81e080250180a5526805590101050440d0031101a620960040e54100820364616000314269601072051507019003000807001c3d03100140d6007000068880c004202c96150380e4030300000310180d0090500c030140d40d5542e410300442640d031000580c40d11400100910280008910060302c440328001c411034038640d40c10100041000c3e40c101d520445500810400c0342c0d6944417103140070082c0091a090320b0754a0141740c4150a20305103d50781010214104145402c0e1480d502c1c22682d03c40100d050b80d11400c8c844c40050140d80d0b0b184003511032106a40078540364a040b02016150880142008c1c28442c18440d0900082d20358140301005e0784d4004490307901c1c848050030481e003005106444113404610001f110154070400281c1e01310441c0c5d0a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 504021834 1250 504020584 504020591
    0xd0302101a060301030b07030e0601080102090307091416030b09100503010c08070f0e060403050709090b0a0605030a02150d0504030306170f06060105250b010e0115080601140702030718 81
    0x500c10900500001199a0782e0002c1c0034070041c0040707182c160301d41754404140e080010307030103103004407842c0390000982c0959601c4e03400003070050040c1000e111420007408440028003076100c03180b00640c601c0c42e0003802d0400800a0300a003001c03240c40307504642c2d43c103074002d0310502140c1030070f43da20308900c28140281030196003009002484984503407a240e2086950b03585e4180e0340c00c48480101c98842c4091040c90340450140700201c04510144003a1000b464805000540e8005078540b0302100c0b90010107810249103400000c20164901140e640741d841e40c100d50140d44818581020903c50240c0c800c0c10243c20b14060400041582550010040d20300660440f5541c1c2075211040d551010014881c05403600907401040055000c1d5000c1e00d4003014081d0810800d50b034501410701101040c08059a1072001e5400400c602c80c21451841d001d4400d0031481c1c442d18803a2140948510006094181000340a00c1660020320510702681d009903802402d98420300da6841481504a610848101c0e036281b5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 504023084 1250 504021834 504021851
    0x60c0516031806080f040209070e120609061003030e1c24060902070804150509191e03020303070b040602130909020f0604060f0c02031c23250c050d030210 68
    0x1429614440e403034500000185070b86547c01e105000d60b0141a031024400144a141060307580c44a88002010f5084000c264070329000185500d0028050142e07854240c049809101280c0e00c03480490b50040e0a880741c10243c96240030704a203d151414000e451100e039680c0e00024556601820a00000e015406000c7c107922405500205d20404000501c260f400304410007c001d45941070f140207080c11305042c0e08205209021612007c030314400024101c4941c0e006200003c00c0c1d071080001c9498401c0c52541460940e80826541d2080f1080506150003110008081061035011241c051640880c0245500d070740300103030b2018201110007244207030582400864141406801e03282210071681d54101c2e0b1025028059030381f505084c00a0f41c0500a01801d000b40540003510811880314545c1d464520032001440203000490364071405210010401c940402c0f0701c0184040e1aa40c0e84000d034080515185151840e080110356000c0d54110040000070b40c145500460380c201e04500f910300134800c80e003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 504024334 1250 504023084 504023087
    0x304060e070b16060e2509060b03010b030c1605300712120b0405070c050c1005031803130906050a090b010504060c2f031e030304060c0516031806 64
    0x7400f0010b0840f00103500e00500400d40941084c2189a03504055880b98100d0985800c50150f410b480c1490300355a00c1c40410004010f44924002407d056000900b1035040c058003c003248005000e04580f06c8010444100e1510a494640d05079603000c01103440710307003080340d4010290703a9102c400d200b00340309078060901c810307044c0d000ca03000f003640444401034a01c000001910101042402c1d861141d580702c40086050700c80c0d20806000e4120f90300e07240c0c0507211384d00d4400e2402400b044217900510380420100c070482c2d08002501e0304104c2842c4c110704c0c10300034240c0c424950b01401d089211000315200c40055080d1555000e06c064443c1610312400013610390340401c040d0303400a00e406000500400040040620402880e107201e842903040400d405280440494502c11035156034410b4107917501c0c02c02207454100b1005040c01c0341c0143c178074001c0c90208071180e286d000080c03016215030381392a050300700980306108941d880902c01c80490010040c03403c00402c1d848101c615a520b1040c40d800200340107 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 504025584 1250 504024334 504024337
    0xd090801200904050714280201020c2112041a0603070b0f090d08180f040e0c0d06110d0903090509060d060b060409020a0c05010b0f030d0507170304060e070b 69
    0x5600340d4030051502d000c002c01d1000601c0001c10040420560104d12600005600010040b950050307a81100e5014540ca4209107080c0b6608140150ba20400116200a10100381c10680e41c0c0c0c2c041c8810b4043c142001455070611501100d803c14103a800c0400040146c0501d080781e901c102c030b04103070050f9a12002895600c0c140e030b009451400f2402e006400d0241402e000a0000310b03c05821092100455038070b41c015500000385519030441d002d0300e592242d05201c90341c40341030303c000c840a00c4081c01113122503840ea1000c9100c540241090b140b40350603c100f9400030000341800f07602240d9168005502e82c4001c00e948101200016000c20b0002954500841e03024058480140002d00303104490350f800c40145200c0071015000401440006055501c91014000c005095141d03422a05810b00e0414210f0700148102c83c4100c2c01c1000ca2141a1800560754950413a80c0c01c11542e03405260515000c1024083c0c428119140000100400c109190300001940d901440841c3e45e0a501c9202200d06da = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 504026834 1250 504025584 504025631
    0x807170703050f0a03060504091218050f090619060f0f0305240f0901090204140603040b1810180b0a05010b16030c02030303131208090c0d05010b030d090801 69
    0x5642031003040600f800910090800c5005800c000940590b03800c0070806407128090f0a03154100107420307403079005400800d80d840d10714001c2d4103450110705140000b0200f40380401064090202203002502d103494402903001d00a40c8044482d10956036010000d100801243d0302d4000a881d07544240000c1d0302a004480c012002c080c480381682d031041c0080c0c40c180491181f1180e00015009082c480360301ca01e04542c1c060822008050703925400d100c0d45034103168585510b1402a4020403c210100d01c002e40c01a4010761a0b1111603e94420070303021515081c421900040b8251825020080c0c5060808440d04560703c5031080b02d44a58a080350002212024420a6520603040100c0001c49003540c1181580038842e041c0f03071000603015000b0925507042110048011242c1984440c140850b514804c001022503240c41a82480c04c18101c0b07480d005240865801001494a0326041190a41040340c1d08600a07044440c01995508020b060700ca003442402c8007546013164400e01c0c00c900c44d088444 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 504028084 1250 504026834 504026837
    0x41202070b12010e070c0215040602120403020a030602220f18050f0f090a0b0c041e0803040311040b0d0b06010306060c0506011a12010b042313090507050d0807170703 73
    0x82caa00c0c041c45034100080090041c02081400d208680040c0d40b1030080d00700090404020b40d494604288009c2d15002c0006010342c021a8184800c20040c1d5a0b45455403e82e5070084026844045e454081403e05080d03104500080051001c042040a00355491904039680302c080741400a140080c0d110440301c060710040c1e8007501c0c840c0000d00000f403007250503400045600841c0c23142d070f032113031611070128000380c54101c06030200003820003429001c103100300c03044035660030340321245d600d48005155680b08a12004102030120b80f9104220341c1d17180d000c0300b000c51000d402200c61820b035240411090790100c41e443e0200c0c1c94588082542886054000e030900e900c82c0c01800d4903400d002c0086070410b01140f40c1c01511004002e001e00c00d19100c00b81034001d051210103240c881e030405803104948403040c0c91002d0309035601c200e207183d56a41da014403e81101e0000c03001030561564201981400d145402c1940c006000c400300204004004c4010900345000b50309100700501d14503590b00303d5210384c02002c3e0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 504029334 1250 504028084 504028117
    0xb0304060c081312050c07090617030a020721060207030e090928150903020337030b01030b03070f1a0c03091309020d03050c061f120218041202070b 65
    0x1000139007260100380005486050050070502c03000310140c508a41500300303030305944c0c540c101081000601e00d812155a8004005181094901d1070029a21340c4a0300c50441c0c1d071494402002e0046d007071405144e40882d0005d00c10b640d540c0c0c490801404c0c9070428480f45005040c42c10000d0382d4903a01003400c4030888a1010006d000090000c550300c580d0b040940e05440070081052080f0401c490303881440c1e85544260003a64071110100007480f03503c2130705298441408070140b6074010b51045500b5041c40700f01c0301e0400142400084004a0042410001d499090702c500c240100d80c144c140b0740e40400700ea1607450361002500d484c484045c1c4501413407418000b0340e4000e1001500300e1400720480215405410700000390800e8540006408040d030502c2940400c0001500030490780c8188070590380007124010b0004008680001c0b003800246600c1a00c8580540a0760102156103180d4203031007000c403081e4809590705284c10144040350402000401510845500180c5040194161544004a10200b5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 504030584 1250 504029334 504029371
    0x2061f0b09040b0d14121602061605010f020c070801020c0303070c1e1b0503010504020306010306050a020c0f070510020a0b060603040606091d01050106111f150b0304060c08 76
    0x800d40da401c51180e9503803064541e410150107840e207400362010180124481e2082c85040c281c0b5a080c05c0f2100307018803900c441044480340b2200607900b1510700550669041d60b80317034140403101142085c0e200004066500700300c0000d01c141d02540143c62507108540039100741030f5484007024201d100f41c10000d40c5503041800010b8046024800504116006140c0000b00c14040c0000001d0f00c0c0600d0b1007281d08030700c11008407290790b40000c0301c5c5003c1d00d0240c00801182c1400d800007aa2004144002010075840754000380a40350740d6010f6607400007880040310601401084403d407500b4960143c3c074000c034400ca208440071071001440d00d040c1a0080ca42d40d90344c0c1c8628081c04841d61005000b5100301d5103640000603146240e108045c500c09c607603490003c0c64030841881509545060307100808006a0046400c0ca00320041018003010743d103000d00c0790900c481040c04002601e2444140a400c00e1120000642140031a00a51246100382c0042111081d0b584003554003d8081e10740c039280916098a0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 504031834 1250 504030584 504030599
    0x702030a0e0409050f0d1713051506010224011703090a03060b042d05010905071209140a032d0c02060c121314041a150705010c080702061f 61
    0x45a03042c050810380784502011040b2501e405046c926500015600680410800800da0040764002160700c4004040c1019512429034032950340214031082a41c2d003010401c0c907030080100309608900c1d40c900d1620342da00041c00c203141482c01d00c00c0b40d103100100e4405903040c0300088120380080d28010a030040c40350460f211302c0c0c01002c00d20000c40c1c1141d0340b80801d40081c8440300d1a1414500708018408444840d040c541d0196101a03010015080c10070090001141d08044002c802a041001c0040c030202c4a0501207961202c21032030340752a015491004007459400028100c405002d01c03142169644000c0c42c40a134008401c103844000b42e07c001d050001850031600901c01d0b0407502046030522003003d00402c40c02e6001d500c1036903103240307074400400c0340e601c00301261005207008940130400c40c8003980d80c038044005840c0509200740444181d142804510400f0380f4401c580020080103040c80c1c0e180040e04000d0203032242009071080b0b40008800c200d00c00403040c0851011045d02c2c41c02441c6c000f4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 504033084 1250 504031834 504031841
    0x60105031f02040b030a0c0e0406060207090905010f05011205061b0409054501020906040314070306051e161202090126010306110315090604020904021209060702030a0e04 75
    0x14103905540c00b003000240281013800554001e18500c0800145400300c91310150122640d1440140120308090b410030041d6004124032045a03000c00002c90350000070b15001c0c2c014014400000d03500742c6440300219104000f000e100850a225070200c40c090349444220204d03000c0304040740e80030580b04002c00d00c90503480d500f00c01c2e000303010b040c4071121300c0c000401074040103000101407402c0b191401280c2d441d0707854070041036841241c80d803000710b15140f00c1c5004514a0b200b1404003030302281c800d10108010704410400140110b81141c1d00300f00a0402540341ea544400503490b29415507807801c0070460301d1042c02907140899529803a0f0441b0190841c86d10000394001103c1507060105241d400e0b880049004040c03500c2c1041c2c3c1e503000c8129811442c0030401c03150703c5460022614000e00800080343c040f0364042d03410400c02c444040760b80c0d0b1940c0c009000b92054040c0320341c101e4004036050090840b41601607000314040e00c00d40d6070039600d040049a4074064615050000b49003a001459241015072 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 504034334 1250 504033084 504033133
    0x60307030f080d0612050d1812060908070c030b010e0604020c15180a0b010e101a09210d020d0201050606160c05041401080c060406050a051315090905060306010503 72
    0x3d40402c84a666000440003000c02c3c00040d213207030300140304194a240d44041e1014854000c2d055519140d8100000004440c484540050040d40d48480386410300c0801e80136100000d0b40700ba100d0741d84540341d02d40860001001c0c8281a90f82a806001c00c1240c40c003070003512640944c510003411005e1842c140783c90759000191000d15403a51b1030700251204c1c8400d008540303680e070013003203580c207154035151032010449070080c5520030342208100244803000665128040005894401584481000b00010229040290101d10441007007280c602080380210711003a480c0e0740d03502039070a0002a41d4084c0d003030b1082124040e038842401c100a501400e0354010201c1118000c1860031701a507250000b040032500320358150b5800000841c010002d03040c040104441c81001660014101441c1c800c025245000702407a1400b4854040360380120f241050b40d282c001011611a55640880018070241c155011400303140740442c14040042c0450800007040c5e41203a101900806512010380e000007080001d00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 504035584 1250 504034334 504034357
    0x30507030302033105100b030304120303060915031a04022d060a1106010b0a080a0e0c0d0c29030a0b0d12020c090906040b010b0309030f130e060307030f08 68
    0x10786990703000d00b1801c200d84c070121403031868503030308101c2e07410b1451034082031032902010a81000e4004d00542c034040b080d41e04896440c0581254105149401d4000d00f10540140e24060303d42000881c100400e42100c50860f1300030784451a24a4903148080080c0008032406500300349240710302d40ca00c2107500d01d80030381da05078442e0b500f5100c812180050035540c4254600000603c10240001c0311711014000e8a0041101c05280c0346040c820450260000000519400c4a5565201505460b00c0c00340b1404212003001026886c80304403034030786540c1208160040d81400307101c6c116034151020305002d50301041c01c401d045007419541e48a00100c0a09400030342180c102010041500c001440304802c140d00c82c54540140c03004009000600041000080c5490b103140d00c20414400410440a1000c0c10345d210300e540d0315030fa56103e00710035266200c2d00d5086250380c0c400050700280c1031511584a002c0d6505546144219101c40c1c04050b584c0641e80805001a8a500e0302a40000c100d03100508031070400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 504036834 1250 504035584 504035611
    0x807050a0c0f081e0705060c07020a030f060614010306050604090c021e280f0b100815010e1e0a050a1b02010b092a0f0c03041806060c03050703030203 66
    0x955441821403918058120f07102c2001182e4402ca80302680c410307554600401e030b18136003042c0c2540c0300c0755641d40c1c0c00342100b50740101c00592001951110380c1c1070707005560030413004220348806140c8031006024a100303220341d41d901e5145c00700c07080d80300703004200480e880105507074105030524041100804120402e0410b52040059840c1d00b00c00d868003250210041b58090055401125008034100046124440c02006924070303000000f040d00020307031041600320b4262200c5036202d2002e14100803540c0c00c030302c05a2180781c0d01246801103a41107141a24910580c58420b40c032003015201c40100790110000100c6400000180e40d400304d41c4c03001e81d105c2518140031529001807108441c01001200150700140d442d00d0306003c8c1c0c0e0078801000743e008a00070f0868165000c1052101820071510400d281c2d80c51400584000003070240d00c103456820b98041c0a0700d546698039410060b07100104200740c01d586080010000321203020322640c407007181c2c2540f05d188c904400b42d41c04500a500080880c440c1428 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 504038084 1250 504036834 504036857
    0x6030c13020d05070c12030c1e021509010c110f061f0b0f0304021804020303090f040f050106020f0f1501050d140a08090f06090d081c0e1c0509010807050a 68
    0x1042d0040c3c5000314919110349240005504002024080d4015010f0a150524000050482d442502e20a00c000d078451203120703940b08508100d050460000e80d25080407602414880041010340c80141c1004998682d0b108019800c0001502c9101803240726030303d5005800000c5070084510045031040c80007030110301a194603800e45880c2c0350402c1d034402261000110802c0308609101d00b00700440007a01d65071404a240c40c2d40020754030b1086c922850302446600c01c2d402c401c0d403600d030420b034043d405016061016603102e01c1c0081d40e48407002e518901c68801c02190503103a03000400c2041d81100c0d0209030b40b0950307003400244044007052000440b86100804054201400d0030300284c03080d80c0c40f640005a640b142b01041002111000300503a11a17a401c000141d06a900c00020b43c00d01a40304911a40341e2250385d001411198402003000c9081e4200303120341208030f001143c1c00c40c80d01c000c40360000e0248801c41c4202c03100d009120a00340071524440101f43c285020714058842100c8034a4500089035 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 504039334 1250 504038084 504038107
    0x2030703150b03120f072109061103161e080d0504020306010e070e090411060304140d021b040b01030b0d030201020309120910140408030a030614091311030316240506030c1302 77
    0x4104054030300000c8120308c0500109034400340000d0301c04090f100850170481c08034001442c600710391600805803484010000110782c0d4041c00140301e036401a0202d5200c1d001800c0d030501418084030101d1080c05030800206040c440180e0250081150303540b4a00103110304410304c03504202c080c2040d201c90401c0342019a55540321320045209611031924078004200e81c4894901d40070400360300740b080d900120401001c0c02c2d0303440c83c4003c0d500d808480110354401e6603001a8003c0400d1440b0b03076081201d082300710041c160150019405048140200c034807541803810148101c0c052a41c2e1640e005283d004906440e0f842861000c0114030704150040c0340955a00072286981d020303200076030109031244c0302045040040e19a5000a070410340701d0390281d14000003030000c50400040000c001c550300b8506180c80b62003c0041c0d80a88076a0354541c205034050b4242203024024015508010000284251580300c00038060b01e0b02689001e0300501c0e424048408210510914017a14501d603a400d120a00550 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 504040584 1250 504039334 504039383
    0x1050d150513080304060f0b060a02030d1d12120109020304170d32060301020708030115030e01060603061e081b060909130c08120406030b030a02030703150b03120f07 73
    0x321b00c03580c000104110795558105c10f4070480e03005544155000e000100c00c0c039401000710741c2e101c0c0c0305500008822001e4103003034050030310104845410f8840c0c00c02c21300b4080784440003015209840c2d000182d2903030742c40700140207078441242c00614004481080b091000c00704005402102030281000c280715410040d0650501980965031030a200c00f1500401134042b103d603102d4029500345c00951a16980c1c0e105c0c1d88592006102700800583d20f02030150b0058480c0e0710505842002500901a85507100d100074007519442c040e0100c6064504014202450100001405c58480d54090a903042e510882c421440305403840840e0444010000c0c91456541da800d91449904070300001c0d040700da55070418101000c0150000c402a5000c00e40208108400d0030036502114202d150110b00103401d9800b1074103000a08a00075018490708c9008070030002d0b801502d00312605019410481c200c5d400c1c0405070340d0401d034080002460810440c2520050500d8004e08004c0d000b500400c0302c5242c01036408961 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 504041834 1250 504040584 504040591
    0x705030918070f0503040b040308092a0a05040b031b060715020a0f09030506040f061d1b010c0305043b22081207020c210601050d1505130803 62
    0x1064030704010094107a402c800e0003100c081441c50858114541503490601a203000380c0041e081c001c8400018242503010081c40e41604000103e10385a2a810381c03818008030000e80200d1b1003061f00e03101c0800e0500b0315200b08107c140c1d0040041040305510740450640d000071051441c0c00c10410001c450200c2c00c00028200c00701c045280059a415092074000d10400c4c2ea15000130030406480b03020000b2603030000744d543c0c115800c040005a5107596240c002c00030941c03161900c6400304403840054800d1070125000e08402480c800b00f01800c012170b401141c5402d404000100411000c0c0004c0c081071000410203954503015081035081050300440b180142c080440004150303000c81002c2142c0709941c0001076482c01d121220400c0034408503a201d80e050702035020448031950305000000c140382d10801c9021001c180c0134120b5881d02120f114078103030403001028011420300c00c0400005090820501ca5000603400840901c0c02c0416011110090704000e013400042c0710b900d02e60703100843c0c80302004600 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 504043084 1250 504041834 504041869
    0x6060212090306161e0e130506100503062d0f12101e1407030b04021305010e040605040e0d110f0a140102070203061503010f0501230111030a09030c0f0605090607050309 74
    0x800c6c0c0880b81c20000e40300c079900200c0441500386018442d80392100c5003d0746a444180c10502c3d203075503a81001c90fa92901c0c8841e1400c100c0c08100b0340c54201d10800020102013131080d651049003044404c24010881d40b10b075041d0500380c1c0f007900c46802c0c07030f04542e0114001c40c20a03c20b940103110004014001d4513107040f45e10091010b54400e11852710f805210b6800c0342c040c19542036040050141e4080c001303140e5445214180180d88800b82c1e00c6564a50000d0051709004004110409400c0c20b503981d628103140088002c5000f20220101d91280002e8004a5040c06402806019500d135a400c071032500000b82c00d15503640a01000380181c1d402d009071740c410010312600c0b0a458a0040c01c06003503c2c01c088007008502d10f02401444058a05d00c807c81c00c10200b20507101500b0207a0004840004164045400f81e00000c40d00c00c454651006028040382d004e03040c0c15640c1074542c1d580d6016503255209a4002c118100a18581800d0540c05469254015002d481c1010348107008601515000d805001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 504044334 1250 504043084 504043097
    0x6042105060a0222050102060105060901110a031d0f031c140f0a030b01030c0806010e030f0a150501050a211703100602010509070b1b0705100306060212090306161e 72
    0x400402c07103a02401241e80c0c0e018109900c04d840d00e400030b500d031901800740e9070003901c1c005440d000c2039000c2e40c0388510190752203040311400c0c24142401040040c103901c184030711042c0d01304a6135403458020044118400000c0140c040085101c40346080c0294601c2c5000a00c400030991110781e540d03810107401304003e45100075a030f0341d014040003412070300425501814940f0340410505099403140140703a01c0507003804c0c541507030b411890000e46013031001550141c42d407186844410800c01c108554481138945d91009000c50790720b84007006100e2045025a4098100803400c00e205501c0500d826880d05016031241480360452134281300040e8002c954428201070021810800c45609205e20743d0300804040141410324140542c3c295140b00c0d01d03074036100c00c40c010700c100104481c060049400620300241500007020042001a02400c0da5101d0304000d8000c009800202075011021601618001405080b0304d41d2600d00740742d4901e00c1c0d801200b0420140700d1181c0700c0c2c500c44c2c0c0c01000350320000383c4a05 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 504045584 1250 504044334 504044347
    0x6030b01080604050f060f01020c12032d031f0f1212032904023702011103060103051302030d230a020c011b150b1002060606042105060a02 61
    0x5003003001c010740864020340c982410080c0302003884603902e4001008550104ea401c2c0c5880040303203040005614070f58000304560003038840a000000925980703070076603c2c136000440c0fa0602c07107003040d2a5040e00c0b1100b83c410000104941d1019000041028000703015503002d64a9005540c0e00443d181c1000030008102c44070902405881c014042280c4494601440001e00d16410f00c117552038030349604115131040c2d1240e65a5030382c40c1c0e01035410040c1069064030185621590b080041ca40c0c14800c90b08070140043d0500c007681c8113010f0f082c41444240c0c02c65180d61140700c0110b0007424001c0022000c85500e02000c00143d405000d66115070505a9a1403241da5011600420151590b0640c089109040091000781500403558a00c41102401c1c114451034114000d400300c0b624129000309104850b00f902d1014021660008015031000c0d02c1d4001070007a80f4000b0b0340d94100c151031107030780f041d010301c4100840060013090341000d405100d4000303201200daa07921031400c2419243ca040715900407969 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 504046834 1250 504045584 504045587
    0x1031506030b0c0301181a0d051c0203130e13151e05060a06021501030b04081e120108010207150b040b040e0105072706030c0e120f07090b06030c0d0e0706030b01 71
    0x29100b40345500c020011502400800c01d035030681007c0143c002c004c515405810b0200520250661a001809038040c002c80203174005d4403075100080c05101007410840101d5140700049489216416041141d600981c00751661110560003154141c0215200e0701e00e03c08840054001407035140400b0b00100d40d5003081010800030346100d401c038404540c41654601540840c150702241107075080a54540c032600c440c140382080340724520010f840b8075000a0903c030883c241c2c0c0010000c09008030008400ca988442841d400e03803144520141c0351000a0000081c543c0b119886491420700017040024611921004201502d00550500405941d1101080107143d0000000c0a002074103c03101c502440020015001d2441c0601460701056690440069214025004e540d00c0e001c00400c5400010050014913035107a40c145d0248055015200700041c224456000740248504000d00590641d581c1050107045604408406410161034003101d59a4140611260707015140a6401040f00801d0000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 504048084 1250 504046834 504046859
    0x20c060609010b0a05070f020a1205060601200a150e0d110c1203030f04030e0a080609010b040501061d04060e01030503040311010c0b062101021c2301031506030b0c0301 74
    0x1a00d44043c200400c1002d2580002115806540324079860580001d9001045082c00107405c000d00d2129903000820a1200002d11144203030b800f6030300d0308034200d8114200040240241041c1f641603101c0e4002c80d0020b08524250003004c010107100280c00d1b007203217940703d1902854200d480d010501e400c0405503c0c4805100080e10302d802901c0858802d94540b510365905e1000130300c140140c0c161800490200b40c442d01e44071f458000001c1141007101c0d1036100300c0d41c49a030705894040c0150710340680541c0351f00301406018101c98854070f40c01542c218944001c1a62480002c959a04c40d940340b038042002c00c0355010359030185005400440d01c40d4254508001103030f0003540024103004052002d0700000c0c080300b04031980008181d6425142040448804559001c1960a0051540007060103401c0c0000001d00c1100400120b1040c002c582003404160340042c040e000c8031744502d40c05001440801d80c0b02c07034800c0c050121040c00042066903a180c000d01940d055841429450000004200c2a00001d1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 504049334 1250 504048084 504048089
    0x306010c230c150a05160c030b0f100f0501030c021006031202060a050c07060b030a0b0705130b04050a0303050a0903060c020a0c0905060f1002010b181611070608060d06020c06060901 80
    0x1c0c0c03e9201c1101d109416442d42c00350400100402c0400240700c000201c4842542d064594444103a13001d0548a01d40340c00001d80c201c1d04641114109800546d000c00140000c8040b9101c003100b81a0b99030404004501400e07c3c100014294030401c1580d041c911503a00c500c8000f107014605d014521001003c00a080c100701070a41644241000c1c248800b000701c0008580155a20180004441c043d52000c41d00700082d1120162003103040b0000c10460300e8100c0300610801e050300e0705a294030703911103144d10341c0d41c043e501034190000700700316040c00000e003e41d00070b10700680a030910521055880e075561041c1c8600c1c204040058008151071000c00201d000d0f0400a89071608040c001807a0031004240340c6402156803e06c540302090310780c104c440c003c2d03004903c0040068050810003041c200f08a028110550341d01d08181011150005581d02c15198034055555030380190680900e0b141048500135800381580341c2c40b02e41d1001c070b9400114107200400800b003c03403001e000540380c0350080140e4104141d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 504050584 1250 504049334 504049339
    0x1c05121201231306120b0405060603030408060a090618051014071706061c05040c05030a020310050405030f07030e040e0318010c11100206010306050601020d0f050306010c230c 77
    0x106015440301950009500d8510b0940f8182101e500e03800014001e0400d80e030002c4150800448003000348440c2e0046e0a1056000c0c100b00c801f59140e8a0500d5500d110310300c03031a1107941001010498101054000d042000d00a034004241d103880c0c0c508885c907038442070201711b40c1e5a00c03440ca048880c20490080740f0700300152110700100e5290a06004c0c0100d44614140c20b0481010b10000709156250810303100c2d4a0341050b410b24940300280341540050000f6501522640c040003400107091038001408640150701038060080981c081450b82d0240074017910480d140d00060000c00901c0c52410007500303645010340e58a04c81040c03400300780012941c981d410503085400401c1321182080b4403a07080f0010310b07400c1c6004802410141032020321031f4101940325034052481c540c0e40c02d0042d030001d5058180d078010403040246481d800e0040e41e481c0007101c890004503038012402c2003224003034405194000c0060404140144866a4051a2071900d04003001425030326a0a20190241008404240c0c3c0c4d0a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 504051834 1250 504050584 504050609
    0x80a1206050109121b08030a03150e060d080a090e0c0a17010b0f0d06050a080723030709090821370b1309150e010b0f1c05121201 57
    0x4103080200003104c04100944240c0301c50307a0945015911007030078802001110709494990040900003001307001c800c500c860320980071b000e001c90240c001440d07160286a0041c44000c0441140d40d03004255004071801c0001c0c4206400009243c900585182c0e104400d106a002d42d10b09044c1c0b4068280000c2200014100d80150b0050110147c120f08032880da1242400482e00c2c0c00700e103541880902129000f541d08845510b5001034004030000760f080503a107141041c0c1c0d00d0303804e42000c1c8400810112034502d1307255108040400080f0b0484c3c0c44640100e0290590a203803403210401e030b0240e1025080c10084885180040040001c44e204106085811450482c0d032003207a907000c0f101e0003440398448220895510141e4059580e59441c054001342d0b82a64180f200c00c441e820700d4080c041008800707202903030401070000d43c150410300c03c003100843e0007414000000440300902c00444100890200300000500b1f1039004941e0800040c440009120519540c650041d030b1050700746103040e0f000e4500c1c0c422 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 504053084 1250 504051834 504051839
    0x8070902040f12050a0b1506190215040305070209041e12110318101803150f1112040c0b0d02090312131e090c1e0f0c0f02030703080a1206050109 64
    0xf011445c0000a40c10846903030441e164001002070039072401c1119980902c0001300080e00380c5416902c21083d80383d903000c1d206828800902c075103024100721001800114200300d590014982541d10783d412038080c0d403c0e250641c50780340c00b00141c4104000161181c444a80c004001d130b81c4e10a0740645402a10030195040c4a2103811241100070242c0001d48203100c0400d0710500036100b840c243c0c8000301131030b0040c031445980e810300682114805d40c0502e0440c0c108800258000642e008059403407a920b10110700c0d040800c4c5e14901e000c48042d108890310030031070800003180f11120006d001100340210005070f5400c0d100c410145040b00b5034468075860003060110242580d80403140000f140d000040075518030b155040b401d400900d00d0f400900c83c4a10340820609440d80c00b80581d460010000c80d404c2c1c804440c0f0358280c500141e165011000903046049900c005034018050003241e0744050111940f882d200ea0303461843e0f42102c0243c6e000200e441414002000141c007800000b0705084c28540d500300d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 504054334 1250 504053084 504053093
    0xf040309410a0302120102192d0801092c03040501030f060b03010506070302120d0e0f012a0201020403120c021c0305030403030903021005011401030e060c1b0708070902040f12 77
    0x441440f01034441e0765050301300c1104480079011070340d90003210851110500c06040303018102d06408581c4101015101d403000220012030344001034005100d4442140c80e03803034440024090081d4030a030000d0101100500d5201c4200c421140030545d02d010302454455051a000404440700c040301500003d05003101000800400d00c1100e044d0b940680d10750303942d0309581c20140d190000044406d4120b40700041c8005038080d4542c40074850b9040c140944121022602e1410300344c803007071154050528400c00380310140301c0e6904001c4206031807a00003d03090a0b541e44030f13a01c1c0403420381550408500510403a50451401c0001004c64040640d00202c081406807001003180c04014002028543d03182e410310103140c000c1008003018408403d09005c99a15191540181008490b007140482d0404a10315505400401c4051045001c0402182000303000758110301d14404600c480741c1e05000d121808628950140141e0002d0110030b2005641d4520706090b049030500035611031040400b0500c43c1c0000107 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 504055584 1250 504054334 504054349
    0x10206011818150906050a0c0906031a06040b0903010c0512040803060103060306020a0e01080a0c0c020d0807051203040c06110c0919060315060603050606030f04030941 74
    0x1d0300c1203400090b904207061040c80d90b0040d40c0c0780180c45030070303403400b41e00c0c1d15100c1d078200740360061055a050110380c036040303043d40a0301e100c44c007030f0008254134050034411284250b20801c1c508000340d1514002030800404204164841d42005a03900c000241c43c030064102401209101e1006280c00c0d480e01010b04210080c1820107803004103540c800002140c1c2c268407030b8001030091600400210359031440c0c054040d0036220110b041d20b002c141804001084824988149450b07110691141151130401d070342005440f03588107104450f103c0c02407001c0340c00708030100705481e024040300b10100d50300c0c14542800d03107000c00036503c031200b00038200d1880308241201094101803070000399200103198684414180601100c1281c14455620341480002406202000302c00c50320b00744201042080e494003812000c0c0d400890b0386035041441000441c5011001c0b03000580c1c000d00a00e0304241150312a544c2412003c1128506a804000c1c81011043cac14815290210b0b006511351031807042002c2080403483e403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 504056834 1250 504055584 504055619
    0x309030a051e0d05040b0106111f1503140c090c16020102070b0c010626070303050a090e130b090c0112090503070f03091802090102152a0c0c01020601 66
    0x1042008144203060402c0c80c2400420700c4a5410030580b58080b240c03c440c0200310440b82a1892559030000050080c0251003510041c0301c078401510b643c0c00400007444d551869050003e400e01d81d210840102048080780c0d26024512031710129100c00800c0190518110110500510071070200c42401003840b04074003118402060801e80c0a81d0403900c5c0010b034104480b0b0b610000e046400040c00340765140040d4421000d5901540e0041210a041034012003985040b101d640e5071684020028030100e40140c000c1c1c88041110f1903e04440c50301c4030741450f1502000e0340c60110300680c1803045c1c0100701c0000b880741c0d480725644004002a01c400d50000f000085005a02140185d54a5528041c844c05104440c81150446041c070b8580f0001d107001010038480c0d2084035094443c115403800b80000600849100100590042580342101c00c0c1c80d05203644054036140030300030101007210034070068241000e55a0721100e00c2a0b19000c078980700c0c50808000020413411900b00000500c80c160a10b8190b520 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 504058084 1250 504056834 504056837
    0x30c030a0c020621100602071406070c03320a0b0615040b12090d020a150f0914010902010305070f020a0807060e100b040b100c1502091809120309030a 66
    0x95081140c00850240d100c0c0080d0740d0040c5420031310150040720125080303805110740d0410948200d542d203104070386501080c041c3c5080300e60402030440561510801500080b03002d00c90040789140d8a40d110501c2c102d110000146094140c1d181001800700403803440d8801300d421000d0300c019010366035601d810403030042c0003a110761451449800c407131071281c060707a02500d5440e400303c0d6584502145128071000880b415400c03445141c20302040c2500c0403903000c20265020741312802e0005415000400f41c44464465211240d4030006c071000319500e0b802c0d402c4c4181c0110000a00801517000060982e0340040400050208540d800344030560700082840400d900b0005c0740d03456010754034041018002d0208080300d548905030844011a40320ba2108049180445040000c1714050043c407000b030b07c4200c8031030089078140150785e0100e4681c6001401816000138011700c3c0541601c001003800300c4424450a00c21070b00c0f020007503100003c1020180800c1c40c601c07150306600e0045840c65891144100000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 504059334 1250 504058084 504058097
    0x120a060e013201051f030f090209010608240307090b031516020115260f0d0509030601080601120f1106040e1909020102030f1c2c030c030a 61
    0x5000300c0d420360040082d16404092101251903a51180e4007452540c668071200c030000c48000a40c1d4680480803064407100000e8a25000300700c90380c2a002410030741c250005054440d007011005a49483c0454041c1103162200705660901e11204030b1598032260601c01c00510102558189540000d02d21003201d1004e8030118560420b2408603081110044608004480780001d00582e540a2120128400b9066008100055001d43d010703080030990f101c0c9c4200302100c00c003e03007412150042e036120f1820701d24048900e180408a4200d05d0700801e40301510001d08007040108240ca818483e00d070040a10100820181d41019000802e081c8041402440300703122000d444204611a02c1d504054000201215125942ca07c19a06480021191020085181503507900307216054442e0305881da80680c011030510049101d06885980300c0c0707030340d040c002210b102d03000c1200300c1c1d6018035035a544a0b500001d500135400f10106161201035007440074141c00c20302c00c50058450000035920004118640b80703 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 504060584 1250 504059334 504059351
    0x2011b1218022115060f010f17090303011505181c0c0323010c0e040510050a14011b150506130c0f18031505060307050d060c030605120a06 61
    0x1003085442075000039000f080c07031042540e07a444410f003900382050501043e942000380b0020200380f4003004407540380d84150b00c241425000e51003903903684010ba08030f091685400300c40340301c0e81c22200b41c02c40f100212648008014070200c45d040bc5482848042820914200f2154055200c1d000c110119498019a000c1c103017000c11140c091030001900760803113200f000d01e580741d08015050100d03150164000c0d070420242e4007414041489031740e211816960303410120143e030600b0070024210140c4255445411043e0108180d40c4107e4598000c1030100c0e20600c04038558800034125400b1300708042c2c0d020428404c62400300703442e40601c010110550600044030345d115000100ca0700340071101e0443d501c1c9010004610b1940004503250340d8592901d0307001c0b0070818488002e2450140d400024548030f18400d8804112445400058211100600b0358504c170342c0303840120750640c2e590101501c24070f498098003002180c25110720405000d09403815481d54000d25001c03941c07444103420080030903603140b211 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 504061834 1250 504060584 504060611
    0x1020d12180206040b0d0b090c031923010f1a2d1c0b030f0a0b09070305030307020601030c0e0628031e030e04051e0709050303130602011b12 62
    0x300c100319a03006240c1a101c980700c1d01c801810307800c0b01240103406494007d50324602d2400c1d141403481100d80b114001c1c41c60380d07030312a86001c454414400311005521912a86481c1140e59941150036890140c0e00c100d540c0362000d1442816680d5201d20241440c140200c1203100c400001c0b11b40032404035a2085030140110000c0c101c40c0407298948a4840d80450100c0c0d500400328140003000b40702607400d02c030240d1030000301078441040b200482c045a02c040351900014943c108450381c040e0103a0141c3c0c2d00c1590303a0300c800b0306540c811514100140c02003030050082101c020f4401002e00b91001d1881344519105011500e9240d0015000d2100c1311890307485e410640c03201c442240034651180601800c06506d032401340c0c1841881408030089001c40e51130381030300e0a0510a440c4103184801400e0140382007041c40701c00504000d80f01404201c40014007203103a84003040184044c4051512410322140b80c0b0400a00b100c1c0000150460303c2482c1d94450001580300d0412840c1110000c000a0f900110004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 504063084 1250 504061834 504061871
    0xf0d0201110a2304030c06082403060601110f06011d092d010e0d020102090a0e0c040504090212060c030f150a030b10090608030a3f02070b04060603030e01020d12 71
    0x2032820850710300100b1140c8e40410864055220b104a400351500200284074540200481241d010343c440b60000b44c0540c07050710500c403411109410394000d5001c2d0000c0a0905800343c000c0c1c2c180d54804401c0e405c6103040c15089503409400103000e01081e0402101e0507001d20000d0355102c000c90070301020f507a81d40c8c02c20362200c00e00c03080500441c2d646000103078011b4042c0d041000040d114515003000051210607031201d41c1d03c10884039910504d06810142000300038034003d51305a070000c41400700c17940081800c00441d4003440c56540d0300d940300d241c00c8030f04d0b01440400030705e402a04010041419001c1c1c1740c03008080e0941c0c2c0d1000201c0303001d60314400c03c042684000d50144d040f450814600203540c81000c4000d0603c05540d98a46007c2031544000b5010407405c101002c0304050715034010021100020740968907441000c0c0c000d450002d050b241c0c001c12b00402d0700c054509507540c940400816400c82241c1752510402c0c0080c10500750106006400050031813043c0403015129080c81011101011 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 504064334 1250 504063084 504063089
    0xb060a05090405100f0b0105030c070c0b030c07110f0105070210031104060914010c03020703380a050f061810050612010608010518060415080f0d0201110a2304 70
    0x30007640542c5031604040e5943c1c0c03005464000500c0ca8120b9020055a050085044907070042c0c41e1079107103880f08040c9207a01c0e8032106040d80c0c0c850907404041806070000006501401e0002412900c44006080c1601d45088100740b8601c24111503e50611598010b802c1d942041d8040b01c0c00482940303040400d4001c3d0604030060104c1180c001804120560401c0c5c1590a4980c101d86181014a40c1c40055401c100e10030009405a44210740801c001402d00035401915400c40d00140b03105d041440c2007800c071041d540b803081080c40e1071800f0400c00c5405840350316845198104100f03864100300c0042194245a17102894009001100040e41a640c400c107420040c00c010700b070140d84103000c004c0c0480c1c050081c09044002000f0344000140761030602100040420302c20030060240c0c441d401080001d2030b50b002c90000070620032400140500c0c0501114600060200140c004590024002400c43d403080001a4050b4000d00640d810250300009481d030f50504402884e070014903095454105000c0c55 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 504065584 1250 504064334 504064339
    0x1e0201050f1522150806040314220b09120a08030c0a0201021210050a060807050a050c0a240b090c03010302011b05010f09030e010203070b16050408010905031803190b060a05 76
    0x50028407425444d400340d0340c91590480203441c2036480c0e043d0161141740c180c2d00070300011004013822031940745000050204c040c110f40035811a00306031803610744103a22607000006410000c038141da801d04140311300c0505001d444007d000210706d10794543c071aa00000d0308030140420b0114041c00d0080c000d60440b14000ca24220030006441d0800d00f440002100303028050050002d1100004c0703080c001e011050184d58151503580c01d2140c103450444454001c0301202406205008001e001709072001081a210700200c0e00303980c0b01c2c0b00078480302c2c010380d820700c200c0714089c803010000c005401c6d41080607241902e40c2440c22100061200e04524440d21120300007030074952804e0200d00c4511341903030000d241144a2b072103500f040300032003006a031a40114003001d0003002210b00043c1004203140c0e03001c100003030542080d0b0700381070300d802c0018215070b03c4110850b0558000a1030055000007400444080b54040700200340340107013160032541e81f0b544100020158603014000c500300d07964810341040a404003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 504066834 1250 504065584 504065629
    0x31303030e1f0219090e06061809090a05070605130e0603070e010902040608061005220b040314060109090804090c0e150d1b020703141c1e0201050f15 66
    0x210034034500a50003050007410b07072041c101c04c051030180100505012076000c0c0082da0308598819090042d5075015001d11141904440d00d0810142d40d075041c001e0080da4030000030724082849190040c138250341c81e004402401021301c9010343c0006000c0c0300000b9156001c2d240c02c95500e4040100c1d290500980000c0d0f0321a42d4000080341c0c140f01c6a02070002c481c074540e1044050703211001400040c9c0ca82c1c00d418000641d040110300c00040304503076113102c1991030f85100100d9507502d1200c1200c50700107400482c0c4908650b00907540c0480208075560140010b0345c82007001d41c0542e906c10341503109030300c5481f400544581a022501d40034002c0c2c0e500c490700203403082d41d41c0300d4680e592144560001106040c0c080c600180020110781426070407004007019001464070034115266800e20190120b540c211610030a0b2119a00e4100354983d00c03071001658460307001c80ca0309418042e008481303420401d8110380c5884108034000c0001864503070440044000740c982c0780c1c0d0314070100d28007030900040c554050f00c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 504068084 1250 504066834 504066883
    0x6110709110c0f030d060f05061b0715020c090603030c0601060807090f0608011d0603070603090212010905071706160e040b031605040f0212040210120e070603060b031303030e 77
    0x2000c0300400c0f005042544c201b01c500d80300c41444600030800c0c0610382d00031109004050345e003003850f0b541d105c03a13003020000c541c840e0b592402641039240d0b10094600041c0c00500c892070450501d00710a50304441e040300a1814502e010058075540c0e68148a0034041103000c50104003518050840100a010740c0a803410041da200c8502400c500c0003881841c40c0c000c03003100704d0340003540689002c1317004440c0200500035041c580101207010309051001aa40b0030b440e01c0f4082031290092088010003440350024198240c64400c0c0c0c8050003c100b072214285410550411440000102d128542e1038554103250214030062000704000740b10031b41125800d40700b02d003420300045041040003000c0b0780d0308903000d101180401d01f20300281e00801110019111800d00402c0042ca8030380d2480a1100c800e00c0c006824441c0703d07180c00103071001d848012229402c410428000c00340d040c041c000260051442c0c051450501da800501512020040a010507544640e003188103a4280641d1985e81c2c0c0e100301c806550907 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 504069334 1250 504068084 504068113
    0x61801030516090213051009180504020a120c06030c0c05010c0801080d0516020f0612010e071713030c0201050c032a0d051204021804030503070906110709110c 70
    0x744801d0710030b1414002c50000c2d08414034000c031880c4100100c800d018480c03510061140441c00486c1d07800c1070015042001c500074480480b03c038134a42100b00301040508150040c858510b15076000036182400c505101404644111020740495640749000240c400c1d444600700ca03980d0082c3c2d170041155007420f1041e03004c5680a190281640c2800c000c3d60782d24000360200b84c1d490300c5130420344543c100c403039851070340036140a1000300b0a01c0c80140010707107400c400303071040003216209812500080c140403040c8000c0b10b500826000d401c0711070a0301100303d41440ba2003c240a800200d00070104140000c000007164450810358009030390550499440b01d020180740c01d04007043e4400300582c081c2c0340a40c0c0200420008001d0316518603911200c0c031341001c0310b4804401d0304000348140d8122900810881040c203061000c544a03d001c0e5803006d8803814041c00c01402030380c05d91300400420404400e80c2c8081074001c920380084902031240011501d266a200b0712142c002c00360802c005002e004170000740174 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 504070584 1250 504069334 504069343
    0x1103011203051603020c0f09010614090d120f020d030204050a0314010b04020a091a0a05030601391b060f180e0405031317030304030c0f0506071e080105090f0618010305 74
    0x2600103e81f114440f010b80d40034480441300074445c20300002c484650142250350b041c0e00400025401a00c0100319248a403202d55059000321900000101c840c58004c14841d41800903124440c150300c1c0644c81c20785000000b484450701404081d00420072200d45444015007544180e11080c40588195111500c8c4840900b118841d8450385500d00010f01c402d003040c140710b00403548220080c0d02c03505e0031529504011a01485c0d4112620100c120047c403056004c041c01440d1003440d01440050100f46134a0702e030507240c8511010b081b01c00b1040d4104180f001e6034018903c0a18000549403001201e8200c0044403c010025405481d41c00d0101c030911050001c0403004000d0084c01c0080b1001c071503074440300c9060f00c0d06208010711268000f40080f9000911035001c3c81c1007640a503000440318501703622810305211081d14440041030440c0c007001c0c030000f410706080e4a80c2c07003503007080e0186c1d40c9010041641c0c081c0003080b501e2000301900c0090322643e1014030266003c07080b40392030a130340d41c1c40b80f82c0103598 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 504071834 1250 504070584 504070603
    0x102090a15030f2a03020304020a090b0d151d0d090905100b040801050414190f061407110d020102070f0f140712032c090a0209031b13110301120305160302 68
    0x20030740d100c2404c10103602038000c0301d019550203800003918515042c8003200401d82841d820340d000c0402d080d1030003c1080d013020300160351403502c4000340c0458400007103401c003009400408819084000c5a00107180c200031080125000f80348080f4040c1d8034460b0b11880340800d40c10403c0301c5c00c00424007241c40041584040e21491080600598500c0a01c40729540c403a5550f020181c924216101000020601f101103220a4452400491544880056452140c1003181c6080c0060440404000102c0c0100b04480c40120940021450880b0030345a03010040840d8002800ca00d4411501ea01000900e02043c42130204040c155040282c5982140a5005e10341d2400e0b0005030702400400ca8106145402252810340f12409080c4500300c502809114072005200c0c1540075400d01407503015407800d20110312002071481c800039108003604204003030b201210030011003080c0b400031034000044070002124152410b070070b0310010064a82c50201c3e0749124500410001400305d00d6807100b05500041c60000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 504073084 1250 504071834 504071891
    0x10f1203080a0f14190923011107031106060603011d0606070503031303030b0a14040e490806190302030a0f0614060906010c030915050a110102090a15030f 68
    0x3108421891400d0686194007006403040c504000d0084030192217401c201c180c00c1c800000481c0e4400042110413040d00560320680202d84210740001c3340c4002408030503480a000c40710f4504550402889907030540c05800039092403071801010407a036641303c10a5841880e401402c59a5910380802d1420120403111800c8011a0800c0d0403050941340c04422102905c0200c01d04c00c034401c440c00d0801000d44030300c005020050140082d400d2041c415400c20b01340b1420f8442c0700d00d240902d4850020055901c40b2a040b82c0302c4103c40d00003020340d134040e1155070005811903c40d601c00749003504802c90381c25241c4c0029818030400c0803038020003a0015085070300302d0058008010424070f05106200c7e15104840075a44070001c2030000310315600614040d80c07807034001d18103803088584bd04c41d000040e14410340300001040c0040344031070046920464004030400390200075801d001c83e03d400306140c01664081c0800c4040400d10345c403009403007640f240380d0101040e43c00b0b102c1c00c1040200000c4010000110b01c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 504074334 1250 504073084 504073111
    0xa03050115081b01030b041d2503050606300601180c0207051201090b010806090601061b1524030b0a0c0c0602130506030408030f010f1203080a0f14 65
    0x90b868a0200302c6207100301e548110003445100b5400110014111060b406520560712103401008241c01e20003100c004c41c0c1000100244042c00101040b0400090344040407040220024000503002040c0a900a54241c6078050100383d01c2d0034503000c80c24110882451850803001d903003a00180002c8150407900c0210b00000040340a440c48400d685c0c08650060141e0303ca02070403c1a810101d03c0c41102d580c0090000075049259038450034024421380c400d005036440355050200b01030040c000c15006145c0d81c1405074207403021a03423040800b002c0b1500500003444002d041c0000d024550400703080200b4a580010030340e01d0118010004884074003054800341d41102c00940541024414488075241c1c82c0c6452510a00c196a1000607612455501d29882440c1d500000c86031a0380700518040c5110b4050f50f5105c0c40c084500b030080c1754059100c2c030252459002d0030000b821100480a4183d40c1600c1c0c0101c4941d29200c051016110003170700c5140051400710600f03003984c0c948070a030340124102c80ba0340 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 504075584 1250 504074334 504074339
    0xc1e0c0f100501140405012d17030d060803070510020913060b0c0f030307121104080a0c031e02150318060a020a020c04020c1c030605130225210203090a03050115 71
    0x10045506c24010000d6081c1c4602210304a110441401c141da40800080c3c070581c103480381a4100f84814080d440003050307002046541b029034240c0120070281030f951005504050a0b51601640d800010700e40e20070745540007403100711a07101c0c149045212040c80205002541c0e5860403070708144c0c059003640c28036000340440e003446081c02102312800340e60715980d0300020f03260b94a030090080207402c00070140150100000101c0754800c0c00320002c000d00a00c0d01070050340c95070400c0c80c2d820300e00d0001114212850508200180c0c2e8900262040c03800090f11641c4036035820640410b00710541c0ca02921301d100c1c1c0c00400508442c00d400804032802c0503425a09089030314020b00083c3e000b144c0d10306119800820f4508104082c540d503d014401240c6004180c441d0f80d04e0204a2804000c0039012040e41c0010340b14408001c4203200c0700e0741c0d030b03a00c480b030a6001024ed1100700c00e02c41803072000000b17803801c80e024000c101d10810030f4658400000b00f20204040d605d00c3c180380240221075a0000c0c080ba43c5000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 504076834 1250 504075584 504075589
    0xb0402030115030201020d051b010c0305090f060c1605100e0f070504140402042708090f060702010e1003090501020c0606040b0108042429090c1e0c0f10050114 70
    0x18200320f95040c0c00801900c5d02d4010b0a8540e43c000700d40040c4d00405900410885110900680c000034019440020b0141001050142080401d0520202950164050004019040040380c410401d401401c0c485c020301454001d0810741750214036451903080c42041c02607481c0104500c14201090022120aa5581d8040c0400d582c0e0400100041c5a203200004d005801c05412910145003815041c0603000042018691140034200044e83c1c03519020881d0441e9081c8500c803005031601c11180705080c0001580005c1039042c51684442c0920130042c0e4654040c0d0280c0c104c1c031340b45544003000b0354461086415041d0740302c600f2240e1922441c28404000c00c59400341e10818042d90b003204098601d22801e11140c0400b541814400007440d40da007054541c1b150a51140031208407241c580a45101a45400c02c440c1080c042c01c905e00f4100c2c02c003e40320561000d040e80d6002c10031103601441d11070f00441400c078100a08a0701070803e9016210750780d00140b00c150b0146050740e207501003a802c0030410106 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 504078084 1250 504076834 504076871
    0xe0a08070609030b0403020a0c060512010905010b0702010f0e060a03020702181b0306011806120b01030c020c010c080403020a08030318030f071e060221060d020f0915030a0b04020301 80
    0x941d00071450b40201032021034a50380c400c0b80d12a0290045400da48016515a00180f46c00c0d80210000745003c078110803002002c0310054010000041e05015650401e20258520309c20707560000c1c140b1184a00000000b40240c462800118004014079200e00074100090065408094121302c03c04c80c00c90503d071016503080c8068010f001c1c04003801c840100c0707030b00e540e840c03640090012814811f40c1c03003146110701d03400c0d142c4101600d070940c3c03151003400c00c141d203480036201080d0307902d41454105074107000203690000706a40340754000d1900c81c001040506101003944901d410280d00040985008286000008000c50003804090801900040c80f080d03801e80703074000d4081c0e812140c1c2c070030004032000c07440c82601c0c054079501400855080c00d49640d10341f4101d901000c1c000c1100c4841441d25080b40000d1009250f2004060f40d811000c00e02c55400280035a004c41130081c85106030202288101d030454080390904c00c0054112a2100300c40d00740300e03070082003c0b030b800c1b0f21940c01c00e601d1815840311000d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 504079334 1250 504078084 504078089
    0x16020112050121050708071203171501030f060504050c070302070b1c0905150405010e0c0a05031c11070306051501051206041107020303120402090c0f0a0c0602040905070e0a0807 78
    0x50003060b040c1c5144420300e643d2601c5400585692050f010f0114000000344404c070010112181c02c88c1c5480c07920319000c0c00d4081d0001482c06c3c030500120405c4154411240155054103007440c0019040d03034884400e50013031106404c0740c1d80251030032040000200d41d4400030100d46000360211000c0556900300c80c041c920806904001911402120f100303c500035400511616100d14180d481c0c0c0c000302c100111510504940c01d95950391564012000c0d202c080c0a0442d034010140c800b14000344c2010046039540007503040180044a80c0c211000801d481034100000745840602a80c864942e80e0a108010308800c1c0c81c06030380e1202000030602c1c10360050342258080d98820850a83d41d0344c810040100401541c842d0316000402008100c0050b9410300080c414401c480e0581a400d0910707005110901c10010500d2503400c404020201030402084207540722440c1c186408038490002e4645103020f80101c0d07000c50503060521341400a103a400c1112182c640f0790a8490700ea003195541803a0b9990444d91 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 504080584 1250 504079334 504079349
    0xf031a09060c0901051b0114010312030e0c10020705060705150c041d19021b0f0a02011704110a0303020607120209010f0302070614010e0702060c09090c0717160201120501 75
    0x300b104040d1940544007501c10824040910000600f1102c06d25094502401c040c2510b600d0305401441001104103803c0342d4440c103450100545500501c5169856219142640c0304400c01304020a0482c400c100d6800a0403000e400380d9100c0c1c8039441d1142c0c0e45c00300c940784540030000b98000110350580610569049480c000503000360502d025085141282e0f000e0005050025060034844c02d10703c890004100303110b2542c201e034941017480c02c90380b424018824104407030b541000c500c802c0541e0780505c800400390300340035014a16440e2440c0a1007902c017100c4403070b034110503641c00000c181500456924420281901c1c5c29548810610044c8202d124141c1020301040c00c0800c01e03450340d44640d0140542070b104000001300c030b1052905000b8500c1c030980c4150b00d0884107000300b084881c0d050104503000301040311410b0400c03045c4000118800e6004040804691002c0388130820b1041d1517050b681c103401007100f110b80d11a0b019100d842d03d00c00e0f2490580c041584103a10010980c00d920525040340c054 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 504081834 1250 504080584 504080587
    0xc0608180c0f060a030b100e010306050612041403070215121006140f0d09080304020a06080412050306010e090106080610080103051213090f0b090a0c0207030305030a02040f031a09060c 81
    0x3404000031600b200c050301303080682d522083d075559140e0410003165001251541c218038800d16000400b40d03041900418002d0030300380101ca0240c40382c0143c16801561002c48880080c0b200c8004034590b000b102000780d40003150b010500b50b0303504030074014458908035034210040b5a4410401c2104000d003841210000381c12003072220740d803455070320140c9070030283c82000a24000c501076115003580c3d16071105556441d00041800b013107282c0301d440d900050016050041443c40c264a9000e07034228188040b0050080000004059038460054100d003010000c01c452415616920000d000e0f8004071080c6009020300d061080c3c250380100200d60481c0c3c0e03c500241034114a607190f11449400c0350014080c1310701013810104809401d80a41442c00449150010b0f035040344008118a5000183c0844005e51074061035a007083d0303010548000f521b0b0907003003031556500e40f4203941009100756801109003031607003c004800c001140c0441c821824603601e28610f1503c2c2c442505440354170988425028410 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 504083084 1250 504081834 504081859
    0x507050a020c04150e090706110604080a0c080409050a09051b091302010912050c090714030f04020f03030706060314030a0206010e1003150b010201060902090102190f0c0608180c 78
    0xe09130440700c0c2a0741e4007042d100c59913545440c43e51a142041c2c94110304c0344c01a0f00c0612895501000030f02242c02d81200a24503030030191608091403045a804504005600c3c0c250000c0c00284021100208101d1400b0401c1d03144c11131030f0000421420704110b88600a0001020303003440e403040107610381200102900150f0300c800d1704012a000e4070500c12414442d540800280f0608103000b40c44020740a540a41280c4a00c4410030000103002020700c000d001000e80440b00c0307035821800350ba501c814003850500301c50700d5038000242008081041140e2510000940b101040641e0700100d044a100300040c40320703034405020341d5407a80161080c1600507808000104081d115451809e5004400c0a441d1a84581c40f901c03003180818003454a0500981c54141000d01c81d40c0c244201d41c010048888210b040080d4840002c0d07c601ca010741e0f6210391a14110341e0802d00c82d40f00b010500c1c1c85d90094501c83c0707603541c414000d00460b0088401501c0c2800350311101501c0100800d1140c820040107002000414 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 504084334 1250 504083084 504083089
    0x13060f0e061302030c0c150c030406050703060b041403010f0b1f0c0c03060509250501050d142703070302060a020319060b0301050411120601030e10050411040507050a020c 75
    0x140107110720380c0480742c08240c0b900400c503440114001c1901011a5503200c2ca015004ca10300219207080d80d0701c00140e40c6c100040d2841c2c40b01901e4020340d10040201c1e140d240c2a9040307016046541000c4804000000d00141040301d0361800c2502110503002881481c13005410720040705c0d078640070b250300041d85800d0700301020f0520002d220003c1050401002c104031944402c0b01402003900102c44141c3c0d2102480520842046501000c030b080401100010030403880d070307258981c003034410b1505000d00801c1e4014805e03450380100c04000c00e01c449924851604034080c0302000c080040002c0c2c0c41c401d10031a820398500200444085903015002485140c031490b10b400b0096000401002d40c86290454038000f07a42c16000d100700401448240c03d49950606040004a4a074100c031000004401c00800c3e20760200c8190705a8010000d090000f030301586004900d0420b0201240707281e0903440c0108000801010721040c17425428141c1e810001592024400c0c1e0b8940714260a600c09680219030b05181032 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 504085584 1250 504084334 504084359
    0xd030506010212031003021813030806060d110301060f0504080d080c0904021b0c0609010c1203090c09060305010f0606020a110303191706091603091106041413060f 72
    0x28034103204a5100e0b150302001c0040d180c00940d1483c3c2c1030100c240e02001503103000c858543c43c0c0c0e080075444a0b01c606012140781c030307070f1843c041e002024020340200059050391568242c03000b4100144085c04000342c3e80c041080554000d00488011513a21200612240d1080080e5815a007400c0c0040050b916000b0f416564414003c2c4040c0c0c0391b030703801c01011445840c0c900142c000c008c1c090b1010041c05c0c11440440e0709101c0007088640c02002c0c00d0040400980c2c1c411000301701c0e150800014461710304940781c110302a210844010f040814180400a00420a50b00c0f0740103ca02600080040316094004041030b940d01e48200c1d0010707070000c0b20000c007203918015441d0b0f5144000b0200d078581801752000701c44403000400b203c8041400c02c640c0000301505001060351100e4220794140592422070388480000006074040d130300b015520304800080003e041641c1c046250020107454686546201301406c40d07021aa0182c02180c070100241941c0c4058000e42003925280d061300403040d41070a11002d1038 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 504086834 1250 504085584 504085591
    0x120316030f06050409081804020c0c06070807062a1e12090c06020312100806070c050102070615061d0603070f0c0c06050702122b020c0307090f06170d0305 68
    0x441c1d64076680007803a651503200300b0056510940c0744989a07800100c002e040440c48030340d05400389004214100700c400f00800c4050900c0401c07910b05480c2c041c94284030b0b9041c000d02c1c200408482c90801440301104011215404050032a81c10703170000200c1903401c503054004400c2d42d02080042e0a00030680038044c00443d00c1c560600c800c0080c0c5501e450b104d1042052840c3d0007000540c00004c2e0002807450440e0500768044c1000400640861401c40c11642d1000010001010040410070703102c2046820740407034500a400010070b104100b240d104c2c200501c0d00b01d10810020560710b04000e0204581e400901c0d92811000305400c2c1580d540c4002a54018502c0201504010b50400c0d0780c000900900e20807000b03000075075180342d1641c6c250310511a130800700606841031540881009200203603440601c441d00d803191103100031598120201a4508040000302c3c0d41e16005411012903007a006a228404c40506003405019072070303071074039003803c1e850001c921901140c100c0c2d0b04840c4040e0094210980 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 504088084 1250 504086834 504086861
    0x9020616150504140c030a021f0c120314090114071101060308031503120403080706020721021f0c02030906130e0403031a10051c020c0a08040812031603 67
    0x210364000c01c0000003290000c40382203c1c0803803001054090030204004e524401181580200602a80da800003044044507800c003504044030400f4900701640304180c2c032030301181c1c80318036442c4030101171034003601421440f86401c0c03c51000e080014052101402154500180c040360501280c580808c00c807810841c011400459640b01d41d00000004d03c0440210b104000000028103c8070043c42014102400c00026845000040c03000340040360010007207408840d070040005940e04840d1405520801902d680410005201c1c0107020300a40c0110700a0403500381881c00888850501e2001c034100d8003160903200c0164002d00c8442018208480144081400e40c500c540145581744041030540c0f0084608600103511154403031680d00403540c1040031580101d03450180504860300060060185400c0d000b01b01d1408001810f03400c403603a04440b5601030190a403841d500302414004100c0e400f92041c041140b04107080758110008a4064074012005181085000c90020004070b010300f045802920 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 504089334 1250 504088084 504088103
    0x30a0b0303190e09010614030c030402030a02090c07020405060301060b1e090a08070603050c090d030309021f090e090303070c0b070915030e100509030f070c050915031009020616 78
    0x82c0301503010700c144907203005640b00320740310b5000014071071a050180e1100c01880500d1a440542590b030360301b40c0754080800c4180c0c1e6100d0b0354600001c0d10340011801e019400c60740f01c4090040342452480100019802aa01440542c55140c10b0608031903007131007802007240d0244032000412150241d03c218406800e94800d0070504a000060f07151051507000344002d9002000c20044035070507000c0c455104640308041c90520080f08081503880d1806e050041c2010380d14680c0c0011940c900084410107110000c5031303a01101c3d0201c0160414155010700c4541e508140001044120300000701c91044840d40d070707054060104c075500d041d180ca00141019051204051002c030b81e040f10540400500003140d5000300b00e14280d40c03000c5042052a220003e08a030401c1d04005400000100302c034042561410216074602c034900b00760b00812002e4000552008401050008688503020140d1603198110281c42c103a414001c40324048400c14900250010410b0200000141555440c080c1050060b0f2440 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 504090584 1250 504089334 504089347
    0x915010908011d120909070503040515070e010e0a03170309281a041112010f051f05010503012403020405030f060f09070305070b030a060b130311090c030a0b0303 71
    0x30300350385110003d90403508032400e40c440480000c0008003010062000360614001d800c0c004038810380d078000c14a4090000000102d01001020803184501d40415421204141804000113042c40b6032a11180c0c00610700e11040c100324541159014101c90b400000010310312525440c001c01500000c042060a00640340b00006040f10407110a542c1e4002c5c00c2c582e1460003143c07400f010f039034130032960300c8998001714000c000020b050740e04141e000b0f1004540582c0e1504481440d40e0240a140000e485824200b1041c010308034240c8105070219511381600c100708640750f00045a29001c01d1003000c0da001d54020140071028201210003011203440e00d005403070309440d10007007440d003620301591100303640c408002c000b0700b400048403a50f0007200c0000a00f035050b2031516607540e251502d01440ea10b1110001c04112650700d03603400040144003401580b91a140c1504030365003a00090300c419990520b49040100442c03400003041c170f1184042200180c1523485541300b0200402c1c07042d00703880c0c2520041002c1c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 504091834 1250 504090584 504090599
    0x31f050d05030904050a0902090402040906020409090311010501060e0d111f1808011e0e01061a0403050105010e0601050f03040c0515040f0905040308011226090118030209150109 78
    0x110038400c0d009100a40c2d4914000081c0001ca88005003808102c038039000c00da00040c3c1e107004030b4503007041e0122404180b68a01c0e0400034004c3c881c940c840742e22076240881c41800c143d001495182185041e04c0208550303030369228191545000c0c90b45d09648152070f0200140050000541c0c6000d04d80080d041800d0511740074110364000d40c241000c500032540349510014040740da0140e21024280c954000d02c041c3e103040a03a4403040396074080c00e000c582d45034040e07055100300075801500100700d500c0030307a050288000b00303454017507016000a80e195428140003182c0d0a0032822504c0c011001a954640303420f01d40388180030103820240040310008252600090f4554550079100d000102c115075060380c82d481c00690141681d004c0e0304c070380c0c8801e042c03034104000301c1d400840c200d04458000c500100301440758a00742c80b00410884074015110340d8200c0301c10a1140c007101401c550602030725081c441d0b41d481003440d800d803040361000941c0000080000b82c00c90090000e18080c40320181404160580c07100715 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 504093084 1250 504091834 504091849
    0x70e190e0f0c0c100902120d09090e0f0607080f092107150f1a0114040302060a020304080a060501090608060f0a0b1c050105040302070509010b03011a0d1d21031f05 72
    0x104d0070b0003d03110b100080130341c80c04038040c200407081c401c010101c0d40c0e0006006080321100744a0400b005988220303261498070184070b13814881443e1030940381c86141c0307000b001e400c41c8030a0341c03005100d10207040000c504400001d5510b40c0008501c0801c0b4007800d05c04c16010140d4800102115602d4600107104c1201060307019501131040e40020120b0b85400003210340803a4100180e800341000501c1c40c103510202e54480c00c42d002c0c2e03070b010b58850766038900e440010303881c500c40e60348a95842c0c420000c41c0c81c20300c00707142e01c842c0c160350700c2107820700c0742613074421025503524815130300c400c013000c005001301c0c400341d1f0350768442144400d016080d458070030145404a19000c40e40c0e002550a41d465400300410554103020690141000302c4400032a9410200f44c081e03280014014206499100281d40310564441010b075208110111014003000e80d40b464810003c0340700d400c000016200301d160081d0000400d43c2503846080d03402c10038070b046598a10440001084410003100901284003006c115504c1f000d0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 504094334 1250 504093084 504093103
    0xa0915120c08190c091a040e0a0b040c0c1e031e0215070c120f020102090d060c200c1c0c0f0e070309111017070e190e0f0c0c 55
    0x40b2415074514203100380c986261840c52844500c680380c26444208036800070040c0d810f81d280c440e94094400042c841c0b4503010300c2590002c0c03a903111030700e08000c1521010740210f616610706490038010b500e001c1d5410b4511208001008151021074521000303610a000c4480001078000d10307100c0c09100943c400c014500150150b8500180c0243e800f000301016410491074200c1418034100c801c400c4903484d034085403151002e03c0c0e400c00010b40241200d992003501071b2803000100514040f5611220325025004050104401001c18440b44020000a408502c2c0c0c402204555001c0e10402849a040102c001d44c604505812404c015031031101184065460fa4081d000b220110912142098095501264018003200415080025110000e04250f60b004803030792007507901d4007081c0345019040d0340310b05a1ba82595081d0401302d08102031958006d04415084900b42c1c0c08810680d00c04610601c0c00c4454014402c00300b01040114a98001400e400c40e031007404184580e080c000d000301c01504041164 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 504095584 1250 504094334 504094337
    0x10b100309030207120506011203120507030c080609060901090b04060909080c12070201050d0b13090c1e030b04030503041401020705160506210a0f0509010f060b0a0915120c 76
    0x184075820400d0307010000340000e0000c4c50701c40404050307142c0e5804d60360300050050360250142038105800305801080700010b5019064410b00c0300380382c10680100103240c140c5140c0b00140407038020402608043c465103000d1300000d070101c0000d03030030039101101030040c00406540003a03540380b0005807040d10780708117001c00d0320480c01981e0b03038000c80e013926140c01e14038589100c40072810044280180e0700b19086414007041200085900594480000c800d140cac44d9500c1d902641c1000b91200403c074a002030107040d50f80e0310034012201c132240080c140144649000041107089810301281c0403034010350155502610035440c2c0010310740361010382800c0e600b0020048030ba0798403100415602c0386990262a001d81429645942843c00840d80d041c640541500300d03807111501100403541110468015000c60901d0761030a1140e81045c43c480c078001c05450010b604043e20300300b0b001c25035a400e4021a04000040c0d52003403007113400d00c40541c022141174143e9070203110b4603e05d010740c10000d6000d4005200100d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 504096834 1250 504095584 504095591
    0x20a110303040503010f05011a1204030c0c05090405010e0d0203161103010b0604090c0f03050c0d0b1c030503010906060509011d1804030c02010806061314130e03040f2301050309010b1003 82
    0x10000350700d4581d56019049c4982410922099503801c10980060303901c0754140c980300307075504624104030303004038110f42003190000503550030071007030200542181815100d1002243e4201c145440100d03181d0103401109402842c101c0c01c43c90205041800c071068107040200001800301e00c540c0010704680c0700d40c1c0100f104581b00d998000080d07400109144040c900d90800340708511b40b00440c1e400031721400000e00301d1940c0d200241646d0b0344030050911a49544001c820702c08611504010340140c10074801c1d440d0032800c1c000c003c81c0072803150b02601d80c1440107840e880f0450b00c00c466000141140f10024541006150042000b140e4926255030b0042d4003030f03101c0d0429808680001840604000d000500410b410401c9551031080e0141d548211551406109a83d8200000080001106480e04064103003014040366a9031004001001110180022090007032355441503012821500910109022509a5100c100b540502d0040d40c2c0001c404000040e040c1c1c04200245001550341c11800002e543c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 504098084 1250 504096834 504096839
    0x507050906031f24020606092205010c0210050c070506041e0f0c080c010e0a0501030e0c10020f06010e090303061201090b01080106051503010b090607020d1221020a020a110303040503010f0501 84
    0x9144d0340c02e40f46981503101908480c50108041210b9600103042110a00c80c03c620aa07800032110381e0401d402075000f0000d000400701400004d644500713070244403102d549000c011800010245040b81c0700ca0f94404c0103440b456403103403240303030003088868032041c81e4680720103100c0b00042c05e42986c00407062246041040490501d9012407402820302c59260620054800070700043d07440304510004c84509180108892401c00380260401404101d015000480400513101c4d0540114040e070700c202c14401260101d80e81c1d1070980c0e050a10680f010003090b082040451581d04048240c2103000d9402c90011601034100d5542c4d107a44c240c240e00c00341143e50b54a005210364501520034002143c002c060407402c0d541003958000a903c10810f21038400ca400040d180215201e490f465401140c05c6080c0c06c190005001c00641001d031944001c41403c81641d0081240c03204a109a0b0545210f075801051840d005030b40d140110721f49044041d600d40300500001400d66000d0082d0003640c0c0071501c4c040790a52 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 504099334 1250 504098084 504098129
    0xa020a030501080105060a05060901050f0d020702040b0303190305040f0b07030c18050102030409020d0902120706080a2903030c101b090e0a05040204140124030507050906031f 77
    0x84041c2c00c0091585d05000501141d50b0b42da0352558140c400444820340d888410b180180d99505c40e64111000000e0003241d180c006034510342c041c00d034040c001d039024424074146400705071300e0740b05030380400c6030f00c480e5036842e641d0f03c600c00c0e07100c60b5003c0e21030004c881c45031166440c0c00701c19004c111051400240c90b070544425181d8803903010380c507a1140c00280383d070b2142002d002039141d0045010b14040c0b51707804541103540c0c80d05500000306164025260401035801c81d00101e403a14070324020390010902d40f90108203000c0e95482410f02c1c2000030320a01d00c8020742c3c0c2800200030000c13030b003013294544030502107040e03078940500c040c4400c00d40760400000d0f008c50b000c5103801c5840c1d50b85001001d10600c0c100800c0b204030750240d40340c2d00c8040890002555952403000400800e005c0e14001909a030300e00c004142050b02d04554580c0005404162a170440071780e00071800d44804035241000190f0500c50340d00c1c40e0406801071904840e07489003000d51486406149184411664410154050051802d90005 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 504100584 1250 504099334 504099341
    0x3509060412020d050d1a04150320150315060a0c03080a05010e0c0a090f060804060b030d1d0301020918070f0201060f050d06020d0510052b0b0414060a020a03 69
    0x14980050040f01950090161250060200a242c01500c0d1030060a441180c8070100710100301c02030081000f241103041000c04402140400c40e0b0382807407200005050000040711420460009005c00104080403820000c80d80000d0704d14140c0c00c1202c0b06001d00c41c0ea600015184180c50b80c3d40c0c1c4802d84286060080140300041c001c0402c0c90301e418010301c001095040c0c000d40c00070510358415910207030302c030b82220b1851080c0d00c0040322241110000c14030980c00000d0340c0c080c0c0d001e5030050100b084454101a15043c0300e140310320204062404103030026031108021620702500400050801824501080c2500100b8039480c40b0881c0302001c01c01a1368014444082d860420b100070010700e0b00708081d04551b510103009803403003034a244c8415405c01816404039074040007400c2d014000ca007041c0b0043c50840000303000f850300c24510308200c10300c4c08607480f45030040304107200b015040301c9103161140ca2400304090000e0f66044501081000030706420000b1502506041100517541d00c40c104008044 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 504101834 1250 504100584 504100613
    0x17070c090f061208040501081b040e01090507051206090619080f010c09080a020f0d142803020601050d0812040305070c24030c020c030a150506030303040335090604 72
    0x41c110310300f000394007080c000001e0704c1c10b941c401c0c00e01410580700c1ca0a035072101c075020801c0d811100340000b0042041c440140034507048802d1448180101e8903286000d031481d00600300c2e1007485410310000100c2e50310300f0228a94000300040c00d414019031901c0101e001c01c3c1d1103500200501d9000c00d0b001e584070315091040303480c2d0311040d240419010781020000c6440320140344020b840350100f98400d26060390b031303114541d4a10f5800592036201c1003a1103c0c90b80c40782e0241c24498900c000180307000d0f05000a840c0140c0d9104d901d0390290601e84c0c280001c1042c43c2011900c103450300e1005002c03d00540740700348411401030340261225a00d541c480e03c0d14440395400d580010440c6801450042002011704004002c6069242404a40066a010101d28094840360b095925102c0c108450007841601d01e4050340195420b5020310043d9603071028165284400d650040014a000c003510b80d201c0b4100005038086100d0846101c502580103d02040203041940c0e83d604c503030801d4061004000c000c4184414 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 504103084 1250 504101834 504101849
    0xf0306050f180601060c02011205070206040b010f14120a0807051018030504170c0301060b120c361306081009080f0c07210b0f1317070c090f06 63
    0x2419002d07044240c4890040c170414050255049694045a0045280781c44e08400d0802c00c006601e046d4100030b54604080c1d5068580c1c4400100129081c0c440c90f90a03826076400540842c10014006c06004030070b00d0089000c051030041c20000c10000c0d146100a11b2840d01520007448020003180000c2e048400912241940e01114141400000d8210055034115000850110352540540340c0c0c0c1c40c1003040100c40a0fa065180144c00b041036000c070406086240c0300040003a40b00e60314000d04100c5031242451804d08190341744280701d0f0390000442c0803011003980da109101e1054841011801180d80d4001ca180b00a03144d0700184824a010040c0000507d02110b05000741e00c120348803a44140301d0754422002c0340a000802c1015440304000480c0240003242c00c904124017101c1c00c911001d61a030300d04803001c144000204802e0702c490030380796014400305058180420f81c1c0b5540c10074005d0282d107407101815014003c203c0030401c0303d45000000d081d0000042160f0000700380c007504480759a0010b0b038 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 504104334 1250 504103084 504103111
    0xc10020a18050102060109020711120d0e0f1e0d080307020a02131505040b1c05030c0d0f080c1e031e0c2823040801150b1804060f0306050f 61
    0x482d0360f90014101d0304441c0314000040c0c0e03c0300c00c0d003440903107208502e00319500a890521031104402c0006600881541c0d250f17581030a0381120000c0140d101d0104c080140e0004000c030011403920b41c05440a81d0303070301004144180d030050580d11244c1c260002c44003200940c0041c8044815030421039115025840200810410304008003c035a005149030700403180120794400720080e8903190a600700c4405480e41c402c400c2601010f2900c030b59240c0c8100d1021081d8022101000b02d403074040c6002d00010100c0c3d4682c0600ca940c0d500a12a5a402c80d03100700584101c1200b09001c0d8181c02c0c030041d401051060001c3c901d00720150f03040b4041482c054000ca0034650700300b029058804c0240c1d64102d10019002c01002030b03440c1c041d000c032490003200c071083e045a00255a540044241b0400420441c0c680360000d0100c0da100030340c01c1d5050281d0740300d0214500d20401c07401030381d80204604850048001080043e400751a0200b00d40c15007550340040b600e0384d585500344004602018143c03688a02c0e0030340c2c3c00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 504105584 1250 504104334 504104339
    0xf07060c0c1a030f060105040803040902041e0605030a0f0204240f08090c0f1302030117060f060d0602030718090608010f060305190501060302060331030e150c10020a18 74
    0xb42452100a00440343e481400022501e10781c030990850380100710a0080303039101c50326010510001c0d070241c80b45040d110441584204c000e411003010204481c41c035150300341036076602c480001c05892903480200915900308404590b904040c0f40b00d00c05421030121200c03500c00c4409e0003500c0b00800034010001c0c4410001088042c0307000051864161409441710101d0303d0074040883c0301c041d10030f01010049e030b00104c000b060301540d46141514407640001100d603d6100c0040642040380b0a60745281c20100040c6181c020480c1500250307000780300b514281344216987c1d00740c1825a00950800c0081584a82081100030402d001e4150900c0040004004492a568800d940c1d41442c40f0050ba00113121a0034200344103082d84040c0044d50082c00e52941c0340340c24003401940c6070850440f82c0301005103103800500401d10060380040d6503415103400841d81c01c1c4804000004d122503008048480302007011000c400000e004031806001c020714050380b5030f4008100900114500282c10601c50b02d1182c08 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 504106834 1250 504105584 504105629
    0x40809130e1b01111b01020d050a08010506070807020409030f23040512100207051c080423030903011107050d0503070206040312110a020d08060613090e0f07060c0c 72
    0x86602d107101240442c003904103a00c0058520307410485203040c0700d004420f0403010800c0c00d8415440074007001d9080d0340d49451a0752040da1503010301d8105a00246031400103002d2410b01000900c2124011a00c540c2004035690008041d15000e01c0101c0005081010b156a840d82182912546030500c0a10b515802c410058180c0c1500070f600c1003c0c419120510300f00700c8003c0a00c11400904820b45065540740120300f40b40d552124608550700c280254019064840342c45480c00ca4022640b004130800383c019241400d0510301c162010300f24081c04108107903240c83d036092203020030110300402695110701c2d10f803c0290520089001032024800304104004480350301140c03156100d40d043c10040e061902d00d00451001305140e154480c02158005581c0b152107400088540e5003a45541c0c13070828030b40d03601062000d940946984450f003069050402e02000f00c0035040b07003540035001002c03240c0946c03000081c146040c3c0302d617019070003003003404500005000a2480000180107000768440b94800b03000b40 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 504108084 1250 504106834 504106843
    0xc0b1509061017180f0c09180a1b050402040e1006050a0c0312090b071e0306050612130b04080d051f06030b1206090c1212040e071205040809130e 64
    0x1984520f1192100018500640c2c01c80d542d4422205102100daa18101c903030700f99582c0c0c1417034640d14030840c601d000103403200c501c0510303200c0c1c025103070b00242c00301816540d910b030600c41c0484048460707201070302400f0500740c03514405040104003592042d0010f06284801c0d44100788150001000c000042204820040d045000e1250813540342c44c2c903800100310380b41c0d450000c0010040080c0941c0b004000d2011041c1d1045403007030b9000d4800b80c540040c100d86c02c011b5045550078451503801442c180300301051041c581c1d9106911100000705070083e281241d8078901d250704d0440701216004d4010481c40b014885c14030445500c4000c08400a290b44104002c0003403081e40340c4580300030984c5560740111103031aa004000024207103035088411500380b0890f0651242c5510401c00d00420700303000041a034010000f00714100c3c40e00080c1452800b800c1480700d08820b64020548828005102528292a6480d21489210350302400e5540d407501020170070400d030040404400074106040c200300011031500441d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 504109334 1250 504108084 504108107
    0x2191d150f07150506100c0b18030d020f1c020a14091309060605100c020a03260403050d091205120a0c0507080c0102070b1e0a0c0b15090610 62
    0x103040c2926024040d4040031140b0540c240105805001e00f4440840d01c1c0b1908214003440040340c840c40503106410003250382170741055003d0324111041000c2500c143d01d085654002413003c405aa04c0c01c49442107210680c0e0002c8205882c1c10380c001164580048101842e9103041d000c05020351070040e120758020b01107140301050140303513800050780701395a80da5a0b551002c10f01501c1c0051101d01110b042c00801001184500da002390414900203451320300c2074170819600c9900805130700b141030558a075014003140d031882d0750b000340000682800003400d03c000600700941c400d000408030b0104c0344200401c0171941c5c1d44150310f00701c0400203001c001407012400c0400b0b000c803000046c0e1908031604040390b9180c0c81e004040c00d1402001d0f0702080c48100421452200c44083e02101e80e00d9a0303c1c03900d41704500c10618085504000180209101640800100089070040c50300c01104d02207a02e4001d1100020381d15024105650441400030742451000b550344640c044a02051301c10807a0006040e02c2300c2030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 504110584 1250 504109334 504109369
    0x1061413060e2b050606030106030201051603020124030309050603070f1101021c0605031b010914190e070305012418030b09060405060f1005060c1002191d 68
    0xa242c055034640303404145030104450115015030000c040044400444074208050300e460050400280c40ea0405010b01012603a060391598a0040c04281400603200c1100c001ca0465481e01c43c001d000817038280d440c81c200086882c1026105186190107800c03400c0c69800117016410910422403040d400c60b105009034146d03401c002404001d044002c50080c81039607410500489008491044901c003503000304143c40003a01140d00e41e0b078040320013900c5840c1c000300b2540000d81c030300c000b4071608107040390240144001500218641d003060130584510a0141c200040250741c5008000841d64540241801060040c070110900382c00c5c80c0c046a0000602612142030040807260b4620200e01a90007800440e0080d401c50610305140b160340e83c44644c156026070311481404080340f9078556003610ba078051149080c0c44414603241c00240181070300040d88585250180303100c1b01180050500040c10341c482c03c442c81566162488402030100100e461402d41a02d4104400205644072580c402d002d19228 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 504111834 1250 504110584 504110597
    0x3090d091d0703110f0a020105090303010317180d0b0f07090e15220e150c090d030e13050601020f011e0914030d0f1b080103030509011701030b0106141306 68
    0x9210080e00685000300c00c000c044c03840050b08605040000028012040d0990700a02c040d032104214295240406c0c0009800008010a0f0306d84208400d0010103e40344140c3d44280711500203400110b2004140905540d42c0e080d001c20040d0703808404001076841021400c00e40c007260708280f10300ca2820402401d100c0103a41c03000620707030380360f0f582c820081d504502c440050055404002075140a824a001e0351301d218811494100200810381e41d2051207007502d0348029080010b1035007001070080d0400d000340c0078030001c1a15840c468030355071141e8001c032090140102c0c060404000081c0b82074400b25110f001c40e4034140d500e510301c0341940d5203007402240a200101c0c24002501b8080e0468034004000c1069100002d08540c0240036a0055600300226040030000c5d500703541700b0341d031441000410110000d803541c001400001d00032005010400c206240080500b0b02c2d0300010000b070384080e003050301d028000000400c20250b10202841e607080090824909101c03005901c406d24228501485c0284000c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 504113084 1250 504111834 504111841
    0x90307051e071a1b070605070305160f0501060501231204050c0307031a0c040e04031202090a060201020c01150e01061b06020d09030e060903070b0d020d0207030503090d091d 76
    0x4102a4014143c01c1a4000301031080104580d101e82c04411500140d120407101e180c041c40010500c0700849040317403556440d0140300d0f50100d50b240e0000d00340313401c07282c5c0a605103c08900b841c8200c10f000c40c400e05c000a080f900b45000507003034200d002054140810368071845882d4041d02c0095840b0401c01d00c0700060790781c03a02d140141c1080c1d541035034250140300b40030f400020300c0004203040c403203610b4044d2112003549070010414520301c6240504406140c100700890000b0f4401c15103100c0305000c0030350050078152041d00140ca9003110303070300800c0141c3d0041044c05400b40c0a101d0000440b202d14400902d840c41e1402d54a02004144140e200340020001010620010424013007643d41d4801c4046503200c2103020260020144840c00345e00080708000e0108445c18034130222032015a000b0000e00c0301500d80100301c00e2562000c00d907508003a13000d012208861040e0b0001d030040902c030362105a1a85806e401700303803a048114610004021444504015080c04e185078020004900304d00c2d51f50566 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 504114334 1250 504113084 504113143
    0x5060a060504181b0f0f0206040c060e03100c09030b10150c0501021306031d060403200309060c0c01080901150b0702030a05070e0a1d0c0613090501060306030b09030705 74
    0x40303130304a411003009261040c116030744401403d800012546a1500c3c80304d0345030040741c0d07410080f900145580e008640610166000c4c40444084004c010b0886201020411104054400542e0840007080340105e050080143c41e03400b07076500c0b40d025400705082034900321a20101c09284d0f6500700900086031201d2003405000e404031030507011154120190590741c1c0344014014030512085a4287d81c4058005855010100300319010b036405079110010300003c030b0300c108061500459403078081d11081000080c1626114090a90401400c1c060a10b0100020014104030b1000b010b2240360392628400c000110000e0b9001801d279818444034945807140c80c404649041c1d03040b9005403851107429400202620801c100703505c148500d844c180505510045134442d4852a103181c26401d81100b03801544505080c40605600c0742c0b142d811850b2517544036105421a0004c4e040280026102c0000340240540103c9494011000c03000651a01d80c2c642c40d429250710003140c07005018100d21112038100c1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 504115584 1250 504114334 504114341
    0x61815050f0f1b01020c062409010f0504150e1302040b0627040902090114010309140a03031107080d05060a05130504050d02070315020f1b0109050105060a06050418 72
    0x40211030081d55032100300c0c403140542074015600c01c4049802e4030900320100101070003175500101030300008102948528241491901c1003100c12500110621a200380c2603440d409000d009203100720000d4805030910040c0400d459030403014a800d1070341c201041256810304070040d46c2c001d070b108403d0024488130f44006005443c4056580740d100e000031448901ca88000c0704003404200d048170584546500c1001400103a4060300707006940070b1a40c10040106a25490001d95406014900050402e000b6a1aa80e601e1070800d03082c40551f21045400007095054800c8a424100c4100000e041090740d1f40c413088548500c10981c01c12645a001088461701c52034000006806c004240320989409071900c500203000c1120150703014854010040907072400440c4220540e500406007075160090602400d020703500ca041203c00014013000034040025506844441c00307a4841c00104000c1460f0400500b915000740646109141101d010400c50390800111411901080410728881d0405400304009 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 504116834 1250 504115584 504115597
    0x26310b0c07170c130506100e06090a0602060403111b040b0a1a0a0909140403051804090308011e14040b0d0602031008060c03060105090f04091203051006181505 70
    0x10b40c201941c00100324010685058010055806040107400300c035044055070016114181c01c03c02c40008104800d00c41c8035843c189110103442c1e94602010030f00400c40e030811540c00080103810440501041650091242c104101582c00070003003070800305603130504c1c101210500d62251744e44103c11003a03134550f12070300302c000c0c03030300725a08280f031044003000c4400caa0110101200180b00f200c80400c040050f44610f0002481e00e8000d14aa03560300d03a0240c07101d6010001c03c10300c050b0f90401003030750755a42d4025040680e1195455010035490f050003000102024010407004201485c42407040510f0100e000444000880d0b001ca000034133840815081c80c2d454101420320ba000004020a0004040c0c0803c212000002201c49a6407106480c00c0c01d800b055801a00003031082044103510301c0c1010030b10f03401000c0100b000407a03038001e58400903004100e41e80600403d07120010082400c40f400d400200910142c101070f80345078240e0301c10b941210214001c2200d040d12001598000034460411f0303909 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 504118084 1250 504116834 504116849
    0x70305061c0312060506120f04080c06010f050906010206040506040206030709030b15011112040302210105070206040605060111060c030a0b06030403020102040513060605070f26310b0c07 82
    0x950211a09004000c40202e5000d190f5441c00d0800024050a102007195031401a00215410984403e01284510700f00604195101503080c014000d004009010790750003402c0500402c000145000d09101003003030024841415500103070200030100f0404a200f541c040c0d030403203010f981d84e074075454203403401d100075040a800d42c03400d0010003900e91142c0c602e0f036844920989960f0864501c001000360741c2c080c9108400d090704001d00080005050003035100d100c00b09180d048165007524840382500b1150100d4503800144c1c400c80a20081c48440e11800b81c1040b020701c0e10031103565240201903901c1401802c400c1580c480000003030700001e9a9030015903120030051241e035490a107420f0080c040e400500030540b0507103c0c03440a2880e83e03494440c40048039840e840e01e5040c07520540f54035281d640100c1e001d480185081042441102082c00220140c14002c40740d60340b1400103451144200221403124502044122100051506005400001c5480c4131601075550003840b4076540c100031513030740b1010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 504119334 1250 504118084 504118129
    0x18020702030d230720031609020f1b060a0e0d05120a0612081c05190b040902030105012303010605091602070e07080f070201090c18090206131a030c0307030506 70
    0x4c080025040252807131140c20400d40c0040d91041c0101900c50031010f100d07540c030084e44102040340e40d2030398000d09064000c6040850501035605040311003d2100c500f0707040250400f03810828401002e1103010306001085008040c080442030707014105201c0c5100613410404010b0024284607a0b54201c0390160200d84422010ba6590703150001c1250026441c807242100076034401d00a52100c5d1054600c11a50303103141e40144201860303100000c124024003541c02c25100d842030b0001da00e0902840b80200b00c0d040040801c541e013040c52907480c0c620790320742134480e90600504000035604d14482a400c10000c03141440704030f003000000d80ca48851035000310300b28400301003081815500400075034416a42d41240310459074407803000b00d00300c5001d180001e0040407600014400100e904100d41d080132140800040c20825940000d5416000001307810154403c040082c000b90040d03480c4504c804420b20f40d02400c5040080307000c0817901004101d40109961900000d0385a81c500030171a4000b10040090f4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 504120584 1250 504119334 504119347
    0xa030602040f1d090c091906080609010b120a1e06090506160c15020310090203090304060f08040c0b07031e1701061803080306060408070e0118020702030d23 69
    0x21a45103400b8420070700b80100c4401400f42c00d00c140400c46220700c1c1004050b140c0124440304221500d01d01802c400c085d80740302e05090380550814400c20002c0d026080041c10246045880c0341c0c25984400d0fa145d001e04950a0115030703944000907040c10540e80050214090a0300042444500305800c1c00a84001e0829290f802484404100e1307030b0007500a502e849481c005039800a90b00c8500400004102481451101c0700d5042e00b64042c6420000304c1e0202141259281100c2042c3c3e0004d4488040075000002d040000c035400240302080e0506500381140c65207042c0d1074400d030007000742c4a50010804005550380c2098444c000b030415150200c51440f07011201d104005100058001d14591400b0444001048260266942c000030340c2c0314503039883e64507007523603a031800310380000e881c041d04810141b1000c41c01060522250000d011a41821652589001190003001d00071000c1014014130420050380542c801040e2502c80d00424148040440b200300149142a9034603400c1080203c804a0f1b503 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 504121834 1250 504120584 504120599
    0x16090903170408160318050a030206091207053001180609020a0f090b030c01031802011206050904140d030603030e090403120e100608030a0e24040e060405100f060e0a03060204 77
    0x1212486101484d06c0301c9030340c80d0700034000070034554000030b548a07505001001040ca8003030390000044106c8400d40d0081c030b5880e4042080f07007094110b21000c05000340d400008990240380031819110342c41000707010030803500305094001c00711030b200174200c07944400d500700135074691001880c02054400104280d45a58540000c002d20217005400e11074021100341807125842030144d0740800c00100380c464003031030881c0d0040d40d045904169a490440e00d030700001039269030301c031815403185010b030641202c015030102c00c4900304a80000004203051600b00e051010a604c50700c001c130303440001d8078050b400ba1542c1c181078880043d901504d03035400c0e042554526850348040f420225030384080406008036a01c61908a84038010029081c0c006207102510121510b02450503110300030104c200d0081e42c2c00100fa0203540c961141d00105861079100b0140001400d1a11405074024a0b200040704403506205419000349814440e030010000c0350720404000c2d664044030b81c0000c6d41d100b54215503c0707035508074 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 504123084 1250 504121834 504121847
    0x220e0d03060510020105150f2d01080a1e090618050c01020d020318061605011a0f01020309091801020c01020c07030308070512240909160909031704081603 68
    0x1641d0080d049191826407550050040e1030182c14040c3d92940350b0001c08088c0b10b019224a0b1441d41d00c490700a40c0a14168491068042e862102c8810241c841801c0740000d0f04801d0041c11175045036103007400c854841c10800b20031a004024481001c40c003e01c442c01c01101402d02d0103800308400307940b24060f13002c1040000e4042903c05e002e030213407054428001c100341c2c0c41e80100201c4408156140350300d1201c918040f402080b401b5040c0407405034180c030f5600c078036084440c103128400c0480c41200f8407544610700144860240030003407000b18903019008010401114024042c04154214018140552442034064503c142000b100864032101045030b4142c0d201c0c4107202c190042200d080106a20794459412501510101e10702d8840f11740716100342c046400c05911210004409408400c91250f480c5401107000d01d005400400c040480c100c800c5042160503441440c00c6490502d16a000907044948020209240000d119496565080400040c801c2d21402e0b0308010613024081c01301904581c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 504124334 1250 504123084 504123089
    0xc060f0421020610140a0323030703080a060f03120e0324010e0c03240310060311010809030918060d0b010b0309061b1819120203100506220e0d0306 65
    0x1340b1410101da96004010319800359040300300d40101c2c40c07020610104920010074285014000c0e80b0361036034401107400c0b60554020345412400100304d0070900c4001d0305c50780602c00c003034024507088009045c81c566852100340d00e200c0c80c1c01c003070004120010206c0d0b86c2c103100f000c1d61a121038240041c0130105100e0200d694509004000500509074046265425610300752449200100b04000f691008400c04080703600c92030040c283e15103e0328403007604204450140000031440b0b5212024202122400944807120082c8450129401882004010b40d14440c0c500e0801514420510503071b05c8400202e0b04000701440043c0a03d2550000003400100c914019882803c0c01c01c03d645454036600707141d40504804141600640c00140108800c8900c0426000341480c0300820f044a0042d4603a10480402c115605c65180c0760744d00100c00041d0304003884005058449003070204800d01e09600002c030810504220070054400907180c4840340f401551095050020110480e03500b0503256500401626090 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 504125584 1250 504124334 504124351
    0x120f0605092d01030804050915030318010e041e2304081e04080318011e081012050312090f07091e021e030c04120c030b0108030c060f04210206 63
    0x1a0700c100e503400121100d0b641a0395028014030318281c50171040284840c805030246041050380d002e152501d6604100030611a004060a1b0f100349601a0000d006c600442c401d40740114285080400084040b078102c4080003068000003490030840c2e0072501540c0003030201078a86440740404d010600804101030061440c11240b04020b02840e40381c214824008c5106941c030355802801030740c0e81c68048000d40440f11006141a03e83c503864086e07200000e00035050460080780d614401c2c070148030b00e141010000b900c1901004110b122655a070690741c0c3c0320708030741c400385107005a000c5500d010003442030304488d1451804480000e9140c8001500401d10140e51220412040b11011188001030003a2134921403007120b0700910004407101d50320785030301c02850340c1900c007002c1101150030000b424101e803029000e8049010140d003140b5141d45043c1d4103801c154079680c81404030350301001e400240305510260a10001c0700303d445501e23180000488031040680101954101d55400a41c0052480e20a5640 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 504126834 1250 504125584 504125641
    0xf0f150504060b0c0c04020d0e0a0c0602011a0312071a161d010c0b040c050a060801080706090806240a1502010506060307020a02210106080304091506120f060509 71
    0x11800f000d41039108141e920000340e000320b507840030149003680c044e0041c1d46450380d01041070f0328107030391702800c02406510440300b6800700101031102c6642407003101101c3d401482c05403604403064000950350070403c0c0748a051701000141d1f40c410800103101e06030846c1009908000d16045c00319007840901d005008103030015510304890103e841c0c01d00c034034080c007100686982d03040b141130f40c80f03840220400420982c0c0b00301c21040001841d03124114044020041a03440c6a45541011307001c40c1040500d600c00030400c0100300090064510218034560000d421001401c50400e12461180f101c054030460300740d102180010014421100400311609620580d0007044181d84480411403e80010b03900c000040e4000f00c0e11303030014244200450400c5070015040703104a0a442800380c01c1d00e610381c21030000d030b07040031078204040f000310b01400206590443d24100994288a4010000080c40d44d507580a40c0c1c0b55500d1944031840c075030200c0003902e0040d20541040c90022841090788800050000e0040003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 504128084 1250 504126834 504126839
    0x2c04090807032c0607061b1d10082208040308030f100e0604020708130303030902130501030b0a051e070e01110c0a05150d1a0109080f0705040f0f15050406 68
    0xb1010307003800032256024407814089403d50107001064016140841c6e400c0da4031051045000002c0038100003070b080d16503a1001a1010f4062800700030760980f0414021643e90007400780b81070300884880e521803115035500c40c01c1c904000301075240300e100b500044c207503500004000c42172054480007140710300c41a05c50030300c564685d083c211912140324880c85542240140c0403800b90b242c46c0e001000c046025200003420002214808410311100d41c2c0214046a9904840e508500700102100360850009608114641c555100c000074048010542c07400c4030ba8442c006000414082c1002134038a0010b80146400c0c41c1005000e0700c02c8404a4450380820070320600c0108005000401c1c0c9103040e0f001d4080d0005d0762601052040d0f001e4801001110040b0500906921400074420741c01902200740c03031545031042134000545610102e401a800540012916103540e890008090b01100c1040c1c1e8001188000e000885000b4103040070381c2c0c0115420101c5c0042c60084400401c400c2d01c500f104c1c10090140e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 504129334 1250 504128084 504128117
    0x9220c0e151c060e0c0a0f0f061b11122d010207022d100306051003020307022d100501090c022a0f06030406020309010b09072c0409080703 61
    0xc04035002c0203100103203001c2c4580055515007003031240d0329500f821548054100c8001882124140c0c0001414094000041044006520baa107000b08131070304140c80140200030741d00c0522000d0b4940a05107060780c0c082d83c2d545d03441e07000010300501c6003001a01c40c4802140c0c00101016601207001d14550080820204603480610071034100940c000c0c0920308041c05040031101080c55443d01003007407411b0325000c00043d180c5034052a0214405d81c2c00240b1340c0d0904081040c5400181c0401081601c18005c00c036003a600011040d81784003031280d40b5188660307070074101c100c40c2e904180000030500032859038400d920b4680c0c11090595000000a0043c80e844000890352849044084400a800400014032503139945494441148019205000c1a092a80400c035036500c00d880464120364000b04020344c8020a00c254120031204903491042401c240c000101441d10300004512048269a4a0307440e407440e000c1448040000504244048069410b00811a800c107a000341e02040c0f10b030301c9145001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 504130584 1250 504129334 504129349
    0x4050a020111071d0a090c060809150606040905090a0c0611100903050301063b090f0f0a0c050903060403081602010b130c0201090507032105040509220c0e15 69
    0x1e0b048080b001640d000000c0c4110740704c1e000540350f641140d42e500004008243d076a0070250241c413858440038420300f000b450f06468880c04004682080c505002030140680d59941100c0803142c0d08000401c46072290800e050500c5880400104015419071001038603541001c180e20324640b480003039030990b1a90310014400d030b906070702d03009001600400060080d07601440300360b903294502d108601c0003101c001156217022441008000032900c03540c54171000c145444811550312040d06000900b1a00701008850f01020015200f100d900351101d41c2d101d40e5070b10441c10f07140daa8100900b103070b0f200c1c00c00d410040c100d45425920340900c11010741c04810498014040c402d000100900f0302449050031007008001044411241002c40d522a80320034003041d410001e42c4003660048140c020b150700c003003407020100c0c0c19140d002030522000b0f00c4204001d90b6800078103980505d078007007181420000e02d4000300d20b0b82006c007402088041000400308255045031240c0340704a0420b5500c804150b28581000340c40f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 504131834 1250 504130584 504130589
    0x14010e0d0203190510090318080c0a050103240f0503160f0b03060a080313080f120301170708061501021b03211b010f0f14041101090b0304050a02011107 67
    0x103900c00f0490188090280400098840c02107050301c224491010360030055501441c400d0f00040c1542174200c206c24100307100d44000b0280c02d07008004240c403507808038403409a244206414140e80f95071109010070340c0d420550409031450170100540352902100d48005081d40030342c41c001d100302e81d030b2280c40900e6082d90031700307841018101c0604070b4030f0305a4120481c3d2009101540182103400001500da00400160020a40c2070220f000880e0038440114606000004042c06c43d070b115101040400443c081164150b42605014031180c0c400b2805103460401203a00001e600d1044070b08005880b400c0300c0403061803002c26070a80e5a02d400c0e40030303075240c0c5441091595905030014203840b06580f107010701c4455003810344c080700f5083c05d030508480d60300d85c043d000d44181c490b5181e406c41020584544207046500d003010324200100c0000d03203e5081d01900040008104d5403c104140040360700480348540100204024a50b07030340303400d00d0310320f03100d203510b00049020910107c01e0301030a83c2d0104280c4103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 504133084 1250 504131834 504131839
    0x2f1507110616051b0c090610050d0209030f150103150204030809190305011b020f070e040f08040906030303020c010c020d120207060b1215010905070906050f1314010e0d02 75
    0x5242c484601030729840280d16402000d0100030080d01e20760005909590034900305140191859050210900004003c020704061003031000310700000e481034000f001c0d075021110301440140c0354210003022034604140c2942c1d481091040d07030030b0a540710400012460582e0300c280307501800c07510482d8801082e4041e03408014118003040c4452200b41c1000e001210031200000c4200e010a40c0d03a13140c4900b116101c07541c0d10910060522004540c0e60108a020010360b5040000c00312a0f280100540150f600648018041c0604442070018410071406403806030200c0c40d820001c8503640d180c050700035030112060390095400c003016104c0c2d40e800860401c504190544480340d06804402d5407000a6000c0d9500300d4500780d99940c50310558032420b000f68240c0c0c1042c0020000c054015401304940501640b007a00030300c0c28a0200071100c1d502400c034004071529800d000da1501c58001c000401ca001c0d58030000001e80791561b00040c1e0450502c1d40c2c1030001c1080c0c8070f020380301a10340c00b0b00149a200400294 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 504134334 1250 504133084 504133093
    0x109080a120e010c140d020c010801050a1e2d050418111302030f06010305160f300b0f030c06070b130203150601020c0d02102f150711 59
    0x203850700c1c0109100342d46400145002801d929196070740c042800700c6140300014070f61040915103a80f075010400f503000300ca02402c180700198036100005480c6010741c002d100c07019805001005000409022403409801c4401c4180f00351b1240414000a24801c1c2004180d410843d03880040c0c5418684038911413011400e6100001600640710f400030900c0c1ca00d22550040803074215443d42807028409580a00410b20880f146d1382031100004068901c090842545541a40c0f685c240c140c1c2c2200d00d0504c4c034510744c03d25044076107460481080d466803941404000d041c9049941c0507040340c50744483c2c4604021a002e0b00130a14000505a94081203140f09400c08420468803000c42d00b81485a540201008040360550190354040382c20003038590304031155071458109102407584c05110040c00b00000380c5030502c6201c034640000b100740c0c000081a109001107a4240b048000d1106282c10030134400d80703028041400e07840801130b035a031a10b4aa1018035281c03103000c203101c144035451800c03111200074002c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 504135584 1250 504134334 504134363
    0x1e1406010f02101e0612140c0d03030b0f2107080c0a0302010507060b0d03080117010c05070305070c03140a0309090606020c011805040501030b0a0507031134060b0109080a 75
    0x1000144103403800032583c000200001c0358540003d00035500603140c800b4224190030750601e0301a009047c100300704d03010740e0411822611aa00e45000424010b9090b14011408110341c030301260305094803c90b6990040d101d20602da0900001d644c5140503c101342c0110741d0855918607886468005200c18542e202c465128100090340c403c101034503085006d07450000750b00c480d0200107400c0c484a48070441c0480d0f9100b004001070504a00c403140071054100080c0080b40f0f08490080040c03184c020002c0900c10081010300500005d40b507420003550744813081400008076400c2a40da0b0f5298a542280012148000800c4114860103130300d08036001a0020199a12040c005407029280c5010010345501030290020310b99445000b40c5c0e008500a80c00c200e61401c095048005607136000303001070145030601c0c005806105490044070001c2c85524003801c075040c0c030801d1400307490151090602c0c40d200e140f00c2001c140038480d07200b0081e1076026214842c07221740da102d6041c0c903a0303400d4501614078401540301 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 504136690 1106 504135584 504135613
    0xf02301504021c05040605150d0b18030c0d0302072f0f01020a0b0c0301050108010f08100b060708070c0501030f0e060c0702041e1406010f02 62
    0x6100a626001081039488500d18800078080c640c0010707980302e103070880b0b001640380e80c1c090002802141800c2c02c0c100d01415042d20320303c3d00c008509446902524010b040f180110350301100100342d5070790b0703180c50760350030058505c02150900040190814000303051103554400f00079510010307260409801c044540c0000e10820146106011040d082c0c115504601c1c0341c0d181d00201e440e44038107800003004034101094400d000344921030f0082400188460003010b0741c140e840030f07070391035080ba0b036a40b2002c1c020201038802c1030f40c1600021004400b06ca5960061061444060041c038a0f00f04c0503958121b2681c800c1c5402d4410320308481e130034415503a05024000d81032003089001d0013000c0181306401d0311040c01809a078909040059070504540710350b04420f40d42905111040340b4a2080c0c100703203018001403504881400010f800148141d8050b0690f143e080b80203900402841e0a184d00 = true := by decide +kernel

theorem cover : BRFrame.Cov 503956834 504136690 := by
  have h0 := BRFrame.cov_init 503956834
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503956834 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 503956834 ≤ n) (h2 : n < 504136690) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
