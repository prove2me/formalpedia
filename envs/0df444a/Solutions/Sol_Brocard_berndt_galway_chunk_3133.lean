-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3133
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:45:22.78017+00:00
-- url     : https://prove2.me/submissions/f0983765-cc92-42fb-b87f-c1dd1e5e3888

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 563309352 ≤ n < 563489208 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 563310602 1250 563309352 563309363
    0x200607030f090902030a0516020105071d04060b030c04030b13021509210d0305160f27090515030a08180409050601080c130203070801060c06020c01240605160f 70
    0x64480007075000781d81090340c61b001c449803a80c09008842c000303601060300325252880200b289203000080100b49074041035501c40d07180740c1c0d615204203d480c0c0340c03c503002400c580b0348140e54070705104599801d503134814803047d00d00c4410440030803001000100342c1d050041d0001c00851080983c106500c0090380510041c40e8000e000c03104c4107080b005038031124100055104041c141d0328100a0b07010303003a250014500c2d07241d048070f8090542c0e104e8200c07040c2544400750b0324021b90002e10340e02d580c00a114030304100b0001c001144000081c01d01d00d0350800c92045605990ba034000100e190103041d50b03902070200007007110030300307000301c00302c25001d401c0710250220018800310305030740c10741c07031311400e20700c00b078000444680001c17682d1000b60404500c05c3e40280010386c000c501d107141606000700310403018010032041010f641c02e82c000f40301c500d0701625103400f016402003000e894100182c01d14400c0c844545825070716030b0b000004140d0300550030b440000d40102d0510426050741e07951280f02c11010b0004658 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 563311852 1250 563310602 563310617
    0x51e011127090408090418020d0b09071a0a0905031603260d020903060f0103170a031b030e0c01050a0207090e0f1209150301030f020111010209150304200607030f 71
    0x110b40e0742c40001c24001e901034450280d84c2c002d400140f02c1901e4841940101d0741d0035112140c40180c44a05c2c400340b06035000f866202c01c030703100d8044003402c0030310907409a905103d80c540d01c0c03556821880018865014140c4810580030742c0c840526440e8000c1a89800034808008010408a400901c00d08103c0d2461001c0c1214104c0d80039102609411407420554556070200e5036400c103080070800d07143c000907280c01c11005585542d8030788c02260f01d83c0700500343d41280881d100780040d01a42201001d41540151035480100800000300107001d0003c142d2440c0c413030019410019401401100e240031020b034040e114040c148580755018260000e41c440d200e22514078030745c8180b1814059801c5168164240d5990380d24020204640b146c150a40103804020030001000001c50031684030700300a6080c20400303520032600a000c0d009001e10030000c0d03008809040003011110a1400a6200300d06c100c0c10300c5411402c1c1102d90010a02d6090501e400510400990b00800e01070b1502c04e01e02d5409180101 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 563313102 1250 563311852 563311927
    0x819030201060503071d090106030206160606090203010e04060b01030c200a020a0605040801050108010204050a05010f140a09051e0a050d0507030501110703030c0e131d0604051e0111 80
    0xa01e0654241d000c6003040030b0702d00d5914586d0402d02419a0840001c1c802480407a0454002400e03512602d000011129242c1c05070724200070190b08007030010950303909c04540b20741e0347d140d426000d140308840442c0c1191400c104a0b58540c000e1240142b1003001c0d0f510717110a6900d00030402803040052000d14040d119100680d0f0042e6110400100501a16550715032250324103125a825507a068104030044c0e40180828001764650041030804c03221b00b480d04c22690ba141810513958005010084009840c001419a04507900000344a081f920107a4592a40c81c05510712101c0d140c50711141240d0002c04a1001c12441c03410500c3c0070724003400340c026500c9581e0380765070f036070b00b110612a40080154004101a01403540601c550459003c01d8113154aa05003040b0005849103092440f032541c007681c5d20403909130681e03070b1050517551400500441c5d50078200790034115170310014240d00b042075911001c00d41447c0078040c0141d504111117140c00c5e50034244c0210300005820403100120010b02d007030711000c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 563314352 1250 563313102 563313109
    0x3010615020f0a1707061404050c03060c040602060c03070c0606090b0109141807050c0a0501060e010915060318020409080d0e120403030e011715150a050412060603020d080408070f08190302010605 86
    0x47e070003944245c004107a812207000038903040080080401001c6001844100040fa80224420fa030280d030109111383e89903100f0800b070304c58806c0100e01406051034140007140c003e01d5680064841c26007621441c0400e40d851003150402d800e25015141c0101c4202582d00301e03c0c45a0150980080150511504158940ca2103d01e405000102512180c0d140d010401c010241002194054201d0b4a014805410503c210042e050228403503001019035684445d900d807c40082c5a1212a50091092020712240d0900c001c00f41c1005030380d40c1c4051321380400c1111080380080e48841602d1360500c43d40c03c191031920305450811020301028107001c10606c003c461070460516292281042000813a41c1e01c0b41e134000e1100c01a903003403000305200d030200200c07214160840286c0341105c0c43c3d03400c682a0300c4994904400508a00d0340001d4001c3c2008035080100040352000d081580d0b441000c4420240d5640d6000701204568418040c141c1c00070100d2000040e08a800134800c1800b03400045159940d840c0803 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 563315602 1250 563314352 563314391
    0x1120f18050703030807030905151906092c19020a0504060312030b013e012c0d080406020d1104060203090f041104061d03010615020f0a170706 63
    0xc9500b600318200030703c10140c1103020345810912030b190403c020445640c07150703a904c21081e580c5240c80075480c0095841e220580c0140c105c0c040c5050140400d940e42d0b40045c01070301d1000581c1040110145d40c0619107d58000707044e030075801e100020485040c003442590711408078040207036005030340d010780810241c03034600515000350f203c2c402c00b5006030540f40c4000e0440d44100b0541741004002d8100c4082c21034440d403060b054102e100b00e8900ea8180c4a034451040f00110540d064540d42000304002e0600c80c843c0c600c01540a002d001d540303902e002c885205032201c95074040b1001003000c4102280200b50780c0e60103440038480c2e600c1c0c0018910060300c0d2696103a00980c3c40400140e10004007407003542480e600d00d4611079010b8809000b06450074610720514090b82c001c0c0c40410014550302c0344002809407000130080c20250003005042e0701c46540c071004056090760b1602600c00c031400c184007940001032000020350412106c4505c00201102407006a025120030fa45080d21072010501400c2200351 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 563316852 1250 563315602 563315651
    0x60420040c0e010e01080405031e070c06020703051009230a0605040b0118050103020603040206070f12022a010206011403010b1e0a0e1b0306150d06030b011401120f 72
    0x4603450081c180b0000100600306440c1e0305030400c1b200c4d0f402d107c00101c00005403880110343c540038145400c0065040c00c038a02071914085c1c00d000403408005201600428a031051b039000344103407211801d004020000380c4007541001412000e03080c450082d080c1e2a03d19412610074540709031841c400705622031000340e52040e281070b6607800d0348900420044070341035002800c00300c1c4040140a99859600081c845001c0240040d01030800000d40b00108051000d10484d200d90100d143c41d100f0350403800007036484a616000580c01d141464a601182840c14070b56100c0e640140d0007040075a00b450786201c0103840c510700b251b815640b190200f040070340e17580d500351001102104020046014140800070920010741c4003118520340c0106004a810030300600050b110940701e1b42c1a0b882c1c0350b45010031105e0710000c980301e10301840416810381040310344d0040c07400c0380e0040320311700d5159803a0041000c072181035240300342c0450940031018139011001e070803003047c03040b039800001a0310030351503001940c001a146 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 563318102 1250 563316852 563316857
    0x90302040c0806010e0307060e1c0206030106020c27061908030d0b0a050406030b01090515060f07230c040f060f081f020f041e080d0f0305090d02060420040c 69
    0x420507a560321a69070071051741e08400a02403e460b110001d0010300d6941e8400e400307030210581000400542040ca0121135a02505846d1307651b9444500035101c244007884680700e100d59040404104800c0ca4000c1d8510002c008070110980710241086400702025015000320a508400011314410600207015040441d0802080c91100c81080150441d0340350401c41c0f03d14585501480416a200c94150548466220000b00340c1c442c505a03500c1c6401444013240c0c002c40000e1038104401c118005003003001d01c10719405c16400c10062100780d01c218114451090340e441450504030300d00d00b030381000c0c40551084c040026500d885580b543d0b4001455004018554010107841c0341100310b020221040100070381c1c085042c02d95288500d01140700341d10504000e80007404000c628121101040c0300102100011225455520b20303001c0c0010141c1e8981b400480d00d071600280a2010100b4030011680d80d036405040c40b40d0300e95031440c1400110078a0788007000c0b403035101141c613a10f651050007440b44154 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 563319352 1250 563318102 563318117
    0x40204090b130e07120c0503030a0c03080a091707080706050c3a0c030e1501050a060203070f030c2108011a090d02040b011223090d09060e01090302040c 67
    0x1024450380100304128120002e2034540048407103900480c0c80340c29075101c1070030300d0905c03003040c00c1040c001c2c6403640241350b15000003e044c001064100780301c0e020f61031180e284d800080e41c0c0c181e00c40e812500d440e440a840c1d501d208508250a00d600c00017024982c1c80b4641250901d01da5444600445030210380348100c0130000a042443c42c07a818040444518910b00b02007492860614103104100051400d991140d031513244940f0114002c1c1c01480540828400700c506003d48186001e845140a106040c0a510f003034002069040c400300840d5889600444004104903d03540c04445c0c0040e0141c040d60002d00310a440d0202008501d9147c01d0041c0303d03500c050243d4140005080c000be144507890012101c20068080d650319280c10030913685804072400152a40c4690041e66841081c80940e424a858603070740b504820344071036407003007515100590007202ea42c030807000c55540c84403a007120011078104002009804e210f0301c030403280044185440000340e55070b07a003c40d05440c440a11030f4042140b0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 563320602 1250 563319352 563319371
    0xf120e100228090b0f04030605101401020d080c0714030301060206070305012103030c02010b060d0617030a1d041d0a0302150c070b0a063309050f0d020f04020409 71
    0x42d1102c0e03400508041d20124161041c88409080e9402500c0340c608401300108031710034543c4015054030001e5410000c180000d140604070f0550501450085c3d184113030f0400351664007940f00154480000d090303900c0340c0b0165211006546895000034008581c103d07007207141100c05403002d102460081440f60020400c604041501509448058101002d86014403034085c649800361400e00740d4654143c180000c20310903001c401ca02609001c441c454103c6400601c180f0080002d40c0031004907540205904840142079250035101d120f00d107a01000202c014118400a0100521482c1c81100081c000507041d181110901d000741c0385d00c000c42c404c07500105202c405050301400340d0511880d031a1003150031450240350000850040240c05003072414080001100d404090381310340060400e0100c0e02ca20742d102c1448182ca4036903c20300900c8043d400700e1359801d015001d200c0c4403081d1000248407492413a90f100902c508090445410f99001c500000e4003440d60b100d030320051001d440070b501d001c070304c032550f = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 563321852 1250 563320602 563320627
    0x7050708010e0a0c08010203040803060f0f0a060e040e0708070314030d1515090602030f0c0f060c0c0d0c08090d08092206060c0803060103090302070e01150801090207030f120e1002 79
    0x101c5d910245960340100204000180b45908607a0300480403203010306074400000120b01085410492141c100034420404140c0f00d1b00a400e0a176211801c0ba01804410300742480c0d0b0791984001d203d00e555560112100b440090755165040070010304c01021030f414070082e107400c00180d40854001606030b4080040c1030140c1450410403254155050419060b190710b030140c001d40e01e1140440c84c0c9280345020940c00c3c4224002d0200d1410015000c1c1260503504004015003410f5200720740c0c00300503200c0d0307401030050280981006503006402c4291642040010801e000b202002c0d42421a65031400700918140341d91900484080c5c3c5803d941d0582c000071441c04407004542482e0001c2c0d0a02000c10f1400e0005612801281c0d8406400c3c41d0108051103a4941607240010a801003004800050004103901d031008011140103c0e003640ca10115990b1603c0560403440b603030074040d0004054005e8054200c0c00b44000032040443d8510000700c6c6000442c40c0350610354203094a10116400103905443e920 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 563323102 1250 563321852 563321873
    0x110102031c020304020a120b04030809100e0f06060a2d050616140c1f0905060307050304030f0c02030a03080613090605040b010501210c0302070b0414121e07050708010e0a 75
    0x1078510700c1c81f10401c2c41611505d0041c08014070080401c404400096458007040c007040b0b00a20340c0500034804081d900000e180c80c0d041c0c050b51001d10b07100700340c00590705150082250341107880310100d50080c5000200310807000940164a4a248600c50100107400e440b00380023000030303410320010210070b4a2280360011030030402100324101d0b5884048600c040d661390f24001c1d1500c0000c40c8903c003008141b503c064502e4112640030380e030311000201c00c0250740340d0090000c501c15403080d034980d000c40301381c200152031020400034069050380c403240f20310000a006003445034100100404003031a140814003c90151444407104640c2e803502c501c03d120811842c0e114403130141c2404d0806681000700510302440342c54400b80d400000726107032905201c200d8002d60440b4000d81d00418003c91130f140c5401d0200c1c040c000310640d4001882205041c04488002c0380c01e550b100c218034500c182000c815030348020b489800208069800b806034240024200c40c09228240c03491100e10041e088002c441e0800c25841c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 563324352 1250 563323102 563323109
    0x1b030c1b0106120308071236020907110d09060e0d0212032205030615011206050603040c060e04092627090702010204060e0409060b130e0c06090a03110102031c020304020a 75
    0x541c08c0000d00340e91007107001402a0000066204103400b070201e004100c119551614000c1e4010b0341c0c1070140050351f6030008010038145a14412541d40d0003a160044940c0e0150f481078034005001c94a0388030440c640b00d0490306025000070104801541a261920b066601c1100d0b084100382d1846480c40c0441c04402e5024001c0c28101d01800b1145419080301200b25001d101060410105031001c608051007644668040c01c40901015142d150500d03005100185038068030740491001a0110443e2410f40038108400e9844500c00e00d000685140c420080c200d07442100200300d5040c0407140301c0085d034400ca089030428140108003c5d0540000b07014140703001501d29411640104014403410760441c81041c207403407090f207002604400385c0c1481c0004100a01072203900144000072a826080035400c04c84446400c1426a4141480300d002c0009a110701c1c441d142e0403201500040011803080d031585203091106005883c6020100303501c85000d42d80300c100c041d90159000c0140700c2541070441d1404041d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 563325602 1250 563324352 563324387
    0x706120b0d0c080c1201060e0402010c08190504031e11040509070e090120070f0b0a0603120e01030b010e13020904021c0e150c030f060f06070305031b030c1b010612030807 75
    0xd403d00c00d40c030548c0c00b8001c3c806811700030200103010422036800c0031207141c4401c802102d00080c6510b1401040e640c00740c441951380900c505400b1490140c400e018000d907640c0440790203051301640e001c3c08050139000b442d030882401545c50010b80d8240f10000e242c89990501c4c00041d2003180743c24692881c81e080d42c01c2c1014a40b051289000013400b040c0a0728800303402c403000c540c3d107569002d65840941b0480e0402801842504203a645203034000b501001d52240907202400070045250044a44c0f43c4400074556200d0a140d68290b449050755004019a001c0900f01601d400380c283c4090422034030081c100d40c0c496645400b200080d0005120038071022108021070000c0303007817403140e00080d070102819484580d4440c402080c00d40c0d59002c0d0411a1405c090003035500d0390a1800e000d407050f00304031261821a010407080706038080d0b074074044a10441d2141e9401e41882c214514041c82c2111501c81d981c4690f50703810f0042580d048007403400f0443c1e482079840c00110f10380040010100c94070120712600b07 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 563326852 1250 563325602 563325611
    0x609080105010e04032c060d0c02010501050108060337080c07060503070503040308070c02030f07170a05061303090302040504081908060a050607020103110f0910020706120b0d0c080c1201 82
    0xa9440840c0118654101881d030402c030650304071685902442046e01c0d80c0c08280003c11590703031940ca40000b1100314040d0000c000d01d82c0d0711001501c0440341202d608e94035411100c00e03511040706018080ca407100c3d4021508003040200040c104c400d402009040c0c6100c600400e60031440901045000094515032a040f81541894440a0042c2c000900000c0038445040009200c0c50721078402d5903600c03a002003c481b80d0206e003503840c42d1608401d006514040d003e040c4602401c42000491404030350f8020010001540d4101110b201700101501c218204922003400102580e1180910340c042e0f40112007980d940c400c0c2e40b00381a6001c1103c1c403601705110012040210603a98807050400301d075000d0f990f9559808032440100d00510240001041c03c400c0460081282c2440b6406050891001d46941c0d45080c1860740c04c3c1e90360609071046c800082c4104513160440a07070742e009030540510240010102050a6541c1c0d2030f460040e8002d200c0d203601c009000d10003454140403069045100c10001c10 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 563328102 1250 563326852 563326861
    0x30501270803040f081c060626010608060307090207060507120b0a090f0e1603050c03070b0405060a030902180a05130308040813050306011206111c11130609080105010e 74
    0xc0716000090002c0c1c60701001c1d03841074040c0003003e800c9900a02404540c0c00e81000e803160076600400650007098000392100107500400b130603518246040325605a403002a40c0e203003c104880a03c5c00a2003240c05015080700000c034070350540040d210f624403907180810540341540c4001c0409405503060341480b410000c0c41d280c00e44a000e025400e8030007030a070100701d0851101d01c942c09420508401c3c0424840c900c408403a40780882001c00070b0303c3c4a042551305070362042d01015641c20141c081c402c50210200020403036458900b0041c2650052800d02207114206500050042181c41851404202c43c2c20200510208075200c0c06a01c04e03d006206490719850341c8000b044408001c20040c010200050020b05c441e06803407114000b424000c080b01c01660311804400d078205403006007100c20350305111803440b1540f102c03400e40301041404107200303150941802c20358015004160292008113810003441007c80391102180300580010b45070806144d207401042400c4400507482600340403c24001e21 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 563329352 1250 563328102 563328113
    0x50120030103300f0e0604030c14060712110a06021b0d110307080715050403021b06070b040b0a0617032511060c010204150c120305060102030d09030203040e0103050127 74
    0x9070f9072000780341490102c0324400c000d481050b8071160440d884107000c0341c000100051181002c09803080301410420000ca14810300542d401480e0000304070107040e45c0302071012031090880d00e070940429811901840e1694460b14100d9111950010b01103005000c40ea212540c1080f0180404541d841c5c00c07901c540da0742d0001900c07405081c17070080c50f80c24002140e0050165024150b80646401c2c030040149003810b2170040c0d0f176200b603070320030100400c4512054209882c261003921011500084200b505c1e9075541e0701d100300100010482407030250703104070203d250301c03039412217415207108a00159030f5041906a101014400e131007a09001c00080049100080e100002c48004160251103c0b03480701c00c0d801c2400d0190040c2c2d0070840800b1032400c5080f10250388640d61008881c0144011448800d03001800c8007510012502240582e00810250708500d40e581e0181044c5c0d4040c2c41603a0500d40c03214101401c3e0402a40283e6a6a4603480382000740000004201603900b100c41c15581d82040319501d2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 563330602 1250 563329352 563329433
    0x21921080402010203190908030c070f090e0a02010e04020d050f0118110406052a03120915071b0b040c030c150819091b03060606090819050120030103 66
    0x200011040d46d035103142e00c980140c400f2805440d031034050700e4a86020036601c80d0f442041e8424195a0300180ca80007400558030722440076083e0000e0050035042c01c00b5001910500201000d03140c109900b0042c0c80e4098041e4401d0602400c80b6203244407a0703501d01f0750b15022106880d0603890030f07180344c61882204240448111003c80c3c00600f0241d03220094040d903002d00300418140c599405604680780390703a03600088010001081c0e070004215031501d41c0f0006a40d11079a0240c1940c004c4440f5010a5000e8010741c81181e100c0c07289180d01035614410380d5843d030b0a079001c0d2030072a09003c11090038010040801e03503030800740441c0c50543c07650800000004040583c06004640108038150140d00d880c0a160410ba00f46a00240107440306c0100703458000d000b0886201c196985890000042215032003102c5d04000c56801c81c004142191480707006003e0709402e100304440c190f59880f0820b04400c4484a02ca2008004080040d143d43c50350900b024100500c14000e039101c441daa90761002580c03a03510 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 563331852 1250 563330602 563330617
    0x40501050108070611030d1d0a060f150b03040b06041506120f0510031410020c0d02100c09090f0f05010b03180106261005131103060402010c080a021921080402010203 73
    0x8020407801b9810548c2c04648003400b2004201d40118191001845180d030401581207405240c1080100b004003000c19908000d400b40368400300d402c2010402054442c0c04564210300300030b10004400222400c0c0c0d0b0001003455000801040c010340700b900589449118181410a041c0c0080c0200d04c0e000300115106141d9000041001000641e115008601009202c0480400384000c66460209402c056a240c0349040d60900600c12898036280c15903150050340441041d035245c0040355800c0144400103031103080c1c0c1100e8500c6d526005c0f4a2188864003605000745060400144e030703824150041c40c1144400c040004c590382c10400100002c0701044556501c1100c441d01401d0310914900c1c8150400700c2c5014106612030806041c00200b05002400740d49842c45103c0d41c0c00035842020a261b200c4030202c4019012030010b1000b8070104003100000c0113029507034030540340c1141c098450311141e40741400040e00c0004940641050144019585841c04681424088035914007540000d50301c1c8103458 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 563333102 1250 563331852 563331877
    0x190b0a0203010f0e0c0d0218032a0d0201120903030b0909071401050f070f150606110a030302210f0402092518030b090d030b011d06030709090504050105010807061103 73
    0x45c07011a9020180d9a10810400c0250f68642080d880700958000b40d15200740f1902500c8282203400f003584113082c4034007001000700b101501100081101d00c003c3d0910036810300c0111610449800031502c00e80c2c090074460384000640c00001c1c0180076881c0e50003001012103030702002d400e01c101d1000504143ca0098240b0703040381c0d6280700174a204c0103400f400d20014100d002c0040e841003009405002c030061100c0070802040610340c0c455040ba000308240c0c1c8a9400d9400c40341036400442d109400601aa884030201c0c8134105d24004500007002070101c55610100711120107203c2145801040d840e00301d0081404200041d41c0a842d281101d10f100c810b603400e0040aa03070383c0001c81c50740c0080340c2c0115003041c045400342c580103400c203446800c10007014001a00c0d04100603000d6004605988165040550400100100b80180029907002a03c4002845146000050800d9050040d94440c41c4113200105055140c05a81490020240c020500780032885075030800340d40002041d541c645060741d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 563334352 1250 563333102 563333129
    0x801200313080c03070c0513020403110d06090b090a0c0603020a0806240a030b030607020604120c050c0d06090c090c0507061808030f01031a100e070e03190b0a0203010f 74
    0x40c6041c2069200e00b00e241200fa02001c2694818403c642646400321141a501888030f010b0794400381d8100d100c0c0d40401000501c00d00000c82c80303820441c480d4060940708a100080d0b040c0c51f9110740d80441021a41c003d0f280e803200a030181040600c244580040c003007800d0940c101905020040d00741e8400510741400b031108802c00d011100203a40101c0c1c5036240304120390780d560344080c40060241028828240c081e10401020515a40c40010024403e070340028900b482c114a101d8122251180c0b0101a1424480c4009410259603021111619207126003c0000d2442c40761411601e81c920302d90207503984030714000f21014143d420804451000e940000f001036214030001c070800d880183d0041c0503182034008810090007020302c0c00d14505072801384ca800c09820361102c0031111842c008540d00c00d4030326030302c2c5410006036640e4031000f50090300608185420301400301c003103440c00c107100b2000da03000d461840f20201403080030481c03170b80c1200c20002c2c1981b0b10341c14503240002e140224450f0302204040d9 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 563335602 1250 563334352 563334391
    0x18060108060d080c162102060d150605040504050a060810020d0e0102040b090a0b04060c0f05150c030703140103020f150412050c1005030609061009030501110408012003 74
    0x5000c101c1c200241c3c4582e40d60340b2001c201c05080da58002070094003078000c0381d08030041000e01b80b41010031b01c14000e14802c050341080079400e10000c2c1e00710324490b2162585170680e81051700d542e442010040c00c00d550342c107502c82d443c00003004103881d000751000c0203003480c004092180b41c1000c0b4a00017403100003000035940d05540049103000705081040126107510100f03000c84e15819040061400d00700880b8824003a03034981c0c4d207103005c030b00c502c2c070501011542d01d018031000500d100ea03a2007038203409041502d07030320200643c810040340800c80380c221078400000100f048240d018412002c80c481e540003505055030455001c40c1c1d88000b640c1050341b1a200c1030740044040500e050450380a0704290150055241241c80c11a6035016800c9000c0d01c00c9101c000f540c41020300c01c4040d240704400040c19a0b030715486000c140002c3d03c1e032080da0001000310400010011070b40900403c000001c242003601e982da440d0580050071504040c034007038281c0c81001441e0050300c8015080d01e03004007060200680c0404c2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 563336852 1250 563335602 563335609
    0x317071d03030409060b04090b01081e19230702071412030c070303020f06060418110301020906070b09070510020706030203072303150901050607080706140916051806010806 76
    0x1c3c40c0d0103000300c2c908017140403505010590203882107802c4407400340f040091940040d01e80d10012505c81980c40000302114888804103042c13290481c0a611001518040e9201120160380070400c0c008180c46040c004411300c5044103500b41d03032210903071015150301414418400d01080d01050200d11951201600c920869414403c0341c1010700f01204948030b9642d24940030b502c0301d4150f13206407800c2c0508000074040d03040c940075040707001c0001900d841c05d041c45660f6140c6402c5141c10030b2505036509003d00022910740380010982c8a0044000d480645020f00e0038034171b0b044054101c11700032556401d00000c05900066944143e40c1c072824056101e40d0b07a8001102e0400c091111000d4000c180c1400306100c2500500541c040c0c01314510800030400d4040034400392607820302c51346400840130003152010a0f148006000300714440c00e0003040040c40e9844502c3c2101c8280d48804154121400c80744a03100080103c000401c0e080d2202001c1da600040700c0102080028441814854080001041c941c1e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 563338102 1250 563336852 563336857
    0x10020c030c0609101b1413030c27020a0c20150c060609160c0f1b05091806040201030e150411040b010201020412080912060708040317071d0303 63
    0x1c0c22508071081807404401c803669074111158070002141c030b00400b00d652518040c0c804141e900d41521070807030b4074008020074403055115440881880c11400700110002c0e03040220744c1c00a00c1110207034900034503100c01d255010707110101000713000e500c10001445200e800c003068440da950040c0441d0b4203000c180007200b8082109078021588064000110380c58000380c1d0001d0850f948036001140d14965401092200c240d80598100a10916880c14000b80c0c1b803041e561204c00718410094071002c8030180d40d5520740c0d8aa42003100c010321100f640e05010504006e4811a846881c00c0c4003031198020343c9803c2501d500000e00003a0405031900b000c2c10441c03d041080c140c44101c814043c60036840c041c200784000010a58087c1c0c0300e9814410303811140c0d03105000360340507105003030101007200c485582c54141030361040c1c1c10b0780d42002c2c040d40f100c045071209100c098401d05035034440d1011403a161034010035942c03a0182e41c0903081840da042c0301c266548204c2d078a0740160702080040c04032100000091a50 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 563339352 1250 563338102 563338117
    0xd1b11030a061415011b0b100e0a0902090906070c0602090d08130e0112020303040902090a0807060201020306040f1b2102160c080609030d0f0b04061e0b04050310020c03 74
    0x301d042c280d1038124600c4082c3c01c80d119806824241c4501002000115400c240700c0345c1c100c03458010041e507140441c00711301d032003900300668044c0300825940c5e62140c4250200d040ba400c280f0181c0e100c2c1810291b05000840d581d108140902504241c03510b540007038021007022402404880c0c2c0400c445d81c0e2a150312880c04205500802001d4a43d0b40c050301c2100c1603180b5003e40d261042c22080006001d40c03041c3d44210005030b004000c1c500385818541c02800030340180d1140c80d03100034102d80014007031409014071000303824940d00160f0b40c3e00d0f04a00340300543c0d4211452407112450710420f0000c4112070021100700300f40c2d074640354806170844985030081280d10908030141a100044043c40c0c2801c80000320460f81c864490070502a07500e11100d034461104032003548030340c0c00030001420302e18141c1d4003159a0720700300c4400141d4403c0050105040383e1450708490143d10004c20b4110411503443d0a4800414088041c607240a0070200401d1715407003001c4055081035004540e11420090030310550740c44 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 563340602 1250 563339352 563339363
    0x61713060b1c140609030901030e0109020910060f0c0f0605100902040f0e09030a0807080712020703090512010c1e030914030a12090b063d020d1b11030a 67
    0x1440030500d00c000042c2c4907204120381510040c80400320035000440c0480c07051031084095418000454019405801c19050100d159540c071418000182e444201c01c074000c0d1104a29040b011f030911001601c6101d400302160240070140500a00140403800302d007013a594441004162600c50444040d4071405640110115500100740801d60310131000782001150f1811070a0281919910004c507140d00c01d60b0105c000182001740040c035094028a011070300f100403842d151707041e0509641544104c2c2c01c1303048100c0c0000d4000c2d800304854502600c0c00c840c2d0005890080005001c0428043d00d001c111a400a07048202c1c03920030300c0707614025402802c81a802580c02c41d41080030107501e540b0780c0d0106030400040341c10380050500f55403e91180b0040581e02011580441c0c80741c0f8108030200d000280c4e2074950303e40e0b00540d400010b4a9000e59106160903000303016100315103c1001c0d0400c0c5150700081d0810442d040c51002046540001038032103038000e101c007808030301d10303001180c10702c1026a800b03040c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 563341852 1250 563340602 563340619
    0x12161103010509030a09272f0a110c0d1509020406080313060810050103022809080624040b0102071d01060e0a0e0615090d03050d0501061713060b 64
    0x408031070110083c05c001c03c444e9960030141e92034080e00c407261352000295021042d1441c840340350041c0e46030b015400024100c2d403411780c40c01104000315071500c001480d001d201c00000c2440c940c60b981010340c2d44550b8039070b1800307080b5510f54240440c481c081c49000c05040c1000588810810340340e15406a08146d8000c0c1c418001c07030351140c0c20a503580d44810b0000c200800c807000c2c002486441000d11714003541001c90092455481c0c038004401075040210b1144045e0b00c941c40001001100c8000c00300016042d485640400c1d1030b040105081000080c00b01039170f40d4890036000800d003000005031000307203400c98000450280481c0100e1602200350020560740c0461500d50f006900d0100b9801d040303400c0c030341d1000040c1c0c0b0302500b480309200360f510543d402d802151000c83c0c260703c0d050035003403446994001c04c2410100c08000290340540ca101d02680815400181c00c6c20802c03142c0a40c0e40034051500b08000307542c680b100c010301d0b140001003000140e01c00c010510010003a10380c12035402c484009207002d4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 563343102 1250 563341852 563341861
    0x101b0c0f0909170304050304091e09060e100c0c02150d020a1709010b0f0904061415150301050a03030c080705060f01081b090118060e01120311121611030105 69
    0x5000344503100083d40c11034545030304415401c4440045a104903403000186003403510b05107820002e8440c505400b001c402c001008808070380d0542c0708500c68540510310110303004882884950030a0000c00c0e03c02d085506003c3e004403100c0d0400d04c44991260305680d40c0e8200c2060f00c456018a019048031402070b107000181015010b544401c00c81d03030080060886244907203648030780c07078201c50f642c00782e05070801c140d0440c00105140c081c042a510a00802c0d01047c240c807501080045030600305d81e0040300018600740c9441b941088552205c0c0070354102c00692035541090009032950b07415100c0181005964070812040002110548000303543c010210b404c68241421000f510040074001c4400c5071094608090720032600282c003401030f901c060155a1242d00b4001d46d07034840d0102620140142d13440b000f00041502c488042030740200344600c0300003c59070081c80c00814184200b02441c00380d601c8030789043c8a0348121011900c00c1c04203001c042c074828071246403c0514658042c8200d515500e00030800 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 563344352 1250 563343102 563343119
    0xb03010509070e1f0b0a05090d12020706080402030c0607050a060501060305162c010306050909060618040b06010f1e020607230423101d101b0c0f 64
    0x103038151071290925101a50703402212140c62103106040d6504c0041d805000c01c0f82c005800b00804401c00603140c40c9103030560200100d640d1803030b500301c12600c80307500e2242564007a038144125409040149840d2030355041c540c0000e41d68210f24500244074600001fa01c5c0308003e000c0244400c881e0b4880d2080c00103603503603840903004140c222403041442d2241c090340d4130350601c184022201e014802040404d081e071a8031152100e005180c41c414181596414085030039a104d040080c81814810000e014a141c0074041c04444c211491307100310b41c221481c00b404000b8001210080e4811000e1801c9070801c5600030007100c5100754800c40d15030a24054910344c1c0b100394042107091041c2210b4860b181c040c03451107440300c00d61b2031413031b20100745082c107020500500c01406400800c0341041012640d030030003071f080054402c8c2021140b0002250340b070400d480601b00644e090015811084455030108066058080c0c15204010040300f401d01c084582e450404c00320b1420400905428a0f0b40a1501c0c0c482080 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 563345602 1250 563344352 563344363
    0xb0a0b180918010b0d02130b060c030f030a0c0906020d080a27050f190308180f1b0406150c1b08100b15071203020f070c09140c19030b03010509 63
    0x6107910f50a10100080505240c1d248018855001d0030480c90401e403040c483d40242000103119900850802c02058904000c1000d0120409181d00701e81d582d00b8455042c0049402c0c030402c000038801e907100200003aa40100e0301e1003084c0b0440c100300c0815510817241d50020490794807080d02d01c0d06a00001c1c900a42c40354540303041c9601c200c044034035504103d01116035490044050203600c098603015440040c0c46411700135000302042c5918641e08400d50b60380c9042040e9140600c100c1d27441076140c00881031203c0c080e01c412030001d51f000c02046042c490115400c14944444400740131000e0003030b2080166116440d5101041c1d0703855074103030603100c0f1115600e0b02c041c2019030711400d0901c10341b00c2c814076200110350f84a001d2407001c5031030402e103580d0382e11501000c40703010301c140f41d828000d030750552000300c00600c2c410b44550b182690381400c00012900f00c588001074070b80c0e81d03541903040098a49400040381e603081e2012581461303600d541d120490181c100c0780415a0554207000600096207000a007 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 563346852 1250 563345602 563345641
    0xb0412050906070c05030c18270d020c030d050c030a1d0406060203031914070e0d060e03070b25030e0309041d07051c020904030c12170702010b0a0b1809 67
    0x90ba048822070504214052200200300355242307012a000c01c240c90b0a145000c0b003241c041c0c0c0e19505003983d100c07440c5418035000380c4e01385015030090540e002d614070f41402511040420781c1805810403004c43d050503628082e100c4900240f0151803042403515000285081250200800c184880390b10346000a481b0b80060300c4501c960140c0b000d2040e15101c5c28060f0003050058949038070080d81c6d82c000116102c000754100c05800141c0c0d9000100451020301402c1d40b0108480011a584d202e0f5103032000c21050001c103111101d200c10010407007a080114100041e120161030007107034841a10f0100d43c2584140301d80c099000c0c1c40c11807002c92280200c0c082c800c42205d01c40035128402d55a500f4050040119041c0000090440c01c8080062800313001e501c0d0054043d2030940e0a045407940c80c04841000c10f007050011030107078452203507141c10503107613581d00c0003444c4020b01504450b1000700319010714a000300203122101082e85421516988a02100c0b054000c0502c0351a0400c01c81c0c07072145008501 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 563348102 1250 563346852 563346859
    0x30703021507090e1b190203091e010f0f02070b0a260601090b0c010609090b041401151215091b060e0a090e1f060f0807030b0412050906070c05 63
    0x35038442c003605022045134200e4450013110340d9000b4505105c10441e81c2d40c5d80101206210300c4c141020188101049460b5a030000c580d559400d408110071800b2109012184001500c0141110707648007500300e4072850b00e420301c60b06401c42400c041e420b1002c0342c2c201004558002c101d107000c0607800103a9600b031100200c94003901111400d414484078204031441404505d421800b000782c01c01d15401058a034441d6400054141d84401d9084190341d801003042e20041900e0082c03200b8014803032022090210100000c0040e02c0d034901340496108150711600c9000b1204a00403024032107200b07212403010740d54102c10404043d071403802c400b80d02005d014000e00c1c02204100840c1c56400780d0000b01c1c040a0041040d681c20345055480000f4008503882a402c900134207503010345d21003c111928003000000d00020403000e0038400d03a01b1714428680c0c044451544003403410004115051081038209070000e409136540482c449040d2583c0c0f01c0c0005440e0803400c0000c1c044240b003002051103041d00c1044 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 563349352 1250 563348102 563348143
    0x80f1018140c060c010c081e061009030203030f03040308090a15091b121a060603190f060e06150414010818060a0f1404030e060a0201090209130308061c11011103070302 74
    0x28880306601c07500d1464002380f80c0c00301008949103180c100c3c00302b11540740c41d00e44030600580741d030301190070358201c16103080000c000071050204058104070444d6021002000520b842d1a45813121003202801e84080d00c007040d6100c94103400d104032502001c00e020311803244110031503640c00951841e1440b80006546d4804584078522041e02d1100c80326026600062449086840b8181c0406080b8081703180c001029544180b1000e81049030b000e14001001c14400c25449450090b0501c1801400644000c0ba504d0040209100c01070280700b0810b2071030700a280003a5559030300ca100c0703040d01c4500c3c3c4d40208103102c0c6c44204100e4901a401040210070303c24820320501a10b0010029003460070354008004c204000e002c86000e0070620007130143e03601c2d54400858070544c0b94010a036210400e8480c070f10300300c003000c1c205401d245d0408111a041403040d03c80104015288400c21365202100030010851290708800ca1103e83c4174140107102c42c844071068a99543d020700d0041d5032044802440c460340c0100 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 563350602 1250 563349352 563349361
    0x403020c0904030807080627160203120c090a05090901020a03180b0a05040507090e0a060c0c03050301142b0b070e06040e0916080f1018140c060c010c08 67
    0xc1d01007a40034592607120413007161035400050302c0102c001002d031a0070151840309000701c12100310002a03c86145000b07011282031000105040115000e0381a05540c001c110100b603481142d82c010354804000c42c480d94503000c4400000e02b0070007950380700da503000b01e403101071040100c0194024108408180c404002c0504059140150704030004c1000e07000a0030440021808000340d0090b903445403056081e2102d50340c071110407130111078880100350510b038071400248042221500c01d03294410407508000409980da6a401060762205005891042c4541c40710071055464900c01d0b80011810910201c000ba116503000070705800c000c05081d540141000c1c0072800301030140014030480c1c0c0c00540b00703070701e001d00300000b440407400007030425486071184000c00801c126007824108044c3c00340201a0120b03a104a154510304102c9501401409290841c0300600c3c4401c201c044511301d9108246541c1031955140890601ca01d04400541000300001e0302e000811042d4420030f00345007640c66143c1139444 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 563351852 1250 563350602 563350609
    0x20706022a010b1f0221040302091506040611070f0b0903150925081c141c0b04090c1403010e011509090507080708030307030b03150a0b060904050f0403020c 69
    0x40b09480540c00103240c9041081d03900320f5118243c1d00c0c9104d030044980d01c4410200c0c071415962022100c031003010004c9030600440c42d0511440742c00500c180500742d0400922400a1510710491203114140b00800c07440d003030611014003c903001010509801c0c01144d558500d400826400300c201240710f0301500e0340005000c03200d800103901815000d00207185500c41c0c040e941040307107031000c0240c5400c0d5801800141e01a002c2210003606020425001c842c0101c000c00505483c03826100150404030a000307171000101407584a05070000041b0b0049202c0c1c59280c081030041c19020b6010345080034800000c50440004405d056902c442980208600700306204002e00302c41c50405158130302d0041c0c0c042003041009075007121141c103000d00155a00b490352504828074004d1a41d2002140e03410100800c020b06030544103a030744c5044168045c1400404d11420145100001000e10740c42c00e54860740c02e403d5848140642c0c1491201034002c11083c140300070a0440ca02c405c40f8118010f106004100740d107401d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 563353102 1250 563351852 563351861
    0x503040b04140d1203180b09010b01020105090f2e0c110f03040e04121403040b040c051f08090f01180501051b031b0f04030f0b010506040b160501020706022a01 70
    0xb500000011030694a8400440c09850303401c2645190040c551503d03004541f402c3d01e918019407a05000003031070f0341c0020000e401c1d210000c00c1e40b80b1a4100d03400308602c04034046250000116502034103082041000d4038018121500b490f02e9000500e002145944070740c0083c03088540100102c2114404c4e0412070003160b4074822402150072402c80700c0b012800291080d00341c4000600d983c180012818104451411142c00480782030b5841010a4280001d104442c01818080d003802c0d00c08000d680000e0035a5500031036442c0441007007022650000c2c05100b410f000f400355604500e0020b103c00301284d0003d20184000517410395240d407078500460f900403520702c4505021101501a542075564040807580581c112071b000e02640b0008100c122180c0300084000c0000c1c62080344485001d81c081d0400cc0d0721220142c21039030003050101f00c01d01c50711041c80300b0b661031806130114040301d04100b07107480c9003e8001c6100007459030f0300203d0b0003001220f0710b41030303200715060040503170100403420045c0500f40c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 563354352 1250 563353102 563353129
    0x12110607090504090821010e06040b010824030706030207031103040609120302070f0906260304170717030c10140f0a0e0703050303060f0d170310030503040b0414 71
    0x36801c507100300420b0909420408000703018044c0181845038841d410000101c001c1c4218240c03a80e04c1d4010711460282200064000e241035a040004000b001e00107400188003070910030003120f646020034141d41e80004024400c00015090745c281030b43d2504007030042d40050030304030081141503d02100007000001541c007110283d07520050424034044810007145010740d000c4e0114003c41d4004161a109c11140740010191444005105403a000b95900400100000703c0c0c0c55104454512800d2200041640d00751340007000000c8110380f8100c0070310301d0265079030700001e5100241406900e02560102c0901040d40304101a0742d0f1031140900e05604651400c04180e03420070201c0086641c61280952265006464245c0040c500410310345961400d44030ba4812682c0381d2002040080e5070505240350400f098054642500c2148541d680c0001d4000c0c001088e4010740c030200000e850105400113a100035500308081ea541c9540700e008200c06a802401403549299103641c1c0c1c2905d508103401022080e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 563355602 1250 563354352 563354357
    0x90a0230150f06070201050c0f121305010201150302100c1403090111071211062a0d0306080a0b06011407030206010302090115020d111015090e120d0b0103140412110607 74
    0x1d081300b0364015244d0340c100b0b441e458000d124410491a110314100035003418040360501e101c2c3ca501c02c2e604081c00c0506142c00103411641840e240004da070380c816114406595044a44140c280ca07000011150b48481103005004a1001c1100103840f202c0400205025031007a625810440c003410303c0b550f540c00c00c07840351f20f420721800c005c5d544c00b02e0360080a0b50903111008003074515100c6421043c4080160709141442044e92a0451009101c01002410807820f030f103007401d200642c83d001c1c80316101d9241020142c03009101d0000203400744c0c861513141000040440d0000d46505030342c00e00030354a0400740412402190030f07400114184034090040c1880a220354000c0100c011180320440b09440010009030395440359003c0e086600070315002e500c4840a1403c29131440360b29041c0000203844c1c4012810184c2d40042d440c410741d2514103012504010310080c1d000c1200180c0d9401240240386c025903543e004000034007030004002c1c010050740b5070901b01c0d035a482c030800d0100c2690f0b0380755441075500001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 563356852 1250 563355602 563355607
    0x2010219030c0210031e110703050f090a03080c151014130219021207030c08180306070f110606100f030207061109030708010b090a0230150f06 63
    0x2490010426a9114034441d10b02000c04000e240c2c003042c88800f013032100d000800e442d15aa40503203021407081903401c0e08200801e003c000442c4405200a10030b00c100502000305c0021806460034080c01152844000a040582256901d0404850700d070010201d004d400d008000c1d00c000c02c1c002041010740201c10b4a03021000341d928011951000314000d40030036400034400340140001c0412440900034000b056207424201e03103ca903400905010100d0ba440d489410280301810220340d12a0083c5040307030b84200c4240d83e410945543c900e500c0d0131002c1c66507240c4261000c02010951103160494491030f0750720349400002144150b1034a07400115a140e401520032100469298800c9a01170291803d03410014a1301d8110f4480c001650f06038032503802280703800202105241010040034009201c0d4074020400002100001000000d001e0290341c40c00f5004108003507110440e45a40101211602a08020032000d12003225070400454000322600980c0026000e2401d0407481c0d28038841005041e5071 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 563358102 1250 563356852 563356873
    0x204060f030917091c0302010509010b0102060f15010c060e0102130e0f1506130f050f03062511010e0a030e030102180d061508030415090510032a08040c050d020102 72
    0x65454005079107107640500b10156448408084a0345c1c00b000078040d60011410740f506489150940e1011000181194403640c02c01c02c000ca10b4a0701150004502d601f00045d006c82a40101ca01c02c1e06094050060707450080c40d40c1803000158018101c5c1200c03203410404450b5a410a480c10400407950b200d02c51030400000f403401c1910b01c0d000e5410210050035a414202120703044507039921250003241c1d45a41e0103500f40b00c58a0404411428031804038010103840c90003000c81c50500c2c2400c140d50b5a543d0f19070b0310414509014080c0b050b407180e507441c000c0080c110703502e03255541d80c500030b03906602041409481008a041c127008445940400815580f0b4001e401d2051042e0009100b1050702c030507a540070020300ca458a001c0103001003022800843c1c075503040c8520002d80101e200c141a0500c080d0220800c61a10340704042d12803482203041c0054118980801d140400c151030103101040b20002c0a130004164006003424060340c0a626445030507500c3d00c0621400d00c2003840041d02580c010602c00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 563359352 1250 563358102 563358143
    0x602030309010f050601211d010f0e1606110328090510230d0c08070809010212011712031317121308070206030a090b15010801230604090204060f0309 66
    0x81f0030a02138401e00150345101031808032080c000b1032400035103c1c0d4480e8101c2000c5205800b8140c1d81d000240084d04041410b40d0050588031030070700c10321080c404403040717919078418203205580c03d42e141c00c02c45c80c0ca1b580d15080c40035548900742403000b000c00e051003004078840c10036a914a050000980741c104c980c007040300c40000401958031340e540f41020100701a400104103802075031040f52032030316051b03000d050040707018107585d500525182c41d40c0e1041c00610050f18540248074112400c076a21040d580740c50701c00d02401d0843c41040e89203845000003c0c0002c003080307504092406030040b0030f008414400c00110084074401c001c4442d41c004408000f01314481800f10114014a101e04038151170000c0d150301003146170704110703060701c0203a5854181c602800300b0802a1039006644484a0807000842c40000c0c4c1024018040d0090040380c50301249000402007110359400c4070001c0100d9180c1703036225044800f81d406802404005089004c040680034002c2c05800b503402c1c1d024200c08181181d2480d50b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 563360602 1250 563359352 563359397
    0xc020d02071a13030606062604020a0504020a1106070815240f04033809120903010e12091005031009020706060b070311070b0405090f1806010602030309010f050601 72
    0xf0a01d0389035801c0010000e44103201d100010003440c0c8494590a44065042e00010301c01512801066415010800160350305599a02500d4080301c006865008203101190384240003a08080c10348103c2d014000c406800c2041c1902c103107a505082d9050700842414416008103151959141034802d5295030304004c8036001516903c40021140c0741000d80c0c903243c000c5c115070003a090a000c072080d04000140c40d1041c1210841001110f01820006e080412065580e200c461500070880382d00800c00d08580e80c1e0a402c800b14a400c54800c5468521450181d0b04060740591110343c440c5035490a41d900c03150250702a64800e0980910b00380196103401c135440e01079848140221207a0780d072640081f032421840d4010300074403406aa18241d2030152108040d03e8000d003500070300254101030104000301d94804903034941c000d1840c421001d1640700d00007400392014044101c1c0313400380281e4001160450340000958885c00c80400240680c40035a1a928100c9a080c3c42c00360002e442d000e080302c00d00a11150 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 563361852 1250 563360602 563360617
    0xe03071e080f04060807020d030e0307023f06060d2114041509050f0607030315030203030a05070309060305040b18070e070c0b0603010c0c0b0a110d0c020d02071a 71
    0x20711500c0e0500d41c071919401544541c2000d804030f2403400520811660400c0104050400c0d41002c120244a203800b041e80ca0080140c002c0c0b0035898074080d4001d0045806e850f80c0407070301c40b90004590f05981c140c441401e0280c0f045410843c8a40c00c00141c42d480d0043c42c01c0303d410b8002c4085448418050520b40c4e01500d4135a4003024040410403251035481c01000402c01032410b1504040303040c0180070014121280b036800a0b105a2000c1c0041955555610803140116450308000411911005d2a5038800c40380385d20180d0706020102d18601d500d80c010b4020107400e8800c0da00d48806030b8039144281c00720742081d02c01138402c82080300000c607240100183d242c21582648100c0d003006030f6415400c0f0812100b11903203000503039400d80071380401c880101c0407508410110000d005446009000038004809064080c020901d120b01041550407558004c500000e80f4800c4159681c007492841e0f0302074001d60728000d00500c01c2d4911000c1c070601c041085803d840d000d00702e2922180400d400242c16800411 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 563363102 1250 563361852 563361863
    0xa050d0602160c030312050106270503010608070e0109050403080c180a0b040810020f03041b03060f09120302070b04080a0201150f060e03030c19061404050c03010e03071e 75
    0x4000c141100c86100b5101803180706a04201a25083d0f25000b40040c02150255080794107003001440102d800c64106655240c0c8207040440800c0000b100200200340b0358010780d0554681840861a04004204c00060310b0700c2080550310b50f641c5005402c11904120b13000b41c001428517010408890f0300c40c1c01041502880e6000c0d0000941c018001400780002c0d074000700d071946c0300240400c012501400106092047c100045050241c20300504406120041004128400c4504001d281642041544014640100f0104640c07030552000c01c0043c0350010f4143c4442022100700c070382662280c000c43d28607d1307101c9510561621030380d07146d00a0780c1041281c01c0543d52078098a406441c084502d44004198032250894103e25129000e4216072841300076502079001041031000c0c0c8000001d4040d0345aa10b80d98202c05c504060501f0002010402142c00142e01060180018068005111000d14104600800c030341e119041c280d40d40c0f0322035072100800b00407110002850740240881313030340003060082c1c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 563364352 1250 563363102 563363107
    0x922141912230d050603011803020a12030207050304060201051e010503030909090c03030c100b1c120909020307050c060c180f03010f020c030d0c05090112020a2106140f0a050d0602 79
    0xb8501110b8028000003c02c0030b41d1001008082e02e024014481d41011604408403da022500c0003910b030700d0a040041c080d515280f900c841e00d030303100350304940d0382a0304581034a41380c2d80c5544000340a8401030740c51200582240c51960080070200c80345c2030484a00074011440c0c840e00030288030700c1c0c450040140059002c4c60700d08000d07585040c0000c0c0f8803100000068411a80c010001908a55040700141d001e10700101d2140c0700403401400c071084441d004801700c00800d68100c011204155141c0046180500200c180107010b078011002e440c6110040c01a6181360741c82200c48482c600a0015401200041522444c61410803a500c1d81620074040d0020031950041d800500030f0340c0c84201c1008499000203007403070300c0083c01e210b030b00d011200f01d02c0d18501d04522280000c10b4000d0404070090a00d40c0060310b190010701810303003144003821090942c0b00003d43c03039004c80000c00162044150030042c90030804442d141001d0040d0300b0200003440d5403070f031034100310074004054091001294119400c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 563365602 1250 563364352 563364407
    0x303041d040f08130e010b03090c0d05010e1504030f08091e0111040627050d0602032502010f0e0106050612040f1e0c0b03150922141912 60
    0xd201c0146402644c00e05480805403900710075071290b2005030b01480000a00303005200386003001080e1032100001c11510101c0202c51400d000d030042601004040c03041c032900c015150018114100f043c400e40c007070b86806882e4030400d00140c60a420403120800c894001884c10010310211179502c0b074110400300d0002510305040000a40c840c0e1054005034046000b200c52054075034803e0070b00d80031983c80100150000c80c0340c440803e104885116004207200c0c1c001c030003d03002c60388020004500008030208649640202003000e80207140404202200d40d04000c00103189074014000c0790200c0f10054900e503d0000c01070005034800c440500111a071000040c105030100341c1e1034850160914961041000020f098a4070303000807642588100d641000c1442082107a0380e4083d45824542404e40f680c0c1040c0e5038800d0b0404030224500e00c9c150010320705540007028860030008210007c071003581142c03800094403140592019200500406040010408800103031255102d002d07a0350a00004d005581c10 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 563366852 1250 563365602 563365613
    0xb0307140409050105041506020c130225020319170304060e120a030c09030b0a0b060408160f050a030b0114061e07020102010f110f09060702090103030c050601050303041d040f 77
    0x415403090b5121625040140054a41b0b4071410f061a0b0b091068041410b24240010b1749030042c60080520032890081c2c4c0080815040c1c0407600401c0c6114454450501d040110310302445003540144c1c02440380b0104103040b8038083e00d900c0d941a80021107501a901c480d168210030703034001003040740c0060b260022a01100403c2003803c401d09401030101b034542005c0d041c01002c0307d0840581030100040b50f00100013060000540c10f40140081602042e1800c810000c5803507880b580e407108249201e4428080c5000c00c8000701c03001640d402824070340501c0e98800070010210030300c0c04040d0260003010010050740c1c561424110805c000a0125410018800000340d01d03030503158103d103815000041d01c8800c42d0790a100340009020014010881c003440c8884c414400d00880c17400c0c2c81a20000200f0180542d101010348004580c002d10400d000d41e1a03280c010603407603404ca41100c00b8841c0100229862030040140c50a490f0448001440030340032280110404802400644004501039202d5003ca030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 563368102 1250 563366852 563366857
    0xf0516060807080705030c0901031812050408100c081f03050a24150504090206040f0308040e15030c1c211409031504020a1d040b09010b03070b030714 66
    0xa841d2a0441c0702d240c1988041d00000b8010520410000308104100c030040041054551006007840c00003080c108401d1041d07000800d0200207403440c0c0079103c5030240c0382e0b8050000e0090f40e50f200c1c1650f03407901c00c030743e00c0905841c1c00c0c403d010040740790500040c510802d14021107101c4100501c0c0075090303554030788030310741095010f603803d84040701800c00e10b040208144551028650700b641082028440c00e001c000380040d00e40c0100c9101c0c50300e5450045c00d5642d1802a1070180100c80704010750b50b641c0749000d4525030b000341b00d5840c075694640c00140d08510030544504429602401401d840110a400c2009c1c1c9076444103903c82600249039a100031444288151100d10b4542500d208504d20705007026000c903101c182e600d41c400c403023041802c0d00c031b0310040780547c11001c02c40e12000403512688000359041c000b0b40c21080f09800b4903501c00818901b0f800c2c00a00035030141c240c41c249511001c450394245e5003282c01c0c007601a48400010017034040c10703000a6510112a107420031040c03034000c080c00401c0c0d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 563369352 1250 563368102 563368109
    0x30a060f0c031a01020a0305130807081b0114090f040608030a120605030c1f030b12010203010e010e090c2101020a0305040c0801090c0603110403020a03050a06110f04030f0516 77
    0x594a036000000d240c2c1502c140920000280d000c400807180e1040001e64a42c10b25100408000d008a0300d084503508450402c00603015001c01d84c3c0e13000303481d0030400b6035502c802d40100b012001403c0e1040c0e9154003400d6940e0005a100030200c2ca0f11210005100c804004c0f01200c035005907940d0702c0014031000520250084244596444005808140da280d0546400741c0166109400038402d065542da07c244030781c91450000f04076900c0240c4401020340c02000246800307a040144034a510241500c19802141a03400e8482400380130b90b00c0300801c015400d021164070007180c1c4183c003d4102d5140c8000071180703044192542c0340c4081034800072107003603800116120000c40d40720f0007400208884602440042c3c8601e1000700400b40c5103498502c3d0110080c0310710800e040e40d450000f6082103008081394040c64010301103040301d60b03880c5090ba0384c1c1c06001d0801c0d50418600f40500342094010006c41e2050031000e0702c458209821a19083c011030385007081183c1511034a888038807038486e240c1004004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 563370602 1250 563369352 563369381
    0x2a010f050903100204120209010608090a15060e181c1710030c0b040807091b08191a040507020706120b01050d05090601030b0702030a0903110414090f0d050309030405090402030a06 79
    0x2152141f06108204c2012b8010314184400c1d08100f01c0c5c0300c200010041e141503045002014010b1186001c0710007490103412803021070003400c041041e15283d00c00780200d5000481c0c212180d03200c129a10100e40d1280d80140800154102c208540032840d854019030044545110150115940c1e541c42c0c0111005030301000340c071000407808000c451002d02a42c001050041018030800c1020440e140c407684642d14403e007880310380340104a156004002e00c114440121200b00035580d60300304004508941148171501c43e80c1080000380b2007030320100341c54007122000c0c6c486c1300010300e018142c14050440c0d0720b500340c1005010312102c00d246a0ba405120f0081c01310304040d09495045080c0722001041c020705400a40d4400c011960400b5407103080001202d8006020034455212000002c0180941c0c40e451b00c3c01c0c2269005110502101190001d0b11f44003000c101c9510804071401540d0a00040361000420380040c00100150300700780415647c0184018240c03480c110103239079002c040f41c10319001081f0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 563371852 1250 563370602 563370629
    0x9030306050312030f0c0a2606041d0a0b06060721080c040e010e19020705010506011115060d11031204090f09020d1101050d06082a010f050903100204 66
    0x4500341841078843e04104210580c1c91131504840d1004d207100040c0141041c4140040c2103032109105014803810001c0b0600e0440003003c21140040f040801680c50341c0c4241e1500c4035900324144609880b010715a8810050040c034040e50b00c0301c2c01c030441c00038000c58000c07808000c088002400c4bc405081e00343d500d88110031480e0f543c8000113007144001807d1000a11081205010344414400f0942c11281d4804140135950b540301040407005403c102c1aa0b011800401c1c2d05040040c19008144a12000c0e031740e811000640410b215622144c0c84080414222540c0108000303050140d40084480e001c1c0401d04050300040c00030910b010b03014001603900d120045811b000400a0303002d01c0740321b203800c881e050083d0042900016100698200018803c1e924950240c8559004405503203a400c0c041c1c0701000662b07034a203141911002d6003964844038260751000380941021041c0c0c2c81e0003070041030f1b454040da03441021041d00e44e54422411250716225070303100078401541c0c070300050025000c2940100c2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 563373102 1250 563371852 563371859
    0x1d010501030b07030605031f0b090a0903020f012c0c09010314060603210d0615030b15040609061103040f12110102070302100c1704060302030405071203050a0302180409030306 77
    0x1c0741d076805883c00c0101801d0102c00c003c00c4c1c0e00011407004244103d600d0241c0560a40141d40081c0141a1120f810580390300410842404a40c024030f45a40681c081e00c41c1405500d01d12422610303203400800c0e40c0c20114000c40085510600c1d017000c4075a10504403020780c80c2400006002803403d910803601c01d5221382c080c0c0c01d100c006028440d080320003030700202401590345084480301c03e0112505095542d02113015074045080d9089203000b0520f104025501e0180341c04010040c201d0b8540180c000c042c0000351106406d202c0b01190111949945c40380c2c9003d040690444200302d107039568071182d1006003c040340c040c1e118000000146104142044901d62926000c01e50440e6016a0f60654110f00d00030009600c82044e250300014170751501c3e07190000b261410f18040c1c00f54140d0501c0d000e002007408996150113a00a40c0690b006e141141c50584d580c007580308060b40d880c030f0010005103040c440000d546000c1d4001d000110f40507243e25425205010206044805106041d000640c03110402c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 563374352 1250 563373102 563373113
    0xc030705060130080919030b0a060b04030503040b0f19020a0309090504380103050c0109050604030f03050f070f150e0f0304050d030e090a060e0a05071209061d01050103 74
    0x6400303083c64036481181c2d90f09800c110325400094602c05054a0303000640300c4407aa03038400c140b091040e030050f4907240281e124108210300c00f000702c4000c1c5d1014500b05011404540f0a4195011280e0180c0150b14203401c12034031241c0b40d00503404001419000b400313080380058510500800c62031042c1d00a0510800c1410014441c6016502500f201c51600c01848041180c01c101904900c0f4a10040c90464261103000c00c4509803442071140c5c484191000402000400b080c0c04540341d001360380d0140758941780c80400c26075110314803009262241ca64041c2d0002801403014000540350f003c0801e007000000c0e103030740306442042c4c00221000030b171806440d41c0822007482940c108506841c01010f044104240340c1d541d9100b54007a40d44245003905461003018400c0603074940c050b5000d0103a0000e03061800d1403101800190140110880c0d0103000203680c40c809120302440740c03d43d6954402007010044909000b481c0c01c3d4030503100585c03500400c0d081042c007180da00007104a41000024a0361660508 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 563375602 1250 563374352 563374379
    0x2360403090e160c1b18110c03040e0411120102120708090a02090a110f0c0c030102270a08010c0f09080610030212070503011d1009260c0307050601 65
    0x403100301d40706080c001c00186007448010b00704100e04101070000782c0c900301240711404c800d0414a62400322071011070520b9410044480346c80c10504207102c0c1c1441c13440c2503246409000c01c1c0380401c0c1e00510040104202410645820501509100314a000d090b808600e4455800414400310380d000614102080b2080030b180e648881c4c6460320001a01b4152145512402d00c880044d205048007004205500c2107680403c042c2c1d040011041d40e01c14021040e20b10a0b04541c0f07c062180c065185019410305048c005c441c0c6411654018080c0000c00c00c0261850309104c0010f545c100001c4c420204022100340b19180300b60880391110f949920b00d02ca402800d02900307801c0b901d11a044501402002802d212590b0182ca5045840590103a0041c0707843c1d1a00303a50b030348400c0e41507017001044060380303c161007000d0a1000c4081600e031002c0140019038259400c0c0c440c01082021850003003c0030001d00034100d08406010420705140007142c048507443d503000007000f6945608078034010040c064070400c0d13 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 563376852 1250 563375602 563375609
    0x1f08150405100b100e0105090d0506040308090601030803161808010204090b04110409181208190509120a0e03012306030a1a060a12060e1204080a0236040309 69
    0x1020f02140340d00c000403880401800703035024148440214500a030b07078007440503560881c1c009480c0200700103460800c036507114400d0b1000c0d0045910307840401d00d5000041441c80c1600c5d0032046051641d21942141d00c45042c000494008011540050340d0140d0528841c100090529000140c1c455040848680803580c15014403449580350180303171a6141c2c00072013035404450b0646000182943c0d55180411281c81e4514010103c10000e11444a1075403c64042402250780806450b0f581c03030072090a4040f16019220280e40f40c0c02040540c0e286825400101130b503840600d8443c28103c2081e012a0a41c2c003401c01d01000040c002d1850005424520700d09980b00004500908140c0301a859121298150101840424108a00060f0b00e501c41007003810003800f040c20aa21113181c0c1d8100040186044000760300306000f2403459400302c0e0300c1c020a64090710814006050550306913820050360200c8154003150506041c04112820200300c0c50380d610703000e598040b640d80c80c45d1515008020b01465003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 563378102 1250 563376852 563376883
    0xb060a060f080a020a0c021503090115060c0b070216080a150506130203040f0807030201020c160b12150d030c0303060b040b0702091e0c07030e090903031f08150405 72
    0x8100703200c11648402d0840e001841450010707501d151001e400c49500030446400780d007008490341c10b8031105204000030b502c11541400200400388900ca10306505038002d21914002400d601200d5000c1840020210303000f02881c011a1999103041c0385a840b50b031800c4d405650f8036004101d41106000d2000d81c601049000746004000c54030f0081d001804025507404d60742526940803000034100500c6070b902d047d600b500710003815282c40c01c0d0314000b8003030350010801c10354a006200300e005030f42a0341004802500c040c01c2071039007050b034600b5106003034100c0103002d84600101502803075140d4a0309907040580c03034000da0f101c80200c3c1c542e040141c20307140c2e241e210040540c410041003204951040a031560030b40e0403201c00200e6190300c1540303890f83d800100c11100c20203e031030034411101c03004c40081c200139211307032101c00c54400301c0010403001103421074041030150402c00c000341144554800c85440d410484490040c15522080d2035840c001d40f00c00c5c3c0c04c000c000c2d001e0910040c81420044000c0464484 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 563379352 1250 563378102 563378117
    0x70f0e030303011d04030203070609080a030b04140109020f0702041407110715030b0f03011e0b03070302030c121903030c14070c0329090a02010f0f08010509060d06090b060a06 77
    0x208101d42c4500305500d0200c4241002000c20f040510038800c94a189d40c02003400d201c04411410071101c1640407440c0d860105e440c06101200d14140750107001802105030005400c1d03072b0320780b1200001030b5100c84031050700b001c010001c0d1801a0759602c0f40034001144004c480075a0300e407080c000b03001c1c103001c45001344260b4010078080085240980d1003501604080c036005c0b0b07005182c0408200708041e644407456040d4207129800d426a5280103a0a900540c003039014401e000c034600c245030302d442503030001a4064101042e0300c4001d08202c0140394400c800b050884215a00c0012000020b000c0381c3d20850000c0d8031180700058aa60003000c0c218100300002d0414a8003d02d69100440f02c001031000170712403101c0d171280303020781040c1104441400c120410504c2d034601d0000c1d5400c1d16842c480d00100d000c1000d102469030130f28131030541030055220a850f0031029909080401a0818008008039408035080b0b5076000040d14500400303e41754803903c0140d106060190801c0001143da402c03100801401 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 563380602 1250 563379352 563379359
    0x1091b02060c0f09220e0a2406030b07080a0b01050a0203040e09030702090405010b0108070e031504150c0306030b10050d060f1b020f0f0c0a032d0804030b01060503010312081e070f0e03030301 84
    0x65403640c00780100080c1030700602c2c213000385230f030005880558000b070240700c000000c0200071500302884500c2084082d40401c003107601c8800644850041c1844403006910601c0180120001c21754420b421010380700031642003102d55030000b01309081c00c407412a03040c0d44a10b02c012181d40c003e410541c211580d810054561500100840e650303860300e0314a0404c80c0083c1d00464188200340807a42c0c05946000c4cc00d002120700da5002074040c04240c8001c507040c00701c10000405004c55a03000005496004005840285d040c0c1c83d00c01c0a000d0418460035903035a90b00d05051840c00c038060b44120352140d0b802601040701c680d20807030706103031020742c2081a642100ea04411107079100740d01c00b001d4a51200d1400f166403030180c1e80020000c01c03d00b140d189408450030b5502401f00c1e0364050f01c21644a40001042c580c0c032048100c2e0030b40428440103209909200081841030300581d04140d005007070700401450f1140520840c0d240d004141c5d07402c400300e0481c81c64802d04580c46164104c3d280402c0c0d0045145515 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 563381852 1250 563380602 563380613
    0xc01020c0607172215060801060f0e100807032301051806090105010803090d030309141507030207050c040f1e0204080f28032601091b02060c0f09220e0a 67
    0xb44d800000704003e10040360400202e526038801070240524074020841c00b6200d007030500120505016119500440360002103001d0100e2050340d0030f86210300090300c1110b185a8400e1802c030040c00d064584050102c0301260400030910901d84140c03188002c80d4443c02880748800d042003000f07003561500b40d051400502c8084e9000040b0b400c04507081d81c3c0a01440700c0c0c0c1c10110700030103480c2270003009940b0041c1551203101d400079220a40301d0070020800c6041e15032000550880c4983c9100800680000c02c103406c1030701d081c8d1300140100f2840903020401c1e611406018444000c28400544510360228080c00020010440d001c0b0088510005090342c2c0e000c080719406511031a6411840700200380d0f111010584110f00303144144054a0782c10b42c0040c13081c0c02d0549070020034010308110520700182c1c60b03042c0d00320071030825000a20341c000e08015100d040503903981e54009185030065290400451001e902d462444c0310408001c0080316400e03032003010409065403480084070303034541c0c000e1507040e0120700e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 563383102 1250 563381852 563381911
    0x1505010507051b0301141305160f0b071703130b150603060607140a0309080123150604080a15050a0e0d0c2414011e0501050c01020c060717 61
    0x9491102202c4244036000090240002040c0706c2c040c0040c0c1c4040c0504490000001106d00b481242a00e403000784a11080c440c21105116410074005004000c1007404082c40c020001940101b07160142503046030b100200d03503032064540541d182c41d20317500e940c240200c000101e50400360780c18011120034651000240140000b8000134420100050000b04015445240758801403210099580702a01420f000d0800035481c170681040303508021509120070200c49404460003107110324414641c86802d01414006640c184980d0086002c00c0041113021040003040722280c1314038800c0c18040341e032080a00607160090f2619413540d00704030340e4480f04400480c502c0d401305402d25001d10502d40e203060900400100c4641754110829034079103402000302c0707604010410042109059a143d03a9000051500001d2000c40c98072204e00d500180300780d602c540020040c40300342c0c0c0c00150604510400c19414900262100e402083c03400c00c4020218040c030b1089503205040c0c031134401c148141e48600503c002c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 563384352 1250 563383102 563383123
    0x5060901110d1107020a031a0702010b0d1407081e0106050f030a02010c030201180807200306070f2f07061103190512041101030f020721020a080a03150501050705 71
    0x83c1e1101c00101c00006a50300740c078203984d00140000d80c07a039624180f03008100038000307010740340c11028000154001d005000741081c200c4090020341d40c80d541500c1c3c0d410f04000ad2a00000213001d50752000407800c0080200305c85800e002170124408068002945d4212003183e800349000f50100c0704480844d560203d001880c1e140c080c2007600c0031901602d022801030002800341100c49400f603132310609002e000380151000b60f202c0d01000024030305001c280e4441100401d03a10368554001070016500394800c1043c1c80700141541440d490302040120328185a180901c4010343d80c80c81003c2e0003031303c1c00080009030024583d905048404070310340714100b600c07031050001032310702010094415410f480c403500c00c40b021092a4804500345003405c1c64444810000707419520b0000341010382d101d0a9113a0303803088a254a610102041d0803031020300c4885c462860301c0e001030041d406103500c06000b0403c4a8001c0050540550740003424070800c07502e81c0d100d5805a08030504210f000d200b101c3c001440018480000b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 563385602 1250 563384352 563384377
    0x1509131a031204062a0c0509070305040213110708070803040b0c120a0c050415030501050907110309120a0c080d090f1d06040605120c040f02031b160218040506090111 73
    0x880e5510b05c4400e00808041c001500b003c20441e80188105002000140d8008407608031041e1101c0310b007282510301c00c0c0c03400f95110007041013010507024141d00c0071410300103a907402c40c00c000c21520755580c9074012031016500047d0020402040040c800242940728440d164507504002c0e10400441443d0002882d0301155552484600d100d203004000341c8004200364660740b030380d52085000c018040d00342845064000c03013904010405960103081c803c101641100000c0d414004644100990514009000706c0280216a0280301042c0e001c4000c50150070410014018558846030040015200e0750119802e071b403000105208540c4090b00701d1b84410381c001c0b144011038442c200014020000b0340d01c2290301c0009140035210155002c0340016041804035800c00500c0301d12803064040e48801c9500c43c0720007410685940500c48030001a200e51500c103980390124801a030301140407440c0601e00300300107800503420801000010400c042e84410400001e0000901884215069014090150b0326 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 563386852 1250 563385602 563385617
    0x40305030a150e04120e03011107170d0219020c091510360b0f070b070903080f0408012a0e011806050a0f0302040e04021509131a03120406 61
    0x2405042a49030382d024000008000103070b800c05107419030032900c14101c9400800d980712074032030203441e06100e502151007a2840741480d0180d5941c41c05600c0048048862040105018403440001c135031000d01490121044d008882e40d206013400703454010801c0c03c1d41d1150103040104000101d0b00300300741e020144251490305010003502c00c00d8600410300e042c500140700404040c504100200e0040704441840c5d810740040079511030034034001d0b5100302141d08100f200c0410020001640f0588006c2d8001c8080c84c0c508950740d04e0355920b241ea5440850b00c9045443c01203801d0100060a200e68412025842064a02402d0307a9480705409170082c0d02001c180315040031528000d0740180d40c185018194203104440c581e44400b4050b00c6034110840c41000218101c0c04510402e00a03c02c68054540d082c00b0700c0003e035210303400c1100300e15040382a001c0f424802e00407642c280e168001c1044c64014903c0001c2042a640b840898240c8000996140320303034040601d1503404003100b03040320b081d00c0c0d15140294 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 563388102 1250 563386852 563386871
    0x10311060c010e0f061807030b16090b180411031612330b030c190309240e03041a090a05030a050708010f020a120e07080304031a01060206040305030a 66
    0xe004007440c3c954000c00380580740c8024440a00411303a80d106241031000c44410341003042c1c45a950f030b2806c1c08002c1034102540c011a5643c1c1580c901410b0722006c2d4030b040030403a0389521549026130888020030794480e002c3c503021441494240030f04600c5940d130030082c50461800822400c45402c400c0031050501400c00420784052040342c0100100e0007011428040441c81440c04510702c070b210242d40d0441c801c264801003102e07210902124020030b010721440b0705107141011007a40c0780160340c081c1e800341b41d40d91842c48005001d000d203140d80485c907840103074540307010711a072641a14a56185660950410442031281e50042100b40310310f0161440055203650302c80001c14100c00054000079032510816804404200002480d0000d4032405802480380b090701d0809103060b07020311031003e408540780f90045200c0c0c02d095800b480b5103004820440d22900d584504588c11640943c0040e180b100b6001002031202410208542c010140d62004203824a42610020a00e02000c2c102003081c0c0e85448000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 563389352 1250 563388102 563388127
    0x909060b0105030712320f0106020a020a0303030c021c02030909060103060f090f060b0c2b0c080904060b18030f03040e07180503030a0c0203010c030b03100c271a0301031106 76
    0x3010540052422405001d030882ca06c00d461041207420403c26500b810001ca2820300c00710740c02c480c0c180e005c0c00d8840390034150382d0103902401c0d60586040440c812015030301d01103045105604080302054002d5695401d0004c1030192904008040c6030505080c644100500307000901e01000701c0e1100080082e04164607c0f41d48064985640503405080c0003060f000403203000402c0c80480501242d41c0c00d0081c0403001c0c000000c0c0b64650201101060f29071880e00f0114100400811041030028400600a03031103140340b5889030031981e68100c6141e4007d0407002181000c1016107803490b406001942846c0ca007000c0c1507a5900000e141e001009298640005a00f111100c81c002500000341030701c1d101c0302c08540003020140070200c280e1107982004a1101c02ca4004c0c410b60020940180282441042807900c87d405044190010300c100182d00310340a103248107900000312b902c0d41d044803420206143c4401ea407102c09600c28000b044601c02c00040000803010100b010410b0015240070347c5405000642 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 563390602 1250 563389352 563389391
    0x92018030f0a05010c1b0203071a19081905090c01050901140f0a03050c181e0306091027060b0a03060c0c0c0911091e03070909060b0105030712 63
    0x300079851085032664001c010040d00080c3c902550396880c900300c0f104240b092010225005d001030f4068010801c00e210b140203210050840c0340c412004289022104220b00d1811b4541860210008070001e040c0492005488044a01041e0343c2d4014025410a9160252101d018900c0c003411b001d80041c10341d00590184501c070f034590411201060315004a5a0310220a92210380c4c008002072401c0d00089403c80407009039205410a515030703401201310281840b107181c0c0d420b2410346d00c40c03c2c02d4501c080d050750304102c540e01c16013070400502000f85003156110181c0d041001c00b050341d105401d05003000030051828050400e1381000700821b081c6125004900c20050f01e420180406040030700b040c0d10545c00c00504071100c1d1089058010306a5034001890840b4100302c2c010f403100c070b0104440d00e1949404005000b01e0a0703401e0380366040150b03020001c0d18203c80d542c014a031041d15005000113002040c400d100302514282480c0d8a185400f101c000c02942c0c45600762480c25550b000c0d40e1800d00850002c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 563391852 1250 563390602 563390623
    0x9040215070602040f09110a0c0c120818121b18090a030e09011a07050106150f02010c0219030309050c040c05090f190b03070e130609201803 62
    0x40d025911812814210040d50141c002d5003002e6429107000035503181c03607200c0c0c2520b2002480c04181460340b001c0d401c883e089580d0000ba1844281400081215240d8180c072120107481a410290344010041e00005041c6400c0d820300d200388412550094070110200d516100542c408042c071004000b40800a080c600302078400002400d214001c10804203030001d4198000e43c02a04d50300c1001900100700120340d602405035480c20520022084a14801c0401500c0b19900c100000300300251a545c03258840c0700b80402050004d030300701c10803401294082c404d90500c01c841d40f001e00300102c514100ca020941c1201001005c06544485400511005101440600e14020300900130710310a00310040c0f03141c2105030124441c4c0d4404e400321a01c0d25100b1070b480704594404205c01c098500d003210100e255000280034800780107a12400750400e0b564a50440c800300c6640c4000568103040011580407154008425403401d11b000744450040c68000d019211410341c10901d41d80d0366501d8402090801c0504074 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 563393102 1250 563391852 563391889
    0xa05070f0606050306061f050f040b0d02032505090909031b060601270308130b031906090905100c0306080601180c1407080d09140a0605010512060105090402 69
    0x20040342003065a402c04003c8032021821954a0384850003082503101010a0f2030300c003810742d481c0a400e864001e50142501000d0203440c28105580e854080c1c21603408192034404043d0300004120358010b4914451101c01c00d10410007900703521182c0060403500c2003140491054004800045000c0340400448501c00c400302134090140281c2c403800e0740d641c04107a45a41c00b01e55880e21541d0040c44807403000da0741108423150402441d1440e15101165880400400d214290b07490340807a010306d000000707502440d80c06090343c03440300099079032200703d40b120341001d03105032300740030045021440014218034550300d21030300000c1945600c00c00f54000c081030350200da1180901d400002c4c03c5034648641c03000c1402811814000340d45120412a91940103d4404800d240c1c03e00811010850320000fa289110116000180e05101c0e901c821480c203003541c0c0e9650007507100c04a15420000d04d03000f85401170000f900c54241d100c02c2c00340d4903625100140181c82c012900c000009041d56503003620103480e4404039 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 563394352 1250 563393102 563393123
    0x30504171801020d0203090a350f013806090310020702090f0610030c030b040254030a020d2603010f03111302130504151a0a0507 57
    0x1403110074881c90030341004602600900108414003400403007110703c28800280318184160604040342029080170504100e0b0801d0030f401942c1340400caa0122880e0500040100301205000c8006805c0d6000101100038401d40410310b100c21038000c84444000004917009581d42107005804148079006801015900d441015103d030f00307080f041ea00601640b4000d07a4864466a0ba448a4164200c0d040d81c1c0d0a0308150102c510b08140d500c43c2d0310007402c10410f0702e0b001c13904580e040d00180503600b00c404845115140501d1204818500b4031700c41c01c4c40030394102d5281169880081c2810b2455030a515507844004902200065907021300002c00c06950051002810400c0c90500e215407105440c281c1c004c10b68407090724140e8540340ca0642c0c0c101c2d03e2001d4107201e19411644d0366200d070303010440015000142007024402c0346081d400601411483c2400f292912450001004261410030700b242400501a0300240503448501003040750a01b85800c51550b03801e0325002c201d402d441030240150114400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 563395602 1250 563394352 563394367
    0x9011707050a140708310f0501021533030111030115020303160e010c0b0132030a032106080d110607090611100906140c0f0a03050417 59
    0x700c0058408001d2a582d440000c20400c802c0c26090b220f030801c0582a0903040c498a00c071a1501c001800d050b0030400d02150101040d40711002e10b084c000c0e0000101404880b81c24003503546e04210341035210344240400300d0380b4104205464004000015101c40ca40b0b44050420000c048030b0820f0003e2440180080140e5440114140644c0c0c200b8000c56245e0080008c03c940316134030001c180c81c012031300701c602000b003104144010349030700741a00c109905002882880c4030204043c290064000e0404564810903481a90112240c4030a58180b000700380c400180001419140003036500a07a9600d41042940c080711105d02610601e0300d1000c40c0f80701030070144042080c000115401e107010585840d211480d2280704d4159440340000c984080000e04003500400c00103103d105103140c4180c110040e54141481b2203246020307030703059903801e60300103440300300083c1d85121804085030300850b40408581000b4540c250031080341b040c4c5d00103104146e21040841c00344103000d03c042c036086200d80012551040c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 563396852 1250 563395602 563395607
    0x3030e0102031c0f0c020a0305030a02180d030806010e01171308040f080307020405221b1203090302030f07030b0f06010e0d0308101a0d1107141e03120c09011707 71
    0x701c404c5100907207080c80028084d0703034000110741c0d50840e03040c1c860354299619a40c42d00c00940010301c2c160428101c0f943c44840b81d0315041c1c4c0454000b4045c3c0e441c072a42c0d140c00c00002d40b003a00c440c890f1604000702a4801c003141070b0003091542e006982b00c1c00429144d54141040011401141c11480c102c1c074444400107140d500000040200c14800d443c2030003540d580009503c80c00640914079050100800174000008a440803030180c40d0300040d0030361401c5a29a69001403030440341200b10081a165070050055290810034041c804502c4002801d50609580da20014402e0142019030404400130128003ea80110420004c28402502101b075030081d9081c01044048165030900290041314008101b81c14902c02101d0791485a80b042840c04400046040040c01c0420200d03440074001d000d02c00000d040044074280d90f48a000c0240040d090400080c0c4420550309442030060b8010490801c04a00003404954011309168850b6201d609a00041c0e4607099801074441511499508120b65180c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 563398102 1250 563396852 563396861
    0x9220207050613050d0905062a0d0c0b01050a06050f1b1c110a020105090d020301061a0a02060f160309151b030b0607320f030304060e01050f0103030e0102031c 70
    0x14040c1e8102e0782125015841962001003c7c0999a0400401c100980c012480443d495540c0100e009103103001c3c01440c1c0381c160810044120980004040300203100501c213250741242d014140840b0b0051940f45002e84c060114840c5c044142034645001c2000a254880d01110341900c0800400303481e081600784440800617a500c0030340d07001040500400d10110700001516168055068454918115080f0200000501e0303903070f800c9034503649840d008200894003401d8482207280f0303020055110802018043d00b8418010045075aa0070b0550810000f925110396038524200103040019482c0d2080c01c03d10840c080c03103604550480d08080c90004d684140101000c4041170035501080001e9040c0100b200c0e034030030010080c29000e980d00485d034898091501c0032040700c00e44140b1003003241c1404500c2e81040103151180402d50004003c000074030400707002c0c201242000324000c2019140c91005444004030600001d010003401002552481c5d000704100c5040b10843c00c907a69038004030301c21134005007 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 563399352 1250 563398102 563398141
    0x403061e0504390308031512010c020105060d0308010509070519230703080c0a020304030c060c0c0b040b0a0c02031014041101030905100207030507020a1514092202070506 75
    0x80300710f2210a039a98000300c078402c4807603080382901142246161962405034101038004821035010a03003009040c2e40d2000c80d80c0f001038580d400400d00d100ca85502900711640205614040e03011402d000d80001c0d40017000300e056032811284400c4c551108481114280a201c00301c000340811b03d80c0b1021982e801c6400c070302501a00031003d81e03484411095140390707400b902c00e005010520b1080400e41101480e000b038400c029161040340d050581d2910341c246503030040d0303200c00c1c0883d11080311340051122883d81c1c0b0026040443d0480d20b003030b20b8001e41040510494240c00c0400c0482040c00c000c541c0c05000354003100301c0f594814442020104070300141c0d00343c255000c0340c49000c4c45504801c0c2c0d50003406400718458002001d45100381200b85444060740c02044120200a010000d0b800169540d001c1e000c09400306060504542982d520060016012885000c801000034402c10308580c0e0b90315481d00084000381d4890b2240c02e41060f48402078001c0300001440c80c0692001c128030300b80080e641c248034 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 563400602 1250 563399352 563399393
    0x215090910120f0f05030a0504080606060301030f03081009061403190b060d0c03020411030f180d030c03110d09021003060e0402060304051f020d150503030403061e0504 74
    0x10340700c42061102008251250800541c960600d0001003031024100e4201c2c540902400200a00580ea810b400c43d40450390402c0481c402040c04d204901c2c0c20417506070303c4201560b9051441d411a06c822100c8510a00b00804104040001951400380110401c008100c5484c0906c2079035240e4020041c400744141a02e4001d101c2e111140d175205200c2036090f001d242d00a07c0410701c5486a01c103000e42405003060550711175210a10010050304c4e0b40c815000d0a1840c81d420340d0300ca00302171070114103451000c1d0030026400781c001509601100089404034245800f401c0000e81100c8441040d000742030b4001c0d16140158010500f211503c006030413150000e4421110400c001310f04c010306400305c44a5000c1c1c0d9034480c42020024005082240007181c029000d001100c0d074007508030250043d001c400c20300c02d0b190703030350041910b2920300000e00442e0f41c402901105040c0c12070514000c26507a00485c400a0070341904c0341680000842c0d81c20a040609203480028071480ca880d080c0600c00b016140c219800 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 563401852 1250 563400602 563400619
    0x26190f0f0c02210301030b070203040b1207080105010206040510021e0409020c24040f0206090d0f0c1a0f0a26100f0302030c0f01030f0606112413030c021509 69
    0x1e48800d03250801c4402d010016120781143d01b5a1107030380550000400e081c055100070000400c101c002c10300074002d404050340d01ea40d6607182515009041140690145065611480600c8001100403d82070a5109050401600c4550340d20311072240c3d00c03070040090003035500014003082d0301c00d0f148c0017802100160411161220b80142010700404440100c0ea504036404001050004448070642440366000500b03030341c242401d9030001003a41c694140111203400c11542c146041080c1c2c041d042d4010400004d0341500c62541e803202646600c140380c00300c04043c2c0001080c00005008400142510040f4030b1044012000e5107400c3c1950b6000741c400d003950700d50700540054044001d80b550360035698090042c000307900c0c5090502440400c2d0180c8030341455124440510142d80794441d03a8000d00d0241d85100b400241e0589281c140100c046501c01510391155014540405c10512160003080b036074541a401d101718201180d103089409802136202c1010b041c0b1500030ba0403070000d0b04a1003000c460488 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 563403102 1250 563401852 563401873
    0xc100305090c0a061709010204030c1d0a02161103160815090106050a0b071a150f0f010807051c020a1e030b010806040b0a0509041226190f0f0c02 64
    0x100f0348a2500c6844000346151046031580c00344142e14603040114080003504040d100c2d941c1c0c0f070030703207060b0b81080d030300182080040001d03062843d41146e000010002c08501d01070441200180355041b9203405030214421000d080c80c280c4041103403040a041c1140100b420381c1e201c1c01c0e600d07201c414101c0721501075250140420714446040c07040004903070000f450251260320344600f940c400e4100743c50603110380859140d0141002c0c2d0856000d031041c2c010684144007010a0000c00c168600104140c1d4051f078501c0c100d80e007a81c1d81190500350131000c0d60030126116145489080c04980708a074506000c1400846c402d102290081005004503041c010303403070f100c8142c1190860441d40001e1100e4009041e410109699052503070110a005401070180600940c580307001c10504070040e60103c5414560701d02e0800305590101d21140400109a40004c11445000d0703031012414016200040090a200400240c0099644914100d80a06c0014000c21824124400003003000c4a05107016000d41e50000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 563404352 1250 563403102 563403109
    0x120e0705100e0109060f030e07080d140f37021608030c2d06010b03060f091003020603100905040506040b010611030304121407111008010602100e0c100305090c 70
    0x224042c0c00c1030750748801c1e851070318508844921a03040c64405040c2c0d01c88058540030800d002d6100901080300c01030026507626840201032003403c0188411902007445241c01210086d0100c5850102201c0c00c6c06000880c10120700c0ca1401009055000390708441c10009a00c0e004108075203401a02c1c2402089942d03150781c82c680340c0c40303100005007942e000092583d0190200e2240e0f03d0400342000e0000045d0a40b43c48810300d080c00c280c018184524011003000385901e0118985424540141c0b00003225085c003002e42a1490028000240708a00c04400503080e0f4032401c0c444401005100070600190903c0d003080c0703450781c100b0340c0c0c1544c01d400f1060000c500280600c03250750100c140780004500d5a41c840e00d41c41c16505035425a0410042600c08114201a146000d0800e20340030302c980c1c041c090004070400140c1d81111600100744040301c1c004004168002c01e240c1c1c0c01403500344011500d0140441d036181021450b00b034a0b42e100e00b001d60403120265069005a101c0e44000045455012580042 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 563405602 1250 563404352 563404367
    0xe01030902030309013f06050a080a0308150d03081504180b0901020c06090718061a030a060b030106020109050c0301050405060c0724091208010f05060a120e070510 72
    0x794050344104241000c0354803c0d0380d03900341220040055000640240c00032226030050503101c031b80300805500465025085407040070018202283c0e07003000949070101c0310381c507100c01080160900c243d0000048000340103043c00d03440b0280c01170012003100810b1030003422550050303641910b60036001480d42900e0070144154601c0448441036050b10480755900c00f401294000c003c25519502485896403418080046a000c4e48110004d0045c04c1d041074a00c08440301030b11700c10114141000400c002c0d023204000307004100003420400d182e5a81d42d00b088500540095844003144c000000b0000856030750652110882504c50310a071100d00340c01004042c20780f001900c01400c0b0385c1011020801d20820300d0000c01c03215110761254035500b0070085072400307015101500b1060182d01d13900702008100103401512000001400c14141035410032400c150850340b03270b01030280200400241e911034075002c1d40d100d1040300702c82c0c5418070070000816040c07901c403e07580c03248501503600001c0d0351452a000d0b200 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 563406852 1250 563405602 563405621
    0x1918120e09010b0903030d0c11061308030c0d0b09010303030c0306140901052206030302061006031401050f13021605120f030f041109041a09120708180d0c060e0103 72
    0xc41d041590800101c1d94081d0b101c207018692500c41002024140a501c3c06100c460824a0326500500080c0c10310040c10007000403d007441e0b00104c0880328001449480c1641e07081034603110400e4a44511010b20001401041175642d03201441c80c00000030154140c002d11040031003503a050003010303501d00b25003030b140c40c40071100ea50050380312005102a040c8440c80444103681070141c00c220041a08000c000c6418907001a03005030003410070401c41c0c41010301024024502445c08006d040b102c3c0708030f040ca041041c042c15200300390781e50b00900d20340c0e100d00d4400040e0314030190840da00c182040d40071100c1d02580d2030031111070080b81c0c40e0101481c014016640015130009400b0328594070410000e0079894020811110140340c01280800b6031583c48107a40710b03074890007602042d0340400211304241034005141d503100b41d00461054403007000200903100015071009943d51a074a00b86c03481107d146400b8401500002c0c11004541400503c940c90400c9803096262a41c03c0c2980000445c00d0714284803 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 563408102 1250 563406852 563406859
    0x702010c020613272a0e041b0203090f0f0d030c050a06020703020a150606020a0204051008161401020d05030609090a060e0106050103180210081918120e 67
    0x40214054100b6400520114400b4802003858a80791075003008036a481c2d04003401038008540e0f20104c501490b200d03440c1c01005440c84a030481001c404940420080b0704800b42c10040010707203403d0962a02e400c02001030720300e86204c000180e480c400c000d60326000030842900c140b81031401e25600d400c2c942d94000e445000901405102403460301d00b5221002c000d04116a644039000c540c0010448501c06072001c1842940907000700e14050528a5080d44038601460405240520420040c1c3d0005422400141c1c15507001c20030307a440001c2c400c085165644101214082d00c0c100300880087c3d12804c40984a00c403001c0c074504498040126a100182d421807130100381e041000c160745140140203217910180c0c407022900822903540da5002a2501240c1030401c40e0b4440c4000e004560301030040200038024040302c0320550f09290000769015484450b030720b003400042e002148007020110303e0840704a60f2101d041c020306800350206800040c80340070517100340010800050a4510900a4031440040103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 563409352 1250 563408102 563408117
    0x18180702031b0c0a150e030c0604090e070509090a150b1c060b0316050a1205030a0305100f18060803033c04050c0406060c0309030b072706020c0402070201 68
    0x1c0c0b420502d203402c40c0e480303015544500046401daa50714418148081d200c0d90348101c2da900c41658001e8a02815080240d2081d0000380640c0b68540303444003580e0481d00e00707071400308900b003070005114100005500440c1c0c2100008080041e5144c001a1001a00e07109142d2000b101b650801e40304201c0d01d81c00f100390740c44500d005d42e00b01007141c02150a2a160b00407440021104006000246010b420042000088925481c00c21092404914500050100301c685407400354413595019180c2c8940c4956009050361400801c070807144214003030300500b01006c81c48149030740b6805810f441c0c4040348154031505080440102d2040d1011060360700035100c00041c81c1c1010308401d1001d5400f03404014038006000041605201c00d11020030f0300c0d004078000c0018000c130804035000d00c42a9000c0744c000e0018094907491400000783d200c07401d041101d4202c107055032591a94003080703511100070341d1882483c00200d80745c0c000c170504810301c6508442e10b90f003c07034450a400c0b03000d10041e4043d2682c0039002c034285 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 563410602 1250 563409352 563409367
    0xf0703080a05040b0a090305070918080d11030c12011508060103110904021309050a060303051803070312050d0b01080c0d0b0418210801050a091d031818070203 70
    0x10358014101140150416906243c1c494a0900090708001c1c48a400134111020030824401c00740481e501902c010001401950320341d030082590181d80e684000d00b44100092071b40d164003283d5000194046003140090313680c0c100790140e40c49030b070801e18084100c1c00484000103030000c03500402c5240c111017601c0340c0b0f41d82da9aa034019001803c1442020422040811a6154641c0c80c0d10041205c1d1505081c0760360964100900300b01200d0000b4140c000c90b03440d140080c000b00780c02c1000d5502c00e406035159034100c011072030b021909140840d07100401c0144610004d1007800d820001401e1074815060080020703064413001161010030aa6100090070410400b100c501002600316011200f005000031910b010501d03005058804040d0050300c6803900040e8030a98807200c2c3c205608510310603d0940d40550400300011180f200a1203461542592051000108800348503080c0a4080000c02d494031130403520201641d60354820103142c410060b4141d415203002018800c1805924160f0096003805107 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 563411852 1250 563410602 563410613
    0x12020907050a030624110309220e0a08040503011406010807030f1b230301051c0f060f0e010b01081003111c03030c080604020703021b060403020411030411030f0703 72
    0x3001c0e032001c0644030b44c0e0204000c000184001004403c81e04020035442485100805044071400b94100a800400a61045640d020001c3c7c041c0c10001200c0b00d800c1c0114008400102203d03420514640280c00b040c1d028410b0000c0900120b850580092183d000840d1781c0107440e00c011603400d40407491420119056a00c25406120320340202140000c00300f0703802900c1c03040300d44e02c04520f20000b1515503c0f203580c209025400d080344400c0b00142811941050001540d03c642400009107581303004644000b0312020320f029203081e680040f400c00c551169070482001420b40d8421000056080442000c0903510443da464030a110800c00581102c0c00c40d035a083e40892078107649a440248031070514082c041800e2000344540c4281c0703000a0091407410064020040108140d22031031040c85118042600070030845060442c14040c910b00d81a8a80083e00a014a800181d007041c9410303070200c25900850011405603000300106a680c540420400d030b031701d501c4d480125030150451081000001d1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 563413102 1250 563411852 563411857
    0x6110a02071827060e0a05030306090423010902010914090a0f2309060708070503040b0a021b0606040b04060b0d020c031c14070201020a1407020d0b19061202090705 72
    0x70700404081440030000298440501280500f1101d60220f4140103081114501c00c000941a40c4400381209000300d8540540300d000c0202868050401040041e0400c4151840712001741c1611450b100c840c00c3c1e4051060007401501022408240700c08004154907548503801160060010014500781d50f0b0700c03000c20060140707070704401c440ca07485481490000100c0da4a41c0c0d6060007245800c0e05520300360140c0c07898800d001d02079a085c01184001c0c414555408070889600c13a0300080c011910b80c51b203100703210003480b448425030056014414032000c030003c042003c81c01341070300322030030310800d00d01d071082104071650f51298501d615000c00c0000c65042103500540b200d0002c010503a414008401c1c068101190503004203072509940b40922080744800301c042a40119891008608102c0d42c040041e183d4455809034005005011510104544ea8801480744a40d48010500070074140040005802c1d0702c10160108a507080000c00300c2c540751000a45900140c000703099607002c2d16985000d48855 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 563414352 1250 563413102 563413139
    0x15010e0f0904140706031a120703080d020c06090c010905100912082526070515070206090c06070201080a0e01060305030a0f0e090f060111010f060306110a0207 70
    0x5103040d40d0042140e5805003224490750240340603001c0c241880701c1c05401e204054000200f032520303207040c0007010010201d600e200a04151484590760600c81041803401c41c1d16880200807090008100d040d506141c0c02500a0308654000c0700c03241d44070005000d41307480c86901468000380001d035003000580b81164080902e50755a08119101717984540200d2481082c0b46003c0d66000b00024104d088506411040c55040d1a041510003050a45507240d4a00c07841d904444030049660b500040c0001c41c1c0e25046805041d880300c01c40714401e080700c50800c40c0710030480d41d48016009040004003a80e4003c208004a608010304d0340307241406950041d02d040c8405000300c030010355109070005404009210704005540503030011070300d850100d0030040076943e4500c4081c0410015008956268840110494000c0b1091500300026070b12400103c46030b00340d178041040d00b50f02b8a550842001200c1d4000402d5030300030708040c800b50312540c00700e042600c5004036050059102c64000c1202e0f585560000140 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 563415602 1250 563414352 563414359
    0x706081603050403140a02011b0f0914120a140d08100b030a021b07050a0f1404020c0114040605010509060d0b0f06031006080618060907060c030216060e031515010e 72
    0x6800b80681301c505c01ea0840401703400544e6544000030a030100300c010f0000389131218a4958a001c203039000c014888069485440080000039460905d0b43d910b0656a01103003000d00c086522550440c03c085001c0210200821040d0240c8070700b105081c6e01c40c00c0c4451060721800802d490f8030b403a260491541c1e40c80207150215080c2e00f402480010286450807004001c80b03c07000f400c00c5410001000700d8480070342d01508410041040c02c01c501000340103c03c84120b01118016100c44030310000c580034110b120410302c0180c0e51501040100840c5030710140c1610801d4900300001d954400901543c141c0344a00a0003840d43d180000b82c170401c1030303400305502c0030000d025607613584103040484042c0c450981040c1d4258021504202500703a42541d0340362088040300040042d400c0c6a0142c9445507124003070003003040345100b941030a02d8000c20084600314810306225500550b00c0d40010068031259640074842e00401c1606c035008402020180e00400b01ca01e000d010b074000038401528051000451a41c2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 563416852 1250 563415602 563415617
    0xa0605030f0604121e02010213141003020f0906030906040606080a1a070c05010f1e1b050a0309082a0705030615030f0d081e0415050a09060603050c030706081603050403 74
    0x4005c0b40c84401c094104610340c00142c3c079140402040005000c00d41c000100710281003d80710040c0d035405c40c00e040d001031241801650751032102400f22180c0b060700e10840c2c210030000184a18158005180340c4501e0240204201c455110501c180d250b5000d8000544016038880c0d03a60300a46030340304207540000b010f0800c2003000c0e04070340d05e8500b5a0b5051040c00f10340d60f5545006001140f0300d15a8401c0316010800400c100c001c070006022040b01500070400402c02d001c14500642802644403501c0c6a4100028035180c03204119007441d0011651110301010140b00301d841c1445800049880a450000340075004c959036280f00c0d0004003051024240c1d151049a10030300030544148603862048440d90358a4040d40b805264115180c0003400d070240700746c8807a03010800803502000314419107010041e0081507540b140031024018140b19140500058030303050b4000100031000405240c02c1c4000e4040d5120380b46d642900b075a414104942400014400354140c100d0544280e000030340c031a01c2410a100c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 563418102 1250 563416852 563416877
    0x60615170c1204330605030c1210020913110307140702090a0f1104030b041109070212030402060702091f0b0405030a0609031e02030a181401180b120a0605030f060412 73
    0x2043c110500134503800c03940c4c03004140443e040c10310010107480c070140c1e80280346250000442d0350350035038141900142c5501242c16811a80c0c4c1034200c40001c0304240c8103004035a81507d0045442d4411b89403c1d000c20324592003400e0b6105c401c0c00f61a805a0020001d001541e503e03400d01c0007422004101c12030b150ba40d140d0f41e4848403079890190018500a145040349031609242046d2440d80c8120381701c2c0314800400800503803640c005040c0c040d45c60b042000907140c0e103c40c0b022031018051034900a5004000208200041d19141c020f948080d00e00c22448010603640c10550070301c0d114500400750190001407a000c04215240c10003c3d03480c1c030030700d4060001d06d50300c09507070000004075081000582000402c0104294001d8407a888050381030342c4d054505d0b10345400c0c118224405030100e030520008940b05100301c2b01d580c00d00320003088020b4401c1c1c0e4945245098902c82e0a00703c50080700b2910b80140071916040000702101e19004c02c000030003c2c0c0d100c50f1200548045140f241008121060781c144 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 563419352 1250 563418102 563418173
    0x40b041503051f11070f0309050a090b09060402130909020607060912030b0319140f1204061b050a031d060a03020c19030f0309060615170c1204 63
    0x1500118002c001428003101c01c0b00a000e016803c0940401181e41451103000c0d10a180604460302c00d60b000e40302c441c2070701c01c910301564031172010390005500c548090000184d80e0704c90307000031407481d100b1121000303142d88090401049020340303090f41d0ba6101c0d00102c01d12500d109544000c2c07103035000600c0503041c0282966408151011280d0842e400781e481004445040d4050240c5150084101d01034005918020206202e606c0003401c00740444030b1565140800c000140625040b0420000696000d1000345500c05841c2c1d00c80d10480f03000400c0d803020011703180d4048404101e082c0e03005014081d100b074542c50480d045c0c074004001c01010741e082120b200841c6e660a00601100810751009600e68a13028030040c2000c0050400c10a100174442410000903030144d02c800c0a82a141000108a20b040c03d041004083d141c004030318100340d480103080c01b16041405d850b1440c400d02240c852654410310a105107010f500040d10701000c20703034080340c00075403402e00c084001c08460b021058040b42502e00d4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 563420602 1250 563419352 563419391
    0x6042037020a0203060112050c0f01050903151605070c05150c0601030302100506030a12050a021e0a060606110318120105251b0f0c180203010612050c0702040b04 71
    0x140c0016a00c400c20903000c43c2000d0049500401c51380440140121454480603120747d00c03070300f80f0341c441d00d403054648156078040d00641e200e114020301160401d0400708411483c00c0700654426101d911101c8045041c10b01c06d0003200d4400f07034000f100b213843da032410090125101013a02381c240684d80500c55413242520801040b802180690f00500072642000f07040e00488030040c01183c0a5008898440e0204410b0341c1c841e25a80510b02c1d01d190340300881c2c0c000701d080480400084080440c000b944a154000018580901a014401c100155681c41c02d0aa4542d2000c8040e16031941090210106010f50140301c40081d40028024281246402d4001381c03c5550031104140410010f41b031111140e10f10f0154000c0304006030421000381c2d2848002d82468044010000700212184007000301009003502c4c03418002c0050f4228a4140d142e003220f0b042c065003090040d600000e080b0264000600c810303001c1d082c0a83c405d1200d1a10300b4400d6001d120240c0f07a40711307805401903204c038907051644031060403 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 563421852 1250 563420602 563420707
    0x30403050a0b19020a05030f0c0c010e0a150207030215060a0e16030f060815090f0708061504090b01030f110a090603061109060f032805060420 63
    0x8400c0d05072500c8441d8079001d28030f180b24540d2a038414012810b4054020003100c0d0402980481104195074160380301a0324465244684665401d10300c12100501c800240040401d1182c22810b101081c1140200101d0140c0e84010b00181e001c603040350b06000d80d0500103030300040d004d4251400c068443c02a140750b404156100c0130303200c080308405114242d00d40716411117101569818001d8525002d00b031955800c5c1040e58400b455105c02c04601c503800200002910041040151544075540c1d4503100d841d44004c45540d01d8440380d1028402c2c0d44c3c6482d10807011481d600c03142101c0740ea4215115039104449540b0304440c203112203032030f650495031240e400b2001415200c1c0c0102d14a030075841c01d0410b4650b40401030784521014802c0940c65034840003901e030800140281d00b500c91361180d00480022601440e40d8081c03401903c1c0104a298490b00050307c02c2c0c4041d1800d00802c1080c03640a0000c001d040c0122030341078800c0c4110038440d00102201e100521a6801002840804480c80341c1903204d07004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 563423102 1250 563421852 563421863
    0x1120f020d0c08240c09062502150415030507260a1a0a030201050721050310170a080307141207140316030c1b0f0203010f0207080d0b03030403050a 65
    0x4000c100001c0f040100c940707840c1d400981c60f5082000070b00501400f54000d40980c9100d0800300711086191074840c252850b041003146144185814000c0d41d1043c8442560142c0c0516500c58044580c7c0083c41c045400300c0d900d602e550800949011400c6005100c064004810080080c40c0034160094140e100d0205000c81c40c292015800d11007119002c541e810001e0fa07400e03070050510706001d40e58041c010021280c080c24a2a9500040c2c036141c1101410300013420034001400080c0041950700901031449440c8151448a000e921070071804d502031101c005480780380c0e01031030400f000100814041c58010241d420712005d00e000d040309c8151941c008402c000c0c0e00c08282e00422000b103038400000802c8a00c02d2490b02d245041c41d807640444c610740d0b08100d00506440380404100984201c1e054206010f034440d6000e9422440d1400368608000d03030405034230940c2440010749840030f55200701d0300500d03401500341d8030703107a881d25042c0c0103040000c0042d03a050105210000c01b180c418448550528441c0e03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 563424352 1250 563423102 563423123
    0x30c090606170c0a0509221505030c09090f06070c0203211c0e0a050303091b0604091a040606050702031605060d090c1a0301091b090315060918030318080301120f020d 73
    0x45104811210310743d004000302c0012301010001520003140c40c8040407000e5400d0301196803404411898141841e16024585c49185d0030045600d5100494500c018400c80503256107411800c000c40311100c2c0003980e82c010b03200400100082c40d00102150000410b8050041029003000e1465401d110031039000307076801e400000c01c02881075014000c441c0e161645050361403201080f140851080e010350701820f45150b03910800fa11081c01e0312014200b8a44004109101982d04c608000307005421401041780a4403d0740521001019168505402e0f11800380086092080426850002d0700ca6000103590440b030100c004110203046c4024400000600420f155684d450010908102d8403402004000c031512140c0c004000d66003c034014003200e0f080005011507001407800400205026408072101d5440d000180d20001d160009411000c0c1c000d8404200400d003214460307190210109e401018141c0401c0103100c200c4420140c504494041c14482c2502c140680c0410201441c3c2001661410801f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 563425602 1250 563424352 563424409
    0x906020d0605120d230c0a0c1e14040908120f040b0a020708070b0916081b0307030c1e0b040b070c14030a0b0712020301030c090606170c0a0509 63
    0xd100c50b4960b0b514614018010304000710801404841700441005414440d00313004014000d0754010744181610020035525040c87e580b403c1c4445060501c0b03503182401d2500e5440ca103001c1801c880600b1a50000700d40441844a00c0820005005682c1d04441501b024080c8005a96403a64035610440161021400a0800d030401030180b14008186801c2c00b40100b2a20340011200400e8440c825480100b0b0b440d1350b26100d880605002000c2d50701c4034010141e0b04000303140a00011510081507d5403110355503400024189902e9030310714000508111141c1348100220521152603881003108060484043c5450b000c0901d580d901c00d5000c101e00520109140090010070f16800c0004d201c0c1544100d003450700003000c0f0307888000c8848058104094600081c480c01e00444a0b020300103a084800c665039a1a850040107050035409508103003071421744003040c01405100d054800040341149440c9a9544198912655100210010412030180708a000e691620540b503407914448134240b000d001c16 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 563426852 1250 563425602 563425609
    0x90d1703090c121b0d060234020a05130e07080f010b221508030a020a050706050f0f030a060f090506090a0b060904090503250c0b07031706040906020d0605 68
    0x1c192050340c424038002d54010f40e85900081e18020404c2140507040c00715030b101c8000b41d0311160440c2c0c0688168000a02014009180394410341070001c50b84030b4010031780a482c84029040c0001c00f0007500001111010300c2989000b43c1d40e80c0440401801c0800c4011440e448903042c00283c1d8040b14090f0700101400d18020000e000710b05540c801640d40500071800c0032001c80444000250840002d0343e52901442c1c4003002201c51005031141c402129503500180768001d40e18030710a0000d9030707079009001c170100e0030600c00d070111000c001090b00f401e0301f0040242c00c1c036030780e030790016007849109136840314001856808020346c3d04c018a140e50f0006107a14014080c483d84030001402019094544103121030a41d03101d0040c0c0d038541000742c50000e039540161800764a1841045451110134259a000e0030381d000c60351081c0701030307644903540325071f81c5580d500f8071110f1500600c400203002c513654005100100051b12070841d031009000340041a449201d8946008a9000c44005200991615030500c003505 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 563428102 1250 563426852 563426863
    0x60b0c0a1a330a0f0305010f021c090512130801060b03060d0206030a1b050c0c01082e0b03040804031203050c030109050408121009060807030807060b0a0305030d02030a050a0203060312090d170309 86
    0x1015040562138a200001c806030300d04ac181024115690343c2d80e5080d01800780c10040e90741203289070700020361344080503000034030b06a0961240442542c00c0007800b184903206401624003c00016006400904244c1e08115994000a0070030700e04a079201421070f40c81d80350030349610f003010040e210b060307550141104150038030031724003041c5050006000510001c00085030680902030200d05041e000a4440040d020f0800711301c0d80510f121840200c00d2105100341000140101e038030400301b00a04030400001a42070382d804980007004904244010002c2e06171a800166215102d85401d41c40e01100c5008000700d55803e5480c1a00194520002e11041403140300c1e10b0044e0124100506050307207148d90394481c0388a41440104003036140d80f054007054603924000c070301850340711083c0c907202d24018804400a4000b01d9414071100c0c00c14001c541422554404c80380540e001502520412a15a20ba440f00c1c0d1700c07a0308101d41000302d07100ea05003c15122108001d800b00600752041c3c0c0d038240083e0300e61910 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 563429352 1250 563428102 563428121
    0x903050d1802030c121002030901060608010e0f0609070306030206070c030516030b012112030504020f010903080a0e300d090609140103060b0c0a1a330a0f030501 71
    0x141d00003400c940503980c00a480c0001402c2200c001208840070201c007400c0c458400c40d05103c080c00070080c04a00401900500284c60851744c0c0c01d403280c4e984001c20b8040701001e44d198650042c00901043d41c1e4100080c0c030640c070001d141004507400c0c1d62a0702044040d84509815180303103d813201d042c02004030501156641d1500d0400c0f010304181503494403c0308e0001882100710090f20015110350318a110302c0c2d02014190049045580030046c0e8102402918085404034400d00f0308031076000240d8003402500341507940001d10704ac01e00903e443c043c1c0d803d201e0281310650084440d2102e8003c03418401d90105c98031049504021a1141b4064140c1707003504001085040c8003c000f8240082a070104070b0204440340100e0720000c0307407103c60050300208800d802c03c0c80c8a01000070586420a0001209c2050b00e1086034031402040c082a03a0003490401a58012480c2c900138400189190008016896200d0400305c81d011524080c000100302c00a2030f40020022206120f04000740407003032040100a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 563430602 1250 563429352 563429381
    0x60f070b1503060c09040902041506020a051203100504050615030a091403030606070f03050904050a0b0111010c050406120e0607170a02030417030405031c020c0d1b020609130903050d 80
    0x1403d08034180d04e0355018611805020320360300c50182d415951150000b01d038201251581c240713280e071030b0b10000f5125554400c080e910b83c4650300104101039500d400700c0b44640d070301da03240000c1241054204000f41001400259200c80303008d40e004280c0c50301200075030166003a2480001c6030320691801c0c1264000742c1c02070200642080c03081221588800088030b002c40c1d0300049148590540389030555660140c911215007052900b42080007030744050703004d8500030b2002d8075244d100c03020103964182a00ca00700030903800600203200402c4030741d01420b0302c1584460309040200702c0001000886e450a50708444280005a15910481c40134411900141c0c0103110800254518501504c1e06030b04a000c038008a035000c01d00000160900c8024030a41c1d000140d80d2051a40291340340341c202d0042c3d001415101680c0c05000c0324611054001d00e01c04138186103094102c0500207440d001c00055030410005035800c14610140e60095a04c41e10907003a9082c800e8807525103844103802403000310380d100e2246012 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 563431852 1250 563430602 563430613
    0x30d110408190206120702030c030d0b0f061912061a032707030b19020712080106020a0302060105060304080405060a021b04020703021c0909060303080f070503060d0f02060f070b1503 80
    0x140c0c44c0d0f44200d45010115020a81c281d0b110088100e180d88a4500341c0c0d04940800300d014181403665400000414101b190238166895010341080345604c244d124582513201c103059901c0c40c050044000d140c0100d02110001022607499000d58031501480e0200198000c000082000c1c003c880300c079800d400305010480703503211000782303100c0c60f680d40710380c003001e0200b051450000703140320300803003041c400640c04000039521426540780056160788506048800b040e80c2000114580d440081d41048190b010360047c481079203460700744000d41c0c0c0090800d0b100241c0400010030141c40704002010140b0641d801411101510745a070080c05c0e0348a00380901c240e00412404e00800d84c00144101c2844500c09401c900038a201c006840c90103040d880003090f01e003080310000903d600040f40a1003208402c45480b2666240c2000312003504c01100c010303a00c6800c0185100c0820592140d0700c00007440501828902078a80c078440e56607030015a011141c00e56140c007000b551001c45042e405040b0b030164000c12 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 563433102 1250 563431852 563431903
    0x60c030c021e011112040506070e0d02010e150a090e010906050114090103060302041806050c04080712080c061003120e012102070606090507021903050d0e030d110408 73
    0xe490706821402a80c0b0050b5015450850403420351083d0041c405004640d40c2d190b14414030407108140c1100e040c0c2d45401540f00041c40740e40540c0d19a070312014000d0180c8091003180d40155104030401d02d04941066908411501f00b1080d41d006000c480c03055102c9045140c58803203881c00d00d040580207412a0303410f102c2d04100c166080b03190f0802003080201103e0700c1c0e02140300101d00400050b440079600508040301c0e880310014091140b011035000d81418440c0e17945098010b4510b02c1907216207403017644071041c00c000c440441000f007150316118107107041c81c1c183c007046110700c0d11509461242200b441010100b0402132414203c02070700010703052641d4030061901c0040d0444800700c00504107082d500301c40d01c03c1c2e50300c00ea0480302c140d0344c0700d201040303491b0b2285001c000505048556002603c62880c045621084410425400942c10b5903005d03e04184655808094028940905214401030207480214070003030040300001d0204418507511180b61213801460941c2c90b40342841d0102ca45c03418803 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 563434352 1250 563433102 563433107
    0x3050702101112031504140703060e1312020312271c1103040306050f04141605040903030e0a1b090b0102280c0f09060e0603030901030902030c130504060c030c 70
    0x1100f540c4504121988a80d9000d50f59080c00412600c05c2e43c3c45454a40b440d002c20140072000c50007a4580e42d000c02800351119082035604e1002c5d82c0c41c80074210385158445c009201006207c45a0025205690620b03040006d440c801810548400d021140101e03140181281b20549400060303081c100103010b68204074034004070030b400038020a0204000c89400d0051000100111401160312000801c10751400903580040c0120a1b0340485600050700500c448000c00001d60a58203880180541c05062611b42040000c0100c503104609054a480f10032544200510800d98030902401000207010610980c0a240c0303802604502000c5190244912007a640010805000b512004844c0300c3d403100c1081100c0c260303aa800c0002c00540c14200702080c0703524410b0540b8215401820107020141c1c40c2d9150740682c0d030301103541c960140e101b071242803059880382e040030070454000380645d6a0618298003048901d20811003400a041c1ca45003408200b040c10300c5141400d03045403038104131120b10102d00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 563435602 1250 563434352 563434363
    0xb0105010f140306100908150916050901060302090d08160b0604060602280c06050406020d05090d030c1401111305090907030b04030516030c020f03070b04121509030507021011 77
    0x1305000380d140601d0341c01818010360100003e400c01d20704681b01c0c100c1106586403084011110754060b4069211421000d03a03000c2e560300c040c0c45004003059101e80c01d0100484c02074000c405550352104141c0104804581d0510061103151030111200319200c00d24100b4401d8110040c00302d90041d841e24408000d6103a011030030360480f40502030340d00d5414202c4686c0c5400644082e001524908902900040301c54100c0001c2084417a15000c5c0c5141050545055a6034010550140e8121011b507030301d100041d02c00c90b5159410781c070803410303000c4404000c0340190855500e64038a50300b13004009400a00c20204d5441c80f001003804449095084c94401021916002c5c50b100040141031180040340400d400342e026160f010b0880744940c03c90500360304008007482800c81059000d80000c112510b0f040c1800308480c415604501800d03468140ba2542c00500000000015142d012402d0403001c6440140c2c0140c66149000380e60301071700d030001401040804c40161640005000c480c6142403048040401e5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 563436852 1250 563435602 563435611
    0xd12032a0507020102030f0301060c1208150111100509060a1d0712080c1b040509010c0905100e040f0e010509061e04020109180e010e0c13090813030b0105010f1403 72
    0x706980c590442d40700503407540c095042099140c100200010581d640c1c0f14410140c01c40c0074800c408440c50032981d090f03e408c801521902c1d140444128150314950141070700c002c040076820308640502001080e0f150840e403090712a107905801007018482e0174021405110160300310018a40d100e603981030a000d6407605907102d85581c1003055100941444030320b07070640b20319400c80e60035202000c080c80000d480301e80440e4074241c032031032503c00810100c2c101403040d2000500e2544907440840d04040c1007046010f1017a203120104280e084070704000361560300130803c1000401e080071401d5005000395a0075603100034906030740307030340440d0421000040e822400310714159901a0702031107440c3e9000403203a114150b00480041c0519404601c0324600c294015858064070310000c000c00041049070984511406004c540c1c0043c143e402e0001c00e644075409034601c00c1c481c154180c640800d903072008070069041d41c815036100107100c00401265802410324a10804646411020410f0001d94034034503010150 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 563438102 1250 563436852 563436857
    0xd0203031308071e0215090906211218060a0918020409020f0c0607080105030d110c0405070504140307030c092d020912120f03070e0d12032a 62
    0x2071010050085000403a01c0b025005400c1c1c4140d40c60030b0214008804802c07004038011980c03a080d44800488001c240c0b810700c0b80c004c0a1004c81e413030f6501048100048a00e0004070407040b180c01c0071068200700540014486c01034500394884844035114028400c101c0b401c4c1c0c0c007507a01089441d10082c0d1001c00302c0140c2c7d981c03482c416890151094400000e0140d504900a45880001e5200302c0c42811400380803212689402c4804a0ba80c400d4121842e080a209558140e07120141c00d61015008004200b00d101c2c0d01021108402c1c00c0c0d01c001802da0300e00759100ca0210f0030000e070600c2500b141e0341402020000950050101d40e01c0d41c2da4504142c600d620070014965a2551518056400b1403503100d040c1d18100b0540d14000703c0c2070039200007940704076201031250514480ba41c14074030010071366000007a241f441540c142100741c030704216644c1c8010409410002c200c10052890341c6c409035802031041c0101c0b18004100e45010001d400c83c0e440d01d0200458189030400380011040701c540c0800224060f2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 563439352 1250 563438102 563438131
    0xc02150a02060708130605010f03020909010b030309041d0109080405010f021b01030f020d0921090513091b0308030a0f020304020d030e0a0f1701061a121905041209080d020303 77
    0x34518100179204030132009000c00c1c1400000501c0501e2403212400ba21f008a42d0303a0290303290040068200c0310000f0115415400c280840310152401e40d00000450f070b183d100c8041200301e0804150300f1141c41d940102c40c44400401d042c021541c0c06012400724459500080419480c4014012001101c00071094105501d40296406200e19074050ba2108130711041d085c02141c000d4540908041d0303035800c208180c2c10305004840c40380b5100e84480c0013160f401808141000c2030400800004d003102c09800c2c0d0b0342c80380f404200540c440d441d00000300114043d109442c0c91741080f0380da10003a00c404155096255005206100140c1d0710b00500e55242c652500744900382c80794243c080781b01c0784295031081091030510500024030040101e0aa59108034420003040400d480398244148884040d40c020b0780e441d4244422070b6041e01d502051500000c45900c0c841c0445d861030a9041a030300111070854100e00c04100b0a4802500101d50b0300207440b404000e0540b4040e5008001d41c2c0b404001c240c4501030489 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 563440602 1250 563439352 563439361
    0x10080a0b06040603140706020f0a0c03020913020303030a2a02030d15080a0302010b040b06120a020304080d02030c0d0e0304060c17070503040f03030f0801120821070c02150a02060708 80
    0x343d900c60002140e1003d130005040000d00010ba4917030815204090150148200380c4440c802c0c0031481c4406c9691004000754501e045800b40001c4240042003129030000c1c20301d8480269908002461080003407820106140b128003e080e84040601c440d994180b080c035000b2005050380100650704e00d1502c0c20f0000458102d03d000010061205600050030350040b29410420315034103400086071341c481a1020b2000140e09024000c5902c10350407480446440c980204541c000944c0096030464040c084182c14041001042801caa00594460900100025008001c44142d00400e0b190780d0500700507504043c60103801400c6122880d078000d10180c10624420360011005099958040d004000c0320380310341d1a9030b846208000b1314007040d4081940014002e00d600d01c14125181a41c2c906520f2402c82242541e8881190300a400020202403482c036007440c40d4100e80c2c0d01144610f4441c2d48105940303042e8018000b90780d80c2800c0400d40c030441005003001d15078000600540190b02031804e007402e82d88 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 563441852 1250 563440602 563440609
    0x15010e102303070b090a0b0c0109051504111002030a03090204090510150b0a0903020d0501021209030d181a040c08150a1a09040206160605090d0810080a0b06 69
    0x14542100c0444031199962030344410750240c0840c0800c00c00d808a445042c0c0303540320034016006409185602003003105060014007550f0b0041c240d107003649030003c1035100b40e43e0340d40e42c103042038010741da400b10041c48204002d11480c0151800707250f00540b10b2600c6900c12102c025203900c2b41410000c1410b85401d440700464449510080c007060b0480f0907076204000100210000d0032005120b101010040c110101d46050b5040c11226034104540b50341004919543c20b100c00c01c101d0034800d80d9075540c24072440c3c0c441c0c580e42180600c5140103901442d90f90001c4442c2c07404403400722825500740348021010f50002441e036908046981d82c0360034010030300d0307403645410800c80e08560004011805000d184040703d110001c407207070061160314401e02c2000d00054a1001d8001111031882d030280e02040030501500f000802484c0442c10140490348401c82520b1703400a507502a00d840312142e21261040403910b600001c4190019600403078446114604106260f83d44002d50001d0904002d80021415036903 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 563443102 1250 563441852 563441881
    0xb011424090108220609170d0e06070306062f030c01020a080f0402030d0e0102030d09030c1e0b040305030c090d0b071206060207060c0212012c15010e 66
    0xc2a50326084402900d80801400d8000034100c502060003640410491445131410720b40e03402d150641d4010007250f68580801a003200c00c0d0540340c415410001c1d15101a12100034040210000400300e040012038480519081c001000e0700308051621900303000c0182d000070141480c501224005281280d00c4100d6150003850022256245c400001c0b14a04642d040d000b070074080a444d00e501e0050340d1044c003400d0340202c084a0083d030580000494480e000e0140c0e0718844e40c81010700c1104e083c000500a00011268885000c2d03002c14410030511003088810380c07140c0c1e4207021200c540300c4c8602486c3d4403042980c00143c030060a00402000240540010201f6164041e400605844040311582065001c940054135004002a102a8004000d500500a03c0c1c00c640d0380c0e50040ca1401c0c17a180c012a004242050300303c0e0701042e551184031803040c00340030b0031800108421580005440e061112015400306140c0100030b500710201c0b0070f01e000b581c80580780c115251240002c902c2c4d03440134010100075 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 563444352 1250 563443102 563443129
    0x30c2517032203061a131823010e01090320010f02040e010e070c120e0a0f090c0f021b0904060e0f07080c0901030b06060702010c0602160218040b0114 66
    0x1041000382142000d0b0726140408120b901a0b8000c10000c08a48682c81900c20300a910f5904a421062098245206580801c240d082d00ca03031039280c0604103540319052111b0b00d905031101d264040c40107001e030a10a22a5000604500d0000c001e40600e541d8050844086001825281d4884080d80c1503000780039000350001110a0b14115a5a41c0f10111180918020300410080310a07003800115401d02600302103034000d82007004626103820829081b911071480c0308400e170300084030000000303110304010788400281c41c020f600400e44004482c801070488010301c00301011540418850421601c0642d8244200b8609035040046a134403070038030a014240e607400341ea0084c460314802004404010445400340c6100784182c5400712002e104100403400c080c00081e06500035040419040c2c540300005214203441814080100100d03600c4010480c4c05c0b40c0044019940940700120442c40c05456a80e02154000c04002d414180788e1182005204140900000c08054145039081c1d9590304a00f0810b4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 563445602 1250 563444352 563444377
    0x1030b07020f0706030c1205040b01090f021209010c02010b0a0e010e130203030a09090b01030b090a020711090a060609090e0606040f021e07110d020108040308040320030c251703 78
    0x42955680c00140242440c06d610b0000411010020309040b64038050280940e0f0802c023651010703401d03c03000307070002d14152020b0001c9603802c002010128444108035031142882000009820b0180031000e4213413040050014800c1d50042401d11000070b0280e800d6040d41c000c1d41c800301a035900e18a0b000960300c02c95002035410710011501940c1d41d075101303002c0004d55025041c01d0009020940041d002e907001a043e01c0d0340421503100042c6480129409800c0c45801707444506070b20304016002c108c0c4100103503044401562500d00910965400c80e2640c00208403501080102c042c81d4840039445440281095206913100c5ca07102801c4901601524112200102800390300d50b04800c540b011035120700c100f00e8400760b009004200c0c602e45a4803a1203405c0e0180c503691031039512640c00b25a940c0004100300d00340712100740d03e541e60b80c51200704400300a0b013400c02145c2c1c0c3d42c4c00110580c07400000d40310030300890000d15840300d0800710b0404034034200c0384a80007055094111800d010308500400411500 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 563446852 1250 563445602 563445613
    0x6030115030b070f020d09030803100e0c0c0f0313030303090c1505040e0a090c150504150509130510060507020409060f0b1c050d082508161701030b07020f 68
    0xd02c0b100c20307032079401504551141e8411140c410310036a110800e100d00080030500921080020a140300001c66100c02c000c480c1d11f4003541c6030349140750100c0040e2102c0d012800f0100c0c0c41c0290b503a04120b442e40c103207083c10003903040c40c0c0318000d00301d400e0850b030000904042e212104c3c00c0c01c2000180001010b8030499003102c50000c80100c2c020041d4105104004c0d01c4a0303032002054a40c4003e03c130b15039240d90400e090909007401c1010000000d030700b4000b40e0080107020000040d01c040d819001c410440d0842c0c0d602075031400b11200700b012202c22000c50041742486c00c0240851314040110007411038006081103078403020340d070002800500d400c0307030060001130401e480c0a5a0780e030a54000c00d04420101c541400aa50303d43d1500e26a1400300e030018803507030044001d034408a0017a402581d0080140c2e0b081e40c1100d02d043d4441c9030740c141450541000c14031900500001044000c9413801e14001c0d403401c3c0300c001c18010401c00800d54103110280100c0c4480001c918034910038003d0355000502c0c602180c2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 563448102 1250 563446852 563446859
    0x10c050d020d17240a03170d05070e0d0b07051215150a1d0f030109060f112a01060f0308130e091f0b1e040b030a030f0806030115 57
    0x2034840c2c8849565030005004941c4820074025860720f201d0103001c0464100502601065006968082d0741d08220380c000105040040054940424244038030445035a003a1120420800d80c002e4501c09001c4805100012a40b0f11250b180d000c007010380550000c1803410340c0d03150300b4010742d02072290300032000c0c4514911040089800410502c80781d40030054400920450303e141e040361144c0159240403001850f142000005440841c51139018503800a022551401d030705070010f42110f448a200325001c6888481000504d1072505c1100c00f10361780c2c696541e2070319018072140c40c4030310003802c0f06503031068803056803d034090400d500400107031044c18240590310382c0343d06203481103400112181702039a4594101240c0e01902c82100ea0140741608001c000d54009081d52444c00041480c0381c00c05507540303141e2280107071f0b2401001031080316040c0040c640e090703401c1e081c4000e80e01e200d1001401795002410740c8001035404854218400b0702e915025501e42c840e030000901420829083d40c803076004295012 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 563449352 1250 563448102 563448107
    0x4090501060807080606010f110c0406080c010f140906210f0103060b0406030b180f19140d08180a020603010308091906020319020309190305071e14010c050d 69
    0x280a40c2d480108541085550318103940d5140d004484580c00140038060454115001d5012181c00010300c00c15243c0c070b241c2d13a17400301e400c641055001e103c482c0d005400c040501c0d40c000881c00d040510a1400301e1807c0e206e0920320000b4840c0451646c01003000203000e2050100b405035004040c030441ea0080c0c0582081c49c40030b06404e20030b0000b81d1300146840d40da8207491030b10b4454541203d60140000c981659000300b250740d10200c0b00240b440d07a010700001010b01981c213001034600c8805c5580070203105101403c103211401c0c58013201360381540c0104a00c0102d1703038204a915a000080b110483d48080c0149141410074100107070003908840b01000210400996030301a08c240312058940e00340760941d145251030941d40912500000da0000c1007650b007110041d01481600b100140101ca282c48180c60108601c400020700c4440c0d0032240120074010040244041c1c0c3c014a840d00c500303a012043c11801c21020700451041c1000c2c07011219050101d44d026403d9461026005025500f4107447c20402 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 563450602 1250 563449352 563449361
    0x30705070303021f0212060103270b180a080f0901231e090f1306030c120506070203040f05061b100b0a080106030f020d0302011409070812030103030c03080a0b04090501 74
    0x79030758003100001d600c41484c2070784203840c3c0841d03001c0354a141360780704c032401580201150440700045401080001554406080541c02042c0c450300e0040c0c0300d81b4060501c14140000c141c207100e9181c00c001030781c0d0086035021040c0e61407104a000c45980d90481071006890806518035002a000040c07110001c80f40054009810142c80d5012080d0740203006049000c002d1055100303850784824200d800812600301454074048111254800080303054590704c409200071504d0303000651010300c41401d07404001061001542243e2140000d5007090305099448440d0b210b640519401154046250714000e0001c03031400481c02010400e070b6024001000099020b01840d1410354003922500000141c4504144900c20850b504890301e11030402c1581d080050300c2c00c4101043e0704642d00c40e0303a0181d0482c0b05031102030040480e240141042c07840d000400d42407428126150440071400d10040000c40e070410301c1011720941c50300c1c00303e4503542c1e0410f5101c010042e610350302d80c0240c5082c140c0810440154032 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 563451852 1250 563450602 563450623
    0xd0b10080607110a03030c110f030702040f020903070e0a140703020c01060f062f0717010b01032703020f0d05041703030709120c090504080a180302150c03070507030302 74
    0x5a601e2507407003810948420030b0458540b21140d000140480102e8440d0380925014200c1e4603002c24070846095a5600d88014170701c8540071030304001904421480c0500c00e510501400c004103608080c0071400107522001c480c403618407800080c40000c4c100195940c8003500b010060084022207007000307a4000e00079081a000206258a000e0700071440e802c1805042044035216580c0b580442d800c00401c070079840b428004a04a025031103090309200da42800410007070710b084908204000d60150005c0c4c25950180b840c18145403070400c4445180544038186d110b94903034a032000c50801c50314a82245016011014200d4a0081c2142203a4480c3d2081c020400c80d4003050340000e0740701d4070f488100d440c0d2009864640210340e0f1000c040084410b1100706008160003408100c6105940300200010340d1021203040324110400502e0540c420707006214010500741c24940380588509542c041412052420300c0240341e51703404a01600031440404c1183d5000e680700c020740c0c42c130f82e84c1d80c60040c1d40d0b043d0404 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 563453102 1250 563451852 563451869
    0x11030f0301270908041203030204080f0d12020f0301140f120d18081b0613120c0b1e160807080c0607110c09060a050618040c030e03180d0b10 62
    0x1802d81d1040d1503400380c2c250a40d00410001d2030140b80444602210894450841c1496024400000c5a400c140180e5154409030300251605005560000b40380c0c00400742c0c0140382920501103501c02500740c9003500c1c107441c4800703240d86070461240001030014800840b02c550021065200388090000890701c01180080b9407901541c0b100c2015032002003007028080c0f0741c0a507010b8100e8986005074141e03c54200140078120702c0c9054058181440782d45010f411a03414a150810080c00b000203809000e001401c00c0b0000d10300300001c5d000c44019500301d0040095280348040b5040a0350403181c2c8845554951001401c0d548442614042502e0f421100b4034041c00c0c0200c07000588024010001005000750240c0074018081448040100b80c02011309500d401c049614408a401c2d110342008010b651402104900d961801001b08420f580c415055602013504042e011600140000152136101c01c031484184d80341903101d0003003006000359090142812383c2200602c811681c0050076802500c2421 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 563454352 1250 563453102 563453159
    0x5010f0605180f030607030b150903060c09041104061110020703050319060803310807060f09090504030c170f091c0f1b0506090109031b1806060e0d0b0711030f0301 72
    0x1207804414ac0c0100d003000c5405412240000c1c030484241c4004216403e0002c000043e550300104282109030015040117010032000542d80c60680c40c100590801401d00034003e528110366a900108640009459075100e96000402004150103070380021000d801841d00f20380c1c1f680702011080c0c0340381c0424081d0724042c01102c01415121255030406406840d0036070010000240781080480740303407134145a90020054280d1001c120f88969000d0360340a40d0080d501d001000c000c50401e40c1c100c000c281d5814070004020442c8403445005a4141c1d0003580c01201e204a404410411850114102c0c0314000d095030008000041080352181c2c1c0303110051041e105118a243d114401e1115032f214490400b804103840d48410000038079210b19002e170489024209400d1a90fa510a915864580180400620f41c4450050003400c1d400440680741110071120903200400d141c49034418007601800d0101000300b002d510340d0070094208101d8491003180094160703a580e4400350910b800300300000002070071158 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 563455602 1250 563454352 563454379
    0x1903020f03010621030201090501110304030315061b0201030908030408040f140315150a0324021c0c0203071a01180506090708060f04021c05010f0605180f030607030b 73
    0x501c100000d603804c070000d80c4101c2c054800b064111074000b54088045649a903001c074000390342030003070010307c4400f500480e07180e04162402400b17031084582525168100030b042000304036441815041110542155005200c5050004030003508000d44064054034000041c03104004d4041c00510403110035110300c01d01e103511440c0c00001b040c15001d50701da05900034a0b40b100b440f81034030040c2d40c22130020f140195100036804045a0032014503481503495406000f20f860000050010403408152a510304510b01150518046120701000c2c103070714101580d540041ca10755000300111104927400c1204d01c0002c0d0590441d0160304407090041501c82801e000380402c0b80c10140c01820b0180c98010502450340d65a0303541112070f590014410b0781d0015074646400c0c5c042c0c44502c014007000804d00125034518041e0002c1e2810b860303060f40440b0201c01440c030704100903980b00f8241d136007025001c00d544140280f603000042500c0c8000c00255454082d8a0901c040c142d0160f00542c1000010f41e000d4050b00304 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 563456852 1250 563455602 563455609
    0x110f0406020d0c0c0308030a09020301050a050a0501060e010203030a11120406061505040b0306090403021e010902100503060a0e06040b100e0f0f10080a0905030c0a1707080a03020304111903020f 85
    0x4503e0000f8204d803641d5805100003842040619448906c0c60390002d002c102c076400090035514156017034100b076595841849800d10440c050140542030030b040020401954100007942ea110081c402801140e4511083c00f545074a20b04a41c24110745401880c4241003509100000b050103204460102600c4621190500d0080c01510100c0300c009040314119a5144d091100c040740c010002c070210300800101c10441ca000004413030180000400000b11103004c1d02c180b0018041b0142c000080c40740a10801c40c0c00c2e900c040c42e5200780c4001c8101031480e51195030100c3d000c1c02201c00e00076445510141c40313a00065005001e02d0420303e045070303900c07901c140b15010b2083e074284201c82503030000e040440b000c0441e03003e41c1040790425a0100009908402900ca036419504240030241c015082011041705200f40a080117940710480c40000c1c1c6441256a81d91026100b003801b140141500800018180702c030702650700b050000090710b03500c40b860024032005c00294503030204901c05c810140301100342d1708 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 563458102 1250 563456852 563456867
    0x702010c02120a120e01020d061403070806071101150b0307030513110f06040f120201022a040504080910020d020d02010e030301050f0d14070303030507020d080106080901110f0406020d 81
    0x1003607010b1031450000039200c210b035496000f00e003488402ea00c030201521881c200344020301403202c0e6440005225424070960342a00c040c1466428070036403282c002449004408102c1581180c3caa00f04001070b0706417000350701d000d460a21505102102b18440018808c56080011440342126542c104410340d20351001003100822500f015010a4904246441c5410481040300194100038940c2d03050503540c0c001d034450110315420200015006280e04000c550301004022032001265440d540300d500c0302e00d6030780540241900c1141c8140e880e00007080a003c25901200d0020304040c28030b09400358020f1010759103052812250005104903816415080c5c4107100d4860703510100001b951450340703048100480c0d10180d01205501c502c030364015030002900700508100307505012000e08205071840c100038041321401000c400039500281580a602a40501500d040d105641040c48441d160003119500404840c10b25110000001500790310840f400c402500171908290700b06c91254a0000c01103070240e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 563459352 1250 563458102 563458123
    0x1090e151002030d11040501030c0903241e1505030f0a12020c0303180103110405130c0203130f0509010b0a12020c01142415121003020d03080702010c02 67
    0x26850301810005407800c039848045101142c4100c0e41000b10404041080f541d07080880c50078081c0c001420041940c050065911215050400701c2c00d452540d01e078582e03851f04003850008030882d078032028101c0d031100fa4854058440d600441081d00903060320048020200c003507040040c0c400b6200002110714000a400e07240d07911f6030b0050400418950340760550329803010900001c0d4050000f0342a00307620200b000c1c14212070f0486920340404030400000d01212080187c0e10280102000240900c2e12265503038401a86e61080010f83c100450034102d00b9401880003001c000d800101001400711881510003090b038000310307800101c4e640d032140030144500c15041d015010030411f1040600e001d07400d40c09842c007007154400202e440040405078004220f42100d00307065050301c0001c05440740e1302806080300305480a42d420b01142c449c0d03a040c0c004602070240000402e0780d00382c00181c40000404a01d4004503406000e0348182c5000780f4010300040d000b00c0b0703004019032070400700110a40c4000b0707400c02407 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 563460602 1250 563459352 563459371
    0x3010b0c1f0e011b0c110a030b0405071809030e01081e0a0209090609041211030903010504060f05310303060909050102031b130e04080c070609140402040b0429030f0601090e 76
    0x440e960750f1402c80b922821b1417a079002c4e2807120008081740242080d00d04c168030a01c0a021114100003600742c070f0144bd02c1c4154070681c80c003a0308900084d002210341411020900b0100320507038698400740d802c41035141c00c038400c402c030400502240f41c0c143d80150074407031011288080c05640303100a204a40f4001c81d00030b0b00103c0c8030741111600f68020b003501c0c0f00e000030303403005e507480d06103000042401d544050b1070072030b91982d4420744240001254464039801c544481032007e0101d000002100050569066030091700d410b041c058000c050003540300318000c15188800b03110100c1d013814400d000b90421643d00ca6481c00040348810381c13455a00c200c030940c00711248070018060401e0b10360801e64030024011903036210f040041c48400401003111130020199681c0b0942124141491800c0280f03050800500550040c04140000c6031141709480a903852031580210011042c403c040707091502d480f405c080048004184159012190f5404d846440c02b81c03582c21010796510640030f9001000c03a0401c00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 563461852 1250 563460602 563460617
    0xf09090b0c03090339030a090312050904060329011206051302040911120d120513020a0e0f010b180d03021c0c02040e0102090603010b0c1f0e011b 64
    0x40c8401d0302016540050324101241d041464480d842c0b10412824131501243c440081c4000e0782c0552081121aa030f4103445000d1414554001e102034011101c5000040c1454025481c0c0f130000b44c855030036503401000050040c444281d07241004c400246d8021640b001000c40040200465161201894101c40701c582c1c030010079007500c1e204d0f040104400b43c0140d10034600c007c6078201580d654011903003000d00030500e807100f07455440c081004003a00105040311030b81014030034075800307078100c0704400c41080b0300075001c12255102d502d20f042c81d19070f5000007544000300260106603107103450380c1d0700e2042004603206075059032244004072190140c20100007441030a0b02c00381525051099903d85818880c2c0120350a240706003100500c2401c20318030640008554bc01600c1c00c0d49814021000c408050800071031400e03030038070041106c51105000b8607a10290000300c049042000f000040345011407880e0201c0072421005075140502441a04049650709141d480101003100078440440c03001c4540b9400c9 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 563463102 1250 563461852 563461861
    0x307061202030405032107080106110d030905070f03122307030e0111030d1a09010303021903050c120301080d0e091b12180610050a0e150307030c0f09090b 68
    0x300030758401070003159280001d0140d100c0c2c90303241d02942005410200c100490510303280c00010b1403044140d01850400c1121740000760151404104407030342040915000c2040c3c0b455080245c40c051050f801082851400c410000c01d004081a500c11285016500c04890301141440780c101089000ca008220140070808880082d024420f91811414181011800b0b8a2800c034100d065410100b00000c6454907414240503912030000310250307441d8100c403140d03001d50554070b0081d0b846040445203890070b646500503030305042c0a4400d407103042d0002d00844d10000051901000b0540081c070076102944191030f0307400406805180414440c5001614580340d540e506024a5900202e00b0250502c440040013440700b1405ca55240c2441541c84480001032450784480184c90807000400003906803460400c10b20041c1d803140c8406044407081c02c1c6400281e103648200b2094500514105545485201000002c015800c8510801c594100c034403065003030345d5100410140e0700c1402c8000d20a0229030b0005 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 563464352 1250 563463102 563463137
    0x807050a05121504092607050703020f1f0201090b09010c0e10140705010203041115030406021b010c02060a0c03020405010219030207083f0315042414030706 69
    0x6640c000c1851036540c1000440c1d5012a04031003214600b0354a0b06502046c0d41c8421400c03030715040641c802041d4043ca4005e00f525035586421840c00b00a100e040c6900e000c0b8001e554588040d04d40b402c3c4065407203d001c003841d074007034000d0048030011942d14403003500040c481c00c0b040c0701b04482c020290302c883c01040142020455010240c40c2500c0030711403d41d000d04a605003480192040ca885034000603030b030341842e0400300690b90600c0c0c1450f02c141d07028100101c0c0030a100b03080e40d41043c1d00040141c0c0b24240c945000070840c000302c01d80d000311b40c030f081d88030722a441d4001075040c0101e403021002c02003001220004c134241d11482c090240582d201c044a021500404042c2816003402441907a101544841c1c01c1801c00640c0d03140c00c01c9456200c1915507800d141e09261000c0c03040c2481800500c24010988160203000007401c07145410a000884000ba4907a50000c5161f1176003070107140c80120350329034441c40140e418010f8410324000300190800300c0c10b00095030b20541c0d807940c407495010040040785 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 563465602 1250 563464352 563464387
    0x20c060906191404080606090c09150d06090c0309020103110309213601020c100c0f0203070602010c0206010f0e010b03090f01110c010b0a0b090607020303070f0506070807050a05 78
    0x1034010804002c074100c00d03500181000c0d0005c2d2070ba00014249605210040002d40d104c050001210035008000342825643d5110301407540c3e1086a0206440c0d0524003001c400a00c0c40e5480b58800c2400c0003141c00b18241d160f8071081480b40300349c804002010f0441003800081c00111607141040c1e0011203580307002c2ca140c01c0b44101b0b00c030b12030710014a03145248a004200700b00c0c0c4c00122810012050702c400403220300400540010301c081c4001e158841080c0d00184000740c00c2102d2405004600d10341c001400305240381c0c0c0d00101d030003404031030040f5078408009000301524009000103008100000c1004100650b50004440f140628051144d0030082500807544c00030300500d04902c507840c00102400320030700852211241618029444030301241843c2e0a4408a15070180314104483c0c080c0143c03003600f1709a4003420000e0755050b17110281c5102082c5544505032018000145407815401003020000d4881d10a2502e0b569284841e1501d00b03096409002d01d90307a00020a0b4144001340c0149408181c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 563466852 1250 563465602 563465647
    0x13050723030709090c060f0f050304050a020301091112150c13090501031b080c01090b0f0705160906080303070c3807020705010207031e02010c0b0115020c060906 71
    0x31100d42860300100002c1c5050700340e80c00741d01c001d81c5815002e4184030301242414000c0109080034542e042100030010694884900d0880c10b00c0004804102808402c02c00320510130342c003600030841e0703030480d04114200c10a1910180c2c40303841d00899151001c080801e60300700c1016080285001501d407048105055082080a0340046071010400103882d2043c2c05160b00071402407404040c0491051440c081d1040150000d40c0c5e550320016403214030b030341d20072451003c40f001c43d4070050303c4840e10580b00c8203a100d4004054100c0c414103203220078400c40401000300300c429404040001d1a0b0f9038918170b443c1d000031514200850040c0c8820b90100d031700d11800d081d441480c03403102462080e4078090585008600c0c503908582e00b00100410101d15010410080a4a401d00092621b02c1c030b1030344c8046030084810414a09009400c11003400c42e4010921840104d40c008034150311903848512806160011019640040c400d080390124103050103000c5514200300980054600402c4005e1402d1140f030841 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 563468102 1250 563466852 563466899
    0xf0503072312060a09020117070804030e0402040b0a050c1e060403030b0d0c032a15110f01050c0c0705010503040b01090207170c03040e162111040617130507 69
    0x7494940c0000512005102d4084d0810014a0758420700004002d461004650b5000d8061340d0203011600d0b4110751000c1c0c2c402d52510748541b030031039202c010134040e014541c850380e003402000c210b4031120b03604031003e13100c914891003c840c01000340340f105042c0341c00c0079900d8078401d400c07241c017040c00300f1b100303410480340940c1c060b114034000e8201d030b51495000101540280c990903441036020314021a0b02d8400940340f8041c0483d180070038244410030905a0300680076100384402448007100040c4140701001e800020f010080289240c01700115455600420303138890a4010320380081040c1d0301800c10ba901564002d0030802c15030f82481c406400079881008140c91002075011841c0100e040c0600500c1002c2010b4007a584031490401c01c51007a03080030b408100c5002920000c00c002d039601c80507010b11000e141d05c030314101200107a5071900615201c0d0f40d40000e6000010003141140e0041080321120340100320480250f030b2805106046c1d0311022900030000e03000303001c0401074200030201c1c00d02e00c0303110340 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 563469352 1250 563468102 563468119
    0x4022b02040f14040f05010e01060f020f0f0601030201080106052a0a020904031d03030f09040b0a15021507020613060b21010e0c151204080903010e01060f05030723 72
    0x40074048441c40c030640c00842085022804101d884c209401881c02c94400a4030a02032075041074022040e61105000d08001c000401054090480c400c10129103c0e0514000365404a0240c000c1d5a8803a0b200340820f90105040000005041c0c0c4100101c60001c2e44440300b1010001e80c40000a4402020340301d03140d0903200d090345070000759403500c400070701880c482d80303481c03081c42126140c1c0c0726044c01c0851980d2280e002031100c2440341c020f5a0480345504021100040c10b00d080e20005010f0098139007104843c500c9134441d40444607000150408504400e403a00105603840c00412603954800315a1194200b40b4100d100d0f00045007600302101000300140214052030781424906000e0000511008007691508020640a481480345403083d120603560f00012074007541040b1010b1091250080044080c140001c0034090300000b5210110001002404401c04545245001c1c252a00a01c640600f94260024151400203009812521100d00c04011044d50001010506c0868035159400510300b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 563470602 1250 563469352 563469359
    0x1508090a0f122001050402010306080d0e150c030a030903020c120319030204090905101401031e020105040b0304083c1b011e060b030f0610020a060f0608060604022b0204 74
    0x441050503e640700c000300028243c1b419000040507103031140e00c00e00b51030300644d5081c1c040340d80c800c15a541c501015240c0c0e007025220f2203031901c0c00e441840c001307404601010070403c1d00c4607415002880254000d034210b901070071800b0204181e154080c42c06141e00d500400420800c986086480007100c2014100142090f954042c035800350780300e108040364103802c107903000c1802e84140e01c103034260b01c0401c8450103d00d60541c0c1d140d180d444e2045598104443c80143e120301160310510444000d0041c801c112501e90400d8036000b20541c02012000a25024070880f041c0440b1041c005001a0007495901403201214841420801d40c0410540d99400c81d0301d00b801400d40f0f20074001c9094111803543c2410703c0d002d0700d04e41c0104661541d007040c65191020000d0000c4101d01c0c1920640068084420b40d00c2466403c1041e890a06d444100070700050400180380c002e000c13554405402c0300d03110001c1e2401e5a546c00308220492113070b4402e046080c4c4105601c280000c18030340e800e1003915001c0b4030040c03410b504e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 563471852 1250 563470602 563470637
    0x19050a0b03070f03051501060c1b03020a0308030105040e06060907050d090819020d0504030201050706020a0c1a090c0f0901030b09030f040801060f140d022202041508090a0f12 77
    0x1c0d1a08280384201180404000b044810000351504142d007000f003c606d941020710050100711002c6004e00305413500555003a500d560300003600011a030041c103825840d5524a8043c2440d0024800e46108500d031a80072103a04d003021481d01d12464004101524903915403c095455800c10100c80410030768078412040001d02101c0208407485e0891505040700c0c184100080c50000348808080810000f03000800c0181d0300b210540b811680d1000c00940c0362040c001c8101c50344425180082e00030700c2a1600c40041c0800c2c1020140070b080244269419120b80a092040205c40409100e40000c00400100701046010810503000ba4042041c2c80c5018880ca0010b401174005070808032059540d85000c001a03600000c42200400004404191030040c0100107912a140c190b0302034080c1c80c0040c005140c4030f00d210340000074841d06a4003151a1522021071801a02117024002c001c034081c640454040140051084007507640591200301303e040c16960740000d240454070800070300140b030344140603214 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 563473102 1250 563471852 563471863
    0x41109041e0e0a050303060103020d1b0918060e040615030b10050a1403030706110409020a08010306050c07050712051204030605060a0b0415110f010c09090b0919050a0b03 75
    0x41c101800041c4940000c1d5500c800c44020b041440b485034010040440002c40100643e680110f09080058907800e00c040c0d000b018044008802101154001d401405613400c0001c40382a2070740c0442441018074105540b004442c002d014100c00a00598000b400003010303600310001c1a0061100454601e980c4c0c2c3e51910f2021058441f0014045106001d1245081445c002d4000f0072031442054101800000402d07164800c0c140090100c035228001502410081c2044600600700b40c0d108556070820418000c00c034810a02086600c1402c14012070070125012094911094004000e1301401d40750a00c1c96200881c0c00c4811600d9002d141201c1030074054040c0500021802110080307036902d000420018103154a0700584441c1a041c03000b4000c0d24400c5820880031296420021100080c0020075460800501d005002c1076007888001c0b4800b40c0c2c40025182110030001044c0290030340e0008205070041d0482d014842e8101135642100d01036030343e810040c1c11140c40380c00055043d82d034201013424030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 563474352 1250 563473102 563473121
    0x1e0901021f110f1c09020907050a030b12030705061005030715090e0408070302011803121a040e030a020d0c122f070519030b040311160f14040e070504110904 69
    0x24480032504c5144180c4168101000c03500c918000c20680383c00f580000c00d4040c001d00080d08111000c22507003015800ba501c05064035800412002141c11510280b640d00c0d48088011501c902074500414290380c140e56400c01a47d00090142440500701404000f03580e0342c05002608005654000003805414070408a00581c0102c5446590b0f40050401070700399090307201e6220501d486001c1400109034403005809928980c4c031408607601d810507406420249060302c0080d40b051a0060744c4218660010003400f94018070380a89400381c0104905071140e8040300300140130441c0761504441c0c1144281014600d20f4607103410781d141c1c1c502e5114060f814a800640016065001100600851503c54002290309030240da402e000181503544100700e400015000a051042141805583c0e40342807111088144940c003461852994a600303003c281c0d0000e10881e401154035211490380c1d410540182d50300703980b405000b004200d162005010013040710801c00c6001180c00d102e921a070340d40710300407032801 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 563475602 1250 563474352 563474377
    0xa06081e0910140f01090c09030204150503010b010504032d051b210309120c060a021c0c031e0216030308010f08010501081c051603051e0901021f11 65
    0x180d250000e6000300303c4081001e0000d43c40c90010400c202644402d001605690080a006c02e030050590402d95518441d0f41000b5403150504040200c18444c02c2d036000c089550803002808241d5200005540030710030380c04080d0600c1e902c10a0302206854010030868190300544a681100c03050352140f80c1418150007269410004507211006180303000c14141d011895010f0000c9403040c000ca184a40da031007212001c034010084490780341e4950301d050103103081141001e80807a80d21008414000d403078841d1030507861308940d081404185118071846d140041554113858003500e0a41c0b06e02083e03810084c0c0b0300b9260031440f0340070f54a126040c0d021315500056100f03880e0070b101941007146d000c04003551504181c3c16680340400401081c07000258842c100041c80401c001d00b079002c81400c44140c40b980301710b003480300d4440d03900e80101580800104108040b0301394030311040640040000040c0b0600c20410700580c821114038200c0004080c40000b400c0429600194850040078900b41d150001c0a80c40c0b0f1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 563476852 1250 563475602 563475613
    0x80d0c11061c0e120405040504020310110301060305071e0804170d0626031204030c0c12051b0102071a071223091003020903010b030106230109050a06081e09 69
    0x200440d483c000e41088804030006041c0848002541021500070391103064411500c4d0030114041d500e052210150900c003d10003480024488401c01e50366920a02c01d01d00028a441c0000741d089104264108510303022418040d020f40820710100d500042c090f10075144010441c591380036214280c00104252000c102000c00c2040ca04124071050380c0324110310ba19812101c490b140c81400c030110840d0424070300811181002d4459060464208090042c001c00d031861241c008180c1041309800c0c41c104a100700d00f115440c0c603440c114031810360510320006001d0b90044000744000d05141d044078407250031141c0010b007081015118902c0210103000e900012074640918400e0119500b065101d1040b500fa28051074401444c010410a00300e251500c0101076011400481e560350a40180040603401002444a01d17191481d007500d003c2030444401c00800300c1690000c1c9940a0030100003103030402007001822901e002c20a850b081c50090240c103149100b601e04103410403040a00d20b00541c1d54100628 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 563478102 1250 563476852 563476897
    0x40b09070225052b2a090207050c0112180b090c010206010b09040903030603060c0e0a080106080c0409230c0102060109110a0c03031808031b0301080d0c1106 69
    0x1c2c4042003151042c04102d4650424890307900d40c065480855003d0292080703102070f000000900020301040000c240405990a40740c800c20088240781a41404001c114101651251000e00300c1c0b081c00300c002c050790801080c04025600440c00c01121001c10000450301141000c51500030255102d0221450440340007803151820b0304111880201d0b000f8001844030354140002200701d0701403004160710607500c0b603484408041c07003908490019913010209003d09c006aa0303000c0d001c444039a9055001c0d04486c0c0000522142c140122000c81d80c811014003001803001c010300020f403101d15419100006582401c01ca5000b01641072404802c038880504000405039000a061402c1030740102801410203101c000454200700c200d83c0c18a00360708102008038000d20b010f4001d0084120b0164034005054000418071183c0c0c03000714402e61000f442903442000c2d045502071640000e0040e400e869006500c1040f816000f40745980402c0e0003402010f07402040c3c0d07400180254000500755000d0400c00e154034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 563479352 1250 563478102 563478133
    0x1b0c03050105160914011403090f010b0402041a030606190f02010b030a0c060f0221070201030b0a060203070807080706020a03020c06061f030f060b040803040510020a020105040311040b090702 84
    0x30f40c000d0314403c2e124071800c40e140390041908245010352241d010404100c2202030b0300541045000f5481c0c2c80d030054807854042601620342c0b052148403421942000d01c5030509240520031079040e10082c0031071a0384076112a519a1075134000410032500028100003a02d01c401c04c0018000443c1c400d60f5642c4400151228024291540c421610303010303600c8a4880000128a00e10303000c1a07807003510b0320800c0100d807030300201d2030090071600080e07007200000b44c6032004030350b4400149441d50003a00d003800300702c07041d00500c0003c50240c86524010b810900402001500b81d10040c42c80d00c2c0a01c246c10305102e4a0f4840300200d034000031135540441c0e400150b44500b1a070500525512610454000306801011802a10281c0700c0040e084101907456020500c3c205640c2d0003403014060100196480d283c464503669a81d41c4680a683c1c03261034040004015540700140700c00f1081d5041e50351500346031450380c541c0c5400780da0000d41ea502980b01c0c03102640395140c0c0c14115205146036802440846110244c5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 563480602 1250 563479352 563479361
    0x2030412030605090a33060908060f0105091b0c01050604240311120115030605250507020409080a08011a070503030609040201030b0306010b04260c0904031b0c030501 73
    0x303103414582800c01c00c00040e5104a41c1c10b0344080c00c1c2c10003207040d01c1540303694500f1001c04103d2100e90303a039114800490b02d03858040401a100d460b102c8001894650410355503401c07040f6484081d21203004014001400d162588075040a01d800c046a004207a00101a0003074020300c1144a40c1ea546604208151803d80504600300c0c4000d0195808a03424060101a54043e030101030070042414503809050317100c8080d003081d0a0035000007040418003456088041e0440b5110030343d005814440032a216803641603a03003080d14813020000980a22092096074240c102c00f400780ea0060b40c40315203034040340f03821008000818103592800415030501c140e041c0b0000180e14050740100091040500241000080342d401100446000240c1c0d0342c0ea01c0100c0107441284003064050090b00000641c1d041c5440281090341c01604282a4101d01c141856400c3e45e81c40c0300c1e6901540c080d801c508440e0a141c41e0083d000760084c940305007080c5902610002000d02d190b4100d8031540308031810000e105080c0314 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 563481852 1250 563480602 563480633
    0x9090c21210a0206010f0e0f070905100305061018140d0605010602030c0d0302031e0402040e0106080f070501030b0906222c0a020906060c28110d05030f0c100f020304 73
    0x806c00b17042818030880c0c0101050081c885c0404030740000104000c140611040e000401c0010407801610305c81d003100801809094130460b014000b030b485d2460140340200880841a0795010041d42850728082c5a48036800d85000b9150b00841a203c546010801c0ca000b2507020344590b400940d40d55040c48502858110312501d0f04040510500a0050160020030300b801e43c4000069800800d4842e800000c2c020901034190011039131030b144000440d020082040c83e4096401c0003500d240a13554030041d81074030b00c2e82040d1a400325540d80044d0003803500c00010070080c520a8043d050f000071440150040f103c0301505047c0c1415428140098040c580780081243d8800e0400780c0070000c8103a0108000179000f50403070b80719590200f41119a90020020212070b20155601403045000c503c4403115086401882136518594241400702a4101035102c803c6090340a80210704e05140001c2c1e0020b2500260800318690017000015000700d02a801001180c4010020050303882c2054a000e902800b0700380c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 563483102 1250 563481852 563481869
    0x601020d030c02031e09060409060f0f081c050c0d0801050316050d030309080c010908030a050f090c102114180c04021812010b09090c21210a020601 65
    0x24880e42c20690100980324441d00d0007008880312102925003c8143c0102100c0075040a408100000c00110303070742200040700d1403026485696510340a0804803020300c2d0103480c0c02540000e140540110400744060b100d20054a01a07017842d604131441814009001000000102c9003801445280740900001c001c00558034211481300d850440425214260321070040e007410b541385003803410300250390200c6000c1c0009000802c4110428a0098810b0b0015100c0790381c1c130f5141100007114003108000e41e80c02407085030014522a02c0200800084c03105441c2131000304a00100d0031000f20429150f0b080c43c2d40ca0f0114045118010a8010546000001c0c501c2140040f00000b40a070003070041000c00180000307403005661425000c0c19903000b0941c101445070400229554104685419402481c80f80421100860395403074080100341da0703081c00c0021a511003681c01c0c1894140f80b10b00078a40e26504150705545c5540041d49410780740860844440d0001400080c02007030440d418840f0034090203008 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 563484352 1250 563483102 563483111
    0x31030b07050a170708150301020a140705030f134103070510170601080c0a0c170304051b030606060d021305120714090f01030b0702070b1902060a09080f0d11030f0601020d03 76
    0x2b0300014459002d0f010902686040051501c042c850240121800100000000ca541704143c1d9038900305140144203451038103140ad060070404600310b00c0c12b8080c0103004070010320701d0542d82203840b031200301641c94980c0c5440382034000078954440d001c1490a01032161255100007040689842801600510710750400014004001960420005565500d80c46241800c4024128506a104081c83c1200760350302d01004405c010800100190441c2c4140e00e24442101d04401c2074140b41c2d40c0c0400b500d4041d800b0100b8800c07515081a035034082c0041d00021001101803543d6100483c110301d91003088814142c06c0b41d00705001c0700b004403002e03940064007900c071207845140682c0c5940c078074041800020024071110f00400e041d07903c200001c81c060324580c01e5950342c48043e5140340414401d00a45a0054025000016105816403154004560f000403100313240c14100c00000d462130307009108500f581a0b40c1d080c0c0c0e000d4046d2403c080c51003840d2001e44501c0e02e00700346001900d40b06c6a4070203030f41007500780b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 563485602 1250 563484352 563484367
    0x1090605011409100b1e0409090b1f0e0a0b04020d05070903020a170c09040515190c090b0f0c1f0209040e03030603070911090631030b07050a17070815030102 69
    0x10170007168615002034910761683d0001d034011107424440c40c0e100c4450710b0300380048442400141c2d646e00c0e0240d41100309400307021074440c000c1d18034221248104403402010340c0028011000d550840c4102d2903000308010701d09000d465004c01200e206a130342c14000b600f07010080c030442c1003614402e000b801d0442e442a961580810a455403084c40c40b01003400307803402002040400c40300b00000910307013000b0b0044160b42c2c07400c04050803940301562a859100f505020551403407c1c026403007141a6580002c40307520b044000040c030800c50740004400300d020301c920700c115a00c01343d15140203501004d002c81c000da5140440c404000a40380d042c2140382280e0420000d1000d507640c006801000c60b007810f403020540910403075045150303005503032010382c002038002080e045c0305181010400001e1794000d18030042c107134190804040c54070f543c00001e01ca05058000301c0c40c414000d001800c102c44051034000b2188082d00310303200345044140ea0050100d408401807005404041400248400064000310b00780250b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 563486852 1250 563485602 563485619
    0x1503080a031113050a080a1e2108100501140d09050c10030c0e0906010c0f080f0706050615090d061e022107050c07030b040809030f0a120c0c06110109060501140910 72
    0x820b01e03100500300b00305100700303400c0000446619050300040300c9e42c0126007410780000781075008100d8801d0340400e8244400328880d0700a51440c0e1441929240c1941080d12a07e81d0b00c0003019400c806441900c10303008203800315642c042103001c503440c841da40441c001000070b60203030144884004c481e105407911400c0011590707000312209861600200707104056006d5052952070f510550300394007050f120026612040c003a190f005030703004071b00a40c1e420540342418a0102c00c07501271358992070b80c0070529401c0d420128165810603070001841e1008001c2da0303070050804000702d81c400300201a50b1440c04240140e40d00c02e035a4400c0e8071455030700b0000c1c40c05940c4140c158492856020042100320389401280501580c46c09440e200d03000035003100c82483d03240420070760720b090000040321b154850008100d00c1ca80314600c40d1480b25031100d450004c1ca0309160081d62640e10a0f05507124941d6168101c901081c45401454001c041006c40b00c80307100a08000c1c410028030003030901c00403000300d500800c25201c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 563488102 1250 563486852 563486873
    0x10506060d1d01021602030f07030206030c07050f0610090b0f01020d14092107150207410312040518130609150509011503080a031113050a080a 63
    0x30049800160b40b15a1200c002c100c0c03400c0e61441030700756102082c1d41c144d0740c0d0f9400301c03034900034001c400300e4805183d050342859581c3c1031800000c0d0444818000311340071101c01d41c09810b8092241090300d914060720380742d40e4584101101c00300310780301141c44200485406807084440310101078031041030300f0b010040041e41c1c03010140e0700003040003000e6041001c0342c4100320548023000c4000344614005845803041341d001c1c0d001e0b000300303001c14000c03420300092a050780c00d43c02d085441260060172840b450a14400c103009040a040c58010030061042c03d0f000c03a8042e203100d075000c003401c0d054105041400c00c0c03514120b2502450000640c0c1000144416943c2e880c859250343d0000500030002c2d41c61540b8044c1082c24407800502c55070030500d05108105074481a1705c21085c00c0c81d0304000e103070b6440d003c00b421303225514000002c2c110a04000d0012910810090100394030606020a43c620f0780712841c402c41c4e02510200d0035120394074070140924a004150304008000c403000400013425541c40e0b120004 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 563489208 1106 563488102 563488117
    0x90605010e06070b060913060f0c0801120f06050c0f0d0912050f07020405070e0a14120109210c0b0103082107050403021504080f100e01050606 63
    0x30b052074000e5509040d0003850b1030030301d5200c0f80203005002c540600451451f02600c9091400701d00c00c4c0c01815101002c9480024080000c40c0d0300030020382060b084807258401d035054620108a980c010b1750300141c6c100c0000100d40d102d81000c00060b2103001d194540505020525440c07040040c0e002d4162a4001d400743e50401c603038194200d41903c80c1c548000e5031110240200d00140c20f159200503486000760402303440840c20400020348403407895011601c480465007504080b4103100203400040e45024000f404004030b01d95408401c1032840100071405031400301d14500d01841809140c2d000c9030001083c0704656160b04010141d030b8084c0c1c1080940f4615413801035446021806140d2290220350b8580d4245820f40c1e00308405040f4070720f0b4860b5004028440030400d9541400000122000d00d80100845a500040f4a05480c101e000e4094180d240c03808100c034a40b00c800c12161103 = true := by decide +kernel

theorem cover : BRFrame.Cov 563309352 563489208 := by
  have h0 := BRFrame.cov_init 563309352
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563309352 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 563309352 ≤ n) (h2 : n < 563489208) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
