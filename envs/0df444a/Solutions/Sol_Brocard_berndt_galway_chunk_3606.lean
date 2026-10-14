-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3606
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:08:58.39498+00:00
-- url     : https://prove2.me/submissions/385d1bb1-8044-47f3-8ee5-7468e36a2718

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 648381294 ≤ n < 648561151 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 648382544 1250 648381294 648381299
    0xc060c0a1a091e1b01090306020c0304051c080403020d21200a020f01080601052107030b011115070203070602030c0c070b1e09040b060c060a06050409110d0c12110a 72
    0x1c1c1c08006141c807041c603041e80304084c5110300e096610555000110145009001d407a80d94503810143c1e081248004000c0c0c0000030308204a107820b40c10119001d1b500c044800c240d05060302c428071507008a00c40a4000d006208851003003200c2c003a100c03003294054191051890981d8880203000300140e0201d6410364041e10164030300884001100c10031a503008010011451112004558801000c1c0040341405801e01c03060300b518002d018100e10304441003100d624145000d0200809440003040c019040c8941e401c080c51111002241d40ba048084500c8050040d4903840301c124139511440401400c0148040305000d408140c84008040c021440e004683c0129220324484290344503031088400201d0b00e10480100c1802050003410074203000400014088100300046000c5512048491181e80c0141003013003240034036407240c60042c00c819182007081c103a4507654014444024482d491040405d22401c10400407110f00d43d0024048540030044d00c8515494401c07980941300082c180f0400c00c0c003202 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 648383794 1250 648382544 648382573
    0xd091509050f0f03031506130303030e06183705150f092a1002060601110105010f03030503060a170f0f060c07020d0309050306070c020a0803030106020c060c0a1a09 72
    0x40c1031107080e12401962440e100c03078220100f00f02c031181c6c00641095090003034500a4070004c081c14002c43c003948000c2400350001ca4441e0522000410ba42480603030340da1030700111880068a480c03025049003461035040c0507514141349103286648138990807054a16103030104a40071410b00c40a08002d0545104d0b0b0f102d400b4032008410084034aa4400d5120441015a01c4d83d6015008c80c6201034400d1071101000b0900894540c039400240d05025030710070800e10806503402000e4150380310320003000f04519414070121246001883c032019081000120214903583d44229130900240b00c660108034140c00101801b9480361080c2c0d92444003801b503a81e002a0710710b40820151b200d04d6480109901d005d42c0b660070007038410120354059040061500c80410192010450036004000a40700c070520b00b00a441003141e80c494580101420ba04140010410b0030f80000d1201201901202c415885402e40070130546899190355015202813880a9610b40c58100c002c40240648481d60503282c005612108 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 648385044 1250 648383794 648383803
    0x905060c0d08150f010c0c05090c03060f01141c0608031b120a0804021302070b0907090605060f03010302042409050f01060c030207091505090411032509020d091509050f 74
    0x102580021044544c58a81d42c03003040d040c8030f094842d200d83e02c1d0b0700e620703100441c01115044426494072100003092001ca481e0403c808140410246015040b003d25851000c946010318107130f50000c03030000802c0e0301c100d103040d811040242081c0c44c00c0f80e485483c100100304840030f0190704545180649205400354103050000c83c1d0381141252614a540e4446a082c402d01e401240009142d030799092241e03400203402e0352103850013030740c02070000d02c07869003406c0e074020446000713a00c0584218010800d003d2440507950580341101d40440f00007500311409000007405009004007000d03d9459a14003240d440e803590321070360098554150614190313807100e1040e81e10600e12a0050056030142c4010015070040c0e802c100d01d0a0a0b40c1d03180c0c0207807980d6030702080c800d00003a2000c80d50000b810540c0710a9041c200401548100511804d007002103c21600f6080d45903140950040b6030340004202c2d40400707040e040040000d40c4864164402c10046a541d8000c007481c0c0ca0031035490003500e22000b0580c80004 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 648386294 1250 648385044 648385081
    0x7051c05040317030703020d1d0c0a1d06030a051c0801121509020303090a1d0c0a08011a1903020c01110309100902040b15070308160c0809010905060c0d08 68
    0x250403000443c0451a805641d00001d0034281059001c020003072a4000038015603481001000c2c0c20341d0a46080a155400c11081c0c82e5030364003e03034010408100d00401e40b291000c5000c4145003454180c0c07225404603040c880c04410141141c4900b0805411a40055001a401498640e9180083d91320303148212803a821710301c1c0c0980704d656503140f1100c80c17201580c0851045031000b4102c80c50441c000d000b203804200d00d40d011661121252001031404d2000341c060980c4262141d11b90351400c9140c03000038003001c01c1801440d01500e40600843c0c1144996000c44140c841031140064500c0c03134489004012b580701c001c461a440d424540d4290070080710380d0680f4001c50160003c2c10032a45400312510040120710300990b8042c0c0c50309402c40b0140c45845d00040001c1d44040b0150b61100a400d000e400c000c1d000d410710142e00d0152182c0012160300441c920907a692101d000ea40d5405060b00481d68411582c00507903124500183c00a580e103400640001141459124a08666101c00700e441c18205040d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 648387544 1250 648386294 648386303
    0x403030806090a0b04111803030408071511031303110d0209220b01080102071e020f1519030e0d09051c020307081c032f030a1107051c050403 62
    0x1440403404510b040700320141e02516104000494060100004042d035401920300c010b86240010311184c100b03542c1015081e0344a080d8011032810386403188035943d030301440c415180d10090301001070305004c9c8a40182140002c0c4c41c02100d8442c282d82e1101c5a1400403131000f103c95206164410000c1e04121001094094000f4182c01596079040c20542c400914800c2c1e450a54613807802d00800074101e144540e0103004850300050b103c080c41c0c5040d04810a502131404020014006060016038440d140e240c103820041c1d5660b036041224442c0c6081c0e41c010000e40506c507000305e410350b10310582c0c107034003a0301841c13540c208844001500c14825208a00207004050300440000640d00c20140ba04000341c10042c0301a0448071207964842c00315060080007000c03c0b40300051420341d400a00d505015140980b0703441108584d03035282e00030582d01030b100d80d008091011103002c0002511451141c0c454031807d60300781c00c8103075601003600c3d180361280c14126107002508192072410705168403440548050303a0340b1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 648388794 1250 648387544 648387557
    0x5060106020d090519170106050a0f060806031b0607060902100f200a060b060c0a03080a0c05040501020c04091b030f1b15080603030d0e010e010b01030c020d080907030c081c05040303 80
    0x4146e40141401c8a88041e1499592075000020340e039140d02c49044024010301d914103024600380700d0010002c0c1000780040c0c1c4242c1c08481a5101e0400301511450005c4045031007564404903840c000b400742c00c100e00003039480011200206500e5411070445114a0015511041d400c1c41c2281d035114018200c00000300180e000301c00480001d00168001c4050311750080a55041000c42806546084844242140002c0300c0d0710501070402c445000d880e20042d6207080042c205818040001d5079502c44591080c85291103420450034490100000f0003055000104031600c1e607100e05084100081c0d0751000c4580d031104402f0b4101c42c0840a004005039040c151240041c404205012100030340054000d6600d0701003000f440c0b25041c00da2085408160001001041101c440e095080c21201c400401c41d0501d070030411920703005940420b00c10390b02041c1d0700f04030402c0d84031012258a006516000141042c0c1d03018804504604000307070a440811403042d0409080c502e07008115200c3c0168130004010445 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 648390044 1250 648388794 648388799
    0x112150311040f050c1305040908250803011e0801090f02060a050c2407030507210902100314070c050d030b0409170306040c090302150a050705060106020d090519 71
    0x1080c41103034038032810041c00820b0060030200310300204c91081d5036018415030006031039800125241c4103100100800c8604002d9403403d034640180030301c0b400791038607101025448540320459881c05426441038002d0f0032261030f9a100c1d9451968540714130080ba280d0f81c3d12050000e1030640c1400b500280035803010090540540640c21700a85400202800040c842c040c0300c1041e40a80070001d802c840c20806102d002c4040400e01d0341581880301401d00300c1018240000c10008681001d00b8200b60704c00c076000220b5030712000c4a900020b0a00100081d4000e40894140d049160b00d0340054414801f00a10780e0302c00c2d02c0302c0805549081d0035903030082041d041201000308039406075001210844000c0c1000c1501d0190740e40d03030303030003c2d280c4c4172401c20b501c0c404000e03c0310b2070400c0e01c902d4000c03079118102803807024207680020b4a0115428080740e4900000200c0b009070600c20380a9030112075002080350b0141d6141e28003c2d4a6200207101100080c0501c0400140e0385411207050b018070850f80c203440940e90 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 648391294 1250 648390044 648390053
    0x3050a06080304080345090a0e210403021309230d0509010c1406070f020123060a030206030a020405180f070f02071203021c020106081504030e0a0e0601121503 70
    0x604a4203125002044a0714034080309440d041ca6424400f41c5c0d00020140403009007c004070303031201401341e08060f45044002c003c07400d400604444034044001402d00fa03074805240489691080d504003d400008a0200000428541e00803400070b0744a40c0100341c0440b80485d0481140c51900750740c2d441a80b0800e4524007242c01100188480001890071600c0081c0a40342c1150b00d090404107038209600c21800c0104540d440450110500003d1009001540003500d0030320803030300b80700402c1d0420102030700441e0712540c8400c0900b0041d6409003040c0c2c0c40c0d02c0c020400700e009400c50301c202401041ca1103070140c00f150031088501d01c04c903404030705402107072280d4000b150a40c20042070f0f00290b01c104000072910070304503110183c030030f0310070750090039201c00c0d4410082040d0310111150301903a0610b4804e00040b0360116010505a180911048059880c0c1c207040311406081d0410075080040a031000c25030402da40c2e00b240c49480c003030302e90780c450317048004010b811101c010b4194600064922070030f10005 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 648392544 1250 648391294 648391327
    0x301150203030c0f07051e0d02010605010f0f080c0c06070c0b06040203040c0314010e061006140403080f0a120c09030b070e0906010309020625020112050f07120f0c03050a060803040803 81
    0x3e8040c0d42114100b1030160321819031090901f004a507998421640224a903509000341e402400d02807800c0301f5080d143c90740181841c04e006503c241403000507400a400041610140c802c440c01101c1122083c0c200180068016900c03818156912105200014060700b8203000710f9004945c4000080c00052454582c182c0c0700011426010b0340e95203803d0400340e420b03400c220050054200b600341500b21032502e1005010304031428200b07600076205000810101d000c99007910712303c54280c440e8640c1ca0020200895042400c4801100701e2440c00411001c3c070756000a290042c0c0b40b1401415040c1c2e11000710503262a484200c06070b600082e600c0005040d0f501c43c0e00b09508451014100c1d600748441c40c0800202d01d02c2c401c109000f414540384003403080d50303403001c110b0b01c951000450811090400703003508549414010b0402040c89404d0120030a051075650200141e40c00454081101d10b494185c01400b411090700d5450515082c0003000c174448001104507821134001c0c5c0001c510b810300c40c2c142036469 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 648393794 1250 648392544 648392557
    0x20703081809010b0c0f0a050c040b121005040314030907050118030b010b090306070c0f02040507050f03040b0f0c0f04091517060403141602220f020301150203030c0f 73
    0xc410201d450203016151002010301070002141025200d903021404c0601c0d002c4500780b8170581d07a002c403a180000c520b022440e00303030001003680d004c20318903602c80c0032a01444036144002c00510415a1402c0e600d41c59500c80d500851080d502d0200b18000e019185e0307498042a41c11702807e8100703000811403176008034000e190300c0c02c1824401c650956031761940e0350400001d0b07102404418000508020030702d005e00c0760603444012814030030001d880341d881c1c41640314040c2800070300855070b41d400300750070b03c0c0918259607501e1a42c090066403441c091411140e825000e5840469045c10782000c1050743c401d1406a4105181042c07440d414546441c1014018010000e000b220030003094101044094240516140310700c070400003820f840c102450001d10a200032181d10018980601c840307072000e813111104c0c0360081d0701140c10722070010100b00280d03070500c408220542054902065481d601c05141c01850480b551849100642c11642c14140d80740d101c1194001240303c010000428610720081c0034000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 648395044 1250 648393794 648393817
    0x30c0b1302130f150b07061107080708160f0501090302390d021807080105010e1e15160b010801060e0c18030106230a060813020f0307030c230102070308 67
    0x4d0001d0041e616102141e0079802c42c0107800c500003803940074001603018140c0055000c9800300d00d8501e941d00d8842c85c5005152008040c1c2070700055128485000403604107100d500042c1400c0c4c410b01900c0d14a0081c0041c07081100503010384200c0740900709030000c14400c180840c104060180340214104540341048204090713100305040403480c0961101c5014400000c8552003140c01c0d81420301001c1c040c0b41d41640018100002d00400f0700752503e492144210340c041400b1a072a810b038207034000402103a002c04008110b0702001c9008000c545903143c0e030106140c020400032680b83d880e408405d013a02e240c0d004901c104409100441c1083c4803480081031030355102c51020041c100404e0000e42951200e1b03000d10f10400c41c0c07881d80300202d0f6002c1d14596480340304032860040c07540780c400041e2000344001d01c1c101c0322410382001141903485580c1034070030645004042e988072036182d14100c145501a400744a080d9210b500c0307288004040b04a5108440c43e05800800d521443e655485030740d903004092501 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 648396294 1250 648395044 648395051
    0x13140f061605011407200307020d120e0d05011a011103070b0405030c0303100e01081902060a17010308030405121303020906012609120711090a110403030c0b1302130f 73
    0xd8944c40390b016030340185843e07960038444003030406540325800e0015000a5151300104040300c0165a41d05c82018081d0380091030f00060428072030203072441100c02c81030719009283d00403440704000041d031044550701aa030342c900d142505804011108006106031400c2640e00810069010a80c40700c0300e10b500601c03c004030b03890309010011007410b6410560b0f81c0081c41c030340000140050a8a0813415001d460030800030880c00c1425140c465051106040c080d000b0072000440f004410b1241c0c9041418000600c141d038002d5039249070180380c540c0708503000e40f0140a180341d254131001001c011520140c0b9484501c3e00721904540070440320440c0588003d0501158807000b09590030000c2180711413030000d550443c464648410954140380d49480c0320700101c1c20070811400051207104400418200698901406940ea011076100401c2c1c0c000429120780340c007007000010103510806c0324041600c15030310140e1a86480d4031400d00c291407160000d50200075441180381c0740aa5a01c100103a103c0c142d03021 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 648397544 1250 648396294 648396311
    0x101e0b271002010e011a1008150d141501050a140409140c100302040b0a0323130303060503060105060a0507020a09050112020a1a0703111213140f06160501 68
    0x144841d8008904480542d444501e61002a8000e100d45000801d0102e074281c1c4031150131000620410811030041c050000007000324683c1d01031010150b0f90020042c10100300340c1081d0614940e40250503840085c1c40c4501070900e028109045501030484002500900785903040c080c444c85840d4950b0b00c0e180d001a51008182d0100e8640480c4511034140c40000d498040880c405002e540a0110145018907004000801455021504031200619149000a60405d04920b0881b000300c0720000c8098800d8100c0600000c04c0d0442c014000041c0300c0c0c0c4042240d2540c0b01c0600d42c0300c00c400d11480790311020a004c0680b03654020030081040c0392000305440000b64440091004445086e042003a0058140c4041c0045080075040725001c0c015682c003489140b150380c0c0c0001da05200e624001400c009035000041440002049920959100e400001da150600072141402c00c298910402440f401c10b0140c0061900b44901030368000c03840581014940518006014010f01040808550565881126 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 648398794 1250 648397544 648397549
    0xc0105030406020d0f091415060111070315050906071103030a02070f0b0709090c02061302120a1713050d05070b160c090923061f0905101e0b27 63
    0x120205d40000700b50005001d100c90a1003000c21000c070951440c254800d640c00100313a0340402006074443d0007460320072070380300e00216101e0820300c0c08d03030004284050744a4883d182a80c0c50300603900c110008400c5400940d682d00041b10664103106909000ba0010404622811100d400030891a40195001200305007a81e50780319401c44211440300000b1241901840359066074043d0110074803c0c1d100400542c2411008185000c4040340001e10403100315410f140032680600981c040640c000444030111646c02c4e81c100503076032281070713030482d05911407601282d1440d002d41807080b410f030081c00910340c00382050000c48807036000410b20b0114854071400e05002400390030600024001030040032074100c01c1460011100f400008a0b815524003201c0042803038000050300c3c59000700601005110251001f81d07640b0781c41c1040e00507514131400c1500300030390b4058845030101290a0089464141380d95500940d1182403a03000d2011001020003d050740c400c20a070048552810354280010b50082c1e4000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 648400044 1250 648398794 648398801
    0x30c0c05030c0106030302010b040614120c1201051005012c060405060406090e060402040b1818070804200f0f040608070e0901050c090607030c030905150711060703020c0105030406020d 81
    0x100089071303460ba41e0603c00c05a080c080e685e0000d0058a003880703968108108640c1061488003100d00848034180c103c120450104182c482d281c002500c21007050300c52112060280c0400c454a403507070007c4100c0000e09510480c410213840300000005c55110b85c00c1580042c40c1c090014480d58408400e110103d40f0740e6550f00140b00402a0340c4030070b541c4900c6c05445801c4240d00403e401c1c812413040c002049201c500ca000c58151424800c44070b503c640038000003440e5044407501010314010910200900c05030800e6002d400b81c0e028411554601001c0701c88440b1080c2221805908021101c5082560342070907021106030300030041000c2051500c0311001c03440c0110940c042e4182c01c05201c00e00264040a10030380360040401440d0520740b10744c840c0810074034401c201d0300804104000280c03005141c41000d01d103000c0e00005200b50070301200203190002c60b81042609480301d031a403206400141c0351540480348999403640140032180011801500c5980005100352500380d020090f40100190910 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 648401294 1250 648400044 648400057
    0xe0d02060408011509090506130c0b070b010608240609030106090e0109021302040308030c0904020913021c0504110d051e07060809030702130f11120406151203030c0c0503 75
    0x8000040f405100100d08004134555484082910301c1c040490000c68030109400c0e40c040c2c060b42184190315210324010303080300c0b0590301605440c500420701d0010000d0306002c2504803136081d56074100f940c07510b040000d03440401c450003c1c11410090078151081c14480064140e00301c005000060442e038824440003a20080038010700c00d659140a80e0013140b4007441c4020407401100421420603046644170310b1544800380405181d14004100001c1d160ba543c0c0454801601c044c00010403c1e072810b803000065003014180d221840294120401d80c1422071040511841e08141d2800c6a40700e034100703000002004200070384850052042c282c004000308849088041c030920001c005051504600821407440a40303000c08a40042000c0400f43c3e0b00c3d949040880311011200081c0001500301140c000c01152540100380c0d68085001c030403080701d0748038a502c154010481405512100380ba201440503060250744c040301c48801003640824440e80c4138210340061400c00441d07007a200c1d122140340d0740048 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 648402544 1250 648401294 648401309
    0xc05090d061e15050907050304050c090a0e0a050a15020720030102130608091507020d03110d092402030705121003350f040303030b13110c06150f010e0d020604 70
    0x1404c12080c14030b86200c80e03100c1c00e28580581581031540d2882e4903050550b80e4907229006080220380c1608483d40014042c5400c0c4003269600401883c01b135480e0780381c0c44c134140e80c401a03d8480c4003040895000b03c6480f00c1c0c0c0403221560704105501d80ca884ca0300243ca8180d01503500740304400c0c01903070341c80856000e8195030300c400300a071030300408191806110f244000c2c51000c400c803e020b03101e81c0020b10079000c100c2e24100458404807030b542540c514011204500442030800080c0f40a0000d101c0407650003d120070300403100c04499404000c1039210585494000840070406480450b0700702038040e030008014030007684103030b80d40c0d103c810701c600d0303019004040319071030b4880c00316a00c0c0c0201c0002501403400140074207150003041c880c01503000758800501499183c800404e441d5480c0790b0410300c0c01080c00703000c00c00c071880c0d0501110303283c0000010982c90701c00c02340404e80360b08941d104066440c2004207042200c03143e000044484600c11326045410404074003510005945050140024002d0f0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 648403794 1250 648402544 648402581
    0x406020d061211031c0c03030f0203070c050c040908031314030d0e1603020f04020a0302190c120201140406020706090b0f0a1805030301140a0b0a0905040c05090d061e 73
    0x16400d000f0520841c241e02c4a110f0350000d041ca600c2c90191001c90071440805080000602251382001d50180007402c0b003075113000d0702c0041088515a08500442e0400313000d4401c031803c085110080c03004844c010440500300e45414000550340d61801150341da1a07601c05d40e0030541d000301321007405246820814810070201d8980d03110250000e81080585402c24171280c82442c2c00d1703e150040349012140f5805c6900440d000280100c0c0035000b50101d40781089403030f0b8902c98202500800800c08a1040d108440500d0714005030310100d441406503290400e41e10b100c0c2c0380c03541ca4a9444000035844810204c41084e11203114401040d02400c01c18410031081542902e03514020000d041103811000210707190b500c03a0840440420f1000045d24192140761a401c070450f4908000605c206006501c215008040050b1890f810340e4051103490882c1c0098606010310b0703514003c180c550780140f403401500b060340e000389440844c040b90007400c0ba00c9071107011441200800c002840075178a10f008500d421030703070 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 648405044 1250 648403794 648403829
    0xb0c2e020d0b130c091511150f1f091a0d14070807030305120907050306010308130f0b07020d24050105130507080f070e060c15100b0901080406020d06 66
    0x2d28100400da08242920100103101070040003901120341401455001b1103e200480e24850090100c628503c08400844010010360500311a500d071084a26461030398101c4040b401e0065081c0304040c20701440100e1502150500ca4200020400800c030741c0100481042d40c9071881d11001c07100c0103014094801c60300300c0d610b00c20490389010301561003800c1c5940300f401c1c1040441ea00005560040b14100341d03680301501c41c01c0c4c103103181910b250060365140c05094000420060071000a0030325030b0b11070300c50311171440d961504286a440144940740344103004100c0c11006161808800700d401b84940e01e0b00b4604080d5054400400300c001c80b001e0301c0b407540c1d10014040c5160086440b04941c2c0c440100f0700a40c82c002c0401071030b11b03601618180e9420620404034aa0714007a8001c0f418031300e800341545031680e64004031240d480700c03101c10600c030380b01d030f40c20101d0311001c0421001030070344425201241c5040c0181d40112780c030000040c4242d855a5080c8010f1030401c665010381c4000b096115404400e884 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 648406294 1250 648405044 648405049
    0x903080a050a35040507080706260105011e031e0204081209150f0c0a0821010303050a0e030313030503091e0d240518070b0c2e020d0b 59
    0x241c030041d0f000f1800207241c01641c8085041c1400c802400d82c510680ca200e0b48892030070381d1400c001e541080115018043c0701003440da81c007420144090010010020100c04840b09000440c4c2003030048900080340e0301000e0b82d0701310620400490341ca00742c0c6000a441c440c440c0046502030b030400032002007150006000c00101c0d00030000f01607043c03034211005140249000001d0504200000440c00c03819000c580c251a210100003640c03a40c1c41c805042e10a83c2c2c500b450254070981c44000015003160f0305c1000c0317851074984402c12074146c13a4181c80d41c501d8240c009005488034130034031812a174544810806440b2840640505000071840b4200030364480d00800d00304003040345030004203294000300c642e40048030340d121101b0f4020300c1e4000c1c40003401c910016038986c186c0c001800c0802c081d0b03800c2a081c00b19203100003a141d62258501800e58100c60340b54182e5840c188145582a03905600030b8003445c0d18010502e164544207400042a04100031320740c201d1380c01f80e0700450890301041d40e03034802d807810381d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 648407544 1250 648406294 648406307
    0x6101701141201020301080a022101050114100e01020c0402160804120b06011103040909022e03050615091225080706050a0206042003150114040b010903030f0903080a050a 75
    0x200d800c0b5009504560420349406c2d5510b0381002c1c0039114914110a61000d00111413503683d000c05031134028441581c4400032103424170101400180110700f607521030004a8842c2c0001c42214105038040c1025030615810080a50800c1140240010440407801d001030740740c50042c00100904e07010b4001080c070a041c407810044000300380700d05211000031040008100030003180c0699498010016100403030340007040900040820443c65910f80c0050714030f4044480240c1044880381317580a00c42655000c062003944100d400702c0c04c80050061180004510b0695182e0301141010030444441c0910b800301c4d001207000c0e03042d0407070a03040c2d020703c1071000c45403e00c8141d0107007083e420410714150071444000e541d0800140040c042c0d0906000d0740e8050303450201c0402c80e401d070080407103240c1c204400480417004021f1007142441c2801c4051407040d0704007800b40c0045248140c50341c4018500d1620195807011200100340108851003201000246034140a0200249690744039500c0312001c090140a0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 648408794 1250 648407544 648407569
    0x31b02060d0c0806030115052211030a0209031011040e0402040209030a0312060609050a09051b0a0e010810080a0201050a02190b041a010b0d230106020102031f0e0610170114 76
    0x2c1c20f01c4035020310492706d0314024000062452200c0c40c40300c0c081410b01c4070080c0315181031042a00d03800814030580b00c0c02da8000e400b07802d800710140e85200224487c4032085500700064411004800d04c801c002a05041c3d610711386c0540040c2c80545040070307100c0001d040001d003504c00c801041031400c5030040440c2501c40c240c00742015040c400201420000040e0b07820003188074641340e82c1d803118002451101e000c0701022030101801d40986d21003100c00c001500d910703511843c03180012043c00c009400f002100c403c0300e080740e480714040c0c103a95179541c00440700c2e80d01031008241548590100a84244914180e07010460301072214480c440c10320740ba200d85100e94a240c842e801c0c3d0b000703600601400f14004100c40428441d500001050941108695401c036100814131245032150000007502d641c041d00250f2242d60440141107200801c1d103d0981a0010350107500d2031b958500b00010001d0926040c2404040f906080107014201c0303681810780340030026000810765200507200c2400d2401c2c8848600203 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 648410044 1250 648408794 648408821
    0x180b03100e06010909050c131b03050106020c1f030902010516050105010905010518071d0d080901020601051509060703031b030c02010c170402060f0c1e1009031b02060d0c08060301 79
    0x80c14107a100c282d80c1d1f40040b042c10b8802c02000194a100c3d40340c0d54420485004c03440f403145074540701040060020102446544094099400c60f41c0c090700c2c0801c901d0f1210786110b0b84608007001844130450007444104000c82c180301c0204041840401d5a04d05458558030400000c1520340c14240303a8825954103a00c281d01a18017140c10002c2109041d40c220340c412840d00c0d05444854500c0e103910801010a080c0641090701d034242a401c0c03212000050030090000c2e02190b80d9640d850b800d00c04400052102d402c008801401300141901d0f10b5030040104600900d8042039107000782c41d210300402100a01400801d903905008401c003a028003e580882c030090810442c1104800c40c800890800144002e100e0760b0300180308040c0c440c22405580303d100702e1104650492803059550a0b038015000b101d40c40c1441102a800031607036250003401c2c0702c1d036455510782c211035070929004046c500c0122003c13a4054030074000e820549080f40f05060718440e417507441c45094240f0a040c542151205500c541 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 648411294 1250 648410044 648410051
    0x30405010b130908120c041211030c0306040314090d021c03031a030c0d0f0501180c050901210302120307120501120503070f03020102130b0c06071107180b03100e060109 74
    0x20101c1c002105440c1042010500c1c82c2060f80c5e410281e1b03c175842241c119007401c0307280351080401c0c4500b0501a8800407015811584030f1140742c0100f60399144101c8000b000900071707900e01d1071081d00c81c0c0c0141020113000740c02c0d110144410782c00918070382c500c0092900108c2000c805041416814021034114618500383c1900604082000c00d0320f400b12215440e000d246003400042c200308003405909803454020000b04202d43c2c4641d4104182100c0c503105451111455002040d103242480f1507504a4540740072440d140d05401c00e000f0744e14081c050081d401c0d8050b44110080a001c0c0e40f005500ca4150703582d070700301804c060b1410081103c106801520b5003030116410040015000011a40c100da0030101103140504940780490180c45603c144121079800d0a100007482c0d0358045c081e09900303620380195000d40d42e0743c900494140340c0700780c000f80090744045001c11030300e486403190125481540720046148692034010a207815800460003032895a2885a080110018480315001d00280601072 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 648412544 1250 648411294 648411311
    0x4060305100e0705060417060a020f0417030c0d030518150402011404080f1b090603060705130803042402070e04110406051e01110a1e030302090303030405010b13 71
    0x40e52407400400380d541607039071a04040954101008900d00034030b13006029a030307243d4903201c101915000b0030b04800598891000490210403042c020f4480c070020014032070f410503240818611102c5903c4481251a0000700912081c800e4140403180452000f61004152801d0005030a50035418045400c2099004841404031051740c011034503800c1502468080c107000990802c10b4604c0c4a42d600110181c414041150b00f40b11000c6441c140000714500010403074421001030040c411000c503096980740d0041000203040600840190140504500b0b809410a072500041c0385582d0041c0c004607400044140404074040580c1c0e0f54654100341071000c3c01e580343c5006a80380d9190000750005101581d00101c020207900c80d035109400801004000e03a961a100c0c800114000030040841800030700c102000650740d003030000314000410b41c014032040a41c403e240703041c25051100c0204808045d0200140a0940e5041025501541c007403000018014041c0301000862030032035060103222410321105 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 648413794 1250 648412544 648412553
    0x30e0901170307060e1603060b01020c04110d0c020309030312010e011505041208160602072003070905090102070f05060a05280e0a0203120d1116030c0f0b070309050606040603 77
    0x107070b0f00c825030701034008640040300d00c0065061801210740c1c5c481e0000302660010502606400610200700c1c280c090315883c0204c207061005954032020820707c0c800d010094101280c0041d4040c4481e03002e14415642401082d04c0000d0035540320f6010401c0180752400103012014882101c2030044c8680380e0704030703111402e0200103000390103a44100f11381c1410f03014050040c800d1103811540b1b0302c0340015000007048214030b0001e0083d002000d0a4402d105030700c4000f40b4084d40d840000d922154018010a22a8540700c007207406004000c1c940482550240070240003e050400f042d89028803900180c480c3d450b0240b1654201ca100070019040801d5480c0613401c45180034a0611140c0304a007001700300320300c40c10303c02c0d464100b01420003905403241c400e40585400d05040500040003840c501031000c91105440b500c2c082c050307090000ca001d81000103520000f0300410440c50310610611400021000315222200c8005003141e00c2d80100e40c030741c40b00b0b40422109110385580040c045030208002070442c0c40b07 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 648415044 1250 648413794 648413797
    0x2310020a021c0f03050a020118020609040c0e0a030506010618150503040f1406190902090a0e1203090a060c021506040c120207061401050303040311060d090b04030e09011703 76
    0x290180350101040126110220b501500a58201c4994040080207250040056000c0306403800154680382c00d0740701c98000c41a005411980040c0311a0900c400c00e01004002d084030309000040c05605500d003d00c80c3c5415078080021800350001c0c0400b5032522801900c007088010052080c0050124140b2030340e03409200340c468204a03032600c5030300c0340c0d1a85007600c001d0b000d070b403800303040f0f8070300b1a0700309088001c00507016119845926142840024442c00d500c240c03140f070b0000030360041d00348000805100486e401269101449400c136210b140c1820f500c46119401075504040d10f40049086d68288061030280d00c03060701081c4000c020031020703500120409070016000b640305644540300c1c050701c1407140d8508200f003041c000e400c5654910a01c2c04200520345c84a00c01d01b4050318200000d0245008025941140d401a140c26004040701c001c0000590218400800b01582c418503440400d00740c2d2015841980b02c3e4640318181310b181c0042003a1840e05a101c120031810010890084407000f00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 648416294 1250 648415044 648415063
    0x30b0603010b04140f0d121103040e01120501140903030a05180309300c0306150303030a0c1806030209040f0e0d0c050a0f051f090206040506090103060e01231002 71
    0x40c603000c161340c000005144206250100c543c48102e2070720748000e004d010b4403003c250294a417a180d520480b2111002e8580c02a44240c0c400a40031000410000c883c6c0031258144a12034030000800301d4514030b440f0302403581074071001c46952000c401c110780205607224140e0090109001045002504034045a07248a11102180074098406814520305031100c0140c0d5020315140d4007a00101040c005169918000a4007034400d1044002042c010858040e03602403007100074018610315a41c0c0b400c400080e00c406580001001301c002c2c0343e4084890400b02d02c0001e00a203a4015035110000010481560300740000d03180598681129000902800a40c003940c0b2121400c2041491441d410141d0600701d200c0b1020b0031000d20001150104180841c80040c1c0001e001c00c0603000c680303500008030440e41b0026000790403060420080c049441c101c07000e05208a414500811b110780c440800008608007a44100305120815841c40250094104140401c2d08203442801000100040082d540d00c4480c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 648417544 1250 648416294 648416309
    0x60e03151306060e0a02070203121204230727050f0109090f0507141309020102101e1a01020d05030f0103110d1a18030a080c0c010204051f030b0603010b04 68
    0x80c02500100203054000c10000c15102007251490700d85104c1703410203940540c20491283c000d178040315900c2d00606003a118107190b0b0007d038031090f6455548100d0007840500c1041100c614103074181041000411102c0d000e440042e60350703560820450080c0c40310841c840d05412400b8100000c003d0038400c420310407811121100d0002c00c500d4641d08001c103000000c2d02014005010f401c1000c030300486030194401e401d00055541c0d0b0301400b41025070004484140f02d0007401600542300b01e81c2080360503080101201c8075080100c180e85400740010085070b60300c588514885800140194003581c0600817400f407c1c4042c10400e146181020201c1080c00050100906c80340d40c0120918940c0c644242ca20b03460340d0f10441c8a042103c101e1400548442c0031184040f0034051000c03140c02d1480040b042e50080502ea0711640c0305900d51240b11002900201c0780300440399824400054690348401100600514440e20703282c1e640380b08140103007a2564032603643c1c040c050400c01080300401a904440444418 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 648418794 1250 648417544 648417571
    0xe070507051c03060306050429071b03090905100603240504020d0207170c0d030e03090f150409020d0605030105480309060702060c0706050c040305030310060e0315 72
    0x2c44181c000340140d40010b440320346080100400c011000b03452100d22080c02841402c0840d6803070b112107034601c08840ca88005011251121092050358528010080c402d0400300e1240d0307161004017044540489118034100d002e44404c11185030903100d0b0b103034813101c0c0c003015110030310104080071203103e80d5121b140d000302d81c001080d01d48089254140c0e011960700c034a204085250754041d828190b001030f00440c5c0c0a0240c1101100c8803400b91040c200f021421001540c24101034070200001d03ca1081841d0f84c000f2058081d5070040100d0000510140c20800c1c001a02ea00001403e5001c840c03198100c64003d81c07411080c00038030307843c061140b4544208020300003244201d07050b20400a5148000411030741c5031910407596008814000b66200c0d0b4014011542c440e41d6560703049075200c0040d5400000b2042c100011404159150045640040d541c00c2c01441c240e5a907a0742c0346158000c940110500314110300034040554001030201036036000300c0041015078004109078450705c13405007600f11041d00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 648420044 1250 648418794 648418843
    0x90303090209091932070801060801050f0f100906090f0506030c01050702060c070b0403110306061831050312100501090605031807080609150c030c0319020705070e07050705 76
    0x403c0111902c45003001503640a112900c41782c40d941c0c2d4040750240206c15402c196000c40c0113281407013014070505042000c1c2e290b64459074984581170401400d90419981907a002040b0040c1034018080205804000001c0101010a000d02210405094548260040410846240c0c1c0c010181c408007501120145d40d00d4144e03c542a03c3c000681c3d1080044050118000060003100309801c0c00340802034098462a69a910400c00e9441c0c1c0790f20705203000c040c2c3c48046048030b030051022a00f82d06800c0c0300b280040710010084128440f1210084585a200090400c108016a108540c01c43c072440d0003541800e003002c0c0040c2170500d0600481c0c1c1007200103c0010040c900e542044003140403d00705541040c1e455401141c0c80b0001243c030f9144500c51096425440e00c441070886215520200109080d9115917624810540c400361002c07100020151040c2c122003028402080104d104100501005c0d24013511441811030080504040c805c003801104080385002c245a1000010460340a02952 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 648421294 1250 648420044 648420083
    0x170a020a140105190c06050108010510301b0f08030f0d0b1002060a0c0203130b0a090e011508010504021c050405031902070f080307150506010c060903030902090919 72
    0x6514180340c007014000c031002d840071740c104090701a0180039140503c803030380c7c07503900203426643c0650f0700040c10404207070100460307420030443d66500382c00002d9000380e900303000201c4a003400f0043c00641e040151040440d103510f1800400000510585241800d014038118019440e4042c00400c0461b0f20400902541008410351084400d1a4020142201c206c4005002035603203004848041e141c0c2d140c01ea80d68a0b050000003501e850f10080201180154240104880680c0020300b5031810b104c4031404c003251242d00507081300d010705038150000340b0300c0081c42001010a1810703030166000d20310401004894103d425214901040e881c1e40125007a1601e00c1c01620f58400e0b0b8542440340c0013940c08d41204a80d003c104001140c80c0181524607086d180c2804907280d00c203c0324010000d016003880105484125001a6801001410302c0c035144926501c41c00c0950744003110031000250f0701d051000440c40c0104e20907070854000c10040020300d0404020b42d0074090411400307059003401d80043d05048 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 648422544 1250 648421294 648421297
    0x305070c080309120d0b0307290c100c0c20010e09060d061a0307080c011e05090301110702041406150c16030c0e0f04030e0d1416170a020a140105 64
    0x4440138403003a0b07034400420703061500500001d5041403107401080c03400941d508004201500c20300184054a403140e13900102d5030401d0f448400940c1c501e00400901c070300c02d45c41900c40c618100c1805d4407511540c1150303180540007041074a5052f54542c1c4c41c110b1481303403641d202c0c0c8071884484041e40c0c2000c413601c0340000508114590400205518140744095124240480904400d0b50b829401c44000d603440700106501c1e040720b07100c100d001941d004604101c401807038084800c80100c504009140c262000c000c00c0c02d40e05800110504034030700003180c404508003841100c50301000042e11030000c0c2800000103015103a101c0c0007034140000450316005501c02802001e00d900c10700c0315240780302c41d940d24001c41c12040e54802c1410711000742000420040b001250507215661540e80c140b051144d0500304001004044002e41d1214400c2c5010780300da0700100815400268010240c111491a1a001540051a007110f40301c044d00034200c16030040c0ca41e581c1602c09e540c000059440007159410040303800e07 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 648423794 1250 648422544 648422563
    0x40e0f010c030b310207020a0b0d050106090e130201110c04090b15060307050406180302040c210204030804051c1e0b06010905010f0c0503130e0105040b010305070c080309 75
    0x1154a00301c04141c80c140c0540c025107410030f080c1c4082c03c0414040324100d848013101c1d07050442011007040c03004500034059005095003807006002026403074680b1840130150f001401841c10407540e54006202082d040f0b603202c8010300c43c0c0a44011a0b00d49940a0342c1c10a60300030b8001d040c40a401c080103c100024481c00303002c400044e02c10010824541440c45550109581004680e9031403000d141050070458112441442c190b20384901d028908030080301d40c0c4900c401500f4400c5070101c0d0110060343d503402031b0f8030300300d010340d4a0120980506a084004030516a01c14103114410401040010080401d80d8100c90b011140e240a62110840c0d002009075148402810100c0400c841c0340969811282d81c8002c0340603440704540d41d503445005445c030003c2ca000b443d0204880c4900981500c1c1f20b102040c1409104800b0b0ba400c0c00030303401913a0044032454200820400c01100148480e00b4a4814590440000d18040c456402e1031107028003403d103204000b5042c00e2000000030091240ac0104401 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 648425044 1250 648423794 648423823
    0x190302031b0102040e0c07021c020402160302340b090301111306080106170a09050a0507080d111605280b090f0a03111e030d050901110f0c040e 63
    0x707460404901082c000d5209001740700079450300c240032a1000da1000300740e4681e65400b81040d40e035807502c0500400362600254003244c0c055000c0102c100041c044250310101c051003500200305001030210b000303505196200c40210200c14001e0342c0d105680c11f024034602141c49500040350303513803102c001003805401d8400301c4168281000980b43d44464464520701c00b103852540d5082010391302e5100850340b480150481c03000c0d1002c604d0210303002001e264491100c0501c5041240d044a116076282c500b480c000b540082e5031904a032a171044026000300001035460020320140c400c405103a00d065008a40354040c0d58020075082c0d04900d1110500364050b042200400d0070303007901c0c030b03a245a9080b01754040c0d440c0b41d000f05041e07144160325051111102d02038903405154071749181c0b074032000c1c451071010214461500007540034585945440512451003261065610355079502003000000d040040c507040781e50f90301c0e800f2132507014440002003003841035104206ca0100c3c90741c08001034185444500c403600782 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 648426294 1250 648425044 648425077
    0xc05030d020a090e1f0e0402060405120a240e06160807020723040c032a1b08070303140702071203050f031911071106220902070b011202010219030203 66
    0x900c0b5000038440701c8004134816405d00003030302c803420030a02c1c040585000790000d50a1009000a141c0314004e604c50700480d07401c030303000031030395071120700410072010720b0000c0c50810368098000030542d5005840340c01e0900c03801001e060420084100307126404400107000c0001c64000300e40040c0c030a1140b1001084603141440f21844502002d945021003d00369501c100e240ca44071020300ca00900410004100e030141594001d0400020855083c3c2490740007001c0050303185419150285400c400e584d43ca002c2ca0090707480f415030f441e0240440d08896544028888040100f0425560004200b400d545581c0b40078121102c0c01c0c030382a903040c040c40150204507000881000480d40701880c004544081414013800f0080c00c0f80645a02c903c110311000d056203034a0711012034241043d000410f000c2d0000a41440488801804042c915030b4036000f0200c010b070001140c3d41030201d0741d40c5450161200e08004d0340e250210b640080c0d03a032a00904154840f8601949550034540240b003035400c0c0320003049014 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 648427544 1250 648426294 648426301
    0xc150d0b010e10080901141e07020f0304030c090f0524130e010516090b0f07140a050604110303090604030f0204090c080c0415050906011b120305010806070c05030d020a090e 76
    0xc0c1c101346048400c1502e81d8030740391001495021010389035020b80c00b840340000061044210303032140d00710020140750941c40798080241c0e4a00d800c000400080d030040303d2075820340341045011400e82c1d40e11088903507828180400e010b00c1c1c20215592001e214007486581048401284c0442c2c01101140b0301903080c603140a178062181101904030b541b2824001040103c00d20f03030308000360307084035a500a41c0c150803011b00c890b50b030104003880281039250190040b10f00010344050090301e0140b41c0281100d25420490a0004000c8404918101c030b803c128051400c0584000100e0390f0b9018500c00540011880b00800082d9250380d48a806510b030041c4030050b01d141ca4500117996000752101d600d0040386080702000b0f1801501c107a00c0b0940e4401026272a494032035a00441e841011406544000c0c2030211450000034012280f01d042c0310322645011400750314008942d0f0030701100510607010b1010100340d4100040c0c0120403285034014500005880e5450014112010041500030200c85050f02051 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 648428794 1250 648427544 648427547
    0x601120215220b07060e0d0509010f090905090f0d0c050a031d100302090f010509090402090702030c0d120b010f0c030810050d110f12030403060903050c061005030c150d0b010e10 78
    0x144104c50007448140140c0b0710303000c07070b9581d40e0241640b030b6400210140064112036204104041501d841450401001500c0f041e821044807400d4500c40180e038020415499040380a02008180c0b56007403e1a12100f000c9840350394494501e10340007400c010344003210321202c50581701c0010302c182c405030401c03003205070000001c0c0003580980d007030034810840896000010740c0300c0c1c41203c0c02a440a81083d405440c1c0d0b600340525a1806441d800c20f50009110043c0e10078000c1200422138800380c0e80d4080113a074030625240460721558500e0741008068942c550300c254000001580c15980341ca0580e0b082d940d2001e03903d4203802c458109643c01499044d500d410300c180320a8502029808544441c045044103003002001810104003010075003080c08100040f030301961103604040d0281c105a0714002e8512007050070440e046603100441020034905001600b403c00003008404420b42d00c030184010800c0e69000035015070b10001c40400e494840c8214264483e505400c010349014261a40c603c104450 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 648430044 1250 648428794 648428797
    0x60513051501140a030c15170a09021f050324040218091006020a080a02012007031202160219080106030b0103050d02061504021303080f0a020601120215220b 69
    0xb8286520900d50f11944261908140c4402260f85c06448003100c21319041c103001d425904203000c0c0d410b000188108086411203090300da445011a4140002e80b82c20601c10000e004000d40c2800182c807480c18112100342d6040002c40303800a030045500070324403009501d4640505031140903190044c1c000301d412881100307203907008080c5000454280045a4440d94500c9200d0007600c200c0b00140e01102d0f00c48017151130080145810030107803001042c04608541c07882c0e02c0700c0f0810382010b0002c0300001c144051560000041d410341d25120025031070000c00c01d0600c0d203103075000740020340303e0488009061a14101241032200418000000340310a07556810440312902007440140c0d00380c02543d080f0042d171032021510602c94040b01d203a540c981f000721303030901c0001e4100740d0200520f509030350030110226205801805240c003850200300e50303421941c0d41c001d08214040c0d104a0780c4445940808006035550022080101c03000100300380c0f035960281100031100c190002c0792008806010020450111300780 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 648431294 1250 648430044 648430049
    0x30f031c06080a030f050f0f0a0c0209060f010206070f030e06070203040617071209020f03150702160f0603150909151b08060f030307061b0306080d0804060513051501 73
    0x800c100046550340541c0b5488a00007580140003422440e000304032680540003a0581c1e12480c2451030504000c2a410038003a44000e0078000810b150424580451800740600e5622100c166442ea000303612880004c0d42d00c2801500c1441030001c0308006001842c403035801501e6858101c1c044030440d00303200202035201d40c0180074090006103850302102d128810a1103082c001c0d10350350b941e900005c020140c03800050007035400803a4020810501d100305550200b1021003000c074114074070f0b10304c1e0900d0384000c0c0c074000740c41d0030403c5524030850082051801c0086102d048407054200450b0b115446059146ca4000ca5081084660314109000060040c2d00c040c1d080c002400e0081007000b1102d50300c4561040c048030540b100003902c200001600c0d81003003042c402080380c02400701c03803d001d259038401059400c00d180c80100b1500c91603081d01241d80c1400b9410003007061001070049007080010080c601c40c0010800381c0100d4450300421110401d00000c00f01664200003030321284210701d8a00c50500e042031 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 648432544 1250 648431294 648431347
    0x31b111501030b0f060105070302060601030b060c011e0e010606020c0409050f060709181424211b0607120c0b0703020c070e01060c06050c071b03151503020f030f03 72
    0x400040c5d01940114105c82120350544c00408185c0e40d140300441c0a0840003003001c0d0483d1303003840f8030403030180b09000fa61400000300c0030380590018a1003003542103e078400c140c0643c41e810074104100c6ca54010441d0030029206030307404503640615061880c9014409101e141c194407c100030001c0b8a640004180c0507070b40340c4411140d1590b0105140001d4816041203d4100340d54900031501800940a101120749140044900c804a00c1400589240700d0080d11024110005200c0c480501040c0442084001c20500710300b5200d006e0030215100c0d003d8040020120030700b240301c054640b4001e4098501581c0d22020142040c034220a000300a500180e5840480344203003000410034580300303d000c50590300d082d560618810b0160703c03a9406004003500361940030000f005072a0100c1e820303140b140203120103d046042c3c12451032528062902c41c00b00c12040c0076190100d50401580000c0c3c014080341d030103e81c0d0403c9201444000703420f104c50111480c51620000540f4030014210300440d07098007001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 648433794 1250 648432544 648432571
    0x10905070309170319020f090f0a03050c120705040204181b080c070309091104180603021c0302010f0914010b06281b0602030412031b111501030b 64
    0xa00360254150356400000a10411070200d000c64070b0741d420009954003080038005551004018220001243d0118a1485880800081704800c5041c01988005000e20940c1c2c00c0301e460b803a5469558660351f00d5407055101da2a42c10141d214040d0811416001e45002001107545640c0c0b820300d05000740b03100c0882d05a04c0c3c00e09410b0350003221584030034034001c00030743c0b24100e41d5541d20554202c00c0e0b2201c4402c90510400000c04500840c0c14800c00e41307074100760745000d0fa603182400c0c0e406901080900f42d9440e1503003041401e0005803918200d9407084079004004840d049440e2038140d02515801c1c01c003494480c0b81140078418844003013080c024a0b07410400801081070814140f0285200f081c1d151449060038030b010042440304400b55999980b2640b902400c15958480359242500905030160ba00d84c3e008814001445000d00420300c0004450504200d0011038860961140791445019424001c0f011201d2040e0300040c40740d100c0300c10112141c59455070316490f000168040c182c2e00415080035 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 648435044 1250 648433794 648433801
    0xa0e07020c041d06040204050c04120b09070e15060a05040819060b06040501020616030e030708120c16030c02190e100602010207050304090c0e270c09010c08030618010608010905 78
    0x7555036602e41d003e40d00e80040c11455899400f440080d01010300032806542d410040041c000c00d610350f20fa00b582e44200030350100340c102840d0440c0780840503000041d010b0515018002c1c80c0b82032000c402e001980c01e862041c2c840102000996250081c0c2d404007540d4000e084240724070b86070750f40301304100b503100302420042c5003051b40500000f4041c0340641805a4800008510003d9180d07818083c51a814a808030759012001180d42c25030304040021112043d01140c807441d0140728101041d03004240d02082c50074510030240c64642c0c1c19403048054144281006144155210781d4544010300d44010050b0a00c0340d561003040110341000c4450310b003c600d401c1c070301182d00351040c003c4444690f0080300850501d42407214880040045007003000c24043e01000626051b11030444071300d41c1c01506074650004200c031490310380b03510f030300140b0204080200304005007250b078100144a044e140c020909903140d0380c03480c020503041614988000140d0100600000d000b40e40145004e06a414250082c4202d45 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 648436294 1250 648435044 648435071
    0xc0d050112050706020f030a1b0f0803041e0b0a09051203550b0310020a02010c080403050a0e210604020a090e03090f03010b04062405030c0f03060a0e07020c04 70
    0x80880104147c10030040100043e01c00d56251144d6a4091110308013041c45aa8103044c500351100c0456440001100300000c1c13000d490100c4a0300c6006011020360500aa82e40c203814180041420085503030380d290040c00c0c00020004400d00400c070603400d03550f90610554060171002d02c0306404080b0072f00c4641042600300009640070303107074580e80000b6a810034013079103281c03600d0480c1000d0b585c1140c0d81c0410380041e541c00c102031100081ca035a00143d07100d041d03407002400c0da0000600c1d18284182c140a0000183c1d102007111071240c124605220703039003004030018000c1401000c0202a08540755080600084041100c5020328421a5100c8015945540c0041520301a00c1d4062a98009100c06010303400c0c54491901d060b1401000041c91241d0440080e084806a40200002d0040490040440651034018808007401e50070201d0561038050340181907485681440100d01c40d001c8082800c42d200c60030b45a01a0503c00000405483c245800039500c80881800301d02c642d0a0104107403010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 648437544 1250 648436294 648436303
    0x7050a02100e2b030522090204140f0108070503130507030501021315021903050409050901060302131406150c06040809040501090605060702012a0609051605180c0d05011205070602 79
    0x43c03800389201c8060090549060303407280c2210302000442c6041c4124200c07196055019180509000d000040e05c5074101000303040b810040860542c09014800030f12074107aa000095558420414a081d41d13681c1e88041c0c0300074070030303960490007440c80c03291503400300c20013006401410105050036004689540c0c0d8404501c032065020760303800b015801c1950040c0d040041c56142060503070080c00e01d27901c1c2582d01c180800032a48111208815a55122024411850b120800070040100d0340001d000843d403100d83c41c0c0665502400c0144504c4d0341e030554884100401c016103600d103040c2d0081e11042e2909051031281c03070b03000701003c0717200d146000001708201c440e40c0302e410151040501304c20f042050f00c1d401901e80c1c48a61001c00c1240fa00303056400c0c403010070344e00d03424410384c03107a000890482003d1400c00c0c90190031824108060408030401e1209440d28008003580700d10954440c2d09644446629034a5807007601c2078040d41e681004004910403040307043c01612180318404503850590780c1c0000300e032075 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 648438794 1250 648437544 648437599
    0xf0d0207050d02071d10050d0311070501050a09090510030605130317040c03080a090b0a09030302120315150c0a060605030f070f062106030b041b0f03030507050a02100e 74
    0x10000701803403141400b45000171a0320508400001101589420024041c440186822800115888915000030300140201002014213080481c18101c154002800c2540c036402030b032403007c0da5980003450710703074541d034040b002950440030070001824400c09130103d00c01d200310141e010a00d200c0020240c1d984140895100b280c00c0450207107072604640e120f180c29888220140104400c0b190041092510040180301614030b0782c5a001c40d884c61450080c0c100181c10501c100140018400c1180f43c20381c1200c0c0880c171480c00c0321910a14856112969502d014882259486108440e605420400198020303025294118100c0b203030080755414007a99461603000700d541c0340003900010030016000c1c4e0261031100c50360708000c43c628268042c14004079519603000751682004602440103000103d07100341c04d0a6a24400b100c002418481000104c00c0e00340b00c0101004030001d51402849424801c0b2058180c1c0145201185448484010909005020198401c1180781e9101008110642c4040c40 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 648440044 1250 648438794 648438809
    0x402180705072909280c0b070510110a031a01020c12120705060a0605030304030302030304021504090509010e161212091809050d050c0604020909030f0d0207050d0207 73
    0x3418000d55590a44240650001c3d000d030490140801e03038039086089054400c40e04039000b400184014441d4500c1080420502a07904221140031000328041200c507100781d429201d22103594250b81d01c0c241d0321300b20b40703510591142417510b01c1d02a80d45080b5001460000c05981c2c091103050744d03201803695450842050680964803031040111903060130081050310284c0c42043c1d982411a03c1140746155000010460300c54001004102074006140f08107005006c0540085040606683d03010b5920b110181010b88605e0084210301e41c4c02e004e11085030040c090a602c10321141c180300034040d007c0c050348001c2118501070703000402e00040c040004402151135806279403409045948405901041c1c0031094810003c09640c0812040302c18145850824030008002440707040c82d04000c0e04100b604413050040010811560703140c8600054140d410680407501e4200720345442c02d900b46144501d07500c00300d4000b0041a1040222590340c003a082c0c04d030044054a2290180007000c1ba181c1c8994050400c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 648441294 1250 648440044 648440047
    0x5031204031a0c180a120317090a050d0e060d09050a02131b110a060c0c03090801050717070e0306010803120609010303051b0a02041b030f06082806050109050402180705 74
    0x3005900720b030341c5480c1c0b40900a00000d0150b62540ba01da51b0886000c007050300481d0b803182d40c981541c1c4d00390010f5580546090043e0103032030000c0c0e0b60151612032811031041080100300c00240e065880004a800e0540c1c0307240204104c0700e81d450500d40354045800260310a500707144924010080c14003c0c0700204210880004645103080e5007941c640d1140480e4592900c00c40c1603000014909100d40301d1441c2e42e030b40322064030252900e4024042029a001a0116414075040c0500c0d290040030410482a000706809040c1c0c0c2c40b104110354504003620810b51501c2030400004406102000a180c081011240703a841c03640c0d14014070107044020f220040009508010321401d000d03030074100c9090300c00f0139804e60300162150340008007a03c04203a1440584004c00100080040c0c1511503900c580c0f950030340600540e45062680c1c1e44900f0740100b4002d42076181c09a80703c40c0411042124401a48030204101c0c07035071121400801020100c8040f4020500030840d00c4100e4801c00e102d40c458003481c3c2c1c400703 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 648442544 1250 648441294 648441307
    0x10f06030e0c120a05060c090904121b0c060224150a12061b1803080c011103010b0d0606091203031a0603041208241905031204031a0c 59
    0x8500030328030920354194030b0091084140d0a90741e40e0200c0070903503115400406840f461400c1041c2072400190400d148484204160080d03034440600066016802919050b445804044141e03640840c44075038060209843c0010f10130402d03200c100c0c2058421030341c01c80c1c0c0001c00079099620401d160103002000003661a000620005003000300b82000e00001d070005a00c0351b9070302170041800703c0382581181e241d622210f01d55004403451001d82171002240c070b01100f641803580001c40103044075000140143d000050350522461094101401100090580603520740c1e4072046c9040070340124280d146400d0400000040c003030300c0b0b24580015180780001380451130780c03107a800b0f8008004106948456181d82c104107201070383c410000d144202d00590b6403503050a04540010b041d402d005008900c039020071080b40d0003844454000300201c820950308030503241c60916001c0e00c1d0310100d42c4042d81c184108800c0d00c11454a00c4054000c40c0e00c40c40703074a210002c0040c240c860403101140c0b0076a4500303007807084 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 648443794 1250 648442544 648442547
    0x120711071a030714040e0a051522020906040e01080705010504061704030909090f0224071112012d20070c050901170705060301030b040209070e0907030905010b010206010f06 76
    0x10b64100d80a42080355055581d0b8071282c00c039411a038441d01c1c1c0b0030140c400f04281c001081c02802d86c4510800d08048400c40503c000407208811010101c011800c0703039001840040c03c2d40d04454604c2c10041841d91030f00d50314080500c10840034040d00145001e05440000c50754000c00a607000d440b0182c803445410b1702c04054210304071000030000d408206540b400094800107074401c41046502800440359000468014070070f5510050040c0c40b04066100140000380b1138600548820036803014070007280a19110006446a401b4082300c4610751901c03c2404508001959140040c1d0140b50003011130403a02d061101140c15024107440307051040f260901341c281e4950010300555105882e01c8021684850104115600c00d800249510440e001d4032041d0307007000c014200040a08603403903417039581540d460340075411020340020b01800c0002c01080142e8040c15280d46030010140203c041445c01290050181c0401d000a0b0340c15441c1c07080d0309483e94070104001e07040e901100400440180381000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 648445044 1250 648443794 648443797
    0x7031508101a1f050f27030703151d010507030e0d08010501170405031e03010609080c0315190908070209070e100807050c2a0105071e1403120711071a 66
    0x1284007004030800210b0207080b12280a40b07501c140c04842d00b1b12144682c03802003540481d0290381442517100e0801040001c41e605010341c0e00404011010400c211410308000040d40c44e541d500c5059400c046c20000c02036415404040b65042e22011114080241c0c2d6080c4d0700300800b03001b4940003d180311404a03450148048040c0c00c148036108480c0340002e10460b441055007050150a6100c200000402089602145c20009050900b000d80552103c0030002030340d40401c0c030b104492100c041340c00900381940950a00c0d0102c0c03001001408250002e107821032156001000c2288a8100100031a20b21841480d0207854200c014064405d010030060083e038000c07900030190303000c00c00100040411440140280442c413a441d034500c902d0742d811410891030050301504540e041003820701c440302c0800c60701074407071040c4805844103001d90555810100707030803a2046e04403d1503100c0002c5520001080042481c03050455540c3c0380c0080202c19660354690216200b00942d2070034250800302400381100 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 648446294 1250 648445044 648445099
    0x305070302010f1e020a03020606030f06010e090715050d14131b050d1514193c050105090601140d06050d0507090b030c130507031508101a 61
    0x501c4041c03a00382c042041d00308220400864010381145100001f0103404008094101404801600da4114940f154076a64101441503d080c51106004200c10040a00018018140040e45071285010000000d80701d0781c000d1f9414060146850034400c28442002c0e01680101a8034100c107026a00079118210130710810002c1010000404100040c203560344884080244d10846030f80d400b00148442040886201c0c40110f4190104542000003544520f045200e0708a59464005134841c0010742c40d5401842100c601e091118110782064000c0c03544140103a03d41107800424841c03aa21a002d110040d03009690281c04500000100944a5180350141c0a4460450070029005582d2000078407203009808003510341d07400214003400480c00c58080c070001090160000c184a01c55800881d117220650740803443e14030390b64008a003e0500c03c1d0040d424002e0740b0060a04043e0301d4406080d10340c070f1110054017066140c440341508030030b030f00b0381003040059000b451041d104c1007885070940504042c0c07 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 648447544 1250 648446294 648446297
    0x105030714041706100303171008030406030b100f02030f0d090803040b16021f110919150c080d110d050a0209010f05120114030109230c0a0305070302010f 68
    0x2810441c114090900034000902e4202540419200414075407410010003802a1110110707048042c0042034110f006002260384600d01628a039031507210310480000d04e5040407010b80070000d00092481d03450b400581700640f0496601b01e2000b10f929043d99501c40d00e18000300580c00038860780c914604c0800161a640741c038440c0108200e41c0507070381c00f12161300c100d03000c850074a240400d11111003403001c000c20100002d400201035101c05180d40d105500c2c3c0219544103119250340c0c101080020303841c15035190990241c8409000d08215014103918516405174a80669505101c951180d00c5402c0304890745e80c110540c103240c5807018441d00054031000f40c01110508041041e800488414401d0710303c600c90890f401a221f0014400040080c5101c078a28030400c2828047e1303500844010750000d04581c02c440804d846e01818001103400340121050160089120b802500700003d0108204000004e00744223980700b40c4400c400300089030200f0b020240207a803040f10180300650007042901240b0145 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 648448794 1250 648447544 648447557
    0x1090b0126070905150a12060b090c04050630041704060c020d02060405090c0702040b010507150f0b060d060315150329011202010f1d010315080106240c030e01050307 73
    0x1701c0301113507400180b940108414480d0581c02814403407980f18042c14a1401c50340360b095420084036500640c041c0d40140e51080e100001c0112808003500210300603030544ca154108a0319100c40320300e200c01422207040d00c400508000343d05404165104550645201e6121048400c04940900000d040000da04036008502000301241c40d075504141d0b10700c21504443e8481c0d4a122510601060321510b86159062240a010501c002040181d03107aa103540c540c0b0002801001c0100e041c800350400822560b041000000d40fa0741c58000d236004502900e0252030400c07031302c0c580c6140c00012103e070340400783c49041d02840c0600020708465400c10900a4100c1844240804000e41440d502000c1e4001c0081c0d4030444a40011940c2008000c110b103c110f00301803072003414060701400e04500e01140076040580d0307000c22215a8031400c10f40c40180c000d05c40200000c0351500c805403126040c1e51254005400e01c602d489400320311601442440c0c03645035440301400c08003840196000e4102074550310a0011 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 648450044 1250 648448794 648448831
    0x110a0f1202150c03040f050102061302120c1f0e03190f050c030d0c02010e0a06080c090307150c0c0e160e01030f11090109140d0f0203030c01090b0126070905 69
    0x110000503200f200c640750702031682d69142c00c0340c910490181d42d2080d411341d00000d0803c058a1611300100c080150151180e15109082d1480d05041c42c1c0005030b80c692180019401000d5500342e6041c506030058140c80300751a404510041666030f2680760b080c9402240130704ca01c400028441540c507809030b44610211201c0261550000341403003054042c001c0050030824260065681c80f21b800c6402c100b00b513450222540c00c05400800c600d60003130041c6601d280004401105032400c00403107009107400c5403a15810702103040003c0c0030010350720050f19441c10300440482c46100c1201030328054060314011264a120030081910949642003246041c507039a4003130030b500b008007402034106180b5150001a9a01c0808002409504440d00030454a9159040e001b803961641c6052044058004501401d801c001d480042c0c41c40c8a260181d03403e075400c040b41a001c100349031030ba007416618070b0420900c50038518800050000c001080608a0340c1c0040c0040081c61364540c0065003016003241c1c3d0711100348 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 648451294 1250 648450044 648450079
    0xf072703080a0c06180209070516031404030209041416080a03081e1801050c040f0905040c031e030909140f040311011a1003110307030b0d0b13110a0f1202 68
    0x70f441c20100042030101141d2081140b03400260548d101609080590030b1164107800042161200c002c01400d0003000340191803001c1c0d40d281038070025030340104a030380c5030b1130320380b801c4509107074515407245851044500072140ca4601040420070f84407088004d04103e003064a00b21800c20f0051b01009082c0103403800e03543c4011201748038502c80c0c04c40205000d00881001065400c40710000c00c0c1c0c0d040706c03902f408184400c0c0300b401e40c0c09084034060003011445440303c0c18444020304880d40028454a0310a4034150b802000d01c87d42c48031140262550140c180e91035120b4003e40f070782e610745411008002c0002800741d00080c00004c4e081030080c41e00001d1a042148028211400480d03884999264000d82610518058041c10740e0007039186814402c4042c03c5030011403d01000c0c01e2401815121803820501751621101e8031061038120b0320744215170902003040c1007103001141080e40d0640b09039040007040d003000080d110803650800744000f0300e140f0307060302071541400541c0c0880e03101d403020f408081d921 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 648452544 1250 648451294 648451301
    0x30408040e04060203151e040911210f01090f0f031e0203090a0f03030c0b090a120302030403030b04090506011403030f0a090602060a06140907050d050f072703080a0c06 74
    0x120303c034410041e624201904015084803901d6030702d074400c1610391000500c81034070703500552054606950101d142c0c00381e07240046608030b1600003a07421640b03035501500d941031038031034143d1101d0403241500c020040400b035050070b0396182e04c1b01402d207002195400002604074105421031900234505441000b40c080041300c16040c01010800050348081003a203900e14000381c00d80700030009002103084c224030396a40a040e50304c03402030241c48541d1203000501408001d2082d00c0b60103902001c43c001c002d12030000a4000e400a650913130000e46025403900640c102446542e1509030400001c0100381c3ca4080000244500d00d502d49406000c148403403500d5200b08000742c0118641c0341c8408070310a0400e4030003881d00100800610019042003003c001301c00520142c12440d1100351010342c0d003a0b40c2c20005a826118504805460b07900d40800c00c07a02052103c0054050001507695211641d1205514244060016072030014828440401c000003215040103001419050070000c00aa1442e03c03908210b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 648453794 1250 648452544 648452551
    0x40e0411061c020405100509150a11070e040308090610031b0e0408030a050c1810050c1b040c02010e031801090e0a0b01080c0c19030201150b07060c09150302030408040e 74
    0x640e0042014170081c40c095072022024400c929100382005100700004203407081c18500c817002e281b00021400503c0d88034400c040c041c00602421100007941c1c03401c03c041c030f20f5011242907002a00f144081085030201007042d5014246480007540d03d182161100710440203100981da1030450280340004540e50701881d114072650180b1481c1d0386915203010f0309802d40e00c0051802c0c94014041000020340c018084a15412900996070184108401c20043e1014410010303603001500c15040c03020300b01c103404d10340f401e101070085d20144001010b464060307081ea0142581c8924640090007088e80a9160b664900661a1305141040e40c982e510341c824181c076070381540d20300506911840203610b1540c100e0ba034181c02840c00003030b180ca403040c1042c0c85921881d003503075400c0001c02411030b640d00f07044c0b00350447d6107945450704011042951b00e400b80d000075400228105c03112410302d142125414062a02841202d0841e108140c00d04a10f101c120020362000b031007120540c0341071001082890b040044c2620 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 648455044 1250 648453794 648453847
    0x3050a171314030d08040206030408091302030c18060309030703030b040b12160b0f030601080a090501021602090109050903160309081519060501140a0504120c050a0902040e041106 79
    0x1040030b049000d240c141100d003200790303080c00302400038000141c50b02d01c2100d921680003d4629185c80004000072082800007000103c41c600100a000303010519000800004901c541c00b01250a152000d0061a0000b2220520305170030a11034040420f000b904080702d4100b00400015124000ea0002500e0940c20344100500d50f0110003106600350b0000341d110042c00c907800411b4200590110040420f110003410707181005440c0012645103021500304458959215000759100e0b81c0080d0740d180c040d6a60102a8806d485a10002820003484d11034180620300c3c0030302035882c0c0170704092042c11005042004508000b501240001d0661040c4909900f40700300c0000d151080c140f48001060014110038040c3c0b40c6c501c0c21004102903a003154204000c03a079a140d205844d2460301e80e0503102030003650f02807411925440032103001c100c450b4224905a410031a4245030315925000c848040780150b0103230844040b10b680c0443c0c0402d03842d4904202800c0010720252810a100d010240505400b091849 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 648456294 1250 648455044 648455069
    0x40f060e0a140a06050f1002010f1103071d0a15050f0c071403010b0904060f0b0a0f0510020f21041e05030c040905070308090303090d0503031006030603050a1713 71
    0x402d031804101c01e034103d00320a206015060070b160014038240c0b030040440340b18014800c807400e07544d4001e40001184400c08001040740e58045504040e07140d004544400c00508a100c00005020404110b0b0301011030150042d031500713080c008400111046150701d5810300006000c10300e40c0110910060492203100c202800d01c242c07618420340d104070603c03480d0503c030364141100481c154032024509584141c100e20040350002d0051100350041215101d1150405c0b0030000108031541d42c0c03600402152010750365602e044412000484c0c4400403901e030303001250030503041c0d441c0310f01c41041c028103203284004001307203080e5660003c242c000060700c01140d000e60400600700940d1409101814105c1810b807003d01080310300ea500da5444141c03d0200500c1c010300494160350a85082003038803460440a421404240900d0901a60304c1d0421940d03404020040750000c135400c0d20a0140380f044035841001050285800d541c0c44990710a040302e0704a4021060081c1c082c01c13410440307a00001c6c43c6084004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 648457544 1250 648456294 648456311
    0x703020a050a08100f1d0102090f120a030c060f020d0c0f03022b060305011811040207020609011b1e0308010e0609040816050d031d0c010509040f060e0a 67
    0xa103810301075000302c0c4603007610740e42000220300c0401c040031101e001000000d100214803c0c00360040c05103001e8944180741c4a88000c1c16071005600070407512108892030300400702007808005400300d85008202050300512202d1000900405100e03551520403d808601a481760548d04101e0f040624002c1030790340c80c0c0004e42c070400d41080b14440e580d1883d10307040d4640007a1000003081010720b260020301c80c808500c2e81e4002021607034444030207958003030f0081c40a0304008059803952036110a0a48019900d01c0841e846841c09100b22080340c4d5000c0d102900301a420030055801c1400d0342c680d41e019501450001000514040071000c001c03036072034903650a010709414001d04000301600065070502c25582880b1241d602d0400d21607100303a02802641d0b640310b104051140d40d580400c8000d00c07500c80c990300083d1803601900006905518074800e03950040905260698403c00300c40600c0c0403e10802203c0d2007801d080e080602c1070044210003150b242e0740ca041a9241000455051146a03510442e1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 648458794 1250 648457544 648457549
    0x50d080d020f133221070b0306010f021507050d0905010507120b24070213050115030c030209010815120a1b060206090c04020d0f05071806141227070302 67
    0x41c410444a03c50a03504d02c18003061540c10011031410000d100e4000307004101c1280c1c0e482e034465001c4852180660700d0380b80d034403401c0c1c134901d400c140c8034070f408101003403081700c0c50b503100255444000c80c42d2031480303d203038480d10302c240c400d03034448210107000c5070701c13017091402280c4240501c41c01000d90350340703e0f000702d540752500d00102c400a0280d030b8429000041c02c103100012001c07a07000d2440e40944d540340d55204610014007040c01e04015030114a0800b400000c2c40e907601d480c3c00a074609191410b11a002034a4421812449800701031400301d4904004103480104070342e6941078001000e02100341e83c8410700892840c003909036004a070080d01580800c803c0450014500004081c64002003c00d401c01e05005600c4a040f80352080c040d0f075001c140080303284015001841e0201c500882005a801c0120b4020700c6840b112482d17420380040d621001914610816142c4c01d1207401c08240c6040049510845040d0800549400c400c151a124500009400c240f0780242001c900c1c0020702000346148103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 648460044 1250 648458794 648458819
    0x2101060c050304050907020c03150405071a12180f2505030d050a020a1208041703010b071103011b0804140105160302090d240f020301050d080d020f13 66
    0x8400100300c980003540000507400400e640c29600111150000c0d070b960f40008900d012010409a0744c1485034800c2000b0074040002240e004038064410384443c1d940311502124008540c00d01120003140030040d41c0b002d100076207001e40c3c002c080e4003005580901c2440d0003500d44550940c3c283d100b40c04c44d907600001c2c5807604514440b45240c40951400c4e81d454800020303103841c1e0700145002848000601d00b00304034401d00c06108540e50090300b400c80301000b1040108802c0c021142118191000c420342204041c0000c00e9038101ca0407a01c1841c64040300b507881c1c1025100b9040385582640d00c0389a5900000102d2548801c105866503500100d071600f8101805264890905e1244a91400081c0240031120614417000103829007005a5030310004004204141200040500018010742d0f0589440d10f1140e40802800e2041c0700511018003542c4098080748401e104c2c4650000602142200103034401e000b412403001c20800050502e41000c08980c419400440b042c1040c070a0214244140d4030802c4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 648461294 1250 648460044 648460049
    0x3305090f040c09050108040c030c0605070209153601080604120306050102060105012f0f0d02060f1f080109050a031202030402090402090c0c0a061508121207030905032101 75
    0xc6003800707a80710340b0401a000126034092581080101e00c00182440703a0204460001d6510001c0105a035035a80c030000d140b038020b4001203105401210209501d00003841d501a40a44000d00840c1d0504042c42c010b80014003848600c00042a01d00403c000680f08100160007054000c2c041c240901c1c0c545060390607200303040c001e64141480e28001f4411a41c0c0028842c1c10740c0c0081c24a2848102505a4407034407582c0c0f011007402409062010468465012130819512004081283e506c60109001a40c641c6800c5460203288242c0f4800501002c8550b500111443d0100340104011500c0701e103e942925076030700e000d64160b071260010300101940800241d841e10318020085045091980c000307583c184018102900c5142ca64002c1061084480111204c2184560071a440031815203801c00c0640011021000130400140c0001900c1a0104800c409400b41d00502484d0240c00f511079000d030000945400109a518680d81c80020300c02c000800c206031000704405104988500301404020b0140c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 648462544 1250 648461294 648461299
    0x610050111060709060e040603020910051c08091c050607020303090d0306080613050f030a03060f0605031e04060b06030c19051e16060518190c3305090f 67
    0x2d410400c0080d4080060030550701245800b0000c020078500090140c2401e030006580441c0030014002d03501415181d0341c08450043e5001c0e00b8002c5141120403540c0a6604c4c05000b042c000c10200c112480c00030342001d40003204000d404140e920944409242c118202e5860025920010a021054008109000b8115201d14081c40858200020203441c1e0703402800c29010b500c0402d01644c2081400d10400d10840000300c1100e0b02c07040c0012000b0080d103680c0c4901c1045c5110361030040307207540c800ca0460340f00f500d00442c410b03200c3c0341c190700610050500800545440d80e480c0030034260355880740002d600940402e02c5950f19810b8074002c0e041e003803520007105028050200305c801d01d40800304030403002480050001c140ca465102d01c660154541025004110510f40001c1013030034101411003c0f46a4400c0e81190f010491704031501c100c800544034040d000368000c08040154150644001c680c40c8500c0ca0111151010808000440517500101001007400860581050b00b0004003290815804 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 648463794 1250 648462544 648462553
    0x110901050a061b0b090706121404150213060804050c031c11030c0d05130609060c080a0e040c0206150315160507121d1801090c020f0610050111 63
    0x5100c0054440c08080c4100d01c00e10070324100b59030761075600c00880110180c0003e0340d05414070b840da00241c3c03100101e00980001c04c03188410240e0003400351117022000c2090f00c041309565101d07a140c02102d801e000c0c41c0c900205408110b90030741c0000401c04000140301e161a5400c081c1800e1801900300841445c0030740c007e900900c0125141684c40344c007510110344a0411070b04811010f0303181c5045216281c040340b01c900c06c00000a8049074000002c05801c2030510003810f600b500c3c0c03d07084410a68074031a610004003080e149201103044400107105440c0c4a08110340c41151060201f8245c0b0340c10490a03026810500c200901d40e104045800d402650481c05010180030304182d0500302800507282085042c1e65444214085005d542100c0d0720036000f0385148230340d04200800401424060304480c044a07201c410002c1c00d4101484025010340d440000c00321140e007044410750003411549035810440c400c1c0d4180038410341050240700e0013102c1e045e41d201c4e116814800003405850000d142e05070f66900 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 648465044 1250 648463794 648463799
    0x9090a05120913050408070521091e09191a0913060608030310030c050607081e1e0d050108030c07090b010e090f061009080c240a020a110901 62
    0x5010036155103041e1651005611122404003060f03807492004100103281d4074040612051180100c05450705138840c40458041240054480101c40382120002c8000541800000b0291070310342000c41840c00043c60011805104a0000e0b03209441661040c14020498101c03c1601c0b001c0d004002d814240709984240d20b2490030040703500260008c00d05143e520032076100c0b0302000601d4101c0c10080520604890322400c0c0a40704455101151100f00e0b200540800006401d05000c6d0075580c00a800c021864180107051442d0f200d4001000b0001407039400402464840d2034070941c401948602011501e5116400721080070211101a0041d0510754014080242c4003070001035080243c0361f01400110b085806031006842006503007004a030321074a82d0701005000d015503211603104080440300b5007200c01c2040c200b55008400c60052101e00e030010383d4084c4181c2412507120010b0300c030160103105550303418405010715800407184000140c1000040005228110840824004003151911035075403 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 648466294 1250 648465044 648465053
    0x13060f0c060b06070606180e01090c0b0d0b0a080d080603031305100201020c0307111008090d110a050102040e010806150918030c06010329040503040b0304020a150e09090a 75
    0x10030300000a1a05440d21a0708000b926070324180c134800c1c0e501841c10b003c000c0d1540c620340c1c2c0c0d070210141c0c9181040c0c0b6003124607403162030501441c89004c1c0c1040c07030718075030a060003024646580074201241d0200c1d01ca04414800317071282d010704c4000b080d00001415080d400001d00500f41701c3c1c054441480f035131003880081108969001401c007242d80840c1d03000c4517014201d00130390190180d000310307070914000031401b441400709200480c91401070460704058800380250041c0c1c2c428a0640b2801540e52214410b84e09180c0101c2c00c0009510303003041114201c1c032055941703500360782c0a50040c4072a04c00040041280c140100480f6030041502d106403440c40d80f1540c081400180004c0140c5200101452002c603881010b004443d1420407007000d6541c1582c481c1414040c136400448a41046c211448410700c1d25402c05800c24019a80a40075500d803a1030210550b200ba00050010380e44200d0400000545034103840e501110440c1945959810028140803c030300c0c004000c2c141c00302500100c44010004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 648467544 1250 648466294 648466307
    0x304080d0212030604181205090a050913140f030309100501120f02060901052511030c0d1103030c0f0d030507050c0d0f050f0c03030105040e010606090e0601120f0213060f 75
    0x10400ba1400641261b00300003071450102c0003c005452001110301e00c004d056400401000c1c0c0080c00c2d205020742070307518820300440d80302c1290b540c503113010081e007124001043e0481c1d03800540803420440c2e803010806240c160960344152030081080e80f140f04c03600b40011031400398500600c804440000e4100c4151101c1e40c071013036070300d0000344240c10016581c8042d81c0100c040c0e600e20300c58400080301e08280001d89480900e004c0da801c0d10044080000c8091500d400035000e102980050000b020108882c3c1c0c3e4201141140748043c1ea040c001880080b072031500800c0300b103203064402c000a02c0111f55401014007281c00140c80c040c04c1007001c009102080c880000d02c28801451031626088694041c00116054007807240785043d84c5100040c006001407000010b136050340c404a0301048a41e0000200500302d41203841000b011903510130041000e80780791545142e110406051040c2140c0521000b0030442d042d0308861a1420744c0800e01c1c03480e00880c140c07248040d011909010f00308621200020b003c9 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 648468794 1250 648467544 648467551
    0x503010b03100e01080a060501050609010c1104020c060c030411010203030c12090c0303040f0f0509090c1c020a0f06180602060615040302100503041e120c0203010b030d020304080d021203 82
    0x415000001040301d6808540541c001040c0c9243c041c086540c5900303856880b030070041030a071405810301c0300120f0035203420300441e05040016100c520140c10b07140d864003502c290308481c0c0e070350050707013071080c43c0042c6028004103220b80c50b040c07031066485c607251402001c2c440b02031841e141154070500800008a0004c803c4400200110f0795901e66542e860408614020200b00d016406000214000400c8641011803400380e03810a001d05900ca9151001d0110704001202d18940552141e0802d40140c01d143c0850703d50603285c8821a00c1c03852254020501c41d402580c04044940746943c410001d03580d000c440344c4513070100c415241a080303140010007541c480e0003410440c461486210000c002c1d10070f100c02c413801140e000c1c01c4c041d031840301560040c003143c104139001d03540304043c0034014610005044400040340d9100e1031240440f0340c4030f038045822056110080b0380565a4540000f036a9030304101503000900c4a90040d50340ba4103059080c0c0c10128010541d4003554448000382c6410794000c4250f0783d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 648470044 1250 648468794 648468809
    0x1020a080c07140a05070602070605070c05010e2d100c0f03031a09090708120703020604032a1410151206062105160806070c080906040b09030616050301 67
    0x2c4407a450304080300b00c003441e190340c070086204000000042000105400c01200c178647c0980d54900d07503d690070b4505102c1c1c40b0000700380e12f0031500c051085600407075150180398005000203034110525082144101213000204071a03281000c4074580b145081f00075004034080d03903d00482c44801c01d68032041080c2503180d00400780740c0c0382d4603240902d2000c003100f104030742d5009100003000e00b460708225031130340024011440c1501525450740421010310088644880c0c2c141d0050000e03070707a5510100d41c080620310441c50801000c0030003c90003132072380507100b842501514180c07500d12100503000d4078140c41302101c03404040c02c01302c01c000d41100344405d4104079081c070320300000e44000b20f28084c0002c04158001c60707082e00c060b42c0c0300d00000416195400c9640e101750304031450f84406510340c80b000348280c03041c1c180961000001889aa214003100418584a0760459007060110f200091003038110390030040f00c2503408078003002e0743c0c078003001550341004442c44015004424250000c0680c0b0050003400e0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 648471294 1250 648470044 648470047
    0x509011e0530100f02071e0c15121b030533040b030d08070e0102031201151e05091f09030f03110a0803061e0a09090f1a011701020a080c 60
    0x21001000d21040044503240300040092800213804a0025000460199403140c1421080d0a0789118150048042e9030031080b030500c6030382791440d5000b801c0400c1d413040041042c084030700b85021405018071040c1804c0c2c0a2403141c00880b2090043c102d410041c034030f40038244a0300702c05c0e80c0700d000d2410403541e0f1010342c0c45848800380d520004c43e000d4107881060b2a05840703200d00b520f8110b603010400600600c0d4540e1a030301d014001b800120780d24020309040202c2c400c8070400410800100c1c650b08843c0c0fa00c1c034102009a000c0503203540482d042d43c1e01080c00414400240b121061921074060702c440c045d1360221b50300d00100120700a140004c240802005079140124074400e05000741c0444e074070185603100301e03207020b842d9142c1f210307081d041628610f00500041469681c1001400c8082e0212580034100d08001c519041100016000c0007000395506258490000003083d070904004505843c0d117151134440d07514103001204031441203601158a41d1043c80000f408540c4004d2550b0480401241310b07 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 648472544 1250 648471294 648471379
    0x1021c0215070c064d0414010906031103072007171905030313081204121106253b031b19081b0108100302280509011e05 53
    0x105114200f00580c0000c3c1001c2800902900c00d81f0307000c0400381003aa00d034403d0540e140c00540540b4a03002d1310302400c0b41c0510014203030303502c52405c0d13862a03c078070f02500303c034250594a254141100340c3c102c0038440c03070303880c2c18500132400400c912f00001808900c0c03821600540c0e1501070b160300000d40510622a110107948007804641d2041d500340c03800600c0c803000c83e81080d1510380c00e03008a00000340d000c20300750380d04a03856810102ea61803140011289011040d0b030b00444a40e4003c560f01810000d000e03a086482d04035440c844481d2103d6039143c8800d08102003040518685441c5511032540300380e01c00305660705001c0c0c03110f0032803541ca001594410700c2d41c001b402c01d40001c03401c1a00103005034070400000c8051003590021031041b003a004c1c0c071269002e403070321034014005070583c0c000650441d20050b400c0b90390321080c282c800c2040003110351000195440d01d00142600e0000c0c1c3c0071203500503c2d180014101d648800320700c0020b29046404c0e415900f010006402402880c1044819014401812 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 648473794 1250 648472544 648472661
    0x80c0112020d090503160c050609091512010c08040c08030a20031207020c01080c0a1b110d0312060f0f05010e151b1b01021c0215070c06 60
    0x3d01d0741030780e0083c1660384400d840c00d000003820185040a50740340e850b085002526042003012602080c02c00f50100b54180c3d520810910120308040300c241d00680c40e43c00001b0060070a02c01c400c0968010b82c0d0b90026400c06091041d20501c07960017106c1c2d20b030020851030900070b07000010f400240950102c18401600c4510f242c50942c01441c1e000c900e0340c1d6981c410081ca040c1d01080b49005542d0988809031301c0e84584481109178001c001402c80802c050590300300d11a20740381804441d4502c10b0510300d1800764a030000c6050300c2181d040403004102000a401513040d845e00641d40036018002070000518905294040307101040c0c81054144010202550844e44400c07286041c3c40c901c110fa1169141104248000700c1e011070000048540181052074a4180001c403400f03a503510164010090040300751408244040c603c2408030551082c000c2e00c404076204060050300c105003a0321180d0b50200b90382480e900f540c2c3c9500061a60b004544d04149214005961004040504013164401000620907 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 648475044 1250 648473794 648473801
    0x102071a09040c03050a0509010c0516150f050925050603190606022d0d1107031509061a180a02130b0703031404030507060203041106070b10080c0112020d 68
    0x8181c0e0041e080c0f4001c0f00701c01e80c16170400b07401250003080801080c0c1c0c0740a4010308880390300c0d003a10b00082c0700300545403c0ca200c0070083e0404034080d03d060032120950103690300455581e110055001e944446c2000483d007820b121240014150000042000f642c1c8241c1102a241500409210740da000c0080741d0917401107800005081c9505104101e40390b11140301039610506844c9181c205132807180c3c0400404101104444801e80d464010241d914103180d054070008840d07151704105124400703001021481e0350102060b003007500342000840c1500e60500d10b040d50b410441c2c14050801c0508611420b807031341071110600304803452030f00c00030381c99580da00c801910540b42c0144a516004102140c00d810b101c00411685100b0748040015403031041991074500c404650185c0031500c1880191301288040c3c0046910612910f4036518035015900011742c1d17a040020300303650803840c0700c0c10880c2e011615040b44028110080003440c03003001081c0020b1100e440781c041e0b00c180340d030041004d501e0a0719940 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 648476294 1250 648475044 648475057
    0xf1306020703020f0c1518010302160309061706030606090703061d100609081c120204060305180f0c01110a020904051c0c080f0310030204020d0605040e010b0102071a 73
    0x41556500c81c1d0b4100255190048404140b0502404941c5101450044410340000403400315460600c1c0c044030415000300001618681459000c00408007601c9920743c0400d003031442178803884034407400c085005094040701c042d00360140403a03005006203558001049907000904542c2039030156180c2c8000c8010b0300d0280d000205420b6a4241b2084a5056041140c410b08606d0140342480da5a0302048480c05094410b64200b80c100081c82000c590100e06c085410302038504100381c2e16076510f0541d208070b038010350180b000699980140304440b000d20f54441c00500c440c2008210303c281000c8442d031038080d240344680c1400f1051891402503007003880b441040703030340042803101e00b071400382407440e214012280444941e51001c4201c8006070b00031039080300495005000d290400d41c8400303200c1425172000d80314032042c1c02c0703c190000050366a800185140d0895442c0480d030103251a05220079500555000c0656034148620400d207a6030004008040300c40c104814906501c40e221004518480d95 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 648477544 1250 648476294 648476303
    0x11209110303030705120906010e18010e0d09061106070503192a0f0f02070b0322051f060506090402030c191d06090a03080a05040803040e0603150f0f13 67
    0x203c00c000e074154100c0081e16121036103040c184010796620848649482d824010403080c6000c1e1404224064081841c460400d07002c407000040300c17061803409514000682040800086540340280702d0036601035034103009001d4190051241e42040308000d0802c1c00010040201645504404028603100350041d002d1103541841000300c407000128002c000748051240580410f10300071400300854841d5241d14460720940e4003810800d81420704c540c440358409485408480c0007201240c3d1207002409002880c0e038071440c010504070b1842e495131285034220403408508145407400801098075903a0484060f00011100140d483e914650403802a01840d0800803917410201800e00c03005410015801110121132035207400003440a00b00011441a921003503000180071904000182d40b02024007022086424424145a154117080e8915000b40c0e00c0940900422014032440c0e060520a902035001404900c1c009071800d00044004408040e1004a084210030000b84800101503122210300d03a20 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 648478794 1250 648477544 648477547
    0x2e0509040f060f0e0c040f050409020a1e080d0216090929010e0a060305300f0403060e010c1b08040b07050c030606100e0405090a0b040b0f070c02011209110303 70
    0x9803038034514503d40b00e00901003500c1c0d440703011543d4911340c20251b82c201c03010b003104d000d0000d081c082400050701d00d004080780c20103100900400c1c000042c11b080085001c0500c1c105540918001040340742002a0000d0025904501c0d0b101d64580d00000402080d250b480c80e001c01c10320348602c2e000040408444031600a02010b0a0300c014000300c40e10814120341c0f5070340713401c44692102c2410408179103042c071004210342d00c4080c26140c082c141c103900c511101d6901d503143d441d0150020240d2020f5009200c800d1980c10006000c0c003c00400e403140803001000761008210380da51118014155000100361095401500440340082090000850f00500102e00b48907803034001510341190360b074070010010743c400d0081900050b0303282041c0418188a001c16903d00d04004e000d03105100080c04081d041140c0c40c000c601d9200701045203003080c0d6008502c211a658100c1c503220401d100102350240580d000c1004003003c0c0303c0943ea006807042d00d107100345800002c0b00070351480c040500300311048150380c15000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 648480044 1250 648478794 648478799
    0xb0d030806210307110301051006180314010e3c030d0204090f0c02150c1602040e030304020108070908060411010c020a090510060504030203280b0907052e0509040f06 73
    0xc000c0013514000b841201000e0442804404060a0b110107c07008800d40c0c950381820404903200d00ba032848603244102045403103030380b203072200b1003403000c0c000c1c04000583d110660340034442410400c80080841c42e5282c444010118800701ca40301000d283e4035034440807814441c0036504003d000302e808405010108541d610780d5902c00c940a0840071561802040c60801c88070081400890540b40f0701c1403144400b6041e41e01e42d01c902200b0b401210000c16922445003c00e8016100c0d0b09c01d074007002c84400001d503102c0c6001d1000404c08036005003034200300800c05200300b00120700060225045503200c600c11170b000d19401d0040b50300c03004400e0080d52061032180e0000340e003901a0b0101c1d000300e0705114041c0b01d440e1210b8042d80c2034031035444003e4150b4401c480c2020314011020302d103180c10000f180514003030303242170710b0310606440305540b0b0042642011758200f065251140e14a00d54501221035040100d20800f00c061001020b03030352807011b001d00001d0070505c90b6940c0d0320070415007211003402c004098 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 648481294 1250 648480044 648480109
    0xf0a0b0105101b170f040902070501230f04031115150402040b040506160c03050c030d081306050705041503020301050f01031103011202041107050a150b0d030806 71
    0x3807140c1030003400c0300c2c105040c1da244076540407901c040c404102094229a150365890310300c0314149400c3c000b01c000f802181e00650344000204020100d44034003680700c5a81d401e145007140e0440748204001015017481c6403c500044180d6544401d034841070300015603881c1020348180d10399410307c000b58011100c0400d599102c24080702d00494220045c0340071502c8402c28001244541d00400008050500042026107424001001c0c0069607030a2002d41c0c050390366900815411a4104555681200d40915035600b42040383c8003400556180201c55400d100c040f00d00c0d03d00045c98041d190f551500300244c0304500031000c032001450881da81181040030180700070000c1d0028020345204518150040740e840d03200c0d015802c0e40050812605103141d290842049001c002c840c400ca8006440d180340c0001000b0300c03c00b900030300340241d010b40084030320b924080c0d0080c9020003a00b044186411080090790301c440242440c540c2d85030030f010203151959000038205801006d4916403082c0c1c880381003070640 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 648482544 1250 648481294 648481313
    0x203030712110f0304050c031903030b1009090e011b110106050f091909200108060a0f06210c0905120d02061302010e100e0109050d11010e030f0a 64
    0x1205240d81c0e045012048042040c156503004107807100089040c844000291420801035410910174811a00511b000e10082030030f02503682001e40d001900b00d840841415014080c820301018119012000200c4080024180003103c0c080d6010b00d690341c2c581d200002c0d600354805100c170b00c20b002d4680d00150302c210b8020842d01b251131120302d995003401000206800c207980c45d41040c2000a10740e218980e1100414085105003280000c001515a01d21101180049440245c1c0030b000355042d02c6120402800548503071700140c8218041e494170401081075990300318032401681c00c1450801220261201d000d0000031454403010381440c0f0f401181d10038583c011040008482c01500c010f85240c000c242d440c2d886e14039064a40003d83c0118001070324002d41581600b8001740f05042080c443e41d1804046254008148030700c0300480c086401410580da084002c900041c40c084400803900303140c540d00c1440d10401c2066043c1442707040c51007103845079010b000744004115048100c1d82c04010509000405 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 648483794 1250 648482544 648482551
    0x50d0b090411120f0c01030b01201612150b13110903071220061c150f060507121b110414012411070f03051c0f030906020f0307020303 59
    0x680030b0790032841c00d03c3c2000c04c1c4c41c0b0b0410f60000140001c65074074801540904840811941001180c40c0200083c225026260002c141c6c0c017030041a2a202c3d0a0f012000580c80b60001c108010f02d203400040020001d40c1c0750000d0603200b01c004200c104a030700c04a501e4665024600b0501c1c3e0800040050750804000030b40b901c204c0484c215050b49a407a8410004030404c04005410200708800b4404858213518480402c0300d8041c0075a4a46490004603646207401c10362880b000a440707a411707480315480200d017a80545a140091500da614000c005091740c4038002004040038203031a410400b0500aa01500d400c0740703590f2404c40f03051070b80d240c401c4078604d94174400741c45149805e150300ba07030480c2505294161015250340000e0586012050b99040c1d070b6a00d845020000b0110503d4081002846150300801c45c00d515024520b0841c03411038208030b08071302014105858107a00300c1c130042c0e20a408501c403154034100002c42d2405400e080780a4803410380fa12603154400000d000714142d000005520 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 648485044 1250 648483794 648483799
    0x30e071e0e2502240406150501020318040b0a080a0b24040504020f0406120b0a09110d050709022a01060821090a080703030f0206090d050d0b090411 65
    0xe00c107031200c0c6a0041e1040c00d0702c0c80c0040700d42c071691900701404400254120704002d0300490340c090b48004080d00c1240404511152441000002d0008005450080c20b00080642250304040303400c01d80001d59038001d01c01d002070a2580300a07551011b4480760300ca80790403400034082a1555846114140e03130341c0340000e01104c0405040c8005440c1c0d41c07003180e0000000b01300726000c49212243c5d2040002030030f4083d10607a030050b144e601c941d94a03611840345070000c2880c6907500450300c0301c07800e03d0402244020015032406003071000900004041c401c984600041c101d41c4003400c043c1500380031303141545a0300300d2201030b88005400720343c0c2c01110010882c1c070b210144012140240c2e1a85160a860080c420100c1b2640140d01e814840c154040d0344030022000a05014141051000015880c00c2070750300101040d08903003018414545c5c032202e1800790103180d00040005003812000d491755058001440f608000d40411200b00010341b942220748080380041c040b5a0700d04203400d040c0b80890002e900d50b413 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 648486294 1250 648485044 648485099
    0x50d0501020301180506100c05031201080619230c0f12010906060203070c15050d020310140d031e1e020d0306090905030d0f1d1507081312030e07 64
    0x31303200003400707040c0c03003640040c02c3d07a50781c130b044010161a907912101e0100c0383c50100740200621a400c000c40d05000b00042d000420340340c1040703040100e41d0007004900c101c929040000070100074a8400da035022115603a00d044034155a521070f03a000c2401034104103c240c5000103125400110107c403107034180c5801503800c0061558545060b80d5a00c9041c1000309201304007581040740c80c032031130140310580c983c6d07007440c1d45080001240d141c103da0040360400004a800c4505000802003250200d030080750a82c0c0007200c4071030640f000307050816280011a5100c51031841180301c46e200d21844e0282c0c04141459040d4030bc0325060194450341801c40c1c003030019150650001e80300e4000d0041d80d40389500403004c3d61914034141c2d502d0300030341003c0c19105070442d190350f07030500a0b00480078a44441c0e600c91000e000d1148058080a02e1020081c010030708000707495003880b1320342c00141c1d01e011400354880fa4880113030001f03010940141001c0b2410700c0050145074800120041034144a924142c01d010524 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 648487544 1250 648486294 648486329
    0x705060f0601081e07211103090607030908030c030903070c0909150507090b0903030c03040e04171c090c030b09030c01050903041202011803060203070e0f01020105071d0109050d0501020301 83
    0x120307141c110410130700c0e840300403c8000c140b05600501c50749406810f05140303480580c01340b001c040142c035010f09103e00880b030300004002c4811070912606030000041d26040c404045561100c40023804050b2098203881c07400004550641010012901c5042d4085042c40301e0303ea40f861514020105018151044443c4098041d4950981e00c10640b048000351666603101c1c1c10844c0420540d0030500000e505888100520851024204041d1004028044007850141740c40d14005400740d030418003541820380103200310030704251004062150404818030001e2010000c0c207044004100903480900a070729000b0911030141070220040419400c40c0700240051b850b5408866502d200714850007010b201c00b8078030040103612510010a510880039a61114540c40ba1268802c90780b0640700040426201d0f1504c05d010b04000c17410094030b003000d0008019038a8800c80103001b044031200399100e49e41c1411001060f03a0f001d6814400174200180007000d804e0510b1403c24002d60007802880d2000c0c00e4030289 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 648488794 1250 648487544 648487561
    0xf17041e03021f1e050909160207150f050901050702040903261b0310091505010306060503130212030d050c0a0e0306190c0e060c0d09060201090b01050d080705060f060108 75
    0x500c040c403055565800b0300c2d0080700100418002024140b13100304507040241c09a00da5440c200a400f426440c40307103400129507a08003901e46903850307004d00da40140840101c2031240c4c0090008018420504280307036240b209200403036140c4185503000350301900d03210305601410781c40000c086407160f03814440860145100c11200010404030381815806c90542c101c403551502400c041d50b00302081040c6004041d03100c440305400d441d031000c0304140040c60700354200842d6034140074200003081b1504140f49182031114010300301d0b999019020303002d0511100d420492a004108541a2000310001003040381000c00c1d0b01860360380300b1651040040c0200713aa10110f0b28012a4441c01500e409214031444104004605d0140030000c140700d003484500a11000607480302d10040540418000152507000f5180c500540b0b2044590056411685014811800255142c60080c1998001c4032509080426032808445900c9007041c010114003503c02404502c0c9144080340340181401d80380c0041c9595000e18 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 648490044 1250 648488794 648488839
    0x909030f02070f0f09020a0c0203070e070e060c0c010804030e04021602040605040c1b050a0204110307081f091a0301181208040201051206010c050d051b0102070f17041e0302 76
    0x70f451340c00d200200c003c02030b01106030700901e000c1101c0e08080d03426901f1078002a080c041d155024058540c50a0108207a0030340c4101c0680c0d511000311422402e02c4180c0340b070700d561000c0c40c51400e418401040040303424540250f0700c1220400e00100159910601c5405841c1210181e01e012400303035050040c04603d900d4280150021000c1540e6594079221140000b18002c0c011400144c1d4075000c1c0c50b0b07003800580c8860254000c42e00011002540e6810b00c0c82c802003040000801100c035444000c800d20f021a203a6807954411075001c840d010a040d0718081700100d03600010b040082e41580381072100302005007844100304006010b461034000100a40400351045d210848009001800030020f1150700b84c05210816040403040c5080c040785c03140795440358a0160345400c0600841c2000c9219580048514141003070600c82500035400d04200d40c2d11280b0245038204010000f81d030050304a26560f5404055070020b1540056540942e8a010501031a080c541d00007070f0300a200d03010281c10002e03040b55 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 648491294 1250 648490044 648490049
    0x31e020c150a1202070f080318070b0403151a0f130606030e0d020f0c01080c310503120a0c03052512051614010e0a0606050910060215100909030f02070f 67
    0x14943d14003610b540305401f503840249490040b41c14402001c3e00807000300503004c0540a50810150f4603800c6061401100c00340340700c041a01410a4600511800765803003000070208103541c00190130800c000016000d100001402100340c0c681000021a07542c1504545204c520300c00c15988942c0050743c0807038854510000e40040c552201003c40b031154410788406522401007913546040c05d882081942104400c00d40c00c4047d46005080e0103414035800b0444001030000700d0081140d0103180c00010110b00038428a00b01b13014103040040245030150301141c8007605442440d1110281100c0203a450030003400c41030341e80d0b001000b03180f000c0d540200d00b110a50341803100d009410f1100340d0303038801e41440c040d08441f09030f54943c40d20740000352040103899101407080101041d0300b82450181f01508600400e40200400350380c01c2000b03034503001701d20340b01d00d07140440c0c00c494250365807460b40c42115030a501150b141d030300d002010300900d644402680048442c41e030030f0b030310010740c3c5065006980e942070 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 648492544 1250 648491294 648491303
    0x40f091a0c0a180803070f0b15031002131509090f020f0d0b060c0a0b0420150717040e0a0b030309030c04020702030a080f0406080a0504031e020c150a120207 69
    0x4005080450780030b009003843d960000c49000c0c00300d5464a112034119000640100c4440340c0042c48001041400b11700f140e8815482c90b04074110500c0940000d644920520b507402001d40e0000d45041e114010400c0603018250340e502c2122800e040d884010318090f15449901001441d000440816410b43c0c0201c1c0c031141030300000d140c10008400818030042c0311001c45203602c20344c10803524144000500c120b90295026032000c0344540b03000e04100018180440a00d0315149891001740d0103590b56141d00500362142c545aa510b4003841d252448844054060007031442c176000c41c00040c00741c0d884002c02d1003819041c8040c04990103034803d1540c0c234018407485a905802011410002d0704103070340038001540c0003e0031551207841c2c1e07442d0516190f11040502c410b540c8001400c1c402c0c01c1c2c00c07200039504080200c00c200f0184c41d00b51001800080700c8450300141e680721582d000d07205803003000461452003009015000011040c2009411540910400d174085208848810300c111464800e444619402 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 648493794 1250 648492544 648492547
    0x4150c020906060904140c0d0612170f0c03040e0405150106020319021002030c040807060e06030f04020d0515160801050901150504090608010903200d03050601030b040f091a0c 77
    0x542d070412100c0e81003100c845401c43d40d075516000305149940b0394a030040b0020b1920643c1ca0030901300120a4940d10342000102c2180100315900082983c810807509044803c512600d0710545c0085040030b100d03e1005c2100f503c0042400301c1d185050042c61030040e40305004850214082620b10f0311003030824400c107805a0400d00a141d40b200e403580c4041d4600e44240705450106a4440501040740c200f43c5481c01548008102445070314000c101c900050301060801c0002e502095001600c0c6110081805184440c180042002c42d200d81c1d40445c40d240e480001e407481008048020105900c0488900d01c503402c0100c41c079605207009450aa0580744040c1c8101d101e0fa08055110351000703100320b010420064200000240000740d841040701030b0090b0703c004111203e00e400c0050400b1050291801d1184032400650035051001034101c814480606010500707968100043c0e0040144280b0a82c105041c0f0100c0c40660000303a004104040c41150540000400c48031070001682c000c460212540c1c00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 648495044 1250 648493794 648493801
    0x1503080a12060e01051504081009030905030a031205060609090a0e190f05011b120b010210020c010e071e121b0e0f0c090a03020d0c05031204150c0209 66
    0x550000402010500d030070700001840c2418425000c95185500003600741440030010b101c00d1030211000c1d0a181e54101c2da081c2401e0614004645504500d100914015680e10440e400c0601a50f00c48009000c0141680c407001c62a080c0070300900045d01840c2036030f0b403a00c000130f81245483c0050b40c000100140400b00c0e90759400c020700f40180401d90b03a10a152080742490304a804050310000324040c0704800d00803411015142803420358002d0007800e00f425000501d41c6c00702c41e5020040c0c2003401540040800d4100800300182d0a0180d1480060141400041c01101c446c20541054100032950412070f0a40c6554508040c1d1660840401c0b80041000c1d0100300444500d00c001114080c0c00740c20700c41d0841c90b180d005000300002940c08400d080317000c6020002520b00302007425501c02c0c0c1c00c10a03035203412200c90000700141c185010003881110052001002c0c0f00018071010085c0201030120b451030060420425180d810520170400d0540c001d00c02d0306004d0f44100d84806a00c1e9000d0030f00c0b1900c0e103 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 648496294 1250 648495044 648495053
    0x2030907090b03100c0521040209190e0d030b0109151709070b130302030105130b0106050d020f0f0310090b060a08091609150e010806070e03160602010209040b041503 73
    0x2d007140e00540e051140c002020200c0b4028440c1c4007082905443d8655101c074440200341c10040207140081e40f01c01c040c0b0400c00541c85034105568800032046101144d0000c002420005050f5468000513a2081d89145891150590300c0b400380040c0980b91845200c0da036001411061991466010008011128003822941009030140e040b0315004261403003652106130300c1d00c1c940c01c04048000e00c1c0c030145008000790b04080c483c0390b4100f0b6450364900b19050b00b03034070ba078220208184200000c021000845030260230741c7e03505868000d44100c0131343c0d50354071188910011700e820030364903401ca11070203040004e8007546900c24007a06c03803405406541800507034071080c0c560110003403404a1a000742c0710040c03503c01001001401901400070300181a43c20b840e803204c2d04010940000690141910040c81f01c068001512613010134185011004443e036040402c0c1840e0042c50046d021200b11070780490f250b901900584104036007901d003040060540d8007040183d81800203a440388120091041c80880d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 648497544 1250 648496294 648496301
    0x60e160e01090329090307020102061503010b0a03080a0905060319020906070b090d09061106010e04080c031b120405010e0d0825021503070f0c0203070e0703091103010203090709 78
    0x440141003290002d50b0382c0d11605401c40348500640b0298841c2660140740020020500d50480600301c0150b040c000d180c0d0003c3e60740c11014044e0f0090400c002c0040c3c4d40340d079094009041c1a40b001e8203c518070f17a075038602421550081d040d46404940000c001107185c1c14420181c034401c040c403140410f03100500405510007980059262074100d04100310100101c1c0075411140c1c0100c0d00c0d00001c240501004030002c1c03004405800400c01c02c034440802c00b0303807464001041415920010310031003403030700c035490f00a806120b050b02049913400301062041c004004041031141d0110700c0f00a40304a00c540548180755403190703008090102e0741c45c1d0218102c0742021f00d0020111880ba581c514903005000c080540200c502508060100002005c85000c50524a02e4030307920324517000c0b00c5801c5050180c000b1340003100c4420601d04224104000500355a800c00c0160010035080701d00c00b074a0704103010000c020304184401a64800302c0b0602641e241c0c1014801c4038458200c0c200905140c078109101400903 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 648498794 1250 648497544 648497567
    0x1d18070b0309010213120303151206020f04080a0c060908031303060b0307080f0d1202041a030903070b01031109090a030905060d0e150709091404080703111b04060e16 73
    0x243d40d420b1050302c9142d000d00765000c002c0d0400c609850701403e003d2a0050a441800d12846030602c41a0300c1003256054217070b4450b203070395840140540c441c0010141260703940200d40c005d075207030710481c20003100740603100c009801aa807040da02e501c6071035103c05880d6564400c0301c41500030b41d002074404102190050303000700020130000b001d86030034695510034a031400301036400b61041d98000141402c6010f400403504102c483e5a5002541002d150441101c8084006050380651400010004528074001e104542c42e455000011034250b507140e041200071708030f0500509004400ca40085160743c00001010441c59030b05507204050541080c0a2243e560003190500051517142c0c1e1031014090784c00e1224481c404c8201a80d00c21615001e600101420001d6111800c0c0c41e25100500071400c003410f10740c2da8031540140c1502da80c0c45291504803007051190035854164026160b070031402c15200b04142c0c4c82c204040b10300703000c1c954440b50781301030102040da4014815002039155141407401038421018 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 648500044 1250 648498794 648498811
    0x6090a0e0f060f011d0907031e2027041b05061c0c110d082e05040507110a1101020a05061306140702341d18070b03 51
    0x32400d0001c0940c074036081d001c1c0c41940c1440039080052001000281c180320400b45c000e28407500350305015001a4590220b4000a0222244010110510750501100da86c7c41d66000d55110842000941d185459282d8100d103548115000300500b82c070300c020080d16843c800f0352050f04048580799030351a0030104072030200c541c150a245c0580041c8680c1e0b8403002c0d0900042000403540002a990010382c1160110b4680b9001d0100700408901c0511001812480e2608076003041c030704540f203002412190040c58014028010400301c031080b840c6211142a0003107500c243c0d814800e40d01d40c1030080d100740604070076941e2660b00c001c003d000465019242819100c070f040c010345825140790703180c480c24880100c0d0ba00340b0b40b5402d8401d41040050511500d032028039604e40c0759419040001c1d0003501c501d40b072180600e0040c2460910300da40c2e181c1101c0500401c0703441400342855542ca0b0390700c11805140303288091000072400c000520740038007200b40b101c1074024000945403d80c1003105481c61500050300300e81c03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 648501294 1250 648500044 648500053
    0x621030905040f06030c051f05160204020a030b33031504020408160605070c05090a1415180105090106080403020304030c0311031c05031302031908040e010e06090a0e 73
    0x681c80e100c500c01c6541c0c090729240b02103211811800d0082c000b0000303601181c001e81e18200000c00b1020302e08a00d040c0060285011584d0310203d0060a0380c00305904400303584148000b81044855030558013a080c2c1c0c4000b40d8a10380310002e02c030080c0d83d04a401a0b0300d401c0040341c40ca5500410120781008541c03201c521100710490b500c0002c003107412a005600000013540c42203d40201040c070310400301c0c0c0145480d2610034940005650348400240702b0b489013500030350b1280041101c41c03c880e0010201803411003180c8102d4640b807003044079402c0f889401c407030107070003584410154030103880c9030781303041c1c58014000f10303a82d91070f01d003080700c2c038410040c01682180018000800000c402240c80d10045004000e0000c034510703100c00300350074191455960640b1003680c0f2084e881054202080c3d0340d000340081c1c00200f915200340007003414810448800282d03251407408150030041c10038054000e680d0440c0240300320785e807038178402d00102d14150340c610b41c0110740c0390000d0300d840c140b41c0004420001460685 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 648502544 1250 648501294 648501299
    0x906050a050f13080714130b0d060e030a03150e06061c0c0801090c0804050a020f010203040f0f080c0117040f06060e0a05060132030903160c03021306210309 69
    0x900d5410101c40ba44070074540010400c0713071050801c040b901811645c01c40300f1199008400244503181a0344840c4c4015458131402c201c01d030b4800700050f02e03854100704140400c00500000c10f441c2e40c03010119001091074006c9210704032004280c0e200c140c03501d6120b0b50728162961002c01a40d0b070807200c160f0744103965006249074a03130064000c498030845251580c5013107504001d17800f01521400c1401070200711800d0100000b25000246071101540c0588048009140031070040b411032150307402405c1c0c101c611050018290f40c4d05101c0000701c80c54202525085488040115151011400402c02c160068404907011440e2200e401c03810074807400b00024955650000700d80b5040d01120a0761030590f0780c200300005940c000b1000380300c01e0510712080c19081160b80c5040814070501c9071110f1159408800560142c0b03041040b194044001c0f6142050394900380380ca65036180590104070b0003040555105105003a480c040c0c601590440085406585001c00d481e80c3c40194602c17090b020401100c000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 648503794 1250 648502544 648502567
    0xa020309010204081f0c0e06090111010b061b0f01090b150102010204030605040303050403140322020604030606180c050405061801020703020a0603090506061005032a0d0606031802010906050a05 85
    0x88040f415070606000c0e1790000040440c1c0407510701d1031440b030900c01d101000c1007050703440b20304442d0303048401d0030115904280000030a004094510f0080d03000303c0001030741143d84451540185051404404440e68481c0c5591070600383e80b081c0070700030042414071010885501d51a44500248001031000504190343c0b9100c98060703c0d030030f9030160042030350340e0180000d01d42d10039a01142e0b19041d84036030f0721b94280f50014110990160400c819003a103a032450030115524481100c00075500810148541ca4480d00060b00250041c8141261307140360081c90b003003071801481a5011540020081070401d4101070f8021444550060002e0440c0146000400181c0d9a000301901502442e40c00044065542c5001c40c80c111001d0506445050345400e02541c0551240442e41e0054402d80c125102401207504a02e00ca003800b8640c402c41c00001c80d0400f503440c2c655001d24111801d955061047d44034031510854100e04101002e400144840024459240200000c0840341050300e80503290034104c011 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 648505044 1250 648503794 648503803
    0xc0209130813230102070909061d1f0c020c060c0f12090a0801202d0304020f18010504270510140f0a231303030c090302090a02030901020408 62
    0x24441c90900d031030b1000f80210842c005100d01e0200c14403029540c81c840002c0040c0d92025144038800300c0e580c80d144074104000050300100402092040501d24000ac0c403160291103210110260031140c422621010710f42c0f42a0103144588003103600901000041d810901100ea8000c15518109201d81d4821101011040100c40030b001c10b0029441c0d03d0303000c503504109008030740d64800e1115a0600207035001c4800e03011550b000c8034010000145c1d07541c0d45203a0044950024036948620807000c00d00c400c070f95000e00e00096129074400c40e404042c2c58852401c00904903980c6102005010f490001440b89080651140141c08141d148240d5049440c01c00860307440070040007200c40340c101e4058811f40d014503004d0501c0c080310000740500c107494804180181010018280342610b5220300207200c0d030b0340040103c54100d0640b200c85900d1440c020101c2213555402140403000603287c9404c00400780c0c4154403c0007501e600414201326a203d178228040a908080c1200719255801c11000452103c00c21 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 648506294 1250 648505044 648505057
    0x180c07111c20150d150b0403030206040303050f070c020d140a031107080304051e0607020402071b0504053c04120201110703090504090c0f080a020406080d0c02091308 73
    0x3020004002c409035006640030700b00640b030f4080c4900101c04144409280f059904848814000003810713065610060090a003580c4020700040c0c0004020040c140e0109690f80304c3d5020780c0302070001ea120340b40080c84805080321214009650841410010700e48505142c400901424058081c0d80b0310880650030100c0140084010400300103040902c003000340200b9000b0400b107400707103007440e26201c045900901e02141007029009440b8503018550703503842c04e8a0050b6005002107441e4240761410480c0d241c50702d084040c03405024000050a481c00d40599485042c22000f01582d1003244520520502c0b0703015800e00100301950b0084c642c103200074407468440c03070048005054407080342c40e000c0e084681d1f5510124102500b04408008250030100c650211503068400007075403a0b15007030002610f0641e8105040810040c03100040b801000030b81d074420b050003220204103103503440358080e0781d403080c5003917103070101e4541c981c0a0701601e820119181c3c02100d0f20401c20680c441c0340d0301c0c582103500c0b95 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 648507544 1250 648506294 648506303
    0x302100f030b03061302040b04061409071809330b0d02040b120f010e040201230c0604031e080402130504050a0602030907090c020c0102070b030a060b07050105010302180c07111c 78
    0xe01084055140a0041f50121423098400304502814241c1035034404194101c0280500f8041c1e0100d481280b1070400e0b4250700700c0c000e4000300b0194070355940d00c0c0509211005d03010408484811801c00004214000d2040c1d02400c26503c0e0b2146090700792200350f0865514040c51940c00c0c400003c16600080041001100d6004159058038042c2d03410b00f503012068200c0c500e0030f03115808110060760000f17290500c500340f0641480c260f0040d5204e4004901c141c1000581c00c0c0586e200b4481003640000b8072080d889403100c2071105140c094401220284d10854001c0d41c4080107001444142c215036220680081c0118180d036041c04441c0c0320407017030380e0050702e016074aa48000d0041004007118403410100000318030141411800400000b0340d503c4d403501500049590000106e44001c070254007100050001c1c05099031900ca1900b0078074005c0c00700348826400350a0100d08803440d003100040303003032240031071814060804000385c441310324502c1880050f5410010044523110541400001400001d104 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 648508794 1250 648507544 648507571
    0x70f0201031805030919080a1407140108130305090a120b1b072a260c06041833172503080415030606090302100f030b0306 54
    0x1520004040360682518000c007008203206680014101008440c0740500807035041d15541101201c014501c4050382c4843c0d228411402c58a0801c600c0b43c1c451600482d01c5030a40b040b01d035540701d500411030324001d60280080d801c000010340340001d0307079072054840b4000d10340681011100b502280c0300300e001e0707000240300080c10116141003040d00440f80350301004400c41c961a90036076208112290180030310090442e201c4120300050180c09420030342201c000f04202000b01c80e9116460481c1e2218441c14240142a41000c0710b2049400038000d03150400242c1a80c0c90946054484070081034030011000d500f40e190141c400e2150307500e18040c50801c003400131130159401e04072000142100790f60300180d5980205004130741594004a121812000010088880050f0500c02041040256040141100000b08010849050085000800300f1054504001c9980c5409040e50080e1445c0700003980030032031202001d50b040c03058103440401c03021818040b40ca0000f140c00a03040c138404403851a9903681 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 648510044 1250 648508794 648508823
    0x70807050313030507060309170304020d02150901090e0403090b0304060b220e07061e05091302130f12030e031c030203060112111602061303060c0f182907 68
    0x1420305c400001800203003001c01240031f099542d0810225518907101441a010000a0540d12016600000194020720f0080f1051202c01004400d0700041c022074006482c1e40300100d41303951404003090182c0c3d00350310f030046114980304200702c20f68401001114584e450703000c440c0464072203a00300030a04180046201d1036820030000702e0122103500307a44c29100e2303200750001c00055030003034185808407421000c1070400c01440e202c1610a4400c00b510f0319041505102000c174084000d40c098121540c0c00b00d001180070b80d0b0b8810032840b20000340120510b04402c003c1c4000021301401c1e0021a03e14040c05a4110980441405688030f120491080210b07800004209103036920a4010044584440c010006c840d440105840c440c06450b90380c0c071403054464004810740d0380324005e94828844591810440039200d10b00000640740300003622011071507404200030308a000741c41034140002d8003881e20000301c1c94911030b080620041c603061584416502d08421a021892009000c5140540d1140c0d0a001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 648511294 1250 648510044 648510053
    0x50c03150a17340b0a090b030c030a0513030f080a0e06090a1506061d0109050603010f030b16080403140c030c0601050f0105040518060a0b071103010b01050a0f0507080705031303 78
    0x4542008554040c0480d0f0716641d200c1040750364101a1903000c0c150517240e0711a408281c81c8079850f5040b414000a02004001030240440700545c41403a000d00e09000d40d07117a605002622241c0c0d850f00402250041e811030750142c0c0306090305030b84440489800700b260003046100608000c410744203a01160401004542031001c440103111034402d12131820071540d850310b00010b201d1001000c400a640000c281d908626a00c2000d21a0281100806c0c0d9130356540d68144003661070b40c081c4011649220f0000010f80c0642c4403d000c900a20034503243c01d5095540d076902116502e22a52260b04030340410303c105080e01c1c904001070240020034074014180e030350418040264031200c611440d410800d04100038480f0fa1a903d0850269405d111101c0080b5222880084e040c00c2c11504413a111a1012030a5024040581580740300d0100c185c000f00705880c40100112a01e110300844840455030103e010800c440c442d4009081d07141c0115503086c02d001e5582d40e0181940d1002144a101d040e261a0034000d10 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 648512544 1250 648511294 648511333
    0xc170d02061014091b0a2a0c0306021b0f01090308090a081b030c0109031e092106110a02070f17060f040212010507030c030f050c03150a17 61
    0x8a240c2c0c0e80da8119450444078003142d99440c64400e0007580400e010488024816031a0301000d100c8940326911022800e0340108940558410341ca00000c0320301d10a12400c46840200d040140c1001d1415141d40c1103890350f801139441844800301c0c08404050808100341c0510410072201d14910022411083e241001071886501030a05406904000e0b1a07030300050401c01140d480d2400441414814290650911b0031401084c03114151075092240d00010160b0203048007440200c40c039141505185c94500c105c410765414000e00141c01015000e019085c1c56041c80b610003c3d00c01e187c0881c540780c0d00122604079070410780207000035034882c010a00c45503c0d0f01d1f0b8076038054410003089100e8040c103c031480d6902c445c058121543c088108011a0554482cbd0b20901c6441151000030300285c1002e0f00005c2c02807240ca071070500020f181c2011030b00900030710b021300360050841c3d605150a544555546464510300340e40702503800801c1450019481c41c210814507000345d0000003505000700300150303001c43c0c03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 648513794 1250 648512544 648512551
    0x1c05130f180504140a0f17031b0306031906060305120a09030f0c090c181d0a0f1d0d030f06030f0b04080f0f09030d05070812040c170d0206 61
    0xa2403611032060202250300160401c0200c66054041816261030074281801c01e08519440f265000d03c800c11003d101d4015032620a42d881800000603d1020280d0f00c030b280d010644c1e10b0007680c0362803005500d40440000c06541c02a030010141d4414801c4005641c100c0c03491541c0844500d501c9a800300300b030000174040404143e000343c02491030410040e10003800c00d600fa00000b070916080386201c030103101c0e003a6580c170040d0482032001c0021501001c03001e404481c0e40c040c3c0c041143c603800c3d008900a065075092150085848007440e035141c44581c0d8000103007035410f9031110312907624404114429000b0903210803810200c800b51a090b00700c0c6000405403403250600b02500ca04254003000011214244888007503000040011a031301c8602e410303609480340c414484000c8502007032510141072003400404544101318210b540300c40e8004029030f0ac071301072944090242c08041c09003050524640640d11f0f4058440d41a4280315030b2540c1c3c1801c01200c480101c0681984951003d1320607580401c0329640 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 648515044 1250 648513794 648513809
    0x60c05070b0a05120717040b06100e03150a0f0903050d20032e0f0611011416030b090717060d0503030601030b010507050a0b040203070e090c060c1c0513 67
    0x1070008102d50240c414418050340c1c1e405a60300200243d442d52080011107504030303412405041c24282420002e01e0f604050702c45130300c030715400c0c03600c00803c03801044c46100380c2c07001030050420760b4440407990455542c002c00d82040c4a49424010800d45124860141501d1080e00c4e065100c4e1080341940e0102c07082850f43d0040c50b00c90102c002c000300c8101c015240d00c60884c00412842c0386d0101f0325030343e0907407401e070042d42641c0d45a200170a4181c1c4030020001950340d59580c4400500301c40b2511420381c2c0700d103101d0032000850071000c680030703840c20643e00025055500f00404d00300301300780202d061400e040f1051400227502d1106c0c0112603c1d40724819401c21400c0707510304070004054541c01d48a21024007994140b5aa40300d411010b40d010758199180a43c2141c2580c2125216040c10007000c0da085400700c4c86800395540206030301c861120103e008070b10308001400c01b0a482401e0007060351098140d445944a4070040340c3d580c0c4e0350100c000f680c401c15076940946480510080e131072185c006401248 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 648516294 1250 648515044 648515047
    0x315060e010e0907121b0801060501141215061204051f0207150507030e031215030a050d080a0e0d0201150f03020d0611070b04111809060612010b0406060c05070b 71
    0xd60b5000007840300a940154124845c0d4551928002d00340d450101d042095450362140300081310318040d07111b00300321003080c0c17a07108505080d084503440340d00c9140f244010760300c000307408034811a20b03041c490340080d180079090503e400c1001304100000341040b1800c80c4c59034007580072440b8000000c144508881c1e00c0040a5040101641d180d01c080803005105a180c5aa1031000850f401c2c4a0f41011484602410a0301d0790340c29040c190030144041121400a60103006222112070300340020b84624581c1c008000d800001e0b2001000c4801000c0513151001e05070310360000844200d41400b0900005440341c00000e16480078006a1402140342e80c0060000e104003d02040540c42d81821420041c0c1d01030400501d2180300b6140c0b05060140c107801801543c08901004104039010a500c00650710407520030720240e107652850350b0f40200440799424141c0210340800c01c07506081c001c0344407680711400046140c4201310003007022504c0740e501c480001150380800109105092010102406240c031049 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 648517544 1250 648516294 648516301
    0x10c0e03061f1a0705010b0a05030a0303020c031306080412020f1203060d0501110409240306151a0d05090706020618011b030905010b091b0904060315060e010e 70
    0x2030303201c160007050b00d00841c01c80a0440340204071000780c0700160004070346440c0b01ea4220803541003a9080000211800c1d843c00314081551300d00713a684401141c10090041c500d549240d94102c01035004014a030980f403000340320103030310300d81c0c0d43e0010f03005400580d0381d00801c0e29207824001d480c50101c414000c25500254074034280c0000104003410449501030b18569251550f50109070314049081d00540654a4031103c1000300d0050700c0100308072803c002d13050111001041c1d40c01e601180001003103c6c504103144003040040d034560420343c4040e008502c2d11442943c0e07160031002408400060845c030480000307150841c1c040c24860f454016069000514401d810000060b5503698080c02d51003180b030141c41c000b04a0002508001d09600042c01c01843c448103c00c00900a821030b007808132025402c045001d40e090070000c1c0703032610aa4680c42c52030400f000341010788400c1c1e070040d14050f40240d12984040007096a400403100b800e90741e41800969103103000000490b061041e04030202094520782403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 648518794 1250 648517544 648517549
    0x912031b02071202030a06020a0f200606102c181519080f0706090e07080604020d060b0c0d090510020304051e040f060603050903040f090c0912060e010c0e 68
    0x50010f4682c0314550300341040700c60002030700e0b10f0b804100c02040e1500000d0710764000741e03201c4a0b040b18a121901c039501a116413040d050700000342c10b0900101e9502520005840e441c000001c50001c42e69800c0c174803403170f4282d400341c4040d44030300d00e040800b40c0020358001c04840c18030b100c903000b0b031090982000059041220005000e008066550b610468501d2403c21b0451030b0800540010f200840841d1603040710800483d8440905108481c00718a400710f000890b101d520000e544210002c7e900e40030190f0b80c05c0304203c0207402c10b10340c50694682d10100882c08030b005400810001c61010002c1909406455000300811400d800082c040c8945004907064a5000015501540d0302140c0c064251a40c8203900d003075180d41070540f01d80c400e04200d208403403046954010015201c05a40a000c6641d818118036582d101e188640c0e400d1030f9040500300940000d5901188081c0800d24250798030356540d165070141c10391402c2040e100d496485001d14a041400d2160701d51010300c9080030006d00d100c0400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 648520044 1250 648518794 648518803
    0x30603020f061315050c0f011407090e0612160f0504050a020c03120a021201260706020a170f07081305100507080702010e03071814011212050d0912031b02 68
    0x4e108040340e51981c181c114140100d013550f0b50148580226801c00c80b502c8011400b03040c452242582801e160f801007501076101d080400146c410001031208d26465510600100d00d280001070201d0f409980c0b1291500301400c01043d00038001417035480403590400e0108001c4440280c02d00b0300d02ca1041000d00c010034404000c1d100d105007a010040010ba5503d003000c401f0744900944540c6c0100328000101d0f07038001078070b0000840c200e60004081048403190b8100da40313141d80c2c0116009a0301c50541403000429850b099139240d0301452030981807103840d01c0070000310b40282c48104c03a08000481c2041c3e903e01240d09810040100311110280e8400004000d440d920030303440060209440040c41d40d0959000d12040e8009150141c02c0710150b59554480111103490911202c1056040a0b001e26100614488480c162040074100100c401800d41d00c03081003030350011020060010030b11460803080171511910107070038001c0d0b0f1840848030b440d0000600700d900f0b201c00c5c500e140c86451000141039a0000c0d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 648521294 1250 648520044 648520049
    0xd021e0a020d1d09040c030302063403020424020d0206100620070e22110d2105120105040515040c030b09040501020702030c010203030403170a1803030603020f0613 72
    0x500e1281d1010f0003c0b41084041c8080d00340ba081036410060104103d107450070038081301d00070340c2070f55038684400032020020200881c2204025101c50384800b0344414410560b4000318990500600c1c195403091482041110b612143c02d00d1481818602c90843d010b02120f0782d04981880606494079003030202c8140d20307085011343c0d81080090303400410000040c01080c0340020404049031230711559642c5010030700700d003125441c5243c10480101210240322202034001140d1008401c0240c9915105004005e08010010b07078100000b000d00c20400c0c2c0d2001031841c410000c40e941c2c40e6864500c01c09c0d840c60214183d202c0f5010324a00b50030042d140f01c250070340121003001200c02240c08580720404801800c21602da00b0b50145421050000b0040158000c0030001c4c070950560368002c6240b00166100c1c0812a8080c01040d4100b4141c04c2d48000400c031154003140003200010568403012403202c510b5512041100403070750301ca106106501c0e1260304030310b07000000c032400c61600081d0510310420f0710991 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 648522544 1250 648521294 648521297
    0x209040f050a2007080d15090222090e0303131a15100f0210090201050408070e062437170609060f01030b060405060f0304120f0c14120d021e0a020d 65
    0xc030b003031f04260901c804121000b0044680155160b2101040403c9103000c00d452000c18115480c81c0058440c0c200d00070300d00014011005103003942d442d02c1c4406c41304080400e044070034038802c075211340403990301490981c050404504011a4141501d09000070903082c01081c105000c0f0054106454030350020741108000010700700800e070f4142600c01038501e402030740c00101d15802214400304145019007a1544505422034050504440c00d0942492010082000f254840010800c0e00358030508c07075161090304454084070035840042c0d0503014442c50303004031600340001c2c000750140040c0d0600003101508201c0403608900700e0300b07050000070008600b00800c241490384442c02101d4569902d01910003c0ca0b010b000d480e600d40f100141100f03240e204440c00c64400c00c49510003440f0b9031140d1403240a51040ba01c440511b0515612141d00e40c0e00d10340781803031480c8149030007020042c0b800c0d8064003481484813409070321202c0c1c1c40301c040d81c0100d103a014032911403000c1c000d1144069000035120f04c4550503 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 648523794 1250 648522544 648522551
    0x314070f150c1e110607022110110703020f010c0e1513150807020105220f0210032c0307060509030c0d0906080f1302040209040f050a2007080d 63
    0x11001e080e5200d840410b0003030074084400300c041d8883c8910300c4a10a0440c464000c005040000343c0030803505005005000e50408019030300038481c0c1540490b03c03401001c40b2012107046800400300101540d40744183d441a030b01c0081022400c040d01001800c80c20045000207200d4010300020092071040501603192040301c041e03070643c1e0292440000c54180f684204141c000e2540c884a0150b204545080241c0016594400150fa00792040c42094056803440121400040c004050b0300c0e240b4264100580b01c0d2199a49248016030315260449c6110410b034402203100c581007040141890111480c1c510300218038151890710702004022225405d03401a00028036440da075810a03d13500811381500014410b80c1503503d40c45401503604e0003228015a00c48585a8031f0700c140d443d5030b000c10350f05200d00c0e6154060b00c500600d450f0b00546660840030f0300000b4081c41d00f41c20001514001da500b0102641d0718004296001450001e8a20701c00c60b5468803440c140480d81c4a2a06114000b442c42070f8555 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 648525044 1250 648523794 648523829
    0x901030209090f0403110601061b1406041a060103090203191e060906050a110a0809010b1e100516061a0a150f020115180b04090c0314070f 61
    0x680d06560200d4009400c1c101185840000184080402d0341c00794003007070b071480ca0318988400008005042c2c40381e99454100d510715141d0a1508440da1144c00c9442004074a950540c10004201c0140b00754064400070b0070520b40c0b461140024580074026504040c01c118006000d40c40c00100e045283d809140d840502e424181041d030901c1030380502022024000540b960305000641e00300e004014000c0d4420045030b1a20b040700070840e451802d980c46002c2041c46103000403030181c8401a4440d8851001040038041a000035040300140c440160344032840c400824002c0c100036405441890150a100b0b1800664004428800c9550f80b00200f9071030715101840c030800000030841424100161a5078181620792070394580aa00300080c90001850460201c19100c3c41405428251070718100f44038402c90512000360705251038040710646103078961203070795850384030b81c821410f40901500305000c1a509510700030020201e144898090b03039001a10a1002220355210101165038038950210b1104 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 648526294 1250 648525044 648525047
    0x50904020f0402070f0b01060f09030f1406090f060a0c050403121101020a030b091303090b09120a030804020310060f091d06360d030905030f0706020409050c03040f02060901 76
    0x400740d10b50820f001188070400c01c0700c0c2c0b000d03506449204800c59003039681c807070808854104072800720720000707546030703808001140796048542507032405541410b9460920500340741c5002c10a44450070b96501003072640061110621401e0b030080c3e103102e400c4c030410b85d5141c0010034600480c00050906200c040c01200c6881c003d450307825840c680c84000313540743e2546032030140c01011554051405070a0301d030009000c40b820f02d0950140194076864580605051411101180d0841500d094204c500c1c1b420410005200304003d08056119550b104241d1600c1e20526042c00c0b01407d0708040385060980500000c44800050000d55400034800258005030103111541c003003812481c80e03070078000c103018864911002182601c050881000503d10340c28804504542c807080d1040405064200004a144151098001e424405d0050088a0910142100c0d0b20b026520440382160101c2d40010100041803060260650003031302900e0b018114580b50f140c4406910340110028410100090100c409a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 648527544 1250 648526294 648526309
    0x9012105010603061508131118010305061e13030507020402070f39030b0702030919080c0d112b0302012009030a08030a0f020307020c18070905090402 66
    0x246001445956590800074004041c0f45c05100c0e40003080d08800c951103030217240c2c514010904075100d003020342a686c640c1c0a43e5246e810070182d00000c40700d5200c5615041081060103107000314060502410036240d480e0031454540c024180349c541541c10030024a100644c4e00c3ca50b01c1d0107040441e40c41d166403002070001d02c511100246400c204402e4401840550040d400038501201d55030001c1d060300104902e180c8000340100c400c1c1d100c8180e41480081d401094060300901540101c0741050011400a4000410710000c80e00303205c140c1404001131082004030000380d407416100c074045841d01e61a40c140300130071209814000c1c90403040010b9140122401c04010321049804c4600101c11841c000340070300100c48441c00348060342903c558101050034119440300303000400901e0141400c0d5a042c0140c0c00c000c00141c400c554502e0151180001c0340000c5115600039405001c071100c00008129250080c400c250000300402d03000c1002e45504068864240c0f03d0846004400c0d60b20351000074001c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 648528794 1250 648527544 648527597
    0x420060409020a0906090f1707030b090a0507050607150b010903060e0d020c120604230105133003110f0d06030b0108060708040206160b0c09120309060901 68
    0x100500080004200e880766001d060010303480d944a000c01e5680d54001c54804c42c95000c0c850903d591144100004182c406180c82c190001809a441c081e0f542d85a011704881d044a09400300d130400c070307001e1003042b20030702921001d081d0840741c080c00c080c495155070007561000e1082d41d81c1c007942d039030032300c0340c02da0240c0140002940d0200d401c0c04005000f940381900c40013840c0c2180090f01c154200740015103003000c1d6210840900030011315642e511501d45010314001112240216410003450120029080c003800344241c3c231105000d42074a10610b4001d024010841c0342034031804411014480d0201d0204925543ca9010f01d000b240080d450341c0d513402e8030301c83c1404e4488000c01c006604104080b9a030007000c1102c0c000c0301081541d031383e101c00c990346400045075614001035035007000400602e000c0010b0700f500d403044c078480060003915a80d0803180b610250b4640400c03c1020402c2085450514031154646140340301039414003284101044070340c062280c1c0181400300b9a007070282c80c0c40a00c030f072101c0c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 648530044 1250 648528794 648528799
    0x403050a110d140d0f02010911041116110a060c031e1202220803040b03040b040f020402030a09050c060a2f12040504141509042f040507030c05030420 66
    0x40043d80c1d02c2580c0d5078031400080d22020420100c62113000c5070041c400c942c0a075400903c42070309240100c0800000303081c4d2054030300c203141d000d00083e41c8514201c0600c0c61054840c1c500d501c200d01c1041c00b0020010003c0d80b050301041901c0c5e92140009a01120112050340f00021a1132820282c400c00d40d043e0183c491900b100b61300c0810341c0010f8620358510110900c04550741d0050030f03500c070716410344c49120700d0044082c640010408100002c54000103a40c0c8580618a903400390441c1d940002e00b82c0c0c0c0281c80070405d032903d450b122024003405000c0c030b40c14514100c401503e082803d11018242d03124940ca0120041c04280c003101d654403000030840c49102c0310704186c61704011b41091606880c2c2240c01824001c0f45008601c07401440e50496090245070300c8052403454940301c4041065140005100b01d40706083c0b001905040d03480100800b01d07086101c1c0000c014400c01009100450314000d020a04250a25827841c6c07109400c68101c07604142c1100813002403c0b1042e08504a084511080e2038 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 648531294 1250 648530044 648530063
    0x20604090f0204091508150703060b070b090729030604020903030a090e0901051e04020109030c06050a0e0312040b220b030403030e010b060a2a0303050402030d050403050a110d 77
    0x1003207000e41d0700601c00e031901400e04010401640050141c642143d00a050a95201c01212014070b14101d0805e40c0c44203075881c1c0400d0480c1c44524807e642d070856141162040f00321824010103903010b000e580d024060380c4251a035030842e001003061241801c2420300702d1007140040400e11540300e5030102c0b021001c0150807280e4409801000800b0400300c3d1160b0309146200b500402c1c2b03418010300030039005684441c0c07000000c030403481d904240c1040103003049042c0712910700c001002903d0038002d0401071106440f00f0341c44000035078018040601a03001140302e034202c14001d0045921140070394060303d1080b9405e544a507214a804251340040c2240d80d000c1c1955a0000030301c0b0300c030a0009501c500d12a42d0140280e940050085e400d135400702c90312541c810400d2101ca1080c80c450055081040000101e4030444d0a24828445442130400d03070903000691144c0821065040c102705090b40908203141c0b840c43c061a503100d00d17031545503221009011842005491a0954500e01030500046e001680034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 648532544 1250 648531294 648531311
    0x706060320031b1020071e0501031503031b06020f0406031406090106230c2508030904020d0e0d02010c1107182a02011e09150902060409 60
    0x160600400e08030720511a200d20400c989084052440700c060a040103010389401c9030461509071502045100c1095160380320441240403040100901d4008040c1c5440014a1191143c4041098101500107905050034070a60303000062030320240030f0441e07406151410394450750081d0084100c1c40b9030000f62489002107500c804a0354154010012509207403800c0102d10b14180e81c03449007100880300d442e032000c02200100100d500a070440b500820740c12440b0302030b010320f400e504034070760f045410003003880c0e404142d400960004030302d0030141017000041400d10032031401c5001c55507803040b0b0b10100d00550300416006080c88440e04284400300947c402d9611103c800c1d08000d000704a203042500004000b0a010201c500f00821210180c3d002204204c1c950514050034201a01180401044070704c64001607070254030540f44021040d80c4503a0020648503407824a52051260110700d280032185445440b6002038000080300040d0050300700041514100390000134080d016580c04880746a0424105 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 648533794 1250 648532544 648532583
    0xf10051003020301150e10030b011202070b01080c0a0305030301090905070f090510090606050d020c030909010b211501120f02030a140906090a0b100b07080d0b03010c0e0607060603 79
    0x3d14160761910350504031042901900325807480440e50703425003014014194000310707486a0065018200d06040c50b072400815112142c00f264040d030b005884540b455401440f00c203409200c10900a24215580b42002e810368403450b03120311041c0300e520091944c89050104000090007484d004021800007210a203031380f00c03070b0800138100850b4240681e004c040000b082030b0f40e86110360002e4460030390b540e0b41803026070b1582100030f601000031818603200c18845a5001c0e9a094461030107448990101504c0e07140000404000d44451802c0d580d40c04422002c0040c040e0004161400f441000d2030224640440030034001e0080c028801c1d18000280000708200324141d45c1e4025154002c24030114855582d0368002c000d44a07042078030b00d0303c400d80080d110f0101003880001c0301703500074101d020007011056035180405200d0340010001c503024400480c5a5094141c0351207106c4802c40160004c2c04070000c00d007401010740c10044403040c42801d0102c1c2e4081481107940c0080302455000e0407003130200c2558440c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 648535044 1250 648533794 648533797
    0x90115060c29180a08040501180504020403060606020d030504110d260415020a020904170d0912030605031501060f030b120a061b090909210801031b030b0f1005100302 73
    0x90f48074112000602800c4140b00005056610982012078030b814242041d004454034034114400e611121a480c0c1c0102e0207039900c0c801040190710980c00003401c0c0d0702d0040b0281c1400800892241030616240800000c41c4020600600300b00c8100c4550f200001e16280c00d9091030040010385181904403117001e800003900038000c1042d80ca04010790040030480090480e61040843c03402508400c142c004100001e0030018800901d5000c5124641080e6a4800000880e2a0071a007510042410b8201c0d0500503058800d0501800c402d03800b5100182c0b070300311110303400c090600c6080c00300142074118082040c030075400450f5034400100b01104003294807503215500c080c000e00030750b40306190000744403441e4801c240744605030641d9100e9003003182c40c11031103d005010254060b5040001c0c04110150710f0030300071000e01d02415607101c10320b041d410350502c5a41ea030344c2542c0a02183c2c3c0b40200600110b454036411079402410b050460b4056035548200615451050f44680d805c5091240780904c80ca81580 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 648536294 1250 648535044 648535051
    0x70804050f0102070809060c0c0904050718020c0604030c032606041103100314150f0406050603010e150a061d150102120a0e010c0b010f0806090115060c29 68
    0x9044407440d001504145080784602c103002400300c901007000d0b0300d40b402d0140c0a050703020340c104160341907994001c02042c50743c1011181165160041201402140012a0038840c0c400c0f043c001141004103183c8090b680e55000303003019043c80070707004106080503c9007295541e44520915a4002040d4405520340801c5060f200544194208400310303200180c44001d43e84076080040c1454010b51440e10380304250344000100180c0c0d806904401c800301c015400c0c503a4021070304a11826403078500303410520103c520245c001031080e4101000c00e1812180016429000003040d204915903803541c4078000001c090300c1d441001d00e008841f2090200c2120f11500314485c0340c04d01e082e1442c2030581c8004903110b40300c0c65021280c3d04000d104143c24188507031744000c202101818240b80b9644541c45041558909074000c02e02240748400a0090020500643d0b8011640344002e004921100e664110a501180540307401c200d0307543c191070280075011019400040d015040c1603040b10313210010a20181084 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 648537544 1250 648536294 648536303
    0x70320091318030813050a08030903041a0309011a091513050405060907080604021804060b0a03110414101202010c08030a1b05070506010e13021e041112060f01030212070804 76
    0x4c200180d0071070340d074820f000303001030344640139010a00c2c080d070320160681c1000d0715800e01c0c0d200c10b00002c6007620307440d1858484150000c0f901d680301d151082c1180c3c2994800303250504202a502c41c3c840803070729482c1541c0c0e0410300c40450600019268408110340403001a4581411800d0009005c148400070074464090301c0743c7c900748d810700c81c1c0368200d403641d816050301c000390040c031039540300d40c8040c924604141e0400c3c4a00400300e0040340200010303160011540040e9002c04004a40c00c4540c40e0038130540a40030a0404488420300c1c002c002c040c00240c8031b10442740708d030848246034002c44e846190010400d99000c200b0035100d003000e491940081240361030540f51010004030111889002c0c0e0300781c1c2d400a130f000004050302d80c04d003400d9111020000d00541400c05d106c500840041c1c0e64031500c10200300164000d603d030340d80c4000410080c0c030703030200c03c04044880c1040707480b4916403140580c0781d022006460003481c110aa000480013485541a00c070f0280c2028400d100a4035480408580114000c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 648538794 1250 648537544 648537557
    0xe01020d06051207060c080304060b120f07060e0102060115020111041701060906080c122806050c04030f080c0325020117070509040504020d0c08070e07032009131803 73
    0x1141d4005039500d50ba800b940c4081b0300116013041c00207901c14020340e8480e20504000c81d40c1c030850800304000b00d4a14031200b06940000f00c401005541c100800d0300108813914180403d000d40c7d20001c0c1d00d401040c003800182101d22140820894000d4200c0d2034600442d62480d6550b0390380d11400352400c11080c42c981069420441c00045e54402e80c0600e07000d4640f00005001c44001800411088030329103401c1c0852802098604812502c0407090402109140342017881c04000600e0b14000f150700090002c034903500144014404910340d0940c402501d640701070066665208004824950b01804001840106800c000103565950407406828014800c1c0c0714001c0e54034452814901c10903003104d08000151080c01082c81d24071706030704020780040c0050100140b074046034991044001c29a00100b14660100310b00b008841130350301600d82e210b062840d08001c07005101d000380311060340c81c00b610941888007040590160f501d03588a0ba08820800340c0420141d2100f0f80444050380ca404019000301c0d81 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 648540044 1250 648538794 648538819
    0x21160e04050105060324040c02010b1309080a200d11010b0109140d060b04110a2318040f0f06080d0518010c210215061e01050a030e01020d0605 63
    0x105801582d042e1040100f0280c02c43d81c54000125220190b018a400d50000d1410650001d464074401c0f401011541c0d0f0010600b40c85410500110340c80c0012103c801c68940104000400c0da41c50641c0c1c452641d9241030002801c16010604010040c1a1400401d01645640e81b026942111400c0400f45d02400203100c0203405000654030300319a80709000420407031483d0f98880c0c1ca0070400080d0b20314031801000a4296090020808a480c007945582940c02d00103410540542c02c20070018040c41c101501c0e50144002c103100c0c4415010b028548159420018000e55032a685d40c0c005500c02ca0700081d0400c05036103d105890060110340c03007041958011030041002030740c0314000311703440123404044400c0c074004031400441d6141c0c02c2500c00d89800000d0010400e55444a140070749071803210f580104030b508502080307084c0d034031000f0381003500c1004c841111079041c410f1402d5090004409092403519550780310000d4001e416451130380340030343d40b0003d80004c100300d8952042d4191441a00c008240300b2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 648541294 1250 648540044 648540049
    0xa14190b0702210606040209030316060504021f0210051003080a020d0809070501320708030103020102070909020f01030c0e10080f0105060703211803050901021204050a03030521160e 80
    0xd0f40c14a00c1e5409400a0000615a0a2a400070481048043c086134a8030340c10f803401008003c0100e204032641503da4041c001175192003081d00480a041c2e045030000c0200c076050282d0769850312000c0c0e0020035200c20018000f00c01080d1040000e5420541442d07554016200003521032030003002080201d2181d10115502d2007001424100740c0b01e041c0c40310140d4400c80b1144100d0303026904884c3e0b400300000040340018101240107008414441e6000301d84950441c0300190030700340550044d007400c0c0c0c600014100540c0e00d00040c0d80310040e084c02d00051002084404440c6403421000075504108814103004410303034400c840d14400c26088080d41030503625002081a00c3c07051034405000140c80c0040e080442c401c40d108000352424400000402e501182183c1e02030322035150069010900c04a07800d8440e50301484240c01d88a80c011529140c2030a200010381d02c594240805010001c02280c0703141074070440140c1c10700c40c0c94204074640c0a841c00c40072050300c400b020000240080c142513600103071170 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 648542544 1250 648541294 648541339
    0x51017090c240c030406051918140a0806130302010b0f0312161703090c041116021504080c10050c06011401120504200f0a14190b0702 59
    0x80d500401c0641c0901c25180d10380e01c10402c036150760100010402407403d81900400060000700116200c2c00c1d01d80f21400e088c0764031242c90041603028800c501203030311008000080079105403060031600400143c8090007051101c015074019903940e1140c2d10500000361281115294154441e40c02400306a11342d20038407000400c1210b515400d40c1c041c485a0405941c1030001c3c11801401030358001c43e0710b01c1600d0303288031641e400021028150380041801401c0c5000d00560f642c081007545c042c001e000c8000c00c08401441a8051903407025982ea103c1c800f199181c1010761946424501100c1d210f54035000030355114110489003d01c507a10014102e40b104c1d0080007610031180c42900038100c00ea10308800c4401108070f049501e410000f503846807681e1030019100d1140030b01c0c01081c18400708070022140714421100f0b00700e024401c82d0040c010001c2e940e070303044030364090311041d1405401c205050004107861440943c85400300305801a004500490101c002d0886140201e81c1c0f00d40c940703800b1341c42c084103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 648543794 1250 648542544 648542563
    0xc1f0c0302180d0f29062e180f08010b090705221d01060f09030f150e060f0a0516023d06080c0f0303120a020405101709 53
    0x9000741000301c1921071416000c5500058025502000580c03800d96822805801010301a07860028100c801c00381c180840c4465544001c0a0714010f10b22100381c1444420000c03034030580c2c0c0654200580c7c007000355105400e09900d20b00212200300a1645a244802c20381020303010719180d642c60300c1303a10701c118905402c01602424460700da00d40352691505d1601c0402e00a11403010b0140d0110400144280c1801310040340e802905602030030550400c0703402054052120a074408101c41c02c0014804121428101070400f50300042030100c0c03020f4400260090040318001c0c550318010fa03400c02c11000008001e00c2d100c0d150f0007204002554a18240c0007043c01e00e40c1c0c04100517403208502c0069510150050f03042c28017071116200d500e2454900790060072840800315006a84c4800c0c0400c02d003401080402114801200d12164481116012950b240039840d03890007100c900a01042041300c231541106c02400e070181c8046a000c2150300050880340a4114030210702d0320600000f03150100c00300d1018417 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 648545044 1250 648543794 648543817
    0x307060506091003060c051e0a110303011a03060f120f0c0d080a11010920191d0714040f030b0907060203030a0e1c0905031c02030307030f020c1f0c0302 67
    0x1040d01359200d003c0108071031089402406030030018001003120848215500102c08002d00e0f03510a00350700300401c41020350302c0e6221503074420300040c03040a810511088020500005c030301e803aa07803510002400349500d4000b081c1c004c3c80001c030b0400c04410114cc0f041024400100b00c5010701459070a012250000c144042c2203a2410b200c0188020301c104844012944080008103000c4020303160000480c440d880d20364031b0005520311155030703401e04138007e40d810b80c1150301300c061143c644500c0440012250060f0b414240b03010000a440f680101240782d01070f11060b4105880300d486542d41c02e020200c0f40010f0b5600f0150100042154100107041c1c016240c180e40514199120481e6480140850040c0b02d4094010482402002100e50b03110140300c046540d0b900c00010f217460203260501c120340514041002640d800181d40f00e400000712038101c1880d2400149000f04e60ba888002802100640303403403406a040b401ca400e10000101c0901001244410441c44140ba0350070390803441690350340710 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 648546294 1250 648545044 648545071
    0x106230d09020d17031501080903091009090207110405060301180b07050c1f0b031504020f06070501020d0501060909020a090905040203070807080a05070f030308040204240602030706050609 83
    0x80c40e8055641160400034805082d040c040e102e1940c6070160200507080d0350402480100400240003100540042c04500a0a01100d1070424801c10b544900c5000841409024a0300881c8145071007002c01d10014140d5040031074983c0c1180c074000c28022030503003880e4415400c000125109184c18865401c62481100340804066010383d58030300d00000042c942004e100b0244001c1c0424201407150f201d010701d0f2900c80700000c0c000c0c0380c040d0017200e0195541038005d512024000700701c5406501d81a0f000f0382c04540d00115202a100010b88510905c140148154004551442d111420b0b40016050303d1031915541080d649500d003110883c0621084000080d005140400c103003049035001603001800681035668039911041040d14200982d030121f001c660084030200188007042c00004050002200120145855520010800107014001900c210b0ba50404500001008611360440101c14080d40a4843d903428002c0e40b03a0700a50400d60f912420240052103501e400070b103440c8200104451398 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 648547544 1250 648546294 648546307
    0x12030403122d090b041413050615030a09080403050633060d02192007050a050405090705040e10050901020306010c03050a0c0f061b08060f0d0512040e010623 69
    0x100c1d940b02c411a005401d2140700c49003c64060f5940c80204080d10401010303c10813084403090010742100071000d100e42d02d2500050150703560300c0c5031140c0c0c10206200b03081b03502c13611030400381cbc8021b00ca130101c0101a154001000010000041601c80c89407250007440c1200034a4602540360703031951401800052140400f0f2490980f038480301409056a00410043c2011204060320ac1c0d1540b0254421001c5030f01821080080183e10220400001040020307044242c508404031740c076044c007801000c0c4074648400c0003824004080000b50001d01c0014000d101460030f00070044e840e100d5445c001440541007100040c1001b4050086030f000d4001030351340b500d0030700d02600c0c21111504819808010000c60345107503008200c0d40d10b0f080c0c0c44540280750005804003503581c9a0030200d20008200180900201001002e0b80c0d031016000401a0a4940200011036440e0050030310317614904440d580d280118011402507844218541603801e0f64480780c44a580401810302c01c01d00c1e43c011070880203400c004a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 648548794 1250 648547544 648547607
    0x6092a05010f02161409010b070308070509010302090d061a0d0c0605090315161704050d05030c070b040807030206010501021b040c12020d0b100e010e0409030903021203040312 77
    0xd0100a0b26403043e5a00c000441e02200300d50031007540100303140740c008203000e4098500000300c036004003030000b4002d161030304683e009810740344024040c0303090180200d12115142d0103a011101013540040441c02c00d44070320701c1c2070001800048405007008a8407400701c01d240c1007000c0002542c40d001096003a4440c44c0260483c0d4031741c050603015406014140c00411844c8402908a0040341070400312800c0b2402e840c40100260942d5400031500b0401d0740510020030070101d03001280190740c4c41c005903240d0314034028103098452500001c101200701000c2100b400404009810702e24400d07401d58003141d9a510049995210004802d150500c0f416200c1006280c2035001c2020400f860400c2200c050707042c184601281c01caa8580309003e9180e07042c0c08800e2400400c80000c05100b030611051001c9c103040004c042ea00070503040750065170ba0741c0030310086c90f00488070740c4001d65000b072602c00603080c003203030301a204e0700144400c90751010040252212035020f041b0b03030900c45144492882c4d080c6020300f0b8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 648550044 1250 648548794 648548807
    0x3060c0c031201080601081203010b031306180614010801060f0909020123090a17030a050c0a050a0c03150507140901030b03061602070801020c0d050304060b0405010306092a0501 78
    0x4000c11944010040600ca0106800c1c28500070440b550150516602d020046410480c0c000070200701500c082006102946210301626004a98021410180006071600d0b00081c120010048580e000900b01ca4041040c00e800c0f0b001c0610003549a0845a60b03a0303443e041c02d8440302d026005407004408000d00491049901c8800028014034102c0c0603410000080f5400a1051081440e030440000307020001c9d0030f04944a074010b091005003010311220210a0545074024110700c8000c000340040c140a6103401084494101354005c01a15600070749464240003841c158401225085548551090503881c80e100c0c00744207503416200e0007140b41100540d00410b0340071800d03d6060542d09e406103000c50314204082d61082c15040c0010380d9000300500080d00d004032aa004002903801000005008400400c604042182d42d003082901c1c1d40f03951400c10301070708921014540240c0b03000000402c2c0801500a0b030b41c0a030241d400d4020200c1d44900300030072007985105c25026404600300401c6154803e00c03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 648551294 1250 648550044 648550057
    0xa090b03121813050108010c0c0b0c0a12020f030916050a03140109050a051018020604030b0705040b07150e03070b010e070522062a0303200d1b05070203060c 69
    0x100e0410b904000c400101c10308400d50b07001c0102582c034401030100034001d202d0408040b00074103000005204039a01c101008000400d0210790720404200c54510034050788900c1c04ca0074071702d002503407500c24406880d04290000c0f92070001602c5501595182500416544c0781661400352051544030b003162034100d001d51440c150964250750b00c403560780c04240248440340b61180b242c00500300c4900c0d07842505007030369035010300100403d1480345440e00682e83c9404640459921400c0d80c2c0c84da5071101c5081c1c3d0140120b60080540e40800108607080040700c201c008100401000304000c010070600f401c60ba40c0c003540c20010f0900c034400d001413055488901c0003590104c160700d0200d1510020b0000b840702c1c15205400003108005016060080503080192800d031110018069070354802900010854442d0034840a4241a500c640c0f20340d03894078145003c00100031200c101551100c0186451008011410341c100d00d1014a00c040500325104004481c1c4058005005012546402800519a5101e003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 648552544 1250 648551294 648551317
    0x619020d0c2f090906061e01120903030207020d03021515010804140f070b07060c0f0813030216081c110c19030f0b07300518010e03090a090b0312 64
    0xa8004881c5540c0c061405200da02d015001d004c050401b5014000b481e45a0090b4600490760035000b10007a0340c0c0300120000c0c00d0303030056001c0b85415007410700760300901c100c2d0f0020f9084000b070070171641499000a82d001521b009184200001d0760703140d400242c0944419196030001e001100840c020404002d00607000003040700a441d244040c0c2c601c1c981c82c103140342c2c2c4040b807002008580c00303040c0440c51003070010f466041c4c2480c48494180440c01450004010486201c0750301a0303c145080c58070800540006000c6a050b61051a454190240c0e484901c225000740c8070041c44403001032588100ea0300c1d021a150400101484450401000031002848040b032032554071191001010910150000c01d407580038403040003050400f020006d00004001d03d45c02007400031700040b41880a9624544e00101c24076090003c1c0944416001400554030709440ca5640c0d070030000741441161011006007a95181180d01705521951400c0e003a06481f00002420381c5900011100c8084165400c010000031654 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 648553794 1250 648552544 648552623
    0x3001060f02280f15020d0f0b031b0616020414090c0102010603020306012303030f040509090102030105060708090325080c120d141b0106030303051e0103020f06090619020d0c 76
    0x1051400c130700700d03000030460000340f903121070b58055140c4040c0300d007288050042e000780c14003110004151020f10701c1b0b14400f6000311000203120a401c002c2040302d10070740b41d000304140900000c00800c0080d040044d110600e450140e4014074a0780c0d0b00500c51602266405009000030b0fa180c1a000940381d003050344400b191204803000d02c4200da9003400140a59174150864540310740c244000c0c030003060323001003000035141c0c4104010b0000b41c0d5a14280e032590742d407103400c0b039543d01d0b4040046800d20842d0703803041520300c11715034040c80301c035890b04454015652a502198502d00500c4100070720300c06056121042900541140300c650b41c4540401c10310b03512424140b0b494402e14441200c950060310481d03440d26591100c040c4105a458050190044810842c00c50a8024820040c2200308180300003449000f80c00d0098034541c9448040c1c90081500501a903110300b118046045060114a200001030081145540f5928010700e072260341660815210f00c80a007440581c1e00b420140c6448100d580c001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 648555044 1250 648553794 648553823
    0x521040e0408070c08160302040f090204020a27030209190605060c010c0201110a0516110d05010f06060206070903240903110706050405063001060f02280f 68
    0xe45500901407449860080c1e42c9107202d0600a880c038a050f00300c450aa0044c828810701c000074115a031013a660100c0700000c0d4000412488030080c040d4000c0250064008507001400d10382280c1c2c440c03c00d109042000131034140400c030140841086000c02913001c071114001c2076039000c0d0305444c40020b40210400144003510303400001c001d40c015125031556607440746010361040d0b5082c06441e10f082121a01541000c180150103007090241d0002e00000c071100110700ca051101000c4401e9488102904460045145003881340c0030304a40348102c03043ca4285800001e204e0320004001384075500b2503581d407074141d08554400c184e0101804044094403840f0795030003010034540c804c207000b2501c261076801e0351002a030100ca050000070740c8032100b8450148000c0145444030001c80300140c244e00004003a8191041c40301c04418440b03001c10119010340400031074002e820400c030820a440d10707021034101c400c43c60078a045c50a101419012010881015000000e0340c001c41107a403030348070b9508480b0101 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 648556294 1250 648555044 648555059
    0x102010506210f030313120e0a0603050a0b1905030601080a0c0e1305010f02090405160503070f0302070503041d0c07080706110904050708060111060f0c03040c270e0307052104 77
    0x7017042e5112141200c8213250002040544403004041d06403d080803041e1405407400a4213492542c400c40c0141510f80c400614484000d901030f21038a4001081c1c1810032894041c42200214036015450081c800e00f0004a29408006039000109034884507085d5890706003240b02410080141041c10f10300b061949070300000301c0038041c03400c2c8081201001070312101c5200410007075401c080c058012010441c11400700c42c43e408411250b01c80400d041810480035201022070091040200242c4940404540824000039060703520307080440e0806140465103c0c2d010702c80d0700e48103c901c02040c225040184c2c0b00020020740000608010740181d043c00c00e480c00b0003040c01e0311400c468840c0000c11007400c0040d01e41c1c202121030007107034803003004180c0d901d8805405444440c000d000b00010707200100000e0308000040f4410405130001c07540c13a0074101c0003400c00c00458040140b40541c058180000c03049040030000a8030256034010004054454030301103c80b0451590490048121504000200340c00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 648557544 1250 648556294 648556297
    0x110705011802150703080a0518060103080d060b04121205091801030606090207080405091302060f0405010305130b04020d0c08070b0d0507260702150f0402010e0102010506210f03 78
    0x1d050301428640d01031194030421450802c00c69811840b04410311048010a038007828050b40141d02400024203a1200345102081c000a643d02e0080c0b8461742c00044200311145001d880300d1030036840244a101d40f1a010414903020714007601d82d5903151000c00c0d0012642c06c001e4050356460a040c0341d49071401c1940450303030310f454040300910b401c21410010002c01c040d51051200030b00c011a401c60402106236250507140c0304611403140304141ca040410080444c448140105a600030841542c8040e1a540290503401501c0707400c0c0401e1804001840002c1c40c80c0c642200c0d940d00820750301d1680e9840d42002210901410282c5021000c20004240068104402d0016003801510a5101c10030b4044400590394001c01e5401005041640e2042800803003d1002c1d004d041520001c05036a5004030891419082003021400390340c01b1000d2006200284508a0046000383d8441d90071f13254203801a801e8403c256415604810f040420365103841c142400e0324440503003078084e0350780121180c074090701e103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 648558794 1250 648557544 648557561
    0x1c02030403020a02010f02161e17070303090e0c0d1503060e01020d0b0a05060f030a09080a08090d0c030219030314011d0901060f0302041d010912020f0105061311070501 74
    0x160f4801c003042c074103641e000b503283e000e8182148000c2c503156400310303a620401944c074410b00410400307210200307141100c00440c0c040500044c414150380d401150646940e507010b644030680214a0740322000c501c0704030350401ca41c411f082c99140c80f0714107589580c07590000c00e8180c2d01061109500e0314088001001c9000700c1032103440d117400140e202e450f40c42242045030741a02045201b1140701b1030801031511030b4010b441c01e603140b803910380ea22540c500000c4805010301c80801011154002500b81d00d6503045598507010b1825401120300e00303075031444151a050004000500541c0c4800c01800005004281001c28607102c0d180110303024542c0c1e400314034514820380084141d24a10000e42012190201c002d681c014a0b80c40240308082c5400170b000c05000d42800040d01803030b00c906440000300310030790000d41d2b4201c0a4008112003841401d1040b51103562211000040c0102c116803120008140202d90160310b0040c103500d4411600f25103000140401c4594880145040c4014008240207200e440074 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 648560044 1250 648558794 648558797
    0xd0f021816090b03090a060519020f07060b01020d0c14031209010b09070c0f1106090306131e03170406110a0c030e0a0b090f1f0302070605060d0302121c02030403 71
    0x21004003001c0c064129542a00004030030302c01401003061040000a00c2c416043d0440070004168580c00c03010529001c04d80d0301c80200743e0000030760038880d40c00340c0c00500425000d540c0c100541d40d8900b004a841781c41900f102d5000a181d02043d1010038020740031b044807900d41c901203038a42040c2565154411004403070607007059540f0111000c042c24250031282c2d01000c54600a16614050b030f840f40c081c07d2295201078642e45044c140e80b0f9031605c030b103802c69206800c000d08541c09440d10300b0081c11189402c560481742c0481a41c4200980322680c581104040d0303041e218840700d1410b4003490045268024000d0390503680311000e200002c0c45040040c1500c1d1341960311810b00c1030340d905019095110903182c1e41d01500344c503941000b80080701c00941d0002541104d000c0c0d400b000034800200700004040d16586480b03050440601090782507130040c40080d00c1004180002e80c0c5500422110780c1590f000503002d0780002d000c1c034558058400040511516000000351641085090304003260002c5a0480 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 648561151 1107 648560044 648560071
    0x3071502011815060918080304170723070312051308100f0f060803121003060c0c03110c060f0c150a24050d0f0218 51
    0x400d5071008000781030320350b82107810884000c00900f501d012000d440c081c400a0b000000c0d0082241180440c54034850021054a03010001c1d44001e108884016500e0385860301007103510064010140141e09a01d4006e21207a04100d280d10b01c1001c00185a1040604200281d14000800d030416528601580c0b1403d141c80491018040754009000c1800340c0b01c640c0c950556203500c0004002d0762802c0c14080007034810800000c07136102d40608001500708210a40307000d4580c04005401c401034407100d00d020344d60394403408200c4011400d0117001502000500c800d1680c000208900d000c03951000e00120b2449000203a41407241ca00340e403918550201e0341000010b41030007845440f4400b01c103080313410300d0102c11079001002c44007004110144090840048081c240102005071240030701044415500341d00c4113850340d0724101040360302036200120380000000c903081490080200c1100c20 = true := by decide +kernel

theorem cover : BRFrame.Cov 648381294 648561151 := by
  have h0 := BRFrame.cov_init 648381294
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648381294 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 648381294 ≤ n) (h2 : n < 648561151) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
