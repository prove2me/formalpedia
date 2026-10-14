-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3801
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:42:52.750572+00:00
-- url     : https://prove2.me/submissions/c0d4b581-35a8-47ed-ae44-8f76c5f3e4df

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 683453237 ≤ n < 683633093 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 683454487 1250 683453237 683453263
    0xa050108071d121e16080712140109050c030d1128051204140108010501020d030e0304090e0a0c120b040611090d0321110715110a020304060807020303070f050a020708 73
    0x8901907400300060402000065290191790800004e204a600218100080b6914415940c60540c80ca02d801c00b546644412580300c0c952900300c1010a11102084803104d040c000c8044c0c5154444110381550010032404526403160320401c850741015090416100648500ba00000d4550140741d403483d25020350454140070b000d00100e4100071800801082c05507904003424000c11a40c10540001d55404032400040105500c441080d04021801d004840180481d403405100c42181d8810180d0b980000c1c04003140d208101c05800540000f100c4141c049490f40000f09045503100c545403072001e4007048403421341c06242084422a140e85a540c900e800520a40320260390f10102c1c51052000300c80c0c80c0e0204400c03410481805100c01003c030481e0040d0303501074003200b281045825041c00429118039402c2c0d01110020b9403143d0280c001000e003045424035a24048a660740150482c0c40c0c0c0000c0c1c542c2004928500b003250031650054001d4802c0402c03510484040e0b6030f0307510036249041d070030380c1c0c000c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 683455737 1250 683454487 683454523
    0x105011a0f0c03070b0403270b160c03120507110303070f0209220c08100501180c140d15060906050711031c030509120c03120403200102090a050108071d12 68
    0xa0b441c0c03019552304424000441503c0c1c1130091801c1c110500500ca07205001d810074011415203000c114a05d01c500000d1600a03013246184800c106010740180d000490668680d414440d420406140000c1180c1034603900c1482d80d0301c81c04099081c04200d44015041a4000480d500351024040f41203005005880c083c1036603107000e518001903a03090078000c1c800c4904c118140303801031042c01e070098680c90360042d84101c00035040f20702480441c0c0b90b01041c82403c00b12400041c8101c0c1440b030b80e030400381d141c00004840005980e0340c0c96040d5140340c0641700c0d0301f0104200380440e5000c14800300c00c04506d550b024041d0781130000241c0284481d0655998818007007a40e44040c4140107804010000f409a206040c01d894001c203015882d5070380c0100c290205012410500003001c151056600c0c02c0b5400d403845880d6280d48180c4041d50207500302001560161750501c00c001541e61080702800c1c040c5049494094808610352407009040d001c0e180001d0300480c100003165042c038001c002211101d6440480 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 683456987 1250 683455737 683455757
    0x6080d08190e1005060613060e040603150e0706170a050a0207020301020d0c03050702070303020307120e060a050a0e0d03171b0c030309011a09010b0a021c110105011a0f0c03070b0403 80
    0x4480100e4801034105c50050304c3c1030048000c0c0442c2440c201042d181c8504100c9000420000054080c16040d00000c285150180054103a40183c0c0c05c0303542079251031001d42d83c030745071034501c00c5075000c00301002201c96180d000f0108564100710380c0000d400c14000000035241c4034654001c00d003642d0007507541c90a601d45d69044e10318580d5241c03158503040728152002d048040d255442c0250b40b40078460000d03140d001001d264007401d60055521030070366403010b806180c0328070b41180d0241041c3c01c0b08258101059601002454078600a003000e480503505444403c0d40845075445200e91b0750740100305180a42c0460b2103061484900409017400c40c0c044401542d44c1d140500080f800c0d40d2000390003d15206410907226000c0d560540c8040c15211614641c985540004004910341a03a61404100d207032040801d81d06240d80c4880110b429045010080c00755982e10300155051000501507900c2e010f1080c0300500c00c2d4010080100301317001404049904000f1944c4800b07034015010340d0120007060072448 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 683458237 1250 683456987 683457013
    0xe040c1508060f0f010e1314040c060f02011e090f0c2310050f0a030b13020a17040804091e021207080901270302030d09050606040e0106080d08190e 65
    0x6281c3c0d005500c1a04c030700f1070030301e05040040d0600030450300e564401c0404581070042541c0c540e100110507071625042105d81c0c101030819000c4121907000b62400103500351100c541c0a4014002c0e1810010000f105080380c0782544d002c0f0004000004c2e0480e0560a900e20410102d107010003903101502c40142c0c85d00454419820340e0081100c508ca4031402900c01441d1048000c0d0000f09443c00041d203140e15655504500034210014814000840e41c001215408002551004d41c007a244003051520f4102840c0b50f00f136a21060400d00301c40092500000300410b00089406400c1030302c5500507540c0d41100603140000501c1680c02c410b10070031044c860142000281544481410380102c1c61030002c105a103000f054000e4580e55545130341010089000c1d03540700b014401c004032400c02d00000070411901030149082030300c070f40e01921510b1065003482000510b01c0f0701072084400f00d9801030014100e503222a075003901d2400004000c140700f400d20a410a07812400781c041e81209502401c040c11455003900 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 683459487 1250 683458237 683458249
    0x501080c0a03081e0d051303120506030706050d020904020304051b150904020a050403081602030c0117041407031e0204110910110f030403050f190503040e040c150806 73
    0x20214480c0101e03020400202e29181c04444d030084007900a0810007030004e00e01440e6200e15115030f80c0e100e1400080204040c000864180c4d01031190351070b0600c1000c020700c802c1c180c0e030042d143c035681900081020024070340a4401884103102c501c4000d400e1044980000b001c070b800440b000c1da5150005a4030b03a01c12a40c0700082c002c1c600045420302e8000c0c0451410030218011544818040ca42c0014403030149070055090310002c42c0c0c01a802c541d91403010700110361242c04804120b000e4428101c12010075030190190852400c103101e0394010390354503500c030901842c0581c0c0e04000c06005003100440840c112080c6850080d00902030441c80345c0351403051204442492400703465a40f0103021104107a40d035030310700c00180c4030309141044c17407545100000c3d07090600d0303030b404000c5030b1000040c000204040442c0030350b4012002c00580f101010001c85481c0f030100c0e2100010105c1d0010042480005915034401d50000c0c0100d00b0504011f0712104a15503d0380201c1110020403400c004202d06440c1c50 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 683460737 1250 683459487 683459503
    0x6091302300f030c1f1e02070b070219060504061506020a0b060d020a0b0d11030109060806060d02030c12150a06050306150f010c02060f030408120a0c08040f061509050108 75
    0x803100a514000b50300c1080b64403178881008440c0e00030760000103018503070119000061450a9030300c40011140002004034001e600820f0120f5454003801d0000311000d0020a40e800484105903400c248070b4517507610103000349001841150000e6a44e40b40740315180549401c01c01808440d00102890001c5050140c051600100f1061040700d1450400d0300607125604880221080540103a0311859025100ca001c2d0814550300052600c000c000090040d4094124004484090742964801c0c2c03112004e2016a8008800180d01540480d0a44030b45003000701c04000407070300402c143c41d910341000722528a80c3d04107941d02801b2541314082440203103028408540c0280151803042040051040031032552440800481e050003c550320040c255200c110440342e0040000e49095603c0c0b42c00d140200c40d542081484c2da145503000d90014032003580343c0c82103094600301e6807281a926134580e502d410b00888001c0b01116200c5d107c48404040c41030709121a80900700e8400081519030610344064540b03080 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 683461987 1250 683460737 683460763
    0x80c06090607140a1724031513020a12030806010e0118231503070906110a0803060d0b1005150f091e10080f010e0609130230 55
    0x10740c0034021120740003840c1098540f10380010316101c001c40321080c0c41d01041d624000c8000901d07901001907020f051103a030085800300060fa800100c5807042456503801200b0454400d201446d0040307440085009400c840f1944001e040003509a111b031618141030098820807804514450140081c41d078101c0e9641000c0340c000e180207689008551904460301995214000030841e82c01105030115034541c581100c940c2c8003401ca0b07441c8842817011002503038001c81d403102c0041d0b80701002040191040f81a03410100c10603004086900d0151200308840d4000343c402907124411013560000a555102400d11441c103803032000f5041c1c0e14200c10710501041205642e1107803030040003035290301e040500a40e1401082a070320184180c002820f414014454150b61603402990000c50801c01903000030920b00ca034006003048905a40e942c42c0324140e009068a6503540040f0003400101554045c10b803800c0700500081040d400e20045050400d41d0410380e40318290784240707140090714180820402c0380c0400003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 683463237 1250 683461987 683461993
    0xf0b15150d09031107260d021209030304030b0c0306010f0201150e1b0f0408070b0909060103050601090f080a11030706090510020307050d0518040504050606060702061303080c0609 79
    0x2840142045129400300030307030016035032400942031600c505a03c1c085070500000300c607a59a21040d00c1d001c030282505004a248000c040c02c0c00b000ba0307003c2201034486500f90018000884002c0c14441c40340c11031004039805210611002020410000d1500e020b0402001c3d41aa0f03410f0101c001024007002c4a014019a0304242c1581c2c82c1d844008000d80403500b050b081c0300c01e143c4807030303440840340c000d030003c00144c508000c0303007854107441d045006108455140341112074141e0f4504481e00140200c1e40317880d610070810380008601d54080d40065511020525040d0303030341c0780c1b620086540146140c00650941d800780c00c1d0301041103010103c8081c102c8041b0001e015551030003800504a80da54003540d4007d84104c80070000150082041c1d464240d80542a0b80c904118202c000b4169000707441c0321020031503001c0308512035051034452580070300d4115018010640d0303610f042c4401640038240c226040a000c126195000750401e105501440c0b007036000c15a91a00360140071300d8602c014140080e550 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 683464487 1250 683463237 683463259
    0x15050106030e0c2b080c060a1409060402090a0e0102090a0306020408010f140a02071b080105191b0516020d0c0f1715070504050d030801150e030a0206090d0f0b15 71
    0x400356a907444582c00c4024804a0390302c0c2d640303005400341c020b1b02c0f88106144204402e00003e5100ba070840800c0c004000d03080e400503130b03503510300c0f9603100001d4802940006c801c1c0701251088d015900414a907910342c3c40090315250340c42011444284140c3d2007500c03456408a0148803052003030107003200d0940c3c4034030180140103c0b0201c1c2e096445c0060326600c00c082d80000d068080041c0c6441056030055200c00040e40b8a55800015020300002c407030504281900c2e841c485405455841510300b01c03102c5140103650038040c5601a21254000045000340d4140025480700580c1ca55940200d520700c191440388440c1c0c50000c00c3d40c17020610383c0260f503022005040c02460284c000880d000c60401c2c000035a1516202d10005036800d01c40c1e07810440d00b003c0e184030b0b80300a0540016403941243d1111100100c040b512071b10494a8500c2c030403813a9416000070003d040580341a501500d0a9107008108500303c03c1c43d556400c13015100c10504075035586481c405c0240001034940740a101e0030096038040510 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 683465737 1250 683464487 683464519
    0xf010f0903020c19170c01120203070c020f130204270903080f0601050405210f010209030c0d080d06120c08010504080703030207110406082b0503070c15050106030e0c 73
    0xa103038007403d89008544a110055810408162201c02170204074414028a441110441d44802c418208940030030350440601c0e13030600040c421a840341c4160740e034a000141c1039034200308512420561407a88003204c1d50303c1160242c10f920050005107803010154010101c40505038405240384088117100724504100200444d8100c0034469003d401090518110765a5200684040c0078070f8001d5904601140c0454186010516400240403444401c48039a9810151764030f00313034401c000309141c040e00440049a040d06050850442c0940325005040c100341400302d12908480c6507074000400d00406180100500c0007095002024100e400024402d600d8180c842050138496040e0060405600142c0c800500c01c24107000302d070400000308207101156952540310340e01c05038139008036480940c01507809840c8030102007040c0a1341a6480e601c2c00d59031881c1003030303d26000c2c07010256900341002150820345462445000e01801d45920002184405801c1d814500000380c84094012a0742c00301e929a1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 683466987 1250 683465737 683465743
    0x5150a0b03090f030f030105010e042009040b13060302010f031b0503040f0f0503030114040501030f02120328031b0e04020c010f0911030d090b0d021308030c0f010f090302 75
    0x3515509050356030340e5100c030b02c1054a80481610000ea580c04081403603518181208000c6040700d1090340d0764400c41c1c0d141c400b00021603201c170302c00342d0a07100d0110082102c544180d02034060494028000641034032500b0200f48040004036040031171703964554040c0b08660b001903001d1031400c55851304016031044d190400031000080340015042c00400700015040110040d030150200d40d004480111030300c1303103103480c50366170300280a01c45100c0b1205514940900f4a80710f9141200d400540e038111764041502881000001c900116441c0e000802c10707004a410f003402240300048000081841058041d0002001c8582100d1101c007162082101d082d01e10384e20020481a60f00308583c0142c1d1030300e185a0003401000c0380c0107010b0446080900c58024407034aa5400400d21506030290380c51554103a10403500b001e85070084041814040c0000b01c49021345501a210101e5294600780c02d19442c1d50009165801c1031032907032a598800701086049d50002e009115131003031413940c140100c603026070703010351 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 683468237 1250 683466987 683466989
    0x2040e100507021504021905130c0e030a02030c190e0c0301090b2707020102040915051305010605122805041101020c030d120621060e0303130609052503050105150a 72
    0xb100b0140150700302c7c2c2e081d810b00c2e2040c005044c0240f034085a509146940c0020304010404e040c041100440300241c5404c0c0412509001a0700030054141e103030300d007810880f480b4040c134031040b135a00d0030382c0c070206034039020458044c05081609200c94407980b40640d203205690145040c18002c5072100e18104888403900c059900743c1c8000200c14a080d0b5811340d003280280030345e6211341707102070030030345500040b96010540702c0540300c0607030754129000c1000141105880c400c6c402e100c001441005000b80680320011255084144c04000401800ca60301e24415041c5601c9245540c1c10b607250244410001c0c0c07191848100310083c0080c104001c919400240c80e40e5400c0d0400707060080c0045c000056860300c0d8046c9000d0984842202400340b42c041d80c202c0c0e202c404000c11a03c031454618007051011000098078400c40c0910148100b840155030740002400ca268002c8501d0b103d00d8800c0040a900c0ea2003a6841080c0c0c4c15000c0d070442d03e18103205094513000380100300c040c404003080318042e89603449010 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 683469487 1250 683468237 683468239
    0x60e0a0603051315090218161b020d060c08130302120d18030f020d0206060f1021020c1002030f0703090f0b04120908033402040e10050702150402 64
    0x16181c0d03110903200d0b0f00403540c0c1c60300411116010350004107940c0e03107900c4031034024020317a0140380f148001034400d10310760410307034015417002a06040000700d07500c250003408001c40c010510401640c059400320741d0351100312108980c919101da44801c1380b564041009030b44071140603800904107220741c601035100c0b0100304c012148070b2030000d00441203c10756080481001c0450000e403c9800701c2d410004c0c160740440b045440140510011480310a03c0058400c3c001c8200421003000b000d000c50030852340c03500b0001c0b810305002c07007440d11b003401c80740c107429212030400b8017840907030743e452090440c0b42000302941110291902c140300f8031010460b4600226441102c506001030121100c2c00c004583d1900d5000040ca00700c61501004108441601d4905180b45a900da6280300c4d52101c10785a140c0c000d108145807064101c40388542e52090030001800380c0e0300c0c00214000c001c0e82907000300d800d03511401c0b90782405501c4180e500d0b032480f142c0d20589a12519034809060900b4241d41d1701101d080000e0000b13 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 683470737 1250 683469487 683469491
    0x5041a1302090a05180105100c0308010e04020114161502070c03060b060903030d14060904030e012001181205030601271211040506030f070603020d0609090c0807060e0a0603 76
    0x12003544900030f641010700700040805100d9130010703441c051401400d005032070043c03070340c104039074009401415520300e29581500c40614031b81c00c0c4018090010700c0180160704200301584d4901440184070001c116900c40c10070602003689540c1415416480706003c3c82d20220310400c4190040b8035021a0307141503942c40403020130f20828a400183c0c031801a01d902c5ca5141c000014154040c0140d60b025805200907026030418580e511420414540411500500400c485843d0070320150b100700000400309050f18150904130700302c01900c0c0d007110003c0c290b90b078210036181510414011a40302200342d424032443c00794510b16200000130520000340c0ba180f090020381449100c9402554a0704c940604110004065074480e00e0074407002c025010035455005a107442c0100e203080c1800300e1102800b049489c014a42c443c40d041c02100254014220401c80c0d99a5502c042609540c1d400364094107401843d901000500300b160803828464a80c0c4040244a07410b2101186500c56903000c10441e0014100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 683471987 1250 683470737 683470747
    0x1002070602131e090902010c060c09091506111204061202040902030a090b0703060510120b03070f0e09010e10050903130e160c020f120a050601030c05041a1302 70
    0x100c200640100045800d103182581c4001c200c0c003c2550aa03104103650308501c1d00f0345a036680f48413084501604020b40040c06114a10022030011b80100040c07155500e000408644d0b95240d5008031224217174500c1841100040400c074032907000d0240240c046d1100040d188641051844290620661068000703001200140c0d94142c091a4142d4008101e464002d640d00d160210206005241040c8106d480c2da01500105060318840e01c648420b442c0c0280c41c2091600044000382c410120000a40d000a500e0300840c10450310184501002002c88090000307030941001c88400103d03200505c007070204d80c5071a4401402241c0040c401449201114001800c0d0720b0707030a00107007144120041074001c0c2c0b41548000a031258942102d51144540c40352078060800101011562043ccc015400f96018605006084131443e10080c02c0030000311740805c59046000513038440d41851741c240c1c415149580180d10400850505014403138094001002e46252102d0a40005d0448040f2a43c0c4184681c0c0c0415 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 683473237 1250 683471987 683471993
    0x9070e060403080412021c0c0b0c0115080a02030105131110050d05161d090609250c0302010b0108011211060c1515040204030c06080a02090604240809100207 69
    0x1110701554201d4440740c0d90700e0703c4120b190b4102400800481c003071000583e03410700900ca0300590000507680300f03204054036894020780060b55040303451010465540c82c5202490203016843c241c0043c05000060300c0c484c40240109030864500501d0701c81580100740368a0001955035800e4244458105c1b00340509a00c1080b00322514001d01503101d038050302e0700c000d01c401c41e002d407030811410580301e079524855800001c0448071081c400c441c0d001c1c1c20104410104000f80390001078240d009596184455001e42c042c0c032602d00301005103140e07d000c10403d410301c4040c1682030203000c03070340c0c142801c102c9001c2d4035003202c14142c60f03200c4202a100d410041c4170101c06a440e44202d4459083c078400300c501400100050500c6080e040d51415010f0005a00c00d080905040c020f0714210307178100d03e484000524010f01691030003802401200016400c02201a607956040041c0010340404020108041c404025603051009410400001d001c0c00c503003080311400d00000e000340d440c900b030348016840c1c2e04545 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 683474487 1250 683473237 683473249
    0x120a15091a0603010f0605010207091d030a050408060603060403080a18150c031a0117040f08070803072c0d05240f0a0c02060604050c09090703020a1d09070e 69
    0x60003441001a007008041c4000d10000300750190200320003c11181c0380c00840c0c84100c0340540f003500d015030800c800c02c12010245070f118803800021710701d600210210525074182150712601d092400304034081000d002110003001039030f03400007040d0300600301410162006001e000c401002c226400341c440380c0100404004100100b03000d9806a202026959402d4110000d000f40003403410000346020000c03540c044401c5481c0c150325406071a5400702403060400c4d030941c904000c206903901c659801c13404c1c000408001c014403200e4040c4041ca80c49091180c030041c41d415503890515030050518042c40d880d11001907104c0309011040314641d5100c2190300d0418200071400302d40905d54a21409040d101c040e020002c54411242903011b90300c16542c0d92020740c2260742da0700c88030005078443c0c40044e05a040517800f10f41c101500710b248a00381010200025000c860441d08400000d0300420111015900504082c0c19111a01c080c5010304034000701003008a94028041410488aa138049925403180c3c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 683475737 1250 683474487 683474501
    0x909060e181c0203030928080a02030408030304060207170a210e060f07020f0f071406040302060712092304091a040309080d030501151101110a02060a0605120a15 71
    0xc0d1950800b00e00c024400780d00c90700200c0c2e05415500800300c0d11a611942040311041100001c0240b03805844142c45601e0150005c06a040543c8020400800d4010040000c2c511882c421000965074800c64617014404002c4043c1c148070a203400d05c221030a46030001c007810954125a1442284c40d4400c1c030b407027406481100d40c03103034090080c2e406102000c0410340507144500c041c0d80071225000b0580e00403650f580c00d44a80042150410b14007804107000d0b1616107621204001c2006003055280d40020358a507015401c121031041e81c080c44180c01036040380c40c410083c400d80c144100d660309803100050301d100304030320018402d0b03640e1692981000000a0b1840b0030300075503402204585080d15028082132950300980250b40f1500c48403018240c802d00406051300e03040010500500445003080c0c640415112048103d5500c9660080c9140c1440c0d01034109141503900410650401250110855189400030390040180801440d0340c414002040c4030003503403200c4142000d0f6583c20b000b8008207a1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 683476987 1250 683475737 683475763
    0x304060b2724091f09090f020901060f2016091a030d020a02060702030a2f040c09050108040f14030a080c070b010608041a1e0702011a0f1906020604030909060e18 71
    0x10b02411b0b01c0c01c4c415041d00030544984260380c80311a030b0742c0f41d0300f050790800b24607030601c80042c04c0741210081e00d11400c58100c000410b10421a64450300c0ca1b1301c610b000940540001c07003000c0c2e80b0003001945650480c20708032110800c3c1c01400f56086172100c020b4594460f241c0107405203000103010700864604200c43d012041d084440104e441c01940e2000e204601c01500f80c0d0517034101300e481e010041c41c2c80d01c240441d0350348944078030303012a242400664020100a1042c4c0d0f11800007160303d400308103c0c03a1b01d640c074500904003441c1c0e01c2e005014080c0130701d0300180060300d00f01024041d19000a8606a01ca415a540c5060290441e5203502c2e08440842a000c1041171501104090100301c2d0f182010134107a03c0c200c0003d1000f41d03580e00000300d08903a0f01c030441070090000d4200800960a007170003151103814000e00151002c444078660f40031030124641c488801a444802080b0605a011007100f000d001000b4040c01a01d24089144400300c1d0041c040e0181480304110300e00701048200049042581 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 683478237 1250 683476987 683476991
    0x19051b0f0c0f0f0d0f050a08060d0203150a0501090606050403021806061e040f0e040b16030b030f0604050f061b030a020c0d031409120304060b2724091f09 68
    0x102c2451116180c130405014080400c2920801c8500140541c055800001032a901e400c020b60b1414100200e095030024140d03014040c01c83c50f199001c4103c03460320302c180c80240004c140c5500d8950710700c0032201181d0246081010901041c401640c1d0803c1028100502d502d41c03118035116980003518520481c2400810702c85200481d218200c4544068002c88294203041c005603640c490300407500403001c56006181044480c002034120102c002081c0e0f0641207071034002003490704040460b10300804c40348070f00d039168000f404010403c00200400300b140001c1e0005003c250500030751008107900448603e621911000c0000b40c05140e2560588400403059130803034014044520f8041c0060000301c0d030440c2c84d0301e005c0c000120b003190300042c404c41520365124074918544da09e4072400c1c018006144040e5200032450101d031003000c010070740c44407912283d004009003800d00c50342c0c510240703541d021500340d1042d8060744003105690341018a94852003560302030441035458200d23001140d07690341091803028 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 683479487 1250 683478237 683478253
    0x1b0b03161403040f0c06080108031b10022712101a04020301150e063103050d020f0d0e09060d0609060c0203070606090515010c0501090b19051b0f0c0f 66
    0x8800304c11046000713240b00031560351107041c1214680401d020f076441d01d40c0208084001092344110000c006030b20071003620015486184940140ea000340002d042000c20018020510769501c0c0a0305080042242c5184000300e0001150fa11492013040d02890070703540b461040c108503071020059079140d1000f40115501d603129640ca94150340c1c00150200081d000c1d1852101c0c038100041119032000810403c448100c2030b03901c504107601500f1039a502c240244080000018004010340002040301d90094142ca811596040c0e10304021403641d00704000c800c0b4102c1c401030302d6511026401020556901004000a04003800940400c1c1e10080000789040e12418481d035000c0003410116105180502034141d031803100d02c00703403001030343c07461070000015a20203039640c003840203111018170920000c01d402a858442c08040f103000c48005030391040e280d1250000c00400c3c4611a80080d45040f5110f242d0304d0780000810324041d0541031000c0c4040000c1540c1c445404020080f40c520301441110265 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 683480737 1250 683479487 683479493
    0x30b0c0c1009030507110d0213020c190f021003090b040204050915070f0f030e120310080a030305010e01170a02060d0914030904152d030204090308041b0b0316140304 73
    0x264005d1900350356050261810008500d0720594100041e0340080001101c004a20300140096201c40454849031051000030380c03084a490b00c3e003095072406480c014004610a0040c40300c00c0040c1046c0400701450f15038407100040b254001a6003181c0c05440010f5150b8035040e0b5036203005044001c508031800b03c40d041212403540803402e002007043c150740d903c01c0020307141c0b0190300751840700310307560156040303007920b4001d01c2031200242d988620b06101c00f000f0740d541d600d04c0c141840c161040c15000207403104014004040b59210050060100d03000f114090a214605c580d00c1d480440c81c004d10942001800c841909265000040303480d82010001c49005a0140700641d00c5d440074001502079030900100e000d00910340c3c91035900701e03181000c5030761034540a80406d210200d04074070442c0c8032542410300030015031901d105015070103100703403218080c9007000d040c0b144100d118404038005c201c0c400d840900c0201510400d498020002d55a0580c02c00c1600d4402e0300c10720107410a40e261050040200414 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 683481987 1250 683480737 683480747
    0x20a030f1b02070b0901091202010e09010305060108010501050f030307122109060e0a0203070b03100e09100e0c0d030c1106031315060518040c05120a050f030301030b0c0c100903 78
    0x1001e0942c0803100d00590340c5000b080c090103040b1015020400d14002000282c1c4030368000081e0910500d01a503101d0400d07000104846004c0e001542c440d44064014060250f092269078050001120390043d050300e070760000703940c0b44a0324000a01c5152440c452102c4a030054540b049000b8040340d01007003143c5d0100c8160001c0c2112001a6281c03410607142d400040400300341200819000f60241458a051a00380c004aa2001e03082005541103003100240c40c0d2031800e000350141d926078000d030a6100c10440d0040540304800c2c40301c1800c1c1c1092400080660300c80c2c0702149801e0f8141082c6c01c444140d81410032100001c5001e15401030000070403c1144900307c2400031103940b00350824205d4110005c1c2c241c04a918900510307402c140000e421045401512013802c2c1e000b8030882c030390305500741c07602d000c10030780320400c10080103640c03081c0041c6080000910081d24407041c0d1301c0c001c6d805c1d507243d912090814400642410341c14480001c1103645400c1c00e1050b480001c0b07034a1018081c1034941d10300106 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 683483237 1250 683481987 683482031
    0x1121209050a06020c03060a0902030c06031308071227090905070e27010c08063003030115050c07141504060504090e030307020a060b01030b190602010b031609020a030f 74
    0x201c02c2c080d01000402341c44a07846191781c0150064000d080e18501c08042c80360b65032002d010990130300c0c051ba140700300280d07410000303154030740c4648481c0088003031003040680100003d0724411021000e00050074280408000f0312412a5407583d40822201040d00302035041c520650001201100201c0401424100c921004c800588000e070080c9501014804143d0803698482000c50020b5440008515149800300400681203403070b4001c100d030b5a1b40320b00840301489400c04402c0f041d8001000400940d04c84003604264118681842d80c507000359140c00c00e48908442c01601d0080403002a41c81d82e54039510103580087c0944000c096840340c481c40040c041e0780280c49034009003400e180303400024450102c140d80c0100e00c02d40042481c10001d684d10000391601c040c6550415664040030b91042d503481e50b601140c06030601882d2005401c1000c02402c1d42d6208484078001d40c032a240c60f0801c500780d464007008882581c100180c4683c3d4100d011000b03010440d900a80940c10840d11008200d12009101 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 683484487 1250 683483237 683483239
    0xc03030b1909150501112e14010510030e21040e1003150608150c1306030e0601060e0105030420130209090a111e0f03070207091401121209050a06020c 66
    0x80d000d141d0b01d00c0116800300b00b2110000441e0401e0900c940e440342488540c5690680742e291034030131382c1f9240c100d00d01142c2c509040c0e80707e824070721001003007581813007c07035880ca2811038501845110442c91002e665002000e0754045110100c1100f45c3e01700c03a511080c0ca002d0300c4a840548941d0418043c0520b00810a00041d40c0c00d9075455281840d052441c072070a0300310354140001e416546103015142c90f8a01c00103024a180030800c1140090b0480601006800307050b250701c5c0000c1d002000c041c010306d00301b0143c000d00c040c040382240d03080142e070300300080c0c83c1d0060b4413104044581503010100403044000388002ca400100019803030005500c0d40c1c020f041c01210503980c40215075a60701000c0d00b0f0361144c01004001c64401c204690310300d00200244004030700580d401914203d4001c02481407a40b0448400d0010781140400340b28047c3c850048103156101101c40010550422000c0e0b810342800007002489840002c3c0820000740c00b036a00c48004201c0108440100b076a05e110194403108100c2d180b03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 683485737 1250 683484487 683484521
    0xa080c070e060306160e040e03031e010504183806032401050f060f210106030902010f050901030e0601030501020c0d1b0b06061312020a05040c0c03030b1909 69
    0x30ba0241800580c1c0f602c5a00304980d50095017411100590300081408505078210392509282c1ea50000f003000158002c04600b0b503204520124003400035800785040e00441d02c981c0c244541c040c2946151648854110342083d28801030140591031080c1002b1103014452118203040480c070306520012205600c52070055080d250b40300500d2502c0b501d20701c0c207044e64140c80c000e5400144101c0c02c001945403105a0003800d014a051000700c0d8504d00c540060070140c610b00694050040c2c0220065005401009603090078002c0c1800c5500207030400144c00140c03800c020b00840c5d0100d140e0b201c0c1d003000c2c8011030040103460306942c40c0d06003113010354401c1014007074900c00c0f2600413143d9031046648000c4141d62502c03405104240c1d0340d8078950710300003400683d071191081c0107a01e80880d150a00c0802840c2607070502d82246100d20501c400c9820741d0740301c14425032511000a118640142480350210b0741468000381c00c0c030a03400024181c20400000d8081142000c0700821a80074a910459980000d0030308 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 683486987 1250 683485737 683485741
    0x504050d0305090f072711180a08060a0207020a050603090c100e09130305270103150501171914011d160e13020f030f0601031104030f02030a080c070e 66
    0x1c41c81d44ca108082c184401c940c0402d1003000410a41c10240f039040613036564203005100440131240c1035420072070003000c1001000441c0703102441d06406d6500005400e94034416014601166580c80e90303002024034455a8001076a0000c540d0340440c2c01c4058040105241c0c1c076410704821255841d100a00034134001d2000a41101c695070050300030569180b4001d16213241030303444800b44601100541000ca007803010900000d0f5121151900171a900e004088070821182d52800005054034003042907a007225a181c403040c021640d200404050258400c11014123139103030540382c466800301551903500701d2440c1102c10204965000c4283c0e048450401c6507240d440c01e000c06103401c00c8401e64410740b28080d408140d0b18414042c11103121310720801850120103142c1000d181d4142d0b0b10410f100e68420030b0010800a0341500d0003940d0350810070070719080154107501011113040b0b205502010b0b18800b01e0660b44011075600b0007140c09055404450b0035140c1d00b205102c03a81d128950300135480c1955540b00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 683488237 1250 683486987 683487001
    0x3060506040f061b2117010b03040f020d05060c0c1b030309090406200a0f020a03050f090424050a06030b0105270a300b010501210504050d0305 63
    0x70340707003901c150000c481d4500380b81c54416203141440807101d9028908203501d00780451480d0007418004600c072159825011034183c0300034200c48040c0d10710000700c1d0710480103000c8469031a0a0720741c0031754410311100c40010a030001440b101070000e030060040c070a010400c94a40c2106000d04200000201154030303402160a400303482410440310150980d2050140c01403515000280c0c2d600319006901c0050788035014003403c0410041200b81c8c0d08000400078091046c5a03000b001061810018800f8003000c4032941c2d0001d109110700d022140c608840420a602583d07513550003a44009884103d881821400240c8960942058411544038000004001900600a024021603030205940b500e1403c501011451064428408030b80c480003c07040081c0c0e0781b601e54000c458040c0c000800e9540c0c0080b40401d680b000d003c1c0c00f98007880081c0121003140002080b55004906448090a000f00c801d080402c6036129540400c18004189080c80d041c001409404070302c5000c4201c40b907506002ca582c85030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 683489487 1250 683488237 683488249
    0xd0f0e012307140f0d02030601110a050604030305070905060715050c0f03012c040501050f0105010528030b13020c0c04090f0312020903100614100221090d0f03030605 73
    0x201c8880520034250000350001d10911500348561100601682819860411400740740c1100020a50b255030000602c2425a08071240601144009005000102c0c0580d0740c01c0d10784101a000500349a1518046080e0754068903004000e000094103540d00e502c82402d014041076894800c540d400b502d00b9020410044009085801c560541411146546d207403600c0c0100d04442c410412908201000240c00c9038529151464000c5000f00004500c03410700c1494038881d0794041c1c0c01181480b400300700c1d00c0c60341e041143c0031200d00b5090414041d20381418040c150040d0032a5010b80d40d001010f0540491a020320b41d0103031282041c48000c44104d02c0c0d1080a00048034600c14000d0845400b510170080040d1003000e01d41595403440c2d0300541413424000100e494017850303401c1650300c43d0711008103204c031036031000100014000889888081e0564400c01940b101040903581400191340300c42e60307074000b500404071030180b03901820307c414001983c107050008003200c100483c0000d081160000c0e040c6400 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 683490737 1250 683489487 683489531
    0x9060216150c0509210a120305090106170a0803061215090606030118061a060c010605031903091203050705150f0604090312020a17100e1305070b0702060d0f0e01 71
    0x16090861068664000018562111054405e940700d00d00c510030000381c1a01707440b00000d0784ea45010585046c24410341c2d0030345499402c100d00603100003410b9003070b001d000181014030a40000c0000e82c4ca4580802181c0c02c01100c9880701c09a10406280306148106601a984101e8040707059072000d8030b4400800d42070b03c8801140c06844150b02543d2404038030301d0f40c480a080c2c4400c2c441002403000c10004200d881d0000d40f07641e04142d644103001c0140d41024445460307004006140c05100345031590740505042181d025540000044c2e4004030308050045003110181900003003140c0d842c440c200c94920440c4401c0b1202660f4200d080041001e81c240340c011004a40e6041c0c40b8194000c0030950014025000150360b5401c10003400c0180c450208440c04842c02000c82d031905864840c00c2000c04d00040b000601243d403003030710030704241c1d0201340c0c01f01d00071040d602280085c9507a0122800040c440703000d04010303004003e1501440c4d16116400354401180260940024040321a220302c4d010f03032003041 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 683491987 1250 683490737 683490739
    0x4050f0a170319050702100f091703040f0f0507031a09060103080c1e01060503150903041404020d0c03060e0a02070305180a0e0106050414100f0309060216150c0509 72
    0x424180c1c072116101500c003442e031140710006046011040c01d2000410f5510070342d19000546c1141d00d012114000782d0264007504180c50b10144200c80099540342491080200482c000e05c03400720200301042150b030040075400d9000440203050b08007c2c2071403030300c0f80344601c0f0496805e1034007281c2c0e40d102d03002c85544038825010003000d00f03902e87c619101e031490799214030070b030355031901402c4401a105504101c000502c440e08000001e000390502042c107213801451510203040308645401c100e40b0603c000111800d072101c00b841ea00c46200b40d480450b010b80600d40d0b40020041c142880c10040c1503150b0302400c01c0b6510507000c4040e03929500c188408a100c1c3c0c0c2030207030014108100f1000b07003654249001165560190040320130543d01e0001004954007038210f00002100040c042020524182030301509400c12280c800c0c400000b0b0001601c0c55190820700300a16460b508218144a01a4152a045420452101007042c580d242c0728500105a1020f9a110b92602030003500c4e80e8407070030130b44400da00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 683493237 1250 683491987 683492003
    0x1d060a090c0b0417160b0d0c03020702040e010902151306032003010305070806011e030f02120d03060302090a054605061e060a140c0a03050304050f0a 66
    0x84506112000c0d1424610940780c1200700c040028035420302000800c018204240d119829181000c00c85082210750b241d00103515400e07100501464444404607640d4258944000410f50050981540a40a81940694407525003444054070303071810740181210718801c5552070004265000c4c14105401490b0070080310029205090004a003c0da0190300c10420242c2a0720b20b0b0912003698000692003600122819041032404000707540c02081524058004101000310141c0b507000c0c640728920745032001611540004d8106001d6480d5000043c410490200075126407000840c0c003d00500443e01c0100c1c0101241e1000481c0c001072803240c06d001c1c81c800196000074001001000c040d007058110b941008150070020410310700a0040782e254a00c0906d0400315852038450104000c84081c08880059515403202003809541c1e904211600c00c2c4003414049008a100303040708003503003d460103100980c880caa011600303054010010b50b02c100e10402c2101c000c0e0607561100340d100c0410b00c0000300004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 683494487 1250 683493237 683493241
    0x2070305071b0608131505090703021e13020307031805030c15040c0b03040203150703140703090b01260118060b18010635091b09040807020103090818041d06 69
    0x81c1110700080d0340c0c003503908810070340c0d1888286d0040702c005503160b10141d44604810011400d001c9108291559002d0304074128a03038000c00703c4c00c01141d95083c24071156000000821a50203944540094020100b80d003a082d1050302c2c0c407950365405032103029103911404003500f900e13015499800344290343c03011031425924544016051640c0018000f00e9040c00b641034207410590130402c1d201d2103000150380105240d03120200001c4540f0300544a4000c0504040d80c00740810703000740d5180d044905103c04501b10000401541401000015522143e5400c02d038070440b0000c00d1480347e00d8140e001d100d08010f03401012040081300c09801760032020b207121003401000414003601c020408069041011960b00502401d050000954440c52012910005e8180b001441b000c000000c030120805c0604840c480380c5d0800030701c150500420040003030000003250011a4400c5d0084100340b90f00400c02a100d00c14400051a011001900c09004500e0300040f000c0d446500104641d1046d8034101500480e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 683495737 1250 683494487 683494501
    0x6030608120904200304050303041a0f18160902030f090715030222060201090629090405071a07120807050904020306031c0c030905040b0a0506031902070305071b0608 73
    0x6000a4411204c0c8211120503580507580c0301001035200ba032050014540e40d00d403520b4001812800701c81803100c0903d8090821002c0010001c0d2680c00103100d007042407000d84004240391070410050308440c1008200240044c0c11440d070303000366004020300071400c9a1507031082041da986108a20075007038926002400000c05a0099004101c40c9621071064944031101a4a0300301c0b90b00d00ba404100181c1d903400301c40c0706210643c41b42c4002188142c446c6072400c4920f000070b40801d61001c0c0118425050350002c9030801104003d20f00c003d021045078501c2d00c2600103a82c4c50b0316000340105899003540240e82c0a90680b2808815100f810b01b52609400e240711401880000d40000301a95054030aa4803540704001c100c480c107606600b035031703580c0c4500103a0501d002080102140c1c8040e01031400d1001c08403295032070180c004d040c3c0e0000d5419507200d6540e07020320715198184d85158155644002510014590b001e0024544c45000e541001c0d0049502c0494540c8500c140c4901400140c00801090b15 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 683496987 1250 683495737 683495741
    0x50112020117071101060e1509040b2706010f08060703020c150901180501020a0314060303090d02060d0903180b0309060403030f0207051911030a0b060d060e1606030608120904 77
    0x1c44000d250403401c1e800969504c07400c4070300d1500808651803401040015105a200856100d502e0503113014030941000e9480c0f421000300600350120000c2106600060f0000d5200109842d40e100e0080300c500796075801011520040600400f4034034001e003030000c2d904030f01038002c580c480b600410060101c603461001d0200c1c42280900004c0c508d54032100c1200800d10100e0f9513040080c042c40c001030351107a141d0009003c5551007000010382c07890840801100e0380d004001e8410048007540d01e5128500d031407000581a12a185800f01000e103020002414941c0c03081c040c540ca02c400304000310340940c642001d40c410b4002295040b115a009500240002e803003600043c0e03844040140c0941080060380d103403030501c0c06107002960b8690881d40a0024090b940b02a520a200f0942c00b51400103004d0f155080d0094000304400c1c00b0300036041e150020400940e000540c0703010014140c950144040d41c030035000615520940d03001905024020a080740007050700b02c3e0280a44040602d015181028000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 683498237 1250 683496987 683496991
    0x1201140109080d080601021b030c06031e0a0b030c09090d0c080c10020d060906030201050703051e030903090a091523040603080705010f020f030112060906020f070501050112020117 79
    0x2040262101001a80280800040c070f0380e05041d88540c0751625103d000285800341250407081c01014140400c1c1c10341e00c01007100d251903042030310655501d0f0f42e2210402c10703040f101e0340b0705201940b00204012012100b41d200702d060b0720f421026079050071241d0301000359086081d100031030301e40c10817240069054020a68010a64840c07803600f13042403004024503080c250b500144846442d000603261141d07620700c2c401c810182c1400341080000d1421600000c150b4060006c0c002c041c400002070040780c503500c0c44843c01030300d09141900c075600d1a0149085480e50805070500d030181142c0302c1b0204035010b0302d01540c600d24200c14104080c151a081c0c0300e508890100d250340d0f0b20b849c0440c450071b9154640c2e008180c081c50103050003994500151a201e421a4403600d008a6000d20604c18407240b460444100c0c4d0448a0410b401e00d00d01d03c60b4107018004084d08440140114400900e038186205800c0140403207038041e80080101e41c1c0d88008071500030001000090016198030404500b481030b82803059 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 683499487 1250 683498237 683498239
    0x60f02071d1315020d0603140307081c0f050a0902120c01080604020913110c070b04050603060f01030219120b010503090c0405040c150504031203020703020c091b040b040e0c120114 79
    0x80700c15040c0411141260b00c0310016061403611011b00340b0612808045144a01e120080154901a12902c40c5415401905041d80c1d82103042d00500d0290340d1749030884440407107a04403c02c100c0c240313142c40c0f00050004080032030048455440c0100c0c180d10118450041c25010b0f12070041545e41c8030200320003503009071001e40e0b201440c840f2410724101c052040005102c803035a10390760f95098068906103003a0095005050107041004140031640f039100640741c11540540740c1c40c1450701490016806400b8501e41320715440c800c404160040c651040c0040d010640421007085100e100340011a100d20040310001900c2d84000700d244110b0401d41d1100e03071b010740602c0c9441e00040c0c491108d440b10207001031018001070404030341802441038010b490b40807920903040840c688546950080d450781e401c0c5a400348514580000160806541c0042140c58404182c80c540d40b40d8a030502501d454229001d1108503200b65400140200041000c5640041e089100d90345507078680200c03401c0c4564a0381b4a1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 683500737 1250 683499487 683499503
    0x10605031905092404051902120f07090e070609120813150806090105010c140c13150503190f0f15020702040e0d05070803090102040f060f02071d13 65
    0x40c81c06a9240716860041e0403010142c540003201400811410000304943c0034030034501402e01001030b400084c0c01c01d82c0300024103401c000d9005800091401c0030841820380050180f551001400700c00442e5100a503642c10000304030905410045903030310003180c0540004a000000c0903c160089000d4a00d1094441c2c4215441c0081c802c841100300346590344081c5001c41144603607850341d074010212950100007a02c44076210f624140009101000e00f0300040c04101d81040c0003c0004401d201ca00d0701000050500380245c00001c540e04001d0031840c80340302d05495850f60203e014540800c0a03271444241d0800f121000140e611401880c03000c840d401c54012014900401c001400d400d000300c1508000e503401038948080740184005e031604a1080d46550300400e8101010a03040300c2900d520a40212080f070b102c1c3c0d22151418020300c40c940100d6215080c1ca103002410b03035400b510300c1059102c181d003641d0505903100c40c00da0b0800c141c54209980e40344040000f03241d0a02644150801e54092841 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 683501987 1250 683500737 683500771
    0x120621080f07080d06080a1703060102070905070504031b080a081308190b0703091e0201091d16050c151504060311040b01210c05122401031401060503 66
    0x24250340350321402040f03c1c6101e001c56516005029440741307070000d02c400360181851080c180d507010a010442900c030800c60b0404400300d500c5034801c002940190080040070400c60400e640050001d41151000300d400e58003103000b09524081040000e070444d205500100071005440e0fa0fa410136810000d031a086140709404005503840301040801e8902a50307070303070440486107281010710b500400100b410051c14240421100028480814155001088020100c080f041880121445c03605540180d500402c884036041800411101c003c1c000e1400c92031003100080b2880045c1d6940c01074040c100e400d80c0003144010300c0b07102d2256145900426011141c01803e5840b000901200c000381c00540c0c0401501d4006600c5081078400c4014140b400d0800b0075031038072001c00c2009071500003004481500d0300da2220701071250081d02038a128150071841d503a820301d41240100e05580c490344545031045040e50303c035a081c3d4000c3c841c10380d00060b40c804000142c0e0910105403202d42c40580010801018804 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 683503237 1250 683501987 683502007
    0x1401020f070f031401020a350c0a09150909020d0b060c01060312090e0402040c0e060d050402180c2b0914060601050f1207020a0f050d12062108 63
    0x800070029008141c007400b00c1c1401d5040c01d180b20f407030102c04500960b10410a00003a80d4000d08009214083c1c0e422401c031410040201d0102244803095441a0380d2801050224490091018210014640e503c10b644030b075440b4442040f40201c1c0b440640401c83d0f0303010502003005241c000344030481140002007108007400740483e42d140e00100c0d90300441e075920901441000004000004071480b0303071410084440c20a0b910004191001d80000e10541d0340700241e11285006041200b09918028007441d111589075280f54043c0001f00c80c04c81c459404414500c9540c4600c0558900900c01c2125050502c5140e5011a1080c054603401a0b81d14034407880c8441c0e445031f68050130b80010310901100503084034240c0340078034110380900001d040c41020f110003800007403004140c80c15000d40381202d21003511104003e0341007100e1000041c06190825040c4418454009a605e404001c15912600c07100c002d11048000c4811900483d0030300000c1640c9418101c0c241180300728050301945c0071340d142540c004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 683504487 1250 683503237 683503243
    0x90f06030127022703070b03090d0318020a06080a0f05072f1f1512030c170f030f0601080402010509040e071502010506010f050c0c060a171801241401020f 68
    0x2a03944c221103480c0032400340542000e104000007848107405450841c1010900382c5c0d2144040400042010ba807991900304002c02140b040304000e4018080300d8603543c80b8880144015800c03100740860340d060504202046180d8442c0c207201c3c41555443e03505000003189140c0803105514001a1402c4401001c40d107492001e01144051a40c3c00c00840220414511510240d03941c88071b1003108885420000c0103c910b4040400a0305941450001510042442c050b103004070307918a5662114000f05110110142d00e00003140566001052445955031301001103441c079008a6000380054004e21410a07282480e810205000050005880d811600d400711450340e00620701d140d0300180e464100344822941c01c0301e00ca113402c1e10705c6d1500900d04810744c01104d1382c0c3c0c0f2026070068025803000800c204210301c980e24156141010001d03c80300c82c10420300041c11420901c030440300303a502c1d02c1842014841c031650801768610140516925003031504098034810f001c01c9400328150b000d000d4202d03688134414 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 683505737 1250 683504487 683504527
    0x31403030f010605071a16230a05210108010204030c0801021e0f0705030705160e0106050301030305090a09090506060312130b0f07021809100204031e05120a05090f0603012702 77
    0x210304070347e0641060660050030605840e11081c840d06402034145040701140c0c4c100d0344602098204a070f0390313025402101c01c201c90241180020300d0303504000424501c0c0190000c1049900510f00c5401c000d450304802c6080b88503400c1018600b00e9011040540000c1e83c0c000780030169002061507040c1035403601c40314190341c046401107419400040803840c0c2040a1000b041c040c1003040086645503040410150482c4018000034007400030125124101d80d940c0c584400c0500224030b400e000301a01e03494503d98480c4141e80c114032a015607040e40d1501c044140a50310994100c6086c80403840c6402031840c07907517215003040c0312081002c010b01d10151315050041c202084490131281d6251514140f00380c18540c860300c0070380645004020400106824158141034804484040d050002503403620030300d0a1088000e0104001c8003099050740ba9420030003a04822100f507420094008282e8100019480240200b16000905142e004040c41045d0039945c80d204c3e00c417000601d001c01007200715803c0608 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 683506987 1250 683505737 683505751
    0x1914180c0a0611010e030a02030a030b0d0f03020a060c020d17060a09090c06090e060a260f030c010e0a031b0f021906021c08180703060c0801031403030f010605071a 72
    0x1603c101011454800d1060410001c80c20340030f541804000341000752680300318503045003015160070b5403103003550328288000841c41c0d0190074040c2030304c0c180c5030180d1250640101510174524100d1050b080c00d00105440e80740d0040d03982e49840344201e981c10440d081a0260a05400030081d44010680360014403840d07034858007940c0c092045500e412001080e1019603004104c43c0300c954000c4c00f949440e4200060292583c4650114207404800d02090510f82010081d008900c20310030041040e42c030220090500a035180020721502d5000081e460fa90381900b54002d00107107684104144403075618a800c42c1e00c0e84940c01d080c100800c41d400140c085030440314074881000481004000785a0104005049468860384d040f89504850402070a8002c1c000d0407030940c0c0300310459034000e4440501980780a194807200400011013015402003005009000c100c914a40280c488500030000100f500d204400760020400540c0c28010304681d0341d00b1550003103841440040894186032284c000b80c1c1c3c42130f49 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 683508237 1250 683506987 683506997
    0x2071203020f100b0907030603112112040f06080f1f1e0e01120f020f04020d090b060a052b020a05041e050c09210a0f0b1914180c0a06 59
    0x20180c04100034075901820407070031f00d46494010400980c0a20050342d0021003260790384005800002c000c0110b07846038a0300c0382e0714010294408050840300d0040d10950b003080e02c403400c8080e2600801d0711003240655002400044c441e000409690f04e8074041c0c1480320749801d80040d003c4c5d58280d000d140080b804c40d00c40ca84184078034240082c070000c0035224010038421065140001954030f458071024059072000e4000d070b00720481d40005854075011540c038510307142e004000303502c414184900c0c101c0c4140c3c1e030244181e511600004007440c000020403d0044103102d0200a20001071040d030b0f0070a0311807c01c90700403180110004050740c6a206500c0c1100d13080e04101d0441031840e45500440b2001002c01c280100c061280c0541525180b11549007503040151001e410100e11004038078160102d100144400c0090202e807003001005003c20780038121a010f5840a003075541d00040950b8140d25904111140300e0000442c039811984148120314461000d49100119000125500707900702d07041030000c28 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 683509487 1250 683508237 683508251
    0x1104210c0b0f0711042f160c030203011a01020712051e102f03060406261005010302010806010807200a0c05090412081b0a0e0301050a0b0102071203020f10 68
    0x801c001c10214040400c032010081c2e4101c0130020f810314610342e401c401000c560943c0302007401c1c00e10780840c0c6007074680003110136280e1007520340403400400c1404102e013303500301804410050010200740e070078224141c024140d2030f401c1c40031022107030040100941c0d041c40b410544201014000044442030404c0303501500140c182228030f403003941d40b51034860040041050100b54004001d070045c0703016019074100c586d0340e41c07140030018018115640291f68006d0b0b6000340e00000700c03070b039205114401907450190340980222103640f50480b00240320281c081019500081c81070740c4178160843d0701000034104600b0780504511700c50107014a505500e4084d070b1000c61440207011348601c551000704000c542c4541e4a01e0140c2d1410140720030642014240141c60010690ba111007080da010810024130425803500c480b030300c005140702000310700503000c4d52804c004a816030320750f4000e41200f604182c0040403204e2924000b20320300a10100298218001c00c24086240f010512140007103158440c40804c4003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 683510737 1250 683509487 683509493
    0x504050d03030c18240311210c0301081c110f06180f0709150801020a05040906140d020f060903061501180e04111c060603061104210c0b0f07 62
    0x30132014401c1c100c1003c15070104210089407820100c2480d00d0410007004008104060f0040c0c400501c602c0c0c0030b4400031507186124094907001c240100380b15904441c5c2030302d400c442c01d8090700c0b0a000341c0b040ca8224034150742801490310111800400e8514042c19912138820741789040a4101c04031104c6904040d0078400799903132140800410142d5403010b403600541a2404a954801c944122812180c40d02c50100c0248000d408800050140c9402513564066041008003c1d90143c0254102c0300e15000012811001991606802c0007014100e10840d46094082004028003c40e105038040410440003045440078446503028040d850080100510170100241840781c410303c0607002100844010042c01c55002c4001d500240c00ca52500c41c41402000032803041c8219281c402080c10a22209204215140d40b0a4003200e0042c00304002010254084114034811440340c4c0c881e1403c81c0400484a0030480071542d40c19105608070056203035181185070f89a00142c18105411302e01003210814 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 683511987 1250 683510737 683510747
    0x8070e0628020111032205030d0b032103061302041a0408011d0d0503041b3203031b0114040f1103010605090c070c0e0901060914040f02100504050d03030c 68
    0x1410701d0500003400002e03601d21410f100d500004040180032904040a640c405ca032280b0f01684541d0003d040c3d0340e41d5022030321084081c050220009002e0310800c050001c2001c1c9039804180b903510782e22445880c6440307003410420445c19082d0040701d00d43d8200000203410000310b101c0e41c9083d41607078100f42c0350b6103000f05140c2162511a1000500c5610600400f0b07203090100f40c2e100300c0c0c43c880c1003140e1240c86030b00703020602c00960721000d04100c1060002046140d2050855031304c0d1903131210411150000c40d030100565104803191150598024800c3c010210300360780082c201010b40d40000246030106501614064000340c6040c0e9250002c4903486007800700041c04075800070b03010317002801841d14080200f00c400700001c0c800041c0c02c3c4003085250400204918440083c4400c01a0441c141070204509000b0411840345803021031801d22000400301340010138903c00c542150003242c041d0916001c2c0110b9444907030f461000c102c4e0230080455196142c2c2690041c09000b550006080a81001d000d4a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 683513237 1250 683511987 683512057
    0x9090203010f020313030809030f121603090b0106030c1701030602070311030306011b06020d1109100908030315120607200a12031802090a1410031208070e06 69
    0x41d102d801042040049040024200003e584c5441e159070300c0d40d541e5071050f095000e09210031000b02c80006518201900001250740150100d80484910f4818a0003c2c0c084603903e0a009040a403240300400000703011b940240d03007078034031802c182c190102090b280b1180d4580036001141c015a010a41c10180740d4001810140c10240700001c40c40c1d81411030020300840301841c0310340030035081c4002c001d0400074143c0503155100300100b0280101510000610f4050b00305000d8113000e082c8804103191614031402c008805c40741c041014603d944c55141c03020850074004003440303401c01d44844162501403401c2208030f1207580141d40f4030241230705d00b0550b681168201e03616a0416407144200c0c00105124890030740c117000c0c0c1400c000132440d400e820050860305c2d0110001c0e50120210302000800c1e41240c20654040d0307400141040780303a86406c139210103c1c105000151950010018685119014800d201d801c41e41c1800c240b52200c08100004107a0362042080c5a84011808124606121030f0841c0d10 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 683514487 1250 683513237 683513261
    0x40f02040e06060f180d06020307020604050c0a210203010204030c2d0510030b0a0521010b0102010513060c1e0c020901050901350115030308071701030b0a0e03040909020301 76
    0x70b1900307811810f00801401800c4514004560851090171541e485d6a560225154001c1043d07440b03141141d406900d881044a0540b00d90081c01d1180c07140c0d00d00044403800713540c07440e14450508504070ba0100c180030070490041b82c0540d0300b0070012000c1500c04920100030182c0b8070311790904841002010210008444403203440c09000d4074248005c2e680d200002c11006030031325000034041030b028005100000240c1c402c07504020550a6800202c00c9035800d8055000844020301c901c10034480128201c0703404490600c408817001c001c40c130004410740c0000c1a0b00c140c07441e00c2d001c98444492400508182c4441c1000400d000f04a039400318140b03a00c0380c60051504680c1d0a00540c9440070100ba0342d4000d0300d207104070740ca94801e21070419001e0140d0703501a030082e000810a141c003880c0c1e1240d02138014041a03000c01c1d016000220103511407442608000760303451140c13015910b141d0f922041d1000240c4052000f5803254002020014200050401031141400115080405006060841d81410344d40 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 683515737 1250 683514487 683514499
    0x717071a0118140a0c03110c0106061b0519060b030105011403010e0619020f0d0204141302070809010318050f030310080a050d0e0105130b0a1d10030e0a02040f02040e06 74
    0x203141e103003495810b01c40d808010a0404101c0030705c0018210000d000711800703404252408624202e1661055000f00d007610019125040d407a08106804454801710320001040c5a0168401051055081015800e02c40c8540c5002c9080c00362040047e094441c00d0304040581088200c0103134241c40c090140300071f030a5910000d011241825460100b042504540c0b40b62060303000580700345640300b404101d07145030030301140c01c545030b0341c44a03c0211245c00b21030341e0750301c10862112004d011460318421140c0d0580c6c000344030380c9030480900054020345074400700b00107840c24041c0e410000c5401840002c240c10501c1014650324500b074109003500743c549406c0f840142e0320550180c000600d0005880d40030318154188503c2290341440102c480d032040001180c0001031020000481c041c694000d0a91841309844400c0c40c400d12901030100400900840d99220988032048021580242e01c1034000f99204000d581e0b018a9075004181503071292910600300782da00003410005180c408102d650001011226 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 683516987 1250 683515737 683515751
    0x318060c070509180105010e040201030b0312070b06120d020f070f29090a140411181203160b0f070e090f070903170a0e090c0717071a0118 61
    0x800c940c0ca181d00d002d0715020b05521400b00d81c104401d03a1080c4000003c82d0002e0000d582c440c088103007861020340d0100d01083c01c04149289600d00030a0002c40f00014402081c00c0910907120806440c00c050082a041022510500400d250038460300400180e070b40c006285070880900030138500085644000700c0d800c0d9100080c0700c0504c101d500c19607224a2203041e919a01d02880d1054074030310032601200c0d0b00640c045400154104c04181e2032228000803102008282800304c00c1806030b208160000b4802803240b40002c00c50b2815030f0b01000d03107002000c100d900340181c541d4010f050755480003003542c1c105004410031200c00e01c281180c0f58002003e2a2071210b0700d40300030205509035800f074550300120300300e07400240d85036202d00c000310011900f240295055070107445000c0c146902280c2d8400002d0307118448004070341000440c0500030341c0040003035031a1048684441860304400c1140252803002004010003186c00d1005203265130b80180d0071138891394589a8401659004005a150000d0800301 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 683518237 1250 683516987 683517007
    0x20903070302040b062b0f0c0f26070306030203010b0d170a020a020d0804080f01061a070515090f0709050c0406030507120f051603060506040b0f0d060305031806 71
    0x140e14030031a9810b0302e0101e40301e140140082d106005800c0e44108101c0c0d4180700705411003000d840754500e81c441400411140f00d81040d000d003a20740755494480452240c0b07000c80d41c0c16100350700c0c01c40b0a0743c0108040d10109110b6004803942c0030107440c110300081e1118424003c3d40307028450184402c100725a00a800080d40d40e91b07502d02c0c0300e0084500100c43c0f0200c0c0b01c800030703030081c07240510a0360b00070a44500c480a0b803030081403541007030280d005107104541601801644c140f04110a44d284112442d102003a14411441607030700000c02100e1074000c240203140031f80030444502e400780c8194405401e400031a03005680c07034000c40f41c1c0207a40276410130041c005194201c1003107500f5074080d4600400c042c3d03142c54040d281407215080c0700d1050792900d00f100c10096420f51000740140031362480406100c0714040128140c0e819800b9441d440002008200070074000400200724100e10880341900b03204241b2040002c0300c4031540143e401d41c02c0020350441019410000c000403000454003e402c00c050303c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 683519487 1250 683518237 683518243
    0x207170606060f0708030a0f0609051b030901060503060a0f0507020313030b1b0a02100b0f0102030414190303020604030917100c030e0a03180b0406210603060e150a020903 75
    0x984007a0180000040c8142010000021926901c0d0014481c0d5502e00349290120020500c041460341d030346180c000c0203d1400624002c0a001d04900300030b545107004480b008440c0e0b0781c8060310180807590303142000a519101480054401c0250000014241480f4032000b425128010401030442d00200031036101d06007404070800550f60045c01c0d004440e542c10000326801d03411020340e1000c0c0007010a070b2035030280d400a16168203000d06a001e01c83c01040e0f17014803071b80003001061b560140e04140000d22070403030a4941209650001003d800304e214060744038885d0415645c10a40043e04040108014150025074940080c4184910804c6031f841c4040043c0c0c85036001442202400d4491426040c070f14401e03000760307a618000c681030302c00c130140c0c8bc50083c02503900781c151010b240b88542400070381d081100007541c00316205510f900c0c2c007900610124580340705120796130f0038029035030303070b10200100e8994402c810600d49558028500c04101e070705019003001000f0000150307035004002d4084c03d501d005c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 683520737 1250 683519487 683519491
    0x1b0803091f020c0a03080c0c0f010e0108040f0210090314070f05010c030e1f170708010302280608010608090f030d0f0f1107030809010b0d140a1502030702071706 71
    0x1801c0d6540701d56541440482c200800c0c8029143e00600c50140401800300f020020a1181003090460300eaa1000c44140f15810351411b0020740400c502c0d640d1081154014020942e12904c68001002000004c1d40060b40450a9602c910002004401d0610170050314a015141d01d1811030000c0102e80d01c0e017000395081008038003070241000b040d500d8403020580590185059180000c1c64540a0f840e80e40ca07030398209180404c8070002861126212026184400d102400f60b42290340f0700005a0941d020b00250b41760040715000a81000300000c2001c04c41c2044503406454240d541c206294541040240009005003450750030703801c15541020700080c004100d440c4010801c9010803c44143c000e000014404040c0d4686800e040011040c5905908401094810710030f4480f00e0039500c4054040b400c81d5410301c1d030203402c0000ca20b06100130403407a901c00e4100c00980c4045401c1054107a80764031001c6204220101d03410340201c00c1c403020580521507900940030390100320508946540300701b9901c50300 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 683521987 1250 683520737 683520769
    0xd08130b041709030105010311010f210e0a0b0f0a110309071502071a04030203120c121e071b150203030a0e01020408070e1911190509030a1b080309 65
    0x428062501001c2c4480e042d103060340e0340140200f00641c0c1d40d040150328559070b215020700291040c3d140c086414040c10040620105000c003c1c5180b13207120702200000d1079140015071040c0303d10400e42d400540c10110981c481c215400c004051070070240c10705400d4910340310107464030160a00410030300110009183c0d088508000b4500900c0c10055010b074100550764001d1000d0f004411072101610a107407000340203c034825000c03a030810214000e40f00c00d9000b00b800e803c031290003403c00c10b03290880d10405096090440c84041e460700c11018040903840c0c1c84000216294851102c0c0515004c3d226031010300108601000c0300188440d4913802074882c400102012040c40d0f0300c00100c0e215502c2541568060903000d01220a01626400d00c20700450f81207032008040401c0076445c1040704000c3c065090098100101181080200d2003180100e03030100c002c410800c40203220b0032145507000c0140d1812240a01c090a210805a00100d940881e180e044824a64000c128032000c82d140d1256400035554 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 683523237 1250 683521987 683522003
    0xc20010c060f0e100905060f070507060b060d05040f05010506010503060d060e1c02030310080c01050304080d0b030d170604051e0c0d060e0106020d030605030606150c030a020d08130b04 81
    0x4114400b04000309000310242c00948107104c0040814507032684a2080c8900860880324203603250f200c1ca0030400707403c840240c0081c0050110000103003030340d00408042c1d04014841401d000101000d8800c4441c11101968404608100710092140c01e02c201c80d0131a8003880c20500d94a40300e400320303402c00c0b84410009c01440e0345100c001e103030901c14425035804a803001d0040e15000c4000e00029031369002a2000c01441c605000000345507440040e481202c1c41068440d5030459459486028058000001c88000700303032245215429907506200d1400d205005071694540d018225052084280004000500491900040c07180c039206808200c1e44600ea20054000300f560340b1900005240941848000c1c1c00d410b02002040000441030b009040c0c0724581c0c02c90307904c200e240008400303449079403107110381642052004c100c031030410621058500d400180b00c00c4c0b80101c070010441c51680441d40010050300301e21114400c0300e500080b8103812200a0b03040300cc10b450f140e19580010403000d400142419 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 683524487 1250 683523237 683523251
    0x306100b07051002071b060507120e011b080a091202130504050a0c0807050f180f060102070b0f09040e0f060703020703091715090d0c022e0c20010c06 66
    0x60803c1503035001d0152002c207548500a91500c1d06a90380000388041d0240741e404008248240300d2800e951585403c290403070092180c002003607401225800455042141054030159180b144180107408588101ca10b10340d1103003900401409100d00707410520202c1e8403c980301e0f025a8450010180741c035560140024175454624105251030092a40241065202d80001601319008030301003003190f00954100c82c010401d001003010362401d01c4600c0c40c5400162001ca03440820110603690301100c1801100c0b00942c850780b07441401d0704400c1c00340c44084c0c0d002031990640d00b05401a040f0540c1c1107801040c1d003a554007110360701c03200014418010540d01103840f01c00d1600c02c00c0d100004015803555800310800000e50341e81c5644c000c1e921100100c40802c00f0400e0517000080b06a8040b5641e564400900480e900304003c0342841225000d0400d4070441044181d0a6035a110b996503082c0e403070306070744480d05141c085030b101440c103000054142c0304009100d00d644c101c0c04000c0303840ea001e800001c0b01 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 683525737 1250 683524487 683524493
    0x32012031e010f0501030b0f010f11030f0720030d14070204020f030106170c0c070e040f080c070603060602030403021513180e010608011b0f03060806150108060306100b07 75
    0x107111024020395031089040000614401c4411240082d11001c4e6414054405440c0c00d1000701b502c1003190304d00088c00380d104002e0540c030820f00c11000481040c1601d10700304201d44940c500390032442040c0da04803182807440b0134100840b0210b51703042000341c01030b00124401d4900036001041810b50740b02d2564000903154115a80c80c1d04880242080844540e00d950f100d0000034288103200e401e507035602e500200845c010100d45000c0d54130303040c078020040010905024140c1c09410000d031089139807070f24414101c00042c08403406400701240701d03002800d0743c40c03819030003c06540036940000c040d50002c10085c0b000d611030041c0c3c0076540d41d44120455407220080500848000154001544540c5640d00341000c3c501c9034002d84042c00d0410024801c8039102c00e1000d0032075011244070f410200708500fa00c1e0071075005e4400a5207100171421b000074111b9681080c1c500f0001c0c1100da0703038124500314405016568000c200c0c1a04a4020740081c4260b2600c000108048660380c0a0060709a402289610030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 683526987 1250 683525737 683525761
    0x301031e1203052a0d0e1e1609060608010608060f0411130e0c120408040306060810141302060c0f121201081b0910120308010303201203 60
    0x2503958011640316107000d94900050040c0f2003500e644450740c205143c3c00600780030000741c02a009003440d0b1040e1a0040c2005294000e01d0802c0d0f0041d018001c0010308401e0310030b005d01c14080303d040400500b030301c0c8244141c1262904201d03000b2400e6185841d1050180700d82c083c820710305503a41400c0c10741b215200c1c032000802100c1501c010a41c018104034240b0340964800020385803500c030360400c49922035221408044148000c0700c0310452034800780078003a06c1b4840e440c1400d0700140554140c600d41600e9403246019514560422500382d0f00c415043c681d004401e1041404030b09035108624807500f0f010703060031a5420f001c040a84075850101d8400088a420300c400082038074030340d00701c4404098251095480e5003040c1000c041c45104a400000c07500804a0600c61402c4103020078100900750908000f40e04501a0000d000424289008542000d50300d681c904a41d0081c0c94040c0d60b9032442c640100400d900107462500989114001e94600c0c2c000245000804106d1800030384039500c3c1409211 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 683528237 1250 683526987 683527043
    0x2061e0c07050a050106060e030a03050d022116020607260a0e03040806060f010c171810020109020906100906110c030a24090f06020a090504050a0c0206090c06030103 73
    0xc50380c02980640f5003002070550060b8200d0340c01d504c80340c41c1c4440c0d00c4109916860f000102402251040001240c58043d660062415510007036541180f04120003648000000803a8214250500c4820ad140314680410609900000f10320704011801c080e8840c50441014100c2420100c19603000400e01c010355a40001e00e9044028040f02e45959503001501d90396141036550500420b501c0682103450351154850300c0d0183c0c0c0100441e11103840f501068801540800c000e411004019544a0410398030b040c061501e08081da4008150300803140100000504080e05040c800c00f80105051300c1d090f00904bc840488140781403c03d031f04080c1c06d4942d42402c1c10195496410b0056140749401c00041400c030311f01c41a108000e21030703d012142c1c11002242c00c2110064500701c503031303080b150028010750000c107424001440c00d000c1c1640e50f4008101940c10507500344840b15102c100401105504025203503204000f1002840e50030610700c0465032510041c00083c10319044c00700c91354184081e28044038 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 683529487 1250 683528237 683528243
    0x909170918090d1103070b07080c09060307080612010b091f090510060816020705040c05071226010506070f0c0b0c010204031403070203300403050304051002061e0c07 73
    0x215103031500e00c02d034942c1401c1c6110004106003e40e40110440004142c1b40000d0b0b2108208400e0340360307154183c0ba4090700034800440d5800030031100900b62030784000795010300110707100d1146500300385042081c010080e00301864141e162000450b03040e50703100c0400b5048418001010304101499000300c00d039100c2900081501c9040405000d01d0905402c82c000c200c0e03c02c0c0d520345178203850f81c4101c21500f02c100c8590100517844941c0501c410325040e404038900b4149800d040b4a01025559a440b50f40b141401140209440000e480d0000d02a12a10ac0b5000b01441444220b981084001885400b44d0100542903038804c01e04e03174080160030140704c005000010411526048480042d6000c0c1d40980000c50f00121031108844544a0020903117107001e41c003d001c5e1100c00b400403008081d1a11850b44501001100011082c0c1040301d02c0042001d5070151001d503940714240310038025603102c445400000c540c030a00c20400056224010200001c61400c00102280c80f00a02c20400b070058075400307 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 683530737 1250 683529487 683529529
    0x5031e042603090a080d1d0d0e190b030a06030b0c0304050c010c03021e07120606090c09030201090b03070905060f03070801141020031209010609091709 67
    0x4002030201401076040300d50405500519040311a141c204814007060341c51014a5100d0301d0040b000500e00c20103040b0500382a44001440b10013040755103291681d04a8800d580d4200710700b000b0f422a880007080c0240034040c0c41c1c0700c1c5166404544030202d103040f840742d80507400c404000704841d0111900010300864020010200c0d80c2456031040c0d401e580180da04880c02d02c00d0252020003940105503280425802d9000307003542d000b503407041c02e034204001800c0c40301c5030080c0400030031141010400c00c65040d0040d0f0000601c1402c2074080300807613090310040810301028910410060381d01c43c5034072003569004600b80d0348036125101c0541c1c1d4248540c0046a100c080071855024600241d40503600c03e481c6a42d503540281d99070000d0708501d5100e00ba01d9500518407050400c015402401002d039a01003200581030300c0301544a601d420358001604086400200c1014014110001d008a40181c00440010460240141c3e140d0038001003d0108035403001002c11801c1075595003400f5401202203003461 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 683531987 1250 683530737 683530741
    0x30a021b1501090501050d1b1707170f0a0f0c031707051e030f07033c080601020c040507030b0a08100e03031501030902030a050d03020301061b050c0105031e 69
    0xda81c64200c400c50704007550000000004250900e4040d180c100c80e0041c04e1b5080541c16a15040198a0281e418900c100403400f800030701000300159002190700c0503005409158100b0b01c5801701003c5100c1070000340e50015540c400c00c400085825220b2662000954440c506145000310078009560700140c4540840c20481120117a09002007082502c00c07000c1e100d07410155030b078540510a580c400d05a0300d40c801e0000c1c4820034101c000a01c8064080c1c00c040d510a0100f074001000c0761203031421501d0340040d01c15484c40718500d6440c4903052807080c0c141981c00b0f15007400000c0d0b5900c2e6503100f10744a1510744011039282806640000d0030f00304080c000017a107507202e50712103036100741d8903504080c054900b1241d01d4400001205581c000c50390940c04500790040c2600440c094800310784166450302459100a0000f1410000841d8090b000d4a0140c0c4961400704041c000360350b0280d00211400d9010520800200081280301e41c801007400c09946944500e1101d05c5100c012009081c0c00100d8101 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 683533237 1250 683531987 683532037
    0xd02010c120f09060c03090e0c070503030108030901020d090b0d0c1e180609030b0a1104050d05011a010903150e0c0402040803070c0902120a050406020d141605030903090402030a02 79
    0x2400e40d82d6441c950300c80d2411966120011141c02840341e5010f00001e03940e01051251090403c20b0503000419a58160b040095a445490442d4070a80c45406907610020b40f0003200c0d41c040c8182c400c80011400d0040402d454448406000d10408516002aaa40e2000d6032a040c0c020b0200821100d00b40017070340e400c0414914086c1c2a030b488000042c2c0689100714001810034814040e01060742da211000178002d0b00c0341c0e405580585590400c11300c6040082c0408141c0b51521902620b0442c0600e0003c00d2110440600d503044100c0900441d0400402490a0000c2600b440c1080407034a00c0b04800143d10030822030650901008550507a4807900005e03002a00400020180c8940c5001c4c0c0d56010b650765950403950124440c0d40c41904450407110001400080540d01044c2c2c000e00649000d40b13418001013841c4101d03180260000d644000160500c40500d04083c840f81031601d540c24500d2a505189481550703900400d00305a200d650000000341034420f007034059840c0c980a41c107219800d0300d5030103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 683534487 1250 683533237 683533247
    0x1012080307021006060207060513030b040f0b060d020f06070609020a061101060b0703140a05070606090c110a0503220b030a050609160819140702031e03060f0d02010c12 74
    0x203109030005105207030900520f4015445000202c41e003903002095444e103001010342d00340d0003441441c0c01540e000580000813504494410340f00c0c1d403181e03c50464000d000d103403030360701c204c8042c1038075029005405004e001611030302140310401c030045a0389500d40c0001c0c0f5050000d0440c120780290000507024001030102d0304203990001050070716000340700b419241e180d00405402820000350014900c0741d0700d0b1030300040c0c00000701461021441c1003850700d0565116442a6111984034101d00342e40e84081060656015003442103945032280640300354a0161202945c90065041992606410080c41c401150041903c44000d00301191250b44034a04502e0410003001c1c120384c62400342c00d016002a8909551307940068200c1d001d038644100e00c1d100c012680072100743d40405405e80d0341d43c13200500402005440440d2142d013840c0d0044d9550718100706144003200c1c01c20f810110404050081c00401e54509080c0101c05809035100f0a101c0f00500048460600c4150040c00810380c544d050340d0019401 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 683535737 1250 683534487 683534491
    0x15040e010c12050609040b09120c030909070201141909022d0904030207030303050612011b030f0b030a080f190807020706050c1509030c1b040b09010f060810120803 72
    0x1644a0301d441c08140032084007619011110660700540c280000303000a40ea1f1008290801b10680840300422040000040941d004c000d03000380310f501c0450521043e1421400e55030b40034146200901281d02c18480070446410050443c00c00a180412044040603055015985641d002091241c001455044078102a425400f040d451030118060509107420200e20090180b079055000340001031440c1c404400400002e0a1907500c01c10230849403284200c00d0190229014a00d80e8102c03410101c4140070341219600c0c1152840030f4202901040d242ea4089020381039150003072050382da5104240c0310021580714003005841e26103040f0000c0207000340d200e01034503c121429002c0390341d42c2d5102c4101380da540c0500700340100280e01141c1003004c0782886901f601e400503460030440741040d4039025418144510220714640c01221035807121042d01d031601944d040d0701c5e801d0340c0c00603007941400001c0f100e0500501449040c4841040070a04590f48452101d005180403414640309000300d2a000021703a0003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 683536987 1250 683535737 683535761
    0xf040b130f060b09090c07020a050a0303050c0705030d1209081308030c10141f0806070f09050406060e01140f13090506041b0f020102070803011203090b03040203030307030515040e01 80
    0xc2d04502081811800d002c5883d00b41d401480301443c3d90301e5858025042d0301c030003402c0303800810341c6e40001255119141a5005184680c40301511501e01003c440d00d44109548501d100c0ea10409500c10780c6500142620500341d013102d004540c0e10a030307060407030151081d0442580507589c1c0c0e100014100b071020019140c0031400030305482d103090340d03001d0703000c01d46951071100321800486e1030214050442581d08001714050702c1840b00382c610b80d078084440c1851401c490f440c011511001071a034002c0d41c80f08680c400380c8801c071000c12005080c01401492030b0341003541f141c103200908050340c058450340801e50314054003810483da55240c0c01c40c4c104410042500c6590b00e41820040800e1041c5014000d258543c0c0c407807140502001d01d0701008480d04400c0130080740545d5402c00c41c4101168540c00214041d180a000881401d8610f1030b00624200c103507440040f0380401070051000694011080781c1e00244940390208403911100030007440c55509040940d0311510340414255080d0064010f102c440907 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 683538237 1250 683536987 683536991
    0x61412011706090303010311060702030a02130b12030c1c020a150903030b0621060609040203040b06030625030b0a17060421020303043207030209010b0c0c0f040b130f 73
    0x58003c1c0707081d81ca00080c080245540100313405080d06040003800f8200807400181100c80950407074000c50081c1040512000310035450307003a00505400d008034125094601180111b151000901401d0740b50001c200614118091000207580080c1c0b0030401c613281d46800245400c15a4000300141d8020f003850401140480e05001d04071411342340200c207880c42010500c40340c1301c4c1c0e0101849011462407000700303099444002441850340c03d803118030145100394441d41d00c00c00c15040050070940b41000080c056490114510100d503501e440c0107009410313241c124140402c2542c40c03e000903a0565490b0414040740c50900b89100b507240300024014012401040083c0c5d0151f104031201c001218209000c0001da40100040380010380d03001070400b07038524818007074003142009450b508050310040300b90f903000c0c2e48044014420752401e1070300c8a00411018511500e00320760325200380d0301c0b0010000d0380d03845403244100820780c5480d00d070002c13000c1c00c500400c0700c1070301c0d80d845051200804040e094504014 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 683539487 1250 683538237 683538241
    0x5010605060a021504050106090e1005010e040c0603050c1204030f0e030106061b080405030304060908011a0f0f0406180c0e0907090512010f020d09050118020a061412011706 76
    0x800c00500b103906411031a80941031401c1da52068a10000c2c01810484035036582d01c0c0c00240d40801d5114503000f0142000c003804241c21074103c04000c0d140180c0060101100210a001c001801c20f010001103945c45e090224003555031072101c4025005020580e90030a0b071900800081560099000750940200d8441842e224404010b1500303c4243e80110707808102c41c1d040b0000010a48600031454900c920000c91805448001180c21604554817000c08038040e0481841140802c6c01103c24039812034101c11004a003901c001101d26403510707031250280e9038100141640383c8494211a0290840c0b1445260803000103662500501110028200142c46200c403403c003480e12914141c056180340ea20307814110700307020030040400c0310b204560510350b40e21030841c0303010f100700d0003c0c1c21100160b4000003201a69414800d00359100e10220407088512160b8030801039a50599a505840240c680510301080800b8080407900c80c0c0032241003d0903404000050302c034200d0801a90550030b1006440c125 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 683540737 1250 683539487 683539489
    0x60a0b100c08041710020c010b090a050f0c0714060403021605040603081e071203050a0b03150c0a03090f0b100b1c0b0a0302091e280207020d0210020a05010605 70
    0xd01c4501c0740041902d0010042081030b81c2141c009254000040740584806685e140341c034078200e07400700c0002840d40c1d4680d200c04030a482c0c44c50501e684403000000070722140c54101c80104e40360030011b0402c0000c038800705082c01407081c0d2148080c0d40c05103030021603245042038100030795030320b41d4600c4d5101d84503184840815039042034020202104d51081c0424142908aa100b40c00c601002500c0c1b0301a0005124000c08601c1d0007090100006281e1800500340c14018170020540300000c01080c000e5110358180151150681900c0360300001030900e80c1d8848410b000d04401602e0056000750000030611a035078103004294100364000d030b284030510040b4541c3c81c0398110b402d0160f0451081ca4030a85441f040500e40b560700592041c82004000074501500c0303600141c29004165013441011400300d11180c18028002909500038849020407035a55101c0c070103420310440080c20f00d4041c0fa401040000071034440c159600c40e81a802407081d890009584402951400541c400361902e600b450000512 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 683541987 1250 683540737 683540747
    0x612180c09130305072a210f030509060715050a06030302060c0c030d050f06040b011103040605160b0117010c0e060702091b030901090c080115170a05060a0b10 70
    0x1104401070040c010541d00c0c45241d01240e0721128064003800700030840c000c000340a02a0321120b0300700d25000390f00403a10b0b241001d40304103907541103000c1e10607040340b01700e40071503580107500c03a9a0f6206141c0a840b1300e003454200d4540c001d000c007882d04124007180060401129640c61074001c12484001c211594034110600256201840040d025070480c00c08508014580c070024404a00950300712807403d241c801c585021508202c8481403090741003000c1c041585840d010b84055804d00f440c101d0f103852400b40310302d61244110f2166100b0300400040000b440c0845039500d0404075080750801e17405694901d046112002d41400d131415079440e090501c05040d0180b00700b240c5031034002c0c0038103052044030740c244122804050010301042190381d20040a4003c2e00c1c0c0254030070303ca4080081210307103491a150b605c0303070a107070050f0f00340fa418200e50844a00440300310030304842d212031400c088901d003207510f94100040900003030042d000d080100200e024558211910b50034060342d130344000810b00201107030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 683543237 1250 683541987 683542003
    0x90503041d100b070210030912081f06050301150c0515040b0c0f070b09030d06180e0c13200d05010f060f08040311010e0316050601060c030c0b04030e061218 69
    0x3010f803080c0403402c090708040300c58003144152410000f58100c03141e250340000c980540c01060003d042c10703041024000c0480010044c0c0341e101c91660303049a040c0079000c0c0c01400f0500410303079042c4000c0d9089030b100340310300c030010039441d04a41a2400341c1400207061640f40c0003140d041d29084441e50204980f40c1c8008200d443d0807403c4c0f113106041010603558210214405080000c0e03c0c0301c1480f00749405001846100010600203101212a41410e9100419104c503c0706090750b5401542c1c41443c1c81d02c40340d83d84110103c0164000901d04209400c40140a402da4000c1200d101c0200703507481010102c0c0d00c0b00d41640c9100c40d0422200399189411608460344a01d000000750700780c404500020700034a001c3c01d860300d42c07200206296011488182c5507400204070b0441d40309040c4030f0a4140081032200d140545030b81d1034141000d401c1358070064480340e031990380288404032150009081c0761144c01021003040d402803ca40e80c80c00700f103a0303d00c44090256a04c2c004500c010590300c1c40c1901c0010461 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 683544487 1250 683543237 683543249
    0x2150109151d0c0f090907020f06060604051806041b0203030a11041202120106180f1a030a0f031e020c0415062c040507020d09060503041a0604090503041d10 69
    0x40c030103540f50010780c5919000020140c071030110a02800c1510754584c40014403030407182e4010200f0f0194030081ca40741c55009000703280100d1017013109100d0303034660354141712210901006000550f01d03017001090041120b040304102c40849066001c040d90390220056002c1c0080c4075051292603089410f0a803540304620610001d003030030564050050900188600303801820350000154980ea078a0301031305200810f801d078440140d41d0855031a0001891040703003100c00320051000800c8042101091362a2195500030740f030074030b00d01110b00802d485081003c00c4016410200c07001c00700c03280c10103503480000902e4203214a0a01c0c0b4607052102d01744012004070b035400e603a40b00c280d08450b2100c4455840d030321010011102c5480108201d51101e000b164010402076006080f00c0984040052190406800841c20040300300140b002107922032840c240b001903110b4407482692540d400240080c145540c000b0114080407a0004181c2500d4005107000c10b41c050481c41c143d0380b501000045500319020300 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 683545737 1250 683544487 683544539
    0x708150402250213020a02030901090e0609041416030807210509010509130606210c0c0303021602030f1b060421051504050115050d02090103120215010915 68
    0x785403008071224507a401e54005489504604c0601110b08160f80c8907100c0400582d000141000c0740356403000454000f0a440d12081c0014105100000c804a002810181102c03503011a40301c00342c1c00602000c00c03841503c000c1030740381590701c2c074000324140c00144050760604070f05840c5201020803400c50740350510181ea50a0724200c0b13580010f45158000083c07840c0c04c030114010051026106100f0b00018003601d448d041c86100801c2c1c0701c011107040c00414014211700345044040342503081620054007030b0341403d026131540740088002e204070000c00c1002e58188100c16101c82002004035051a00070000484850080c0ea01000d10515103d51f2107080180026980007140c0c070100c1040d2003d0325171240050b18014a815604040c0b61801941c054400e80d550380101a001c03010014010000c00c0260b40c3c080701c034040c1e030300083d40c003c03414800908040d11f54039282108a01c00e000d424802005100e42000658440103130100801142d0f2201c0010304003000017003030a07240f9480e15030301100e0008031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 683546987 1250 683545737 683545777
    0x111f02060f10031a0a0b2202070807081b0d110601090507090e330f040f110708070b0601020f03041505091f080708160e030f01050708150402 62
    0xc03807a2040006051080d600101c00022000410b180d114460000745000e203600c882c02c0c00003000c02250000b40070903100f140103000c00c9400402002d1311b0209a02d540c880103844000508018040d403095010040c020800002d10a40b4400512404c09002a10008458400c121428241c0d0918a00c071a411101d600c16401041000020b82015038007041d1072805400c0265035a04400954030142d420390302040540e103007001601c0404104140080010a2000b414259000454203035031072040c2c070750300079900c61014603070a01c203d41010700400040c06986540d0b0344caa04221105800075402110700045010110b0721961002400c0c801c000a00d0000d140382614181d12012451403400394042801810300402400e5030b10525164084c0c903000d82c4002d00400700c003500400304907000b0603413400e120b548400d12099001e100e00b550b11550f0301c0d04000e07008980c0c01d030020f864641854580405907007014100880d0641c001c8665001d0f003200710000d00401803001c2000203038065026140c2c040019003003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 683548237 1250 683546987 683547001
    0x901150f230d330b060703030c0315140a09020c060c03040f050303010e071803030e0d0201030b0901080c0315240d0203010632060409021b0a111f0206 66
    0xd158442644018144040c1c0c01c580d580e100e1541c0d20300c00c1e150b1405602002412008260012050603c02c034802080020f03500c0e54001070000d002d140d03170180405a40d190240001030096104659505001c0c40f01d055a640c1c80802900c4442a0383c600da0181200d9040028132024900175a5031810340000601000d50740d100c46004a50402041074038000c612203056130108006000840c06042c20603200f00b01e031324003880083c225040750a50400c9069503071038100042640550003c1c08818102e401040110039400100d000e00020754050340c0c4100f400e00000f48072040022280c1c400d100681c00d482500c04e15104039035404204843c0c0300894a80400007400e034004000070041d1060740140300a1000c543d40d0046401c640c8150407101d403089021484035180302d00c45500c5442e107801908204012414003012a14502407032003220441900401c0f09500904400d00c0110084141c6003141d80e14001030624060032014002c03214002c0c103804442d501309501d10444129101400d070028a101e8803006 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 683549487 1250 683548237 683548289
    0x9010308070206120114100e0a091e060909030f020601061e03110c0c030f03070c0b1612030507030f02030c030612030c010e070512071503020306030c06030901150f 72
    0x40340490380f1880c104064583e0070440044140079100c001c608800c64070a800a1041c03864400c403040d01442003010003d12595602c805560980e441c9513804210850903007a17140100090b100c4a06043d420508045400142031340000c2616009030740348c0d03403d40d150300301c01d0740c442c102802140b0001c0c0111151180748000c6520302c0c1c807000101d281c0001ca582e4100c0c0b2501058002034000a119005181e0016403842d041101544c0814448003843c03420249079201d0440a0007440b03412070201022481050b41d00c0c262070b0441c9030f1034006401c131917031500d9400010b00502e03048640c040800e24004010104840610035244216082440380f80703540c0326042000b501c0030380103034440003070b100812504dc0e1004c020701800180c0040300340140001030034402001443c0080d000d041005611004040244001348044004503001c90b00b8010f031740c2d40351030000c6401e0180b89001260410000400c0c08081030f015070020940000c3d0070700203840151141c0001c01060800e00c18900740140304420412052045 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 683550737 1250 683549487 683549497
    0x270e011203051e0717032403010605180f010b090a0b0c16230301050f01030f0c09020f04050f0d0210051b0709061a04081209030f1b030f010b09010308 66
    0x2d06225041010008090804100d40014a44000800b152100400c03440c4002103414480c1003c102d4190701d811411481900100131001c0710745454440302e4041d9403400c1d4080b50113000042c240710400396038001803506410b002e8030489002912200000342d484d8605055070030000d0000d1841d107846140c031811003165084849480c07250701070644103446d84004d4800040003041102c000c1403914801078042540d12200e00710a40c0a03904000c10021100e0741e00c0b03a101d0669a001700540b00760101410f10f14100035094101c1e00c070282c4006490100d1030444001742049030340450703403460300e0305146050116805103060002d421070078030000c15030454064400b603d24124240000c0001d5004103510524041596200d070b804103507200c0040c4511896045000d609038030080c0c04c0c40c41e003032800b0711550351502d440b0904000c000c0080b03101c13109035030144264800d03101d04034100e6011103e1070581c410407900f8000c0c03030b034800c1c8030f9814400c10020042c002c0c04081d0304020311000b09680307980c5401502c0e901c4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 683551987 1250 683550737 683550743
    0x908091807111f2a02010c02010e0703020d061e0e1605100c060f021e0711060c1c0e0d030305010503060109090317150604030f2d0f06020415270e0112 66
    0x2421500c2406101a0134103100c02500a500219118410410180c2150311209a100058119034030074405030711601d695540541d4000d40000f00f029000701c00440705402000e40d90703d410b06004140c80380c101c00151545030005003221802c540d075950802c1044200f10111010040b491038141d240201c0e10560002c04402c034003440251800c02c02d600c00c1000071203440d00ca20300344600840d4440074050850b043c030485641c01d9a5051400e9090321032135960b1030034410f01c071400441c81c0700c403c00e041c0d00c40c902410760510041c06000e1148264540900600008d0050b2800381c4107035000011101c065001d500c0d41c1c1c5401d5121164411406241a10001c400030641140b5051000c4004110740700d040046c4002e42c000e003209010485e003840d20340c4240c04010140d00340e84000d601007840000e840000b403038041c2e90000c8581e11014a628042c800307030140790f009224131103182214240840d000358030800c042c0e2188180d040c80030305d00742800d810700700e47c0d001b0143c5258180340148100c4806440303407429940 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 683553237 1250 683551987 683552021
    0x6050d0c05032203210e070b0309120703170f070f031b081806040b07020106050a060f0c060908040b1b0a0b01030b04240b1914040908091807111f 64
    0x41c00c3c0c2045a0301740400b000300c0302c10590302d10103105006e1060081c140034100d10a50f081c5503003401c00d0030b03070743c4d0300b00018010221070342c005a11001c06008424100c48280f94280a030742038548040003201c4c0990440341e07200840c00e900c20304800c00784240305951040359038001d81c01c0ca4040400088401c002c00428451075410400b03034400c60710f41c04110709407049104940c5a80309160900e8020f00f9901036601c21030184640141c00d00100d03400030f020038000c40d86413902c105e2181c810308205010340b041c1000034040c428005404a20840e40e2002440d4210011703182403c0b0380089440a581c514a060003c2c0500b40c914005200243e0303440d40154200d40031340b00c188610810309a1809981d0010907103030b000c0350740d2801d1340360302c0307003000103440d202c5900440c01c0341117440c60b203a0106080c040441e100c600c101e5554500408021001055903200c90000d003195580880070602c8103040c14055400c8400b184001c03c40750a0002e0004983c29034625240320901c500d01342d130350000003800e04080300c503400075 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 683554487 1250 683553237 683553257
    0x10e03010f06060212030106050f030c160b0a0b060306031005092b09080f0d0e030a0b011203180807031b3c051507030203090303030106050d0c05032203 67
    0x66000d00541c511085400400204545024030107403802d151800031540300c0006000400041d80c00c03000b61244803114040140c1e07269552004020284034641c0900040600281001c040c0540b04200a21480c82c11000f0040140b2080400010303020458010b50305520011131241a10703056005981c1010420084070500880d00c4a110001484c0c40c00a56a00075104080360b0034a90009448004202441c09080403580009600c0d881e42c100c0200790040c0912601400c503e0740301007100041003038011805152550319191301440c045050f00080c2c002862006044071640d0300740f01d14800300c9044900408010f803039540c61050540f42c9000542c0710380400d820000d00c05200c50310b5010307088840ca0854000c1c4d82048038010505208080281082d80403001c18131060700c40c07168849041200c58065034562070544ad0482c5076124107888990540408000050750783c5c0c200b0050b0065007591801440400ca0402c804c440d0340c0001c4450100c4258428107031344105412600c8148000c2c020b280807100d074 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 683555737 1250 683554487 683554489
    0x7090c09180203240303120c0d0e0f01051608012c010803031618030b06040e01060f1d042d0501060602150f09060720011b0e0924010e 59
    0x64514441e0316051a0004104200f113410b04201c100060080054031075490760341c002083e582d0040102c141402c891000110314080c0b10340044d29003440043c44140a05e001542085884182c1c3c201000c006608220110340404600d800020150b00650f54a07280c036841e001481400c01211181d1000000c101c104d49003032412002825030181480c00011503590078200a18226400346503044402c002e8030000440c0da02c80004031090850b600808801000d84400307002600030309002071509403961814000084020785449100304590380031030721003451080c00d405510360013800c4a00804401c0c54a06428231180740007040340903071440480419051003e9601d0508650180e0800701c0582e01104800f2420300d024192a9030100c440207003c685418800941545c1d280c019208400b13204480300c114000c0448890700c0360f64908010300a025898051194801d11318040000800080c0000b080800ba41402086140507010140001044416004400c1c84070004c032590f15040000d180030304455 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 683556987 1250 683555737 683555759
    0x312130503040f0e06191517010905090f2808090904030914060708040e0405030c250b0306010f030c030905060c041715070f0c140a060b0a030507090c09 67
    0x282088101e143c0c640c9080880032401400c0080401d44200c042030142d8150305081e80700c040444400385020b20800350b14400941c0d11441030700458041e840000c00025586900d904650701036100e070b800b9034179009a0841400c6e114412100ca00d5141c101000304402649480c000d000903c03805241c6081c1080c44501c00940d009030141c0e0705030000303000300b401030000000041c00750002507000c40b205c525284495175101218010740c40b500a01e41001c80014061141c14411600c0e500010002c0d039503607907170400101284008003d511a00000c20344401b150380b080400440c1e010703010503100d04c18411040c110440107855951601410140c07101a10000a002002124060340d01004140e0f1194100701c403e5210003160310510245501c059150b0034807404c4010480d4102b034191412801e003a48911043e00d11170000c01000b03005008503007801c8454500411a440c130709200790407e009114a541c208200b110791404060100d42012504000400341540008006201070803c074010690320407541207 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 683558237 1250 683556987 683556989
    0x803070302100b040c212a030f050105181015051804090305030c092101050703060f1406131502030d062309180f030405030601080f031213050304 64
    0x903a00c10300d9510000b0034203002d18011030a0680b0b0411040600540040000c00c52540408000d034908151606042107a00003a080c4c1c01128a440a090740b440c19000c6080002c1e211500040d140128100b401ca80c40d009050489000815140c842c038100540b490082102130418036003004005d40c0002c4800015030000c20b4000140c4502c3e440b0b0b00d040c484845200d03846146907200318501205180042e42240607203403c6001603c80c01d4441c0c00302004104692408008508072500f460080040d84805402040c801c0a20340d5040c00303050790314600080080b0300c0d40071301c2c400031403040e22200460410780054071030500c00e010f1b0544e100780c0d64000b80d10310040344100d01c0d0040e000002c4003840d20f81d450050380b000b8248030742d0400c0350800c41803c241d0a801c1400c40c031032081100001144200201031010030b000c1c4074020607075050301350a201c990b07a6503100f445218013901450b800001d1807080410320f4130340c0c1900e81c0003551501001c80002040a80c008040c011501d401e0040100400c0c4104003901c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 683559487 1250 683558237 683558243
    0x30c12020f0f1315050118030309170708010501091e0606020c01030e1c0807020d0f02030d0e1014091501030b06060c150702011a0f03070504050a0f0905060a060b03042a080307 77
    0x13031111410030703000614000ca05034425028600c440c40800000b680651010122083e540c00341100c018400c06442c10123410307a1240c2815800c00002140b0345030154080d2144072040b115032042100700050f020180c4c2d00910401015030811505800d21354000c1d00002c000c03403040d20a0703e202d0125085040110400c0008080005400004101099804001400a80360a814006640e441040009550744039450300881c0c8030b5114001040010801c00c164800044018424012490003c8202144d000c0844101d42244140051510101111460141030726003000341d60758a0755903681488980e500c00034072030b800303031142c0300181000f000500120707070082e07030143c2c00481c4010f0841910a4000010700f0018891460300d10300d400c0c00c1d40d000034000b00b00c0c0c0040e2400b11f120b0f601c0c14901402450306101c0c5070000750030301468604005001c03c04a00c101d1007400c0c10000a91580d00703030750080c0400c40d80144410f0780880c0c058483c1801134801000703e907842c042c240025032507102560441e00003000c11 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 683560737 1250 683559487 683559521
    0x30c030b030114061504120f0807140c03100606080f041716060614031905030f0f0706050f060a0b03220602030f090c0d0602090d060c09030c12020f0f13 67
    0x400285c0c60041074007620b001c130003491281000d041001c05000451a40030003040030003150003542c10888541e050714045a04040040007941e500302e40d1340c3c1c0300c3c0b804072842c80c030038054507020f0200359242d4400c03081130b1409591480040c1d520600700d06284c1e540508191121305600d00403584100b5410000c2440c13501c004000c615031800342c5854000e0b10034a42060b044018100340c5015607440014500c0070b0f000708040d40c2a400c55550820906600c00c0700b68950340c0090004111045024010042c210b5500c501e00400560342da40d0150741403402c094505540c840c100784010000415402d0145030425071850b85041030640c442e8060f88000d100c43c1c0d0446015402004201205c2c3c400c140c0140d01060800c090b028202d218400580000700504000b440180c0c0854600002c0d201d000d40d00345107582c015001c10140c55895405000020310344070440e0040a1107034003283c0c02100300307000b514080d07000e083c000c03a00c21050304000850b00e1890486400951800b00c001c160201c1c1e00842c0e40710341e82c040700 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 683561987 1250 683560737 683560741
    0xb1501082406070c1e0b0316050a030e06010b070b09062a09030601060c11040605010206071d0a0303090e0109020c0316030c0c1412120307200f030d0c0c050607030c030b030114 77
    0x442e034205c407000e82c040412110305004126400300c054103d2032200d0200e103847c40c1d41c0c8000d03000c01d40040c600441c0401a902c00c2c480042000c140860003080e40900030100e894050b6255580d90342d4941c800c031004450850741811070311f440481d000b1080154050024a1800c01c0d00c1a000701c0e1400d2000da00c88c00003e000440c0c44818080750f0202a01070f02c400385c1d01880040e08000000c0c2d59410082e092504200e0300c2c86c030421940c215660305600c2d0500040090360102c1e542d06004140c503c0b18003490b050059413000000b040e54080c030803200404c6890b8042c41c2070900c010304490390341d450564103030280240110040c0000380303101da40314003804242480900300e00d030020902540b242141c020401a6110701e0701400b080c2c101c003060700d070302020074034100194a5902c00503000c8506c2090021015203d500354240c401c0c00d0100c040e1641009400d410010420b80b800221032707028407450050019007140c80400c8905100390440e86071220701c1e050100b1300e00c514801003421201c05050900c0d0740c41c40141 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 683563237 1250 683561987 683562029
    0x5090c04060e0624090301020711030c030636010e100e0c090609040203120309030d1a010c11010917060105130e030a03050601020a06090b1501082406070c 68
    0x4106805041c07100120b91040c42e2441c081070361502d8445030a0003110010509055020409086404124000d0000e540310159854406c002e040001e490707510030301807000c146d011400d00044d07079071140210f0350820514140c1c100c800d2000003030343d803401c070040c06c50941032084440c03007409040507501800c00105200b94454100d0401c43d5180ea0041c031140d0071401e60500c0719580d68054540100c402c680e0b426950f2034500c0084d1520442e8007400d041d1401c003204102540300080098202c08440820a1000c400010547e5682c074150307240356070119942c0180600400c1c4002192112000107043c408002274540b4109501051845010707100350b803000340140260700b0700550300c0f080745240001c00c1c006110340500c03042d1a405494590b108044d907480025001d83e208002031510b076500060304028a80541c00c120346880d500300c42c200d41280c80c200a10034a548152032061113403130611985e1050040900391082d100c03803154101580250240000d40c0400c006400031002010030312882e02c5611000c5c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 683564487 1250 683563237 683563241
    0x150203030f01081204140a03020d08070c120803040303090f0b011203090e0907030f03020307020d0f0204051806130804050907050406020712470106020c060315010807050d05090c04 79
    0x1030003044044d04000030340e2010f48003200c103135003d490401e600e0981403020740f00405e40c41c11035a1b00107540a9040107002c001c1c0403d52000300300e0309008080c3d2120403615020039880d0900003c800030030309102000000c001c2446544050b04107840f4100f0b04248880c291a210301c0ca540a0b0042e440d1189045148420140c00c20307025002085220004040e03445d080b80150b031207046511015207010803600c001c00816100b030080f134078801d6004088d0f0103040140d0030100540b481c0309400301e01031454503010490003490f813400503d001044200401d405d9540420035625001d01c0007045440c580140000b081f6030b99140d070701522032040c0c0c0c4d44094996181c010024074100d800e43c400c0c0802c01c103000840303022850000d08000e03d07007800ca042c0703c00c081c1c407200ba00c0b07075840605004501800c01c130200c414100044555290480c2c01c0781c2d0844001031181010820741e0700c800e440d50302802039607882115403540520304a50344611141403050030101c2501040050f18400c07500f480c0e080c1c2228507460401d103024 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 683565737 1250 683564487 683564489
    0xd020901170c0a290c01050106030b4e01021602010f050a080c0f070807030206011503060f05090705090319120f020c0103050603070f09050a050906060d060b0a150203030f01 76
    0x1212503800f4145042c044080d0b42e68130b480c442044004020000200d21459000c40d074503140c810b40208400d41e940d0200500924500300c41c2842113010384007000500c000c4103461940e08008070082d00d510b804201d0852401c64291a01c1941c401c6d00e14a8014003040a1000d801024070840c00342501c0d450601c001030101c0c0c05030f43c9142c24801d0901403d44d105034000307801c5a2109d440512603940e4404a20f285815000b6031000401031350000070018109940030501714100c40800110010004800106030141c9820380101c0720301e03801c051010845031900c005e0640c0c00003450705103030340340c41e0395240441e007052000807007299030b06a889170382010890564260b0044e49114500101c0c101c0083c1c034000c0d290058108150304158480b00414965542404010300422303c80c00400b0006035030340c0f255005000111010713100c251909000515040003c10210b1048400a04001c0f40340c02d560b0300c58004080e16400981c005c008018086018003a418218034050000c1c0c00458492400715540f480441d81 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 683566987 1250 683565737 683565739
    0x102030313030e0f060a2d05090d020a03060e06100515090f180a061a120106050310090c08060f0a03020306062e03023a02090d020901170c 61
    0x2042045942003036940703000c400303580c14030b4030325222240200000e0219840720b03200ca038007020000d0780100c1180c22883d6040c10588150050504a140c510001d4420200c0c403640c501040d030400000d109072801e41002680548000c1203001501d440742c41e4142210b81e2461070150350303800383c401d20580d44c5640090b00c000b01412642d03400302d0300805c0c50a041d2401200046401844020283c4050395100c503030b582901203031110407410514010b00c20502410740b912484498a44001080304122341600840d25034108003059a602039181c400c0440d619440100143e4182a10b04c2d0046100d940a00694041444079a56a00b803801d0031020444c0c1030a60501462194407243c0d001c00c01610085181c0398010021111041354420b1100240d50801168405c40d500c0b0350506000000e80d40c05d40c1c058203541680302011000c480301880c031a600200380f000c0c0c0c1e5810f03c41444410890055a4008102000c40500000e103412000c1d4041280c51a080c0c001990f840007403c2c80115005041260441d0104 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 683568237 1250 683566987 683566993
    0x28050c1e1615021e1b0304030c03260a020604021c0b04030813050313030b0f01180207030e1306090e0102070b010315020403170301031a270f030a08150102 68
    0x1c5280904071a0503500d540041100600410402c4060080e41c140d130b42c10009a10070f43c030346500e0265403550503444001c2c03990040c05c03c40701c02c0c000700e8800819036050300d6104031a1203016066458424035000101301c41d40720141b00208250f42e500f03003036000d403540c0f40701a001030401d81040d01c100b208040701080c4600b58904603125a001248110300d5040c1c02581500b414605078603022601f002c210100500901340303220000e1403455041150300620300326805482c406125407140345880d900d24100384501d00c14181d0f030384c80395007030841c540e40208070341c0e4801e041120383c44d0300c4180880c105d4908200d03402009a0351f0034003001740b0314440c09480b00d417010340802145010150343c1c508484400600010b0205440c03854000ca15001e0b9074102d601554008000114400e04402040c0156000340400c40301c0220300d119009014040d00c0c0e2040c0641c030b40d0056050070701049408a41c804050700320b00d040a210b0048051101c620034401000550559521042c407443d1024048240303440307004820341154 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 683569487 1250 683568237 683568247
    0x130303020c0405220312110d0606030203070f080c12040308091b0a12020409061805010e011401050904061e0b031b010905120102090402190206060d0201050328050c1e 73
    0x4d40b1400a10900d0505030402c0d034050065410102c0e543c0b03a8100c01c5084c014a0410852620354502c00a070068800f081410310169407a504214140e002c20782d54a0045100c0400c2041d88130300075401c0d01d03030100c1108032144c1002541d20a030314000d01c05a40c16070100302d0800600080001c14407000c2c2180502203840c0481400b0100801c400522522a00b41e1244500742400119a81c50300040303006d64000c141441002c2058460100102003001e0440700c940c40c007240c0303220442c81806411540c640010f01c0d075050fa8641000c1c00040e900040044802a0780c60240c000b40e501000740c00e00b5912000315000903a0a204418580b400400441e500d03017848209400300c44030fa030320856101c1511020303079155034110500c900803070180c0541c0400d00e5009002140e81400f0021150321702c0404d42d0507a0807a84a922120140b107903803594210040d00249003003000038810908800399201c030b5120000000c5000d502500c0c4901100c80a46503014180000991400c41700300e0f03040f0380c10301881e00803035031440c1c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 683570737 1250 683569487 683569501
    0x71a1006030b031e061e2202040e0d0e01020c091b1b07060f03050a090308040803060a0f0b09010f0f09121a0703091e0812060312130303020c0405 64
    0x10011441914109501c5102c400c1082d2000c1c02204440040c120b03480e0422591440455101c2c242141c018070341c10800c091040c0041e5110807241d024910303901f54548004100c1c034481c4100d51407500160380007030311160160342040b030800203407610742d1065844141d0200710780002414280801400742c800c83d20007040c441010300140e02208001c40703034698a43e56840c0c0c030a81e41e040810300210f441c0203000e52600012200d41100d09a14040040d0790300f0001ca40d94072444100701c0700c010101030001907800b0001000101d1010007103800070300c010806070089a944928a00c078000c183c00220003070002107480b102950304206010a150302038100100805041d0200505047c514850302e411a1281081c04050050412403045580c048204941071403820f500003801030914003004465070291030000000004e842d044002c491940300818502c0c112841104120b00c520141c80254140158450302c0d03020410720300240281c0000e40c2810339031914504000c0d08103103107484802c1c025802e1074100485 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 683571987 1250 683570737 683570761
    0xc2315280c021906050601030b041a01030b120102040b07201f0309080d09050d02120a110705090106021506040612080d060e070e360c0915071a 63
    0xd00c50146800054400001c0c0040785400c119000441c03030003059100340e4050101a4004501c10311007070b24280001d0482d201803008a541b00e2050300c02d02c10f4000506601343d8401c0c0c1001719981c5d0010403c6090b54060700d022800c99000d9801500f5580d4006180000c000803244c0002640ca1384d085030946450a2502040d505207040780c0c2c0d1181c1144c40780b00007001034060b078001c081c1d56400048403600c54000c42c00440081c5240034007646c03248512000503280c6840051800050f0404e18410f07402c011428030140e41d5541c4985614480780038561000c03c01c1d07166565001d0003001c080e030041410902c000c5003400494400360a040c0141d05016051050f103003000c0d084d0040d1548030a10036074a560440700c4000070603654000c0e001c050a0038050040c0c1951003c00452001012501c0c14019803030206980c035415101803070264040386609088112101c11018254402c110018841c54554000b00043f940041501d01c04d000b50404108079090000801e00c0000c0380c0f914150014450030104440d4803 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 683573237 1250 683571987 683572051
    0xb0402090a300b01170a031b020a0803070605040c171f0e010c0e030706021614010215010608040b0106021b190e1812030c0405010c2315 60
    0x91607420002c180c2040c1040341500c000c0705080b20b2000d41482d03041c0c0b6182241000a104d20714104400c20a0000500e001280c2480d8456154562081c00114602c8a000740782d4145820313a4801d10708880040c00d410188020011140300348000602c80c5801d140035604e401685d0003c82c07100d00c0c83c8001c00340701d120024101103240d4280c0303c407a4200141e02640000f800b890817200d43c03154280036402042a820018403205d501003217081c0e84a503a101d031412030743c44100111010401c3c0d001e2504010004d080e070521f00c0510700610583e10711780004122050004c90a81c0702c1000500c1100030801030112000c5018007401662000e0f00c407061000c0303c0009021800c0c840d0760320a400a01070295004001d64030345004010369060030569281071840350206681d000d500e180d16004240c80142a14419802c4a1199822680302800c10b401e0100440307140c060003000f203904010819a0400c51002840c2c0b41e0641ca0501005106402e0036496255030b02c0409031084d00701070101444503003110391030941c0d04 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 683574487 1250 683573237 683573249
    0xa0b22230d1205040c260c1002070b0f041e030219081f0f0c0216050a0501090b0a1202040b070203010c02011104120c05090f1b310b04060908010b0402090a 68
    0x303c2c02c1e88550502c0640d4145980c86900c1c06000c445001608031020f824403021079554a00340c0b141800710206004400a20720217041c0142c024003c04d001d40c2c0743c1175020b00141c400a003901814903840d240300310440710394004144091505120200211b140c00c098043e2812001c1303000110f240e1030f24080c240d44904400e03042c841c0f468088003403040509160711060540085420510085503d500040e4851b1200ca010080c083e600b414041003d0030021407010407182d040e0b40f480c820b01d24009aa6085401c40d0a0400c1004202484488060300c54009070014101d40e243c1203544030f00620401d800c54141d11501d000b9a4100801c20b03090a050209440844540401c031020b80c040c9450705c81c0300c12020760070483d40080d03a4010300c09211103030300c200d5220b0014407180d00c60350001040044118001c50249005c03840d011842484605040c04043c2d18500491411500341a2140c6190510742c00540001002034465201040345407424002d400c5032203425281149040c41c0349000c01c8030071446000321 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 683575737 1250 683574487 683574491
    0x302120a0f15060903021c02091303090e010e070314070206011e09020f2203022d0d21030608070308030c1e04060914030a0b22230d12 59
    0x5201c000e045a0080101000e03080001d600d0b40b500c0f8240503201c0c2240307010a81c005d103160500800c00b82090032000d203115800903c17007012540c4141038507032403034082c5004608108107001c0000e151610000341d64081c01100158010030700d0250401004c80382c80c0201411039a03442810301070221380200301281500c41c0d01121401070030b000024030598250319808058050b20000d403130520b42c0034820140a03114922060b403526400c00c1c4c000407030018040c0c000690b020055410b404003402048944001e1412000d2402069001070800190382201e030702c5007520b02141c01d0100c100d0340c0c039448000b06000790040c02c041054a0038107203050f54414290100408441e000408503e0103070300b40080e14010030710901229924041003403620041d40051040401081072a0302c04588130001555001c0ca845d8060005d042c41c48450712609a4071001070500310320401680111105021903040c0b5403141c84c090100210070b068070010038014460501e200c0e03c2d0b2500300c0504081415800b14100c40844015400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 683576987 1250 683575737 683575751
    0x38071710051c0b0a02090a050d030801060e180717060a06091214030705010b030712200f03010f1401060203040608011811071203060b030912180a03050a050c010302120a 74
    0x42d00103101000c0e00a008116082d041100012940c2c00821590b0410303505d51108590355010302c4500304002c0340090200f600e610052011602c48d440070032001b103000f844417601e00340590b107080300d44009a681c0c00000d84100049820031410900054000000b521000421071410000410704071160084072100341d039011014003403100325101400c3e80e1200f5019260b4440051510074000c001d1044018007a001d0541e00003030401c0d04200b00115960001c114074400c0c810103035981d0200f000d407207106601c400000382030042614240310702010030700c840d480021080b48915050311a514141d00100c1150301c200000d002842e4441049030450f41e41208008801c23261103200e03005091242000100d6520118114003404603000c8c050031320100300d031000c00c5460b44940300c0301100c1c0700440b06c112843d480103026074900b5550a0090205031310700d68030807284091100000d80e5810a070740c400c2d5160b80c880080c080920005005203a10480d003401c0c11450400321100a602c2ea030b038010540c1452a6458071 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 683578237 1250 683576987 683577019
    0x20109023115080f060406051b0405040e0a12050405150414010c0c051c031707200312100e0a020901090303030902130e0d1209050a3807171005 63
    0x1c07840020f01003040a43d070240070360141c5140c1d80ca00071601620813900300000b0407040058071210048181c0080c581920b0a400c00f801d105c082e11901d004070040e0700c034580180b8085103030780c801054000a50303036803030340d446140c10100f040d940d101140c115038051040008100c001100c0a030113501680a081040c5005024205001c1402207030744860303040f041039003c21102008401d0350401740c1b40309450350300c2110702540c0251148502102d54201003074441c2d952000ca95461100041c10111084c200c034941880a2544100c0c0352055511246008551030207020484c0300380c510350b5010500c040114101490800000c26030400c5210281c24503503074202c00401d41d00d81038411048201080340a02c0140a110500f0390707280199001e28000803502da032039400d030349100d004504156070410700400c2c00720071310b407140c46451034807203000000c00705410200d02034503100041d5041200444240d01c0c103646003459015000d40048042d501002c2a000c080049040f14645258103a500680d140366010103085 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 683579487 1250 683578237 683578271
    0x321509060a031a0403030e01051e09010605060414040c0f0c110d0203011e230a0e03070203190606050603010302241c050405070f0b0a0c031403070201090231 69
    0x80c2010f0000302000301d140faa09103200701824007a620a603410001d405040c900c040c02c80303030151540c014000c4003400c60460240482c4600342c2005051000080042c0c1e074000080090784280d104004070300081a415003e803920344150f00000c41103040c070201204d43c011008280301000701004006a07160100d0781c80700c0d05e07501e100c0c030441913016008002814140b00660b20051840391001d03c040e0820344030401d10381d484040c459842000220020880c2c480e16000b00103041c40c1014148684820b000031800340e6410030848000c0c00801c20055248440350502805480d1f0a0f000070340104000c000400040e111408000026103c400d40c441c60342080d041d0f60304103031051800070440c080c4030b0b60219589044940c0800d004901c56022248a280e507082955240c0c0041d114111501c1003d1045034900c90003450000c401510910742541444400319111055402c2a1350b6200140c0d940c05000d000c50800c08408501540307001001b60100000d9903002c05140d110b001a40381d990303201c8005a0a5000d84 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 683580737 1250 683579487 683579489
    0x903020a060809100b061803120f0a020609120a030f060f080c18070503162102040e0a090b0c070311030304050312150a030210020f01321509060a 64
    0x1001420101e070307030785401012404165200c241c14050110400001002881022030800026208508200049100c01c0704900e6600c003441e0175000700801480b480003920014080d07074901c1036449403210244503000340340c1800200411002c1d44281c8912280d00348100559800710b00500c0d010400881c5041c4501c003411080e800907805504503d030200d0310702d0003c04c1ca9500071400b50346102440101008030100000c003641c03c0008104100041040414901001c2d0b100320886e08000c040e190104202c108000f04800c442d00c50181e0100707007800b28000b0415566008400c1210034040280719407200d00c40040b0150a9001c0441e000481d1020140901c1040c0707940300210342942c1e124175044c00d2440d1258024240240c00203103010000d80b520645d84041612075001502250965041d5824411101e828401000961048030740e180d03480305d424020480240c00c1120380c0110130310801640800c045015131246a488010780c10405103603103824400303030040b9045a10315150340710f90340403517030820345 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 683581987 1250 683580737 683580739
    0xc1505010506040b0f091f12020310030b07020f0316030e0303070510020c0f01060902070b13120e180709080f1b15090603100501090e0103021305180f060a0c021507030c090302 77
    0x103410701347c07902c41040c0e40c422000c240c6030311800c48024281c0300307030022848225800d20034810f0282040c00800c2d20f20101c241d0121890040710400e01d64091f0719451504402030703205010640021100805a00445800505400394003e40c00c2500f981c0e250790f12000d916001e00030342e503400b0948c001060410004000e00f84491402089401d07103484003c000703035000c0c0300251760a03201e03100480c8103c1561024004865041500610300c000b6050040f292180910325a40e80402d0106500e254507600d40007884c020041d41d1030303403003d552409142c18248040700f0b400001c6600900f81440094154111120024030219008003084400440c060b000f80241030f88203401c03440c08030030040d034141d040d4480002c0c0c8400741c0350a00d00700c0c1d4403221050554000d010094200d282c0a004030070150541d0800c0740c120b000d10400c2c0d6a0500702050700c0d85450001c4200420360b91204003807001d60380440c032484644030840d01c003502444000100b03083c00c80c04003412036420141d4804907110540d114240c04009198 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 683583237 1250 683581987 683581999
    0xa03080a180605041a010b25150f0f050624040b0c030c0c030a11040507030b120109061407020a020120011401090b2b06020c0303070c1505010506040b0f09 68
    0x59582003030001001c0480301100c000c03030f85015004a1720300d43d0030018101c0d461042046e140c0b40348100307225448088003814898650100405100081454111400e0041141700c00210340035046102d1080d1100c1c50001080c641c42d040511109842d149600074210060303000414061003940031001c543c0c0709643c494003205002140a4200d018088020400c11a290040b902158104400c05448551100c40100329038000580c050107801c040c1c011951120140c03e0014901001c00d010801c6010000f0b00c0c24010f942d110000010494035214429140e80c010394007045900d4102c8010790360701c1c4403071270190620040941c140d0300207030480592010301c0c04682c020300040490319624034040400780039a1900c1824990600654100003d0105111160005410129071082e5158040c0c0d44c0c00d0000350358080d004c00c203500c11490300300002c6000e580d0903a121510340d40c20f400c204000318000c0ba500700f0042d041c4001001241e03940c02c10f0b98246d0782c035011250303502c00c00401e1250701881007102c0e081d0845 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 683584487 1250 683583237 683583281
    0x4020708071a0714031608090313140301150b0a0e150403030305040c090e060601050c031e03040212070b040302130e0f0a02033706140a050a110403050a03080a 70
    0x80d00c03401409002d001a44c0b00c003042401d82101c8032840c0d000403602e0b6403001400d00c000c05000c2d44503040c15504803101405483c07030000400c0011070072000c1500b00c1c030303e08508410004080d050034850b00e00a03d4009140e40c019505210684a0740e220302d035500720410064040340c071015a50180341070540c0e8401e0500c190b48594030300e805005010700b103800303441140c62070f6000241c8065034010f03020f090f05400c019007190350300d0100644003030308807400940c200d2009002c031a03502120403c0482c82030907803501c015220701d440c2c4104034a4401214001300d05801101c810062160788409480c2030700e5040300c1e00c941d0340d002400014024a12007030014464400e03045203800d0140003180150a09000b03405603040d44015810801c0143e20300310b00c401484640440340c16149061407118a040341c45490f012a110041540d100d001c0c00040e03c1c203c903000c1c1d417042445888a518440d546155204030b10a6083c41e14603152540c440000b200c1c00f40a100b01320002030130495440c1e000d8160100300340c0a50102c4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 683585737 1250 683584487 683584523
    0x90a1a070e1903050c0f13050403180807051e09010b0717120601020d0203130501080c040803031810050c16020f030123010f05150a020309041109011704020a050402070807 75
    0x40b482c18442038410380180f540541180c1010500d682c07000b0009011541204081c0f0003040003484001c10540810030101c010068402121030450010b10030100188961404c0a081000e481c141c4882c00304000c00581c3c4100340c43c2c40707000c40d40c0c0c1122403804c04503407200e00ca4100061002c0c40c0310401e1000420018641680102d090101401080280d085400480000200b0783c0d481c400d0b06092008202000703c00c0000b98801c90003250311004841e2014100341e980e0810310300d182c10031f84520751100101108004260002c100c26070750030b0b0354010306100c1070502e42c110035013500c2a007440f0151103040401010554480d441410282c1c1c0c8050000c2004454069035440c80081c00481141c0c028a40340000600700c4810341c41ca810344400074040e0401d08112000301e4280d502000c13208041d400b00740807081c08c030740c0c0c0c600c916104101000300e0795648110700c1000500d030300e54811800003a85201000e000240c0c40c3d8403400c006940042e01d00503a500b1032420210124002c50000424090103510f1240203 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 683586987 1250 683585737 683585779
    0x30f0b0901110a080f070e1f0e03101b080415020a110609030405040b120c06300a0627020901270f05100206060402090409050f0d0206090a1a070e 64
    0x400c200410130032011b501d40f01c1007107a071842850304865100d034107107000c900308050349050070005c6241d6040c000d0b403001509011a04169900503140a042c1d81d86001130011080030541070304400840c6054402c40c50503035203400340d9030b50032500e0b42640d981c00710340103403200d02814003030314400d84050494200d49440c500d031603030740d6000e0302500d8012800c01e014000c0d5420f00445101c1d0007074442010303111008140301408419000365010784048040460301203a450b04490034040041244001d504c4549040510502a5042507002554451403030340a00b40342558013404840d640c0917200056aa40130342030048034a10355644003610340241500c0701e40500503c543c8188105c84080c0c00b60114030344c0c0c031405c100481a031480103d015802400010b41a03103000e5000302240c4100030800038030300f442600c905103000144940342c4044d501444030b01b09029010003026500a00200041c1655205a580c141200d110a43c10310112100ca10100e80120b000705401000008041c0103004040b20f40300350301007 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 683588237 1250 683586987 683586991
    0x100e0f220503072409020d020904022b1b030b0403110f0708030301090f0504050a08070206040b03010914010515070b09030d020304030207060801120c05190503011503020910030f0b0901110a08 84
    0x70f600302d883c20f1904c805503500c0c003800f00b820b500209007010048498080c08650701006000301e901c001a0402824070500c5200c3c3e92483c201e03940400c0d0a0209070340b614905885844d01034102407180d0700070400001d036120080ca40d1240d810700e0500708140c022500d541c03511042580f8009940109a000b1810650000c0614102c40b010f107020302c10030510311003450440b042503c01810541124051102003a10302d40100329840c80035004510b0240d45000c070308100c0e003080c0c0254080d00d494841801180c009030142c107015000403100403448034001c081400440c0700740c1000401001c4031500040b000710301482a280c800420880a641c5d910b4a4640292101000d000b4000490010400883d0704443c60242d498910b40c881d000b41c1c1a181020104810506d03040440800f02c600d00c980810107841c203002e100b80340c0409510030820303a4154810407001d54002000c6c000d030803206680400c0825104c42203120403d8100b104000d0f241c80301100e41f07014120340b500c0c0d030650200001d050480140d206410034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 683589487 1250 683588237 683588273
    0x706020f06060603040804060c08041505070b09010e0c1302070b130309140901030f081309050105040c031e0b0a0305060403080a0b06070201120c2303100e0f22050307 73
    0x1255651102c04012044c00305650107000182c00740300c24010103005604c9043e11a00501803d4245540d82d2403032200351886e11407100018001040ca10204074403041e0340d40d0000304180003400f4152041c0d40003551600190340991060821640c40c0381d000941c1e9040742c1c1556000b840360104c51510710a914002d15100390110001100c2000000c0c8a00080101085211008140c0300060746140c0307500c84160349080041e81c100108115005030140d690500000034410390b400820250303d0101003104844201c0150f9007494100400300071140800301c4420360740803401e203000030303a10000c9000c1080b61071307039800051140c42210280000d05821140c1213100340700d10340d02400b40b0100003091200f5405400f0000f070201e070041c4820240c004081d0854100b145e180d1030641018491821408002c60400711350000000000050044010010b0841c40260461820090290410000103060940d000b0b03d900c0e0f500303989200000900b82c007003800241e21030300301048076202c000504041402d429844151 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 683590737 1250 683589487 683589493
    0x915120102030411190b1b030d06050102100b010806060c070b0304061e09033903051308030f1b0a0f1a01060906270b12041505010e0a0b030f0706020f 66
    0x165119240400e80e948103d170308007400d0319816240c009003ca960700b0400452170000c03c0c82c0340e8420b0002c420030107030140264041d004541d0364038103000a0f0428110720349401c901824240b451000b139802c003c025401c104191019561806a401442c1c2070400f180c0100030f80070350010500c810b1001c0d5412070000c840511840c0c01c0e9807210425040700702d840581c00200881d030000502811000c03400c610204500d52400d104412400301d2a0031248039555000071004542c0204203080c424002a02e600701524134540214648051401076102d0340c090101c20403040c26906800b2104200d045c00085065503200c0317840b0b14840d03044e16040d0112001c0c1030300300b006643c6020001405604c903c6142e01200d07003d45411700114070444a0340d84440c804c1200c01c114400d40140001e00749003c00c0108100016079400c0b0016041031315084003825460040c5e0071341c0728140310041c40007044100b4115003140c040c003000100d2451007000302c0d0910007001d100c0304460142103000242c842e0045040c00c0c0892010040d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 683591987 1250 683590737 683590763
    0x30409060f030210120b120d14090603061903060c080402040e06011802250302070602060a02071a150409050705030c04090f030f050c0723040e060609151201020304 72
    0x4072a40030303400b0b120195101e0005440240c505020303840301d0b90304000785400410441524004101e4080403070405187e280d02c10040d00070a035a01c260011440322642c0301c203502c0e007807520000070a14007028050303d02c140c04412903207145551707054090004540c0f040f01409501000a8040c09031007089800342e0080e03083c200001901a0046880c50584202840c2a01c1321701d8080c0700d1078025004118141d101502c02004440480a0b1061200b8568481d900400c8058240712009017040c502070700c00f141d018014040800060f01c4007013960030085100328010300650315012442c801e42c0704e442003290882e14020750101404030124042055640640850300e159140000748012500c00d24006810180082ca103c0c000078400c06012461f00c0240c58854100000c1642c205d0411089902c0710a1000700386c13140e920300c500b20304007120014a0466040080240800400d82c445d0340042aa5105203001000140d509005003034401002c0c2015000b9103080c20307140707030b458004e41c42070b00e0030350b40703140b0300c2c24 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 683593237 1250 683591987 683591999
    0x38130c0b0705121305150703030c020a030207030204050a020913140106050403020639010207052b080603030418060e0f1b0f0d0219080106110d08060402090a0803040906 74
    0x104440310301ea4448001c0c810111580c3c0703041e0a94020000c1d40c2c020540707044000905a4605c41055450304042da0910343d600c0d0740303140c0581183e080407044411354200206100100703801068000460b0f03019503020650340c2d900307401d04000b84505d00d24981d002e0b0440c04207090115082e441440e85000c8241092881c2c0d032601e800382c5082c052440000d40c0054200014900700e20705007104905c02c0c81c2810001040010311501440c00d41711580e200c10541e50116500003413200c1080210f11f0788140c2d0081c5201c084200400340482100f049121040c0f0810b00040b82c1141c60800c1120300402402d070317412060340300851300f460140102c1c0c0305c1e000010107680e01264403182c01c1c0c0c07205409600e40e0707245001507015101e0100c1c400d40007030340190603a900922010118400c4c0e40020082032a2107403543e5110150380030090410441038205c002041032107041c2201e58480050600000400d80c1440d040039620f131400540a4858940080d4021a41718000141039800001400a603001d428040c040140c0720701d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 683594487 1250 683593237 683593259
    0xe07020f1f020c071512060608010e0a05070c0b1608101214100f05061f0210090c0f0b0316020a030f0f050d0e1e070338130c 55
    0x58000d0480014005260000c8070990090140b20410020b0310a0f0300c2e40c400d60070080c000a00c03518030100b10070501403100c0342400c0c070801c0e000d4082800c004005505211007480711a03402400c0c4000e040c0c3d41c5c00402d203030300c4c043c0c8103032000181d00078403000c41407400601c00d660165500107110701164440010500c400d0000b0a4003003038500d10b1b0051400301d03d19031540103150b424102e03000c1c014055113084c1c421902ea2400f0700b4406465010003c2070604004040c0445800036044041000c098240c00000c880da001c1341e490070880e031b00040440c000c021401d200420031072590205039401b81c0000700041412148016610030712003041e41c4050035903103010603a01c0b1004c11000030005459a41320b688094010900400d18000380c0c5049401d108110040d601190901400d0180350790020b810035281c0f800b02c0c021061020000300160a200d40341d940c401008810b0030b5148c00c1c5250050180e00058244000b04c0c900d4060100119046800c007a6121002d01c10048030540302d4509000001c41c07162524 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 683595737 1250 683594487 683594503
    0xa120e10031a040c090e0c0a171509061c05060105010206010503070303081603020c030a021501231e030a1a062704020301060909150b030f2112010e07020f 68
    0x2c60240038400c5481004000c1902c0f00da0f000501000500219810382a030030b031140710380c9910801e1607541a013071a0103030a071800d180805200b540305008001d4911103000760441c441c1e00176628001980c0f01ca00004006c5070610343c3c0d0454808040030007005002c00040c020303048030340a80980e40707640d894406054840e08203000240c041001c0d880400c0720b038406090a170808526500d030050500c5003810034241154808426400140c0c045081010500303088500f050060034009500b5400c0515050100c0f0200c820703080c0350303101e030981000b45901203880d03e07540400241c0082c223642c41c1500790715020512a200500e2640101e4440e000290141801c42c1c940ca5136074188441c3c08503c0380b40184003254075400600480e095500c400e40090055020301400c00c0c8503210b40c00c01c3d44294006071090080b100c450605501c40d0b8840c030082461450040b40da030704406502c04000d050800821414822842a0707a000c251709500040001070341c218850f0303005d0251007694281c07034640095900b8140d490005d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 683596987 1250 683595737 683595761
    0x2409060f0705090102070b0c0a030905010e0a090f0b0405010b030906160c06090f02030f030901080a0212062407080405030c0315271902130c050313050a120e1003 71
    0x44101151101c0e0050001d0019000144110380101d91507180c4040e076030300021030501940e802000090704042d0004000302c0942400c0c60869500070340640000d90030b402501c20500416901c40d035407070604103290488400100d0140091080f0750b9504c03541c1c00710780e0040b03d00c1c0d2124040c00c004a0454005081588941151036456503940245504c0f500d0041941040803a0021850500e0000680b408d011086943c902c2001441d203036503c02c0b0001d020700c040146424a203034030401c40a0030381501105501e070007000540301c0380c2000c0004171185020080110946034400e03400300d00141080030f28401403050314415026542080b4049052551302c0f000c1303000c03280210045c8000a0301050165006086400c6e4070350540000e201d0b00b01e00c0d00c1c104100608080c0c012480240d41c8401e6042c1030188440b030440f041010013224001140050040c0006080201d82d40b440b0070300501444000c03c01c08e4812600001c800015290400002e0a03620000024034021041800c80c4502075000348a803c0701910 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 683598237 1250 683596987 683597011
    0x2090108061002010e01240812030103140f010f0209100507020a0603110d061e0816060c11060d0506040f06060c0807081909082116080c240906 63
    0x1d8080801c850100b0340e6060340d0840d969415018100b5909015100c4581d032003202e42d020145088030101c070310174615003020f90300ba8028050038548001c85001c50b811a908122810800b00b031088843c1e0074084400000e02c00c942c03e11000042c07040d40d0380d00410070307101c00300ca0110246210500075075842c065000e01035480b11090f442080000c1c0a0341201b0030415107608128030300106241584111811a00241004100140f00c3c2c0040b072403000828010f000004000c0c000c540c51006890305041e0740e409032004101c60710503102c0410152824403289034500074201d6480f80c10407450400104001c480c0c03244124204019000043c18510603902580d06a940e80d00c00000c0684403813016504c80441112052001c00402c04080c051060006030744640c0c0e035900095503d000c058610f8411041084103401c0c561355024010b074103c5900325111080c40016001d08250316007800307480c034014006104e1450007010f902e15801000704020000340c0450320f10544190302c0f8294142e1b55031100b10340000b5001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 683599487 1250 683598237 683598241
    0xc0e01080d090510120e070b040e040b09031611030c04050c180f03370b01030605100e13170a030f0e0d08041b08010f020702031e03042312030702100302090108 70
    0x1a05c4d801410b21006900c04464545541d410403940680c401d03841450170951440510082003c4007490507001200c510007541010380f01c001c4107415900e0310704002d00c000c40940b1103a032035407820310000d2405d40740200104080c0c5414003496840d40d000c0e26460350501c3d10a0030303100700ca20b0496244000001c000d8010403110b0702c851480044401e840d200c841030400b5000361542040d501708920340d40315105490019444d403462a00c0341c107807480a0101c0c4070040880005002400508030030380c0e400484000800485a198100f42c40c40c810588041e5241c1c10f0001105c1d808030350160000341491307503402c030108090b40d200c902e400c0d110305c1842a2000001d6203000880c0200303982a000d19100405030040c2c200455884105908441462070000c0c10b0325004100702d001d41c54180070880c0f10368221030307859840c045074860f4a41c81e40718500a004e10703801c038012002403100221020000021020300565803a840d0740b00d4160740e90f080741d00100d1003090920b81c00c040c802e1090090741c0c00d80d641a101e0014035 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 683600737 1250 683599487 683599517
    0x80304080c1e06160c0f03020a15060302090708040f0b1f060302030405030f0f040f12031e1e020f2b05040803030601390b01050a05060d090c0e01080d090510 69
    0x10700e2000c180d0380800c6a00050440440c0c1b0452202c03503514800c4d00100407064032440d0000724104001c16519105192000400c00b40e110300764010b512141e249461390840d80d0305d180c0751407030007403013040130380380f006802c00700050051124003860b0311941040724502210303600e20044081e40f104843c0105250400c1c484442c84182110180c940347c030b01b50241d00e09107500c41c1114001002c07079a112100c5802038419030742c1855006030164103040344001c2401849400d500010b4032080c22004002506103158a000501c01d10034400c180d040210882a1071384c005021801949081c810107118030b034952880d400784803040c09101181e0031505240042c508555030f0030b005495070003081d03800081c540080b411090742040954003a440c406000c40d0402118252800e0020180310160440ca0052200c40024425030b640c1a0644106202904010409400901d0f0000200c00994800d041c0e0b00182000031511960204103d00d41710714640e20002c03a141d46004002085080c60420004500010101010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 683601987 1250 683600737 683600761
    0xf0a0605040f080d1e020a08042402070605010806090d09030305030c0706061e050f010c170c0d120e01050c09060315030304080a050f03040605090913080304080c1e06 73
    0x1c081e0003074070022015902030b202c14200303038024414040c00c0c03aa60000c6054001d1014004000e48070500300450a0010b20324000d44003500c041c0018203044942c44074061f03101c0031408811041080758009640316129482c001c406094280600480c0c0d00640000500d00301000403031409540055480401d901e01c0c544098845900180201c074202c041080783c0404108140a04002403007107150b036070820708600703c420943c1e00d89900450310910599448c40102ea134460106d0040c0d0b5001104a0441d459605140100384105020800f0501604030040166900400c0742030048092841c10300c05250040717450b600701c071310072160140015014801c170012414400d001c0c650004c6040d600b41c0c030903c0e030136000a1454006a003c0700d05030303108221403c10450284900d000b061420b000071802e02d801c1400240040c040c03200103502441140300040c1000300c203075010170125138104100d00c1c1e072400c280c28801c5069000c0550b502c010b2203540b081680411020300e403020515591001360048d900d4034925000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 683603237 1250 683601987 683601991
    0xd09091107030f0c0f0b01080d0c11130207120e13020301080a080307020114011511210f0d02040e040c1520011e0608010b12030405040c05071e05010b030f0a0605 71
    0xb00201d8000303140000382c42c1451001480e001b80c818603503d600d0403401c64035124040c80704a04020782c0850000008000c042a81000b15040b00d0300702c0d481d20302c0c01504009018480303002c0c209004901400543d16040408407418000644126060702081c500b44410f0344400c0c8075901c42c0da4001314100000c990700d140a035030070076551310022401840521700789110840a82024034400c3c480d5841600280d08001c44082100811010b0078420b80118946a01e13281c1ca0011041c0b00500042c8120380e034000d190440388242440001152603503101c201c00502c44d4070840b012a00c503c460389011800070448200300f4520001555101c10b0b100701c10f101c401c480580984e84810a641f5810500f1007030100c000048460800c401c4000350b100e1514100b01e00f0b49256582c094014011103401c039042c1c140100403103082da202514089842a5440c07011211480362050207086590510502d0603044140658502c425000c0d40090210a0141d0205910307031125184140b01940009001e000007000d41d000b607a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 683604487 1250 683603237 683603267
    0x114060903030307020f0d020a03140708221401030e0307020409061d01050411010804050a06150f090e060901051e04060e01020a050a021b0d0303020c100e0d0909110703 74
    0x5420030501002281c5103070002c0e80e03800050707000181c0310581d401d400c1184541c10b100d9480100030380b20442e10080c00207d055541100441d80c001000703c18451a01c0403a0440308141d07881c2d100c50314190f290303001c0041460069031400308607606041d116610a028a260320b02803040030f546000c002d6400c0000400fa440411910242c8619031030300094103080560100c50070507000841d4071b1420349041c9800700f140180b89811310103405c09200102d030001582c64100c5a00c00740005100c8850f210480306002143d02400d4074603c40c820104000c282500aa10f007100240e04642c40398440c800c1481c03c0e680100e03668451781810400403003040b441c55000c4da801c0340c001c00d00000e107031a5414809003641c1c4940d2190010480020f0101d004503810440c0240c505c52010700b500030300d10214002101d2280d00c103400340405402044a101034001806560201d071460b1508000c414440c06215803548001051280480c21100c00000c021116000b40b2010f551403861a51800e8401c0e030702030310020411740c240 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 683605737 1250 683604487 683604499
    0xe010503030715091506091406030304032d020a171614010f030f111b0d0806090406180b010918050705190308220b070c060e120106180c170114 63
    0x417011290311604000d002d22500110710b80c40c1804c1d080d4184140500710360b0196008000030400729440c1800071000f410f24084020754203142c4040d88800803005103010394000015880094014030200401c4020112902943c01800d83c075805044010554418007031500440008044035610501c10b00407404198207000070100c0505465008440c2c0580400580000005283c00b4085001c1c229245480104004000c070020424008100e04400341043d801007118402007820020355800122400000710b0b1013090018890404030400c540038454401843c0c40d000b8681c4884001002c40c694942d0800000c200151412040c85030030b950310341d0030341e01d4a00c3d20036001c80058450750007130044c6d90070401d01c1c1016001c4900144bd0103800c660003080d102e5020000c460000d030162200b402196000c0c10320a00184461002ca400442c2c9806820a69440c0c50f06c00300f00040b2000903402c001c480201e04101c1c10300c2000042d01c5110005d01d100320f002e101c4200411618005800e8418002809021 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 683606987 1250 683605737 683605763
    0xd0509010c0c092a1b060b0607051513020a032d03050a020c06042d08030c060a0c08091e01021e090405060603130b041403070c0e01050303071509 64
    0x5039000ca0542500502902d0b501c0e40c07107030801c004c0900300d80c550781c0c0a10403680ea03088068000240c10501d0507a80c41d0680a41c000d40d802c00d00c015a0301c6040d44100c040c00301581d07440c0502d801074854103018400d108080b0b011000c45c0c503040c0e00e00381d04411030340e000c0e000d02c0104e403d540b030703500c150084103840804140c503405000c0542c0e2206100504483e00c0390f11003d8640031180e00c06800c104071118058081e18040c04100007002004803460301c4401040403441c0c200c101040d0034070200203982c0203507420344000900d86140c40e80c0000c4603840343d5140f00e020040d00d070b80303682d04581180c8241c55070252036115644103541180b5545001d0040c2d40f188000520304196105100783c031a0b007030400c07203c1200c808500c1500f01d042c503000e042d62040e8210790039803035441c020b480252082804a001760040101100060402840d10441148080110201c0c0e4a44440e4502031801740024000c1000b0380014000006203402d001042d101000d92088104c04810f0f6460f070384600402180d44c0076103c200c43c80700 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 683608237 1250 683606987 683606993
    0xc0d0c1401180b071407020d031107140a0e15010810050904031101050609040231020c010605131b2f030a030c0c050304210501050a0218030f0d0509010c 67
    0x10481d28104105120200601d0b4103042540150400410250522400001c519a49910141242c4040f941200d90003042480ca09088401e680316031107100390b501c9070722000308003100c41103034000110790100c40408901d030321030b08500c0b6089401e0350342ca140c5070006000f28100e58082c1c88029030001f001c0c0c030030030110f82d60343e4002f408410b000e40f402d40c040781450380c038803140800a0040aa001d403043d15040d1190500b9408500c08400780d900d080650201c0115481c010f0f1400442c0c0541003107109015034a030b24165500318020036091054510500003112280080398030740c091407585441502881160407000d02040ea100e680b0102511106501f03882c440100c001108002002c40908400443d21030a00781005800c540705850700c04103102d081d524400c0040e400204803001d4640b40d4012030255030020313408024015144d0002400c3d0350030442040f8161156501811400d4200d81085000d2200c85007415115040d559a020b000d0300001c44400940c0e001d1001020f0f00b0310706250044030304c54152 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 683609487 1250 683608237 683608241
    0x3020901030f0503251109040c270f0e010b03060408180d060c03090501060611120a0201020412060905061305030306010e0303131409160518010201090206040914010b0c0d0c1401 78
    0x31906005e082800050901403184000c2c0e12144018180ca0020644c2000e0b1580d200c4041b041c804d04050304004a50081086900b8400403440074000c0e000303105450001010001400500f48041240e600e8603401141515001840c40e01664108071007502e48003031030404105070018095400d8111020890303842c0003410500c43c000301014559400603514605240031400c1d10513542c0031000700100301d00031b40d540c800c012840d07145041002910030ba803040340f4081613000e40141e034403110b40e412510103050184001c503001140f4070391180040e101282c1e10103a00b103140305550b20016145900510001e11254051808042210b80c010101c9013407002c8140301e402c110320750f40c0040700200b01c07044c80702701682084e0745100d07007000100708080600358030f4940082441c050140c41448038101d00869030b55990003075001c8009030ba000b4040a580700c1d151003501000c2c000045034190440029000024404403901c1601d190b5844407000d081d800c0009801292031041d1040180e0b103c3e0548480d10000610074 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 683610737 1250 683609487 683609527
    0x1508120306090103060c051c051e0c090402070c0e100303120501060c0803060d0213060503010f020a0e011803060c080105120109031e050f0403140f060603062206060902031f03020901030f0503 84
    0x3442010410349030500040c460ac00f581d4605504000d18001440b42040c1c0f200160340c8102000d40f8010b07190b0206041c100b0b91005d85512205551804405003d00640904c0c1d180054a00036180d07000c07188250031209045410912030540004c0720a100000000c003a60001c43d000b14005002c0381d000c2c070716600040c2884c1d4180300c402842c10380d01d1504100c5800c00b03000e00c0301500941d403130850400c1ca01c140058060085150700c5070401485203030300c0e1300034401c0113058030183d13800c00002c0010951582010744010402e001713a5200302c601041d60301003a40140206d056203a410303a0b5652402003c003481407005a0460961414407400380300c804117028419001c3c000440c080c0c4981c440d2035443d090b92078240300050008124a0b00890100a8140c07400103000c0d410171401150059840751075080c0f50501c9003400c000805e000d042c201c000a55002c0c41e00518000c1c90290100c0348000b040d080b55003140400c0d0f01c40250002c48400c01080420403100c5020031040c01075042d00d183c80028003500f0a10026 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 683611987 1250 683610737 683610787
    0x70c060209040501090f061a03041e050a06090c08060622060306240611120a03180b04141518070b040b0301180c021c09091508120306090103060c05 65
    0x280b00b00d100c0720940c3d1b9024940040000101103918a5410100030f44180710041c009082d8900441c0360560701525001550002a004000e86030f20280500c1c1c6207002d1300c406a001d50b00740c0d00c0d288000c00d80100104555014102c010481e01400c1ca0f900021075042c4204081041c1c420795500000000c04d0b0f050254034201d41d880050b0821203c1310011090308004580c0100c01000420f1410010360440001c22042c001c184000b01350300e52a0101044002e000e414500f00c107038071920041c0808201c03161000c41c1c0141c3c420b0f00d1892072070000b03450941e034440c00250a920885164004640d071100d240f00c02800d0320030014150390707030552150103590303040d031007a40406c5000e07400000410501c04101e241c2244001d40700d070144038690003400025680c241c1080c00880200043c54000300355405031285038014a4031103c14020000900804c0d24010810b1040d15014010304a40c40104030300c01080ba8440d800c000c0a4055590035a00c0304d5000b07051407034402060000401c40c0398101c0007440700b90118211 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 683613237 1250 683611987 683611991
    0x110d02070b09060c0a0c021504090e0d1805120705030a23010204050901060503272505100807020703081201181b0516060501030305120f01030209070c06020904050109 73
    0x1407032418142612000704000d010760002410b000c0d2840340c0c002220045203181c50484220016400020b02e0703e10500c070700c01d03112030001800152080b019003021090340100001e4901560701c401d015603181200c03200140410034188000d015500c0c11200369220000b0280850348840e8903200400c0c542842c0070701c15642c0a420500b0000c007090b014800704442417840001751304140c6010040f0303003031002c180180b0007880400300010300c60300c0c800000411300304a17866107110b0125404e08030648400a0828000c5014414142075581c802032100c0403048540180040941081e070303100440d03440700b002d4013203001c40c09080c3c4c001000c00e10361000b5160000403013085643c030f5454480f91103118444150381e80c6145003043c00c00e880746100d1160b403011501c41c6040240e42c0d00c403205410703c0740754003003c03000301518070b0701c000442455031101c081e102c0721016102100c01030f1640000742c04088801d110095026114900107052607210f4a00e80a4240c4240005410403140a0001d01944c030242c000301c440356 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 683614487 1250 683613237 683613247
    0x3010e061b040b0301090b01020a12081005040605130207020d0b041109061816030603082d13150c050124060f090b0c07151205060a210501110d02 64
    0x90035407101010007414000c00310349824a0800090120300052040d11400c940c0c1e401d00440a9000740030302c0c2c0c480355000040c4544071128150107022100c1c00c1e070380c045500301400004074050400d03200703403c161400203002d0048403d5249044c4003940c01424100d800c030803542c030540d0000312403040ba0b5004602c00da412400c0d01c4004014840c078003000600040c411340f2440034122290070f04804041e0002c061620000142070228020b4000d400b0550009110f2100065203100c00c10802c0b0306e0450010f00301550303040b5003e24400c5041d0a0040312841218000103001c00c0040701c2003d001c480c03c4040c0c2c0c3c10701c10f1201c240da4543c02e0031030b144002c206000d036140c040c0011042007000c1600010744000d08100e9030741e03824902c00034075049090181c210407c2c00000c01d11100c40d0100b1400c0010107021001c000d060480070340080c000d60741c0d55254500b0504000c080703a00b80ca8400c4d0b510043c4c1e070400400c01595210003210304000003030300000340c89555031084010f81c00498400208107d003480440545c5d51 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 683615737 1250 683614487 683614501
    0x30c09030c040218041a1201020c010f0b1005180909010e010b010302130509041b170c040209100315240e040c020a0b0711030304150b0f150f0903010e06 67
    0x40700c540540148103034410800201801880b040120407039000740c0f00010084224100c0400c2d619540940640c04880c008074443c08903015002841010007440c001c1c0400700d0310036010001d0360700b05c00c6000d43c0b003820081340d0300c00c0920a070083e207510405100340c4c143c41c0149001040300e0780b070309550340c65445c1d440305070000d03511600b40030f28182c064007807070210b02d00307c080f4600308461501070094910405c0c00ca000310741442650305081824442c600e07040350556940b40c8445d62000e441410050160181050070543ca280a1003502c1050781b002e4848007403a00c040300b0440080001d502d007000d01d000f03200408516418000c0b4a003540c0c075401e40210000d2108400050a9828442c0348588241d05014501942c140e02241c1c6150041d070103820403000344c448540545d1203401d8103143c14000c0c40044100300510000d00e202c2541440d85000c2048030802c2c100c01d014590071100a4240c01940d01406000710362105001000000d55008046e42081c0420000900307594a034050b0642d160f01607828002c107 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 683616987 1250 683615737 683615743
    0x906020d0918021602180402030f011b050901020f1506010e0d0c0603020c100903050a0f030b09010315090b190b0a031101030b041116150b130509030906030c0903 71
    0x4000c25041180c591803900500b24150066811074400c200d4010412100a48440000c0c6080990050010b80c02d040400044204218116426403007803264400c49020403034103216000c05031240c82904c5c2030410502ca0140e41990040148a04500c9103030740340245802c00b40901c4000081400e07104c5d040d420b0140005200d900703a03011442c4626000034400340050342000183c0e0480380350307081c05a150001b010740d1509041c20910100601c134100452101010703480302c000d162010642d142c044014004030b45c210202d40c2c0f84031200750440207490062000c0707044140500301c11421104040741c0300d100c5903908070581d801030745c01d60381001c400740415107001d82900800c1c1d8100c0b810b59601098902d50303203c0c1c9160a88070f90f4154141990b4071001d4a0310f0300d442d00001d8125903951041652886045007294400e14910800d8514260001400500209a0090b402007040040c026141400d50138009001810094040c00c098071040284400b5500e0308400365200c2e441c800e8185e0f4540b600c0f4000e042c2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 683618237 1250 683616987 683617003
    0x1503060906050114010f020a120507050d05030f13030c1106040b0a0315051903081303021e0915010c0303050c040e0403021006050907050d0b220b0a0e160f1b03090602 73
    0x41809000c40340319803451f500080900030950000803504101d21107660540d200c0c440e240c005070407801a160078a041c260018000c1d401410007501c44019035031b5186503007070101240c400c005c00150891880c6408510b1140d110040420001c00141c038181c2d941280441607032000c144c60307010907201c084d100d000c40c404011680007003a05568a42a1400d40c4c1400c0f01c40000300d0000500720180400c3c4024801c003100500c0b406981d003c0d14440d400104254002d00e5803000c0408240f051001c600010455980e5405613020080107031a1a808079a181da416405030100030000c1080b000280b00005141021140035401640250082c105580309001c03104141d421541050f80107034500400d10120359030140071500d00b00c0842800090b6080c0710400505c48100034100d840c8003d10450b6007240070803007580501d0070740f003049580e1510300d60b40740040b01600310100c0e03005160600951842064901035556800030450524081d00e1600e40203041d054008034070102a000180081001d0103581e404007e454 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 683619487 1250 683618237 683618239
    0x601230a08250f0b03041b0b03010b0a0203070c0b030f07020105060f061c0525020a02030a1101140304030c060b09040c05040c0311070b04060c051c1503060906050114 73
    0x1103812410000055030340c029003400281e6209050201030301019103158860b028010601401000f10b546a50614050b041583d06440511981100700f910ba0030041d40d500844d50402011400d40e0729081101c0391580120b0840000d5000400100000401a20006001c1e00a51503c241c0701c4c140000040382d0107200401072019680b42c40244050381c1c2c0d5030130302c03607290203c111076060340c9080d209910005841104024440907082006018034000423148130103001480e015003203103100602c01c00b00da80f00d21440000c0d425030000424800400d13122180d4120048042c1010b825080802c0310042c45580211426000a240100d07184104901c0d8006c00a400ba01150207000c103040c5515100411031a600c1280e21884d510546051094000d400484103055480c4665480c0d65850030310f5905c00c002203c04541c041e2400226441c440d024070705481c00d4594484a0071802c54110a144000b04226010000d51244034035002000070030700c0c0505550184944004269945841c0da003000c00885c0304070311 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 683620737 1250 683619487 683619499
    0xe1b0a020c0904230a030212120c03061801031b0f03030806040e0f071404060b04061205060102030d05090109140601060210110403140304140f060d020318060123 71
    0x140001950009980e440c09a0450340700c6442d40f40c0e0314214802c01260300c9040301407400d508110003c41e8001c14200c0c1c0c054069025103c444480b03072140c01c090b01c10a40c01c0b0100380300a201140201c1c1806004d140d12540282c401480c107130088848880300002644101e070054485003c403107521144600e440c0c010301c7c3c88038501810a0540e9406440d001c0000c0596000702e5450320450b1480074100805181414200d06940380d9a407101056500501d00fa42c00c0e41c0560b0a0031400620680550119001c8403007640c2c7e149007681241481e4805404090709090444c070080c0481502c004807881030500030085840005208260340c60300c1055002d5461065815400020040000070707004070f5424456900c0e000002400b5565203204c04aa001e20381010b00340c0755107128500c00044c0004000c205031a4544080528202404104401907442850886e04507005000f001c14170740140e0061074015048100c114015000c1e100203500d454402d80c801182c030413070384143d4288a14446014400d1000035540 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 683621987 1250 683620737 683620747
    0x270b1b15100f1d0601030924050f01060c0f06020c03030a0615020105040b0a1d0303161b021f031d010f0e0f03070b040309080303010617010b070201020d0e010c020a0e1b 74
    0x41c1c0001c0704a04044070382c81c0f5501d036002850b80e030b20980c007002c142a80700c02c2a0100440120303051248251802c0d485550320f2410003c030381419140400c99040311030b29503619181d01c01c103a4a04880c1d800e0a902299115006e000d1440d581c0f00910246200d00b0032280300241d550f103451042e201c8101d40340084415039250409000100c1c20400000390b11442903480482c01c54003950000c1060300da140c0b8413241d5800048107000c403c814404095410811558502c0d00c9000100407020600550507402580590340150100880d06541c000c109809082c1c100018144465030250004408600070340c682650b40d4002030000710b1551180c440c004946500925400c1c49001000b9981e120701d500c050409010b41000800709071055a40d04080e1000009481e02c950395860041c100714281d441900000d11680004101d1001540569460540581c001c0c40b071f58115242c160b507090040e031140c3c6e0400c406868840013584030b442e0003c0041c0403181407203016103030030740800c81c90b440c83c40a088074840301040 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 683623237 1250 683621987 683621999
    0xd0c11070b1303050f0c0a050a080c1e2707031802130905030a050a0311030405030711030c03030703020c0307060905030709023403270b1b15100f 64
    0xa100029a06410030095458841d41006102c5055951005060303100d5a007214085110120350034505a405486008610f61148108640380000d4041c8600c00da00c00d10000382285031504104c0c82c400c3c18204c00940c032104010220b0700758118040340e41c4241c003054540140300f0182c100b51540c0071005141c2084240c84501840d91144d40c0d030140030348600424244014010059803086018079070200c01c40c0d0380d8200c0044003404035000045000017191a0002060006908000326403107107901902461500500313a40d05202c10f2084400b05816100c0c1e0341c0340e0300050310100000e241150094000b040e601d401c0c00105031400c45503821010800140306002c108035200020034405035007400c1c0c009070b2119920b01b80c0883c8260744020b40702c4802c0d40f40481900c811110074180c801c0500a0f9100490601040303a81e0000c2030554a40418842c2c1c003400c20418011085c002c1e0942c03011008100185a42202a0038942202000b0850035601440c05001a480350030100400400c01500140101c81c6400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 683624487 1250 683623237 683623243
    0x31060509010c031107092c0307020f040509010e070b070501112503020c061603080a0515040c0203040b07080408100603080901082503020a030b0306090d0e031c02030d0c11 75
    0x42c001804d1007403030200c00c058128140b040f1700180000200400c42d0000480700c0d114070211440e106203101c8000c01000e590000044100c4403065005440ca415081e849020310006003001000c26105540c1e640103c43c54100900c0740703000519400307000c01d85450702030801e1401c603003c06404071b041482c2001030718244031481e0b1110a90076074002d00880441080e0900380d00748800c2289461f4403071400038030141e014440340d040407403507400780e52009280e40e100a0000121181a580c0d20b05d203201440800d5014a03041c2c0104c0380401c868415030341882d50701d6481074001e0300a42000c6503070810104050103a40010003845103480c049103c1804000d1660711290070340c0c45003102c021b0420980d1000a03002070480d18241c58514904050f0030209010120b0040c001c0d003280e100c00c00060308024400440303180000f0140d00613200c0ba4054092100241d009540074410f02d811a80c260003540481d03184040c1100d400c640034a1aa0061591807008002c5401108c0072600da81d02804809407002103140000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 683625737 1250 683624487 683624507
    0x20708062203050c030a0f030c03090308040602090616080307140406080a0b040b210607030920011b050f0601090915050a0e01111314031209063106050901 68
    0x24008500041c1000d082c229481e2240c00c0740c500c0c3c00d100004000c1261688044042041d89056a00f0080d21172211011020348505100143c00940e45001050204000381d0040603c080300600075840c01544010403c01c0c0c40350410f007130707034910408800c00800300e8025070100c1e10602c8a10015140ca070a02e10090320101c005860065101e940b0b00300503030341d900c03151311589a4031802003951301d0b0003070398030b0000c26805503958031842503001c5c01001c9200b280c0a8010f102d12640d111014091030020281c45140020008148904004942d4601e0450585001c0700109079402000684031314401c0103440da03e040010b03481039020619005025010510a403611900705260032804640b940741c41803401c1c06007a00f40040c20380b40d40781444903050400034000030300540500300e41352200b00d075035041180380e43e82c0c039640c035160550002408000700030203d00040620000051140382811305480c6240c4400c0617804410415641d0a4814403510040034015001007a0524119241100f101c000a0a40e254 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 683626987 1250 683625737 683625781
    0x120a020a0602130e01090c030f06050a0504020c070314240403080403030506030703060c0306050a0f0605030105090403030e100c120b031207051c020309010f030c050f0f070507090c02070806 83
    0x10200b030803104651243d03500d0000b480020011022942c413400c0d010000c0c000800401d021a140c00060303004890203000d00411940000c001222640c035140522000c0d40c41080c0c194282d0107214004030010300e008000140044103e0001e240054003c035910b000e02004500c49020359054004100010394002007007580107500d40b50100b580d0b25043c011a1078010107800c002d150310708042c00319070322980c103511041c01c803a81210382e002410f58508031035518000501458001806c104014400c0d820302000c01d507001482403400081d40503000400500341851b4690100e031341a19041002903041d4010480000500e21000412602e502500003a5071041d60b5500c64a9543c00415508180002400070340e6990700c080816009901c1400c900030340382d600c42c4c240d45010036000139210702070a10034820803a140e01c4d00e1f1190761604070315428a00107a00101c848a4803400200900340000c0e80c00d022031002000c0c072031301c042074203911000c01a08004240d040011560310a0702040500700e82c890549440c882 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 683628237 1250 683626987 683626991
    0x902090c1c1107051e0c0909030d0c050c01020720190501080c1b0c1002070e060d080702061305010806030d080f09011803020607090b040b19050c15010503120a020a06 73
    0x11221407142141c1c042c24002808070300a80c039031401e1007204040c00d4225101c0e000186d880c514a2107040040341030f42501d60b03442c40c0d803060040c901c4c040c1c0c0950051018850300d0521034203107580030318202c0c2681d0090310201c450b00d420404e241020440000003c050820840c2d203144d6142c0b00c0d00d10755070040003500c2400e040010788070102d5021002e0008640d6180002940c1c8590320025038000d5544080a04c1c029000f68000800391030410b101140c400c0503905902e444000644500b410080a080c01c01c40648100b1400c014140050340c40c200200003ca500000d40802d9071318180c00545440001440d041c025000085007070040340d8414040c1d40d0005c1c1c082001140d948a881629005200c1800a82c7c00000620004024907030005240c034420041c2e0780c1d8400841d620390b00310803200d0146100f010059803080c0140810001000a03c518880340c83c0f0b8128244009104541d28141058201407c80c44014005018505060004130841070ba200c22031850074241c1000290b440400c000060503040d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 683629487 1250 683628237 683628251
    0x504021e150409050103020f0d05031b070506040e0a0e1c031e02030c121f0302060702010228050c0303040308120408070f11040c0914191502010902090c1c 68
    0x364038501e608070719002986800b82c907103840d081c002008010a00069100700b170082e148540c0d03481c01d00042c050032a031010140d410556880001f44d1020030707520421500340600785003c1425203420000d031000380340309100e28856090071140042211548080100250451920300c05070380c464580c981d042c01501d18000884284041ca00c4021304600e40c000d0f80028000428072049a0840f0003905880c0302c1030707084c10300c1c2d03031a8082114400e080da40046513078440c58100800252404030060f1224078010b0050710070b030a00042c500c41c10b10800e400c0c1c510b01d140b4111003034030500804001b1185050801d40c0107500d458219110302c80303c0d01405190317030303500400c031000070741000240002c1d1520190f100f2116540d40c002c901d007025081440e164441c5c0a0741c940581800c42511a4681c0b40454442c0c0030308404520100b0140200a102e06001c0c5503512881900010042040002c00c00040030a5000003200103142c030400c0160340000c3e00d0212000e5060000700c100403001002e104a18a030804002010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 683630737 1250 683629487 683629489
    0x3150e010b0a0e1c1704030f03030506040902090f100b1e0903070b0708070209060414150a17061006080c0d2d0608010e0714060705210c010f0504021e 66
    0x19112840300503800855500b0144c0240892031880d25501c2e01c25a285905402c200015404500903480058201311010440e000403a020358000364210758060700209000c3c41c0707a0041058081c0590b41994055418000c000c004080c3c90303000005407200b01040ea00d894007002c690020101c0c9552a580c000c8400112040c45aa081041c0d800420214582c1901e03a501e50070503032255005a0720581c0201c100d840010760300c2c50203104031140400f000ca404649030b1244c8040301d45482c1c0c000465900042c038002c0106101c50301606090390740c0300c848010301051421210207460f0030300715400300c800e109902c2c0500100c10688070944040041c40d16001529004e41500c181c1c00c02c4d80c03589822009858092145002031f05c0360046002da030b8203000284050300002080f55510141c6101b0058082038052031407441d4a009401058900d024a00f00d0315040072019111005d10440c061203854008009804551104203014015552503100c00820584c178207038005c5600c0c05120302c01c1c400081112079401d482 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 683631987 1250 683630737 683630747
    0xe030313051018031b140d061a0a03051c0e280306020a03091a0c0d020705010f110d0606231b07061106060409020a0312020c0612040303150e010b0a 65
    0x1400258102d199140e1350302d0a01901c106600354560078454465103001c98000c20034411140c42c83e030040e204800780f0801c0c4c1c8404005200c0e10140c0d01890b455011200c2d4143d40e504161006036006d10040c007039400b0b0b0080000d101290754071086083c040c1c00d500000080e135500007140410242510074190f0413001c0d4040300307000182908004c006900c003060304899164180d0200c58014800c40e1083d620003404208101184411148038444010401550861940316006441d680c0c2c0f0030b40021440d140301003944015541c1d108482c41c28510b02041c510020f01060007548014421410803041100072075020040000d0244030450080303a00041040e8a40200407200f40040b1302001501e82090b200c4500510100765020858902d1080c6004144c0341d180034400d88880030b034000c1c501d800f840e1540d5908150304203c603c40300d0950080380d01040b03d5841e03080051008401442c070718840c9227818900503048a00d80c0c00445014030200e031b82406aa6100e1801c5c605441942c3c0c0215202c50752001d040765 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 683633093 1106 683631987 683632007
    0x11415010804151a03030c010506011b0c120302160b0301080f070503030901030902030a0c0e10080303070c060f0e070f170303090a030c0204022205010e0303130510 72
    0x1501d0f6281d5011005240200c1c060701d40d5110740100081c1544c001111040099450b1401c0200d1907074440380d0b1506c0a520f042e440c032207007030003505e550400d900140981a4840315001d03804051500030441e0340980140f240b420802d503501e5108403000fa410030300c81c000c0180b082c240d0240f0400340200d00f003c1500c01c00303002035003040d910000443c09024407002c00da0301401002400c10100d41e960b140c500141460b240c1c100340d036040040d0003542401c0346600502544d0402e10511035003943c0525040c1441b600201c01003201442c0c01c01c03400042c0b9000000701c1d4540304440b80010214000c6040000f10b8581c000000c075081000003085440348801c4418001c2c1d03821690000340068050300000310fa990000d0401410442c01811481c2c1080c01204210708104542c0802c00056902000100303981e48143c01440c207003040913031152090f640f01c2c081c07148a81c00e40e030a8403452902c83c1c0b01041d = true := by decide +kernel

theorem cover : BRFrame.Cov 683453237 683633093 := by
  have h0 := BRFrame.cov_init 683453237
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683453237 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 683453237 ≤ n) (h2 : n < 683633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
