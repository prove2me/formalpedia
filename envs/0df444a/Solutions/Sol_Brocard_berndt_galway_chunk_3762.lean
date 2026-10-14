-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3762
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:36:11.49553+00:00
-- url     : https://prove2.me/submissions/fd02590f-d2d8-46ac-a818-fb405864c958

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 676438848 ≤ n < 676618705 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 676440098 1250 676438848 676438853
    0x12060b0d051e150f0f01080f070c0812090d0306080c0621070f110a0302060a0b0607021012060b090a270c02100f290609040f0b09090d0f0c0c03 63
    0x5070019110b214180f44000310010090070700c1414120b01031403d40e8502100058500020704a410003000e00504940150210309000d100d010040b41803a04540042e4a070032400b10385002583d420398110b0541c2c46117901c1d194802d80603005950032107400c44003030810100b0080074062150b1001140b410081c00c61075031855000a80d01200703010361819030741d1390350048420034064148007210764011404d40c420909000000d80c0051015130180d03282c50040750f6500e5600100f500780c000e00030001d610400811048203d103a11281c0c01640b90050142449100c0da20251940319102e00005283c00c114000410b208040c010980035483c0e1229048080503281d00c40e000e42d0440307007078134507800041c1c00c64100403d6500e91800b07041c0403182c014004100641400107610a020004817224101010310700c0340d0704156503071005980c0c0b024000b42c0240080020b041e9560b005045030107915201d420030001143c0040800650007800e4110784d240c00001140c04841650b034070302c40c0407084424030b4980001000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 676441348 1250 676440098 676440151
    0x30f050f091207050108130b011a0f07050f01110f04030209180f0a060c050c0c010e1306090504060c09050105040e0a06030609050a140c06120915041212060b0d05 71
    0x2d40d0801d40001d8904076007008001061003501400300f06841d061604001c02140401aa150445e801e0a21100c002211812120814011207000c424100c0f000324503e4103000300030500708121656003000f08400190010b0850356030050083c54482003c0c02c2c0f005200508000780c119030002001c40700d00145203140040f8900e0480342d46469140340c2c100300d22807030800c51b20f0f0149044907030780f40c200b80341001121100e03295a00700807807802d07041082007405640c0ca80c80301d44815102c03400032075090088a448180c5d44c2c000d807005960442d40c640c40c0c820b80b50000c1d403040c0c05071415100d0503910149414500003818040d4140905a070002f1681d40301d00100044071403145600d020b00c90000342600b1a0b0604000e01138070301c61001400760390003010814001c0d9840c00d08a034598000701c0004402600d540740c0781841c0080c5a441e101c182c00c005010700040c01b80c420028070780c6a180da614038016141507015202030301c1d01c2d0310505104c08000e202c0c40400c500f03250002c2c1c2c0c3c05180b0700c000440a20a9401401 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 676442598 1250 676441348 676441369
    0xd080a020403050f1020030c090d062306040e07120c05030105040f0b0f0402030d031e0507022b021c030b280509091e0a05030a1805010c030f050f09 65
    0x680c0703a000f10a00c80b951005d600842001210040a038500c0e401d8000307607007541e440028032101c11f0140004040fa000e0382d41c1002e601a59400036410000350030350241c2100070903641440060300965000006115141601800d02d0302100d6001400005180c004082c0035440d450380c00b216104942400400e03030303031024400d6503c00d0b8082c0b0f1030354222078580d0800f00020100076040340540007581e010003003d40c40c0041c4e0a00b8403003240c0b90010b9010f000b5a08130701d544001c6a111500c0c2410507080c80150380c0d00040d404c05c5081900ea201c018100074088a100860f0300d000e100c00035130402c1030000d0404682030038107502407140c0e09002c10034807400e9001030306191841c00512840c2e00701d100d05802012040c40f0b60406000d051700e039100e541c203004840035511102ca04882c0b26003840f03c2080360000c0000e100213280141d101c411a600c44200302d1000c3c11010390321a44818000c860707800001c06612a6480360440d0741c041d01e805400351446002100c80c5d40c0950428203c1030340800c4251101c0c3c13180140702 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 676443848 1250 676442598 676442623
    0x5073506060108060d0b010302060f07020406171507020607180e0f01091143030c0308130f120905100306092d050a06050616060b060c0d080a02040305 66
    0x1090316261100000d003601c80007402e0701c1e0180c01e110009000003444080118150f94040318030f0b07501d070a0391101d000c0f1107208000b4004d400c6401c1450018426501804415844000300280c0b00070300203220f4464030303410b0100d0303000005078050300c0032486286c050829480c10a04503600326104c20b0711000100e909800907a5840580301c40d800040101380c03e1071061150002c900043d0307510305145000e210303a04000e51808444038078848a80018081e11602e1111402c1c442e4a042030320404050030098240300c030f0180e0580114450070005200c4000d034290203905281e000c56100c1154881da118565558001010182484080c00000c50966110b00350607112407000d0750041f580c40e04180499094404060540744d8010040750400200c605c1c1079091180d081000c84c00017a071f40d5442410b2006025164001d0b50403490000d1910301704000d1034090040740c0e00a420038400e482c2060240900d07807241452500b055005a04a03040b001d10504155401000104c0c0150502c1e4032a200c441c01c01816030b422 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 676445098 1250 676443848 676443853
    0x7081b0c0901230618060d060f06080a050603070509130f0506010b130b0f09010c080708070c0305011d12090a03120309120f0516021309050c030c0409050735 69
    0x240c9035075003016034030300552103403e8a4940c103040c1d007070800c1405d244107040b85c24030030701010441075011b60055002e031000b011020a01c80d0401d0303480c0b01c05407811000303039040942c050402000441c507007800980c4004032400036007014219600c01103030400c1c00c07001410840c0e14001600c0c420010810030050240a070005210007990b4150540110380c0819450f40000007541c41444081c940729034140c152a69001c0c01e08004026013403524080b42c0c02d110b5480d004002c02d8003c11803c06100c0d1080d034400c02c1e244110020482e00201c0c01000078038500b695000c1d4101e500480c8a00c1c010720840014103506c4401504404000c4c0e126940c5595190200d9483c10005e692a01d1000510905d099200010749880c1028841d4103012000108684900c030950361001079050044011521400001200780721100c8040040388444c0c034101d80c0f1501e40c2d514551003840f40d20303800904c1346442d00c103a420090b0311600416159103841c0b500c100c0c1c6610401042000c1c4072202000c00803004005c00c00c0010a201c02c003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 676446348 1250 676445098 676445129
    0x307171501020f06061e0d1b150302090d03031107021f0e0d0c0e181b0301050901060509040605070e150d051b1c060f12050601060507081b0c0901 64
    0x80c0f8101c540411100075074414010301100b42c49044065118104294681c01d8020ba01408641c40c2552901e0040007241c1881e01540417030b200c1803001003920f60380c114824000c400d400b070484c240e0041040c0b203a07110000c6d0240c140083c0c0a07920104001e40c2582d041e504248591300081c0031008209003c501000c82c0703882d904180395011000c920325950446071046035409949480340516628042e101925141c44045545400d280546131401712040c0c040b11122100340402c03403076031600f0b401d140d0300035801c1c42c0100e1000340042c040c0c14259000944401c0c420380d03030784e02c0f00d1018040160081081c021000c0d1406499110a00c10821400410301001e540e0310060051034111580200040422490000d0008401074004c08540340241c00e405600111180c03d007405004180f0b580c4451555004464000380142680301d5880d5014052400c0d11700b0340e030ba140c034280c0d81d80c4551980140312030810003484080058411740c982280075854110740c0111b64100100360f185a0070780180b10103404105 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 676447598 1250 676446348 676446391
    0x4021303020a090e0a030302090109030b011707080706050a051e0f03010807140f060a0e10090906080a0201300203190e011e0b0f0409031110091502030717 68
    0x110070100600303110b070f420011088070401c01504d852042c1070007820541c0024070015581e110381c0d1b0481c0610342040151600b0f580d10ac0b800006502485400010340c0aa2440000c00c100b010070090b0031200796440741d501c3c0000703a1a0440341e55110b11f9441d0100d4040c0c5003000380762103a00300540030100380b03444115034a5061008852400e5a240d100200070603c2448e0b00099031241d03d1402d40e50501a9205901c616a80c20181d81c0c400c508565540c02c001c0c1115006903890b400000181100d014010810100f42c9a90440b0784500c2d0501029005c9a031720400c25181c2840c26640401950503504c06440301005011050203a0b40251880c03091f41b400e005410700c170341c40c0034415030070000341e10002000303621250f00ca041f010015113045070010302e40e290726812058a074040c40c010348940040007040802654a17002d04001002c103042e00c0203124502156640607054401c50041c6c9402c240030101b07002c20701c201700019500060441d000c0059240c02e605c2c0d40d404502d6450300401003180d140d070540c02400c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 676448848 1250 676447598 676447609
    0x71a2a06180115030201050702040b031c1b020a0302060a14030a0c0e0105120105090a0e010f050417030103080d0506060d1806050a090b160c0507080f1006080606040e07050402130302 80
    0x1010515503903d80749108030740c4201890309000701c0b64203080c03250b00e4480600004008200d4154030070f406001d450f0604400c80d100100c4200510800d4813000311410804c44411000441d01d60020b402000e42402400580350a4024004484081c644048041d04504543d1615042a90201c1406840e0144854195007094042d0b503a0300081c40d11504080091945200140d0306210b0a4000d90744100810040e01c6a9000300e43c5a0708100001d0001840142503040104003c039010344100c007140311032480c2403604d030080f80d0403203030000145401e2201d030300c0210340100fa012306510390082c3c0030008848815440d009103000f4407500140d08400b41010f00b0824140c0740020907080c903162520208400103003104075036036081f841c841b200c0c00c4010703800001039460588600028029108040740091070020018042c690b8001c0070f01514069086c1d8000d000c2910814020034116800c00e00004002e402c0551102c03458662420448066560b2000030504907400044403c4503007418043c01e00035070509 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 676450098 1250 676448848 676448881
    0x10c030b010807030c02160e06100801050d06020c07120b0a060807081f0b04060b0c0d0e0f01030b0109052805191203030605040507090504050603071a2a06 68
    0x1420248405002500000c000000052440080c11780e20305204269504c2000b050004942c0b20544000c41038440c500c000d680c860448501348280c04491506039454030401e4607604a80020302261204400c903a00d06010303400c420324101281c444c2d1403001881201e03103900c80380810302030740403507465081901c2c048080d98041d4012040ca540100301c2040580c200144000705112884011007111036600340071400340c48078160b040e611605001020540c0d550240080c01241240000c82e00125503000050312508100303948582e00060550801c3c00c0c135400313074200040d2030b87d05161507a9074030384440010301035851181412101080b40c0c00001c44240842c680303c00902021070304040c0003c0e4282c0080f480240340d000c0c85010b4418442040e04040c02a0030a401614005205020034a82554000c0254802c0d2007161300c0380e810a4085805801c01150060603070310f0301c503260051300394441c000c400e0950240384504d6183d1090381049104540d288482003084101d007010300780c9070030f100151a1903070f5030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 676451348 1250 676450098 676450121
    0x15070203100c0203040b070501110d0228080606090d050a050303071701080714270a0b010c0b01060305060102100e010c08241021051008210706200c01 66
    0xb4201203000303400d40010a40e4100c80358000603a64411031703480e000d40076280950060710071070300210300501c400001340c0241c0020104440003000071410f10720103407030b10031070300b13982c0c10100c1c11020114910381080c034000c000260010b4601100c1035240c0d500d840c41d200302c1c0c030420f44050b04003005020009610000c100f40140e03580e9000001941000e06590310f601081c4510f959103c4101f8044089848692070340000c207000c20620701078209006443d54010104440320791029180203102c02066001d4030000d01455004000705445a081c90000d400500015001ca8194400d0703035014860b2074002e000e200c86003c0c900c1c00114140f4445140940440c10140947e000e1030440051308820003030080401d0b0a90030100c8107803c10707110404040c3e641d01314200400b2450442c83c507404103e072809800c10750040b8280c4c86224052541c0f5505980c0350510440c41d420059042e1070b0031039a04500c1300160110f280a81c000041c1c100c0c07000c03500d800c8600320340d0f40315030721349400301d61500b0600c428840c500c009007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 676452598 1250 676451348 676451351
    0x3140f0403080d0b060a09150f1209170d0527150a0f090f0209250e060f03160f02070503101a1206070210050601080133030603020f03030403030c140a021507020310 72
    0x415501c043c202b100800340081c1c10940c2d07a4041000c4c4510842c468446903100f400240c0d54a88481d41d0388007034402141c4050b42c1c190a1040c10042440071041e01c0e4003109070768090b15000d8031041800919901c094034017850b1070703240c0407469444003942c8116500c061198400340b034420384620500002d06c000901c40c0c14034071000041e4032900041d2559080311035001c0d14043e034003641e41c240040c14070300885103011080c4e1808010400e40c505400030b446032725090b80c3c4542140b41184081281d0b107007510701a050b01a000201d049404c4202500407607621055402c104202c0864900410a0b00c8420601c070320035a800744042c421102d4041c0035015260480c500305101a251400005e40044410b00c11603182c00c44a000007002180300c5a081d194010100808032000c0d58203080050142100d070000f42e2003039a1403401c0d08103a140000441c0c08a0b0b030303d03071501035000020340c40d0511880300d008903a1655000303d059100050740ca49894005d40e051008000d615458580103051400b902c0981b07400005 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 676453848 1250 676452598 676452617
    0x9031803060f04021c120e0414040c15030905010e2503020f10050d0504050c10020106080705061c060b0d110703090e0c070f0f03140f0403080d0b060a0915 68
    0xa030440c02c0316036106405039148849a03458a00c403080c1c080042401500780c101c070145003400c00f640841000300b0030b1005c07513051081c465151003110440d4000c0e500140040b9081004000b0071842e01040b0702011010305001943e28100c0e11664256210020b061f40c0c10707000060300051220b0100c16003500c2c0201c810740b601c0340300d06560204289000030308130b051083c0d02c460080c1d1026413140040b01e00010a6500500080c200344c507003140d644401c00e1001c2d105400c03111880070302c9441441050f0458a4100c01405081e2400f03042c40303a1940503807080191441c010120181d020031900810009000d007c0e41e0a607a08200300000d0115840035804d040c40350020008500880d070b002162074140c9450201d06400e5032240d01d00d281492060000042105600c009490180615038044454141c026212048640748401101c0c4440c41450520460054184010700205920001a01040c0b04410780040e200800400103440ca401200143c400030700c0c1c98009011659441c1c0d80340d40d00c0c0d0b50906004198 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 676455098 1250 676453848 676453861
    0x1018030606260c19052e03021c0e03040509180d03060315050a0e011d060f0103020a060809030d0608030702030705010306050607030e0d0803090d030501121e030e0301050903180306 79
    0x1543d01208410344503610400b550102551203058800003880000c100341c3c82e07820009a2000c07483c001a648085c4050120601580203009000320790002040e8200f41c6000a81141c12030000c2c000c2e1245025148820320010400b500c0c0c2c0c80a02e070103002c51040791543c0520f070002a40c030707106c91b40b40184101410100e08100042c00700e13843c030344c1c0300506010103c0d007596505c1030180107148150289101e5070030a1034031030351081541070354a10032036490166241a0380e010340c2c96258203020f200003500081c041904020746441281000c0d088174000041e6803405051444c150161805030b00070b007840d504005041e00c11031a040111000a00c000e0801b40081ca2a04001504a000700e01010301401188044003500b0b07503030313001198000b0750300c00c04c110303140e003084000036640ea940e18102c2c1c0e0110b0300c1c003000499003680702840e03902c80c41e038880400e25400e20000386419090782514400c8084c040301890000142da400c0c02003511550881c401181c4680b20603840480160308103d010380039405c1b05091010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 676456348 1250 676455098 676455103
    0x1080106061b11030a210305061c14030f0406200d0828020d0203010e0f13030f020102090d03051e03060306041106130b1308060f0402101803060626 65
    0x10150b0b00000b0b03e811140000700401c0c00e01016076801032480458a15200c440300406000360300304c00c41950100020740d070355014000082041d0715600d0440030349600c0c000000d40c07041000101c2c8066601600d0604610480820098020350040d5012a44811105414240d220240303110465074000600c20034011260241807044090f015155100c072200c03074030340b860303441c410306000a9580740021076541d0744c441180d800039042070007600d0340c4000d24008100040104280b05001d035640d40080300419405603410383c0c40741c10307520b0980150b54003070100b0140d0b40d54401d03108500c54004c0d1038156031410b41e0070490001003070b0f060545a408a050040c42a640c80000d07003160f100d60300a200c031800c030303da04c800075949000383c2c28152880c0d00c40000109031410300d44060410000501400881103849450054403240110341c80d061440d0b01c10001400f40c9803901845045160070f080c0741010714036940722424040242e4100350755070741e2100000c00100300080c2e60b00218090a80c5640c990703000b0841201e4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 676457598 1250 676456348 676456397
    0x1080906060f190f0e07090f0305120913051005010e030a0321141302030d0f021b130e1b04050103020a1505040b04180608030a09030b090a06090503030108010606 71
    0xe010f030380703200409032114070807a0006029080c3e8141c1031803210741c2c42c0c0704400081801c032140b1001401c82000041d1066a9028480c283c03544440900307016090700d03198041e43d400c800c0480ba445145070030214a045003502c10381d801244084522400241800f0024008182c0960442d0107540700c81001d1002c01d0b44103289030180d203500750300900c29200c0079280310082c04000400c0c817241c00481d02131001754420500c006516501c01d0f0142c03408000c030054243e03201c0101408280c05604800741040604000c40e255a0100e04000c00c00c07003c40c0c01607403411f400c071064641518003903030217950319444841e603004d00340c900b40c0400c84091182c0c0d070455002c256603a9081c401c00803112080708a0343c0030f05000e0020b88018140001c60613445a980d0700000325643c00403009921400d1070400045450070740401120489042500c4240c2603915650340d04020480013007103003c403406107003042c8001a03400e0044e1900710303010300015a00c0354107103a142402c551190380440b00344800c04c01e03076a004061078410b82 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 676458848 1250 676457598 676457629
    0x212090f04020d020912070303110109080a0c1506260105010f0b030a061a0a0f090632030103080c06090601120201031d060c0310050103060b04030212070b0f090108090606 75
    0x35071110f80803003c1401030300540c080c10354410f0340740300c80405540001800700200d0b4003950b00c00b4100700c0210440c5003205c0700803102802c0c035101000300404482c015011210b1551261030b0f4a00d000c52144103110483c0c0d4117070401484c440d1136609075004e168407244c034020038004031002000a940760058201c1c20340131502c96a44c00d1240800019102c05090303020340018030b480e444005207100b180c004840303982d208a0400e00480c00030249100c5d1288200c01420580e5411740b00d03e10340c8044400034240c06601c96040f6203907884e00913407001d50914034901031402144106142500c8600b041001e03800c2403401481c018442d444440104880500950104113007602800c0c0021450040c1d54011600a2341d205403204508c12041440110b0006030011441075440680124145403180011070690304184038100e40c840040c80103201516200c0503c640c9035000c08119280d4035610204034501d40c0000f1001226001c1c007085003262540c001202d80e5016407000c1c040e100c6880c002c000601d258000c0c8412 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 676460098 1250 676458848 676458851
    0xb1f030506010507060908040510080f010509090f010f0608010608030307091a09180a0b10020303011703130617010e220c05040f0207060605060a0210020904110a02010b010212090f04 80
    0x450240d0f4080c00413600c240d03070050014000711030075050100441e4420b21406004d80c034250140c11015210320002c03401111581103481040c0d103000308102d41a80050240c0c2080e00404030b429500220034460219000c00304000494281e140c0b001e00c03400c5034003c1c0d015450940080007000502a03102c95080207076240c0000b2540501481890814107025900603035801c01c0004040c8000f09400e030802500c140134200c5c05220f0b8418420a120400c42c2c20054400075a005100510001043c64001262114800100ca05054818501740c000d401340364800c0c000b01d1880c20100c00c1d21030942c030040c0d026041044c00b500d1282089502441e8202c1c41d10340c80a80070441e082d10318200490440c18000900c0018000e105c5035a9801850f8000d6006d90001c0382c005103040800030701c5013000c10542e04098240d0b005040c1802c1070b421010041d42c080d4804550180d52180290a000a200c0240414001d19400003a06034810000680361480a5640321014041400041042d0b661450b03c10400841602d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 676461348 1250 676460098 676460101
    0x315070f08100902030405010209090c0a020714030f070b030a1103010605220905010f05180105030c01050703020f06070f0206090c0f0d0510090f1a070c02040b0d0501140a0b1f0305 79
    0x4480b03407010381040e0403941c000002d100500005402620003900c0c00c440351380d0940c403141540c013110f1250101850150704203420406c54814012a280c43d10344025054407044000300701d40702c0c20180150072408205e0008030512690b03100c00c3c4900c82d807030310000b80d0301403649d410520081d18030f0140c0d448040c0202c407408403032880250500308020040007801c405001c0b0b0758444070850a201c40c140a424081d2401d10081003042244110b0641219405800b07070040d40b400f08011078540d0300140f426010f604c00d1039811614070400b0000c0070701c179203a0b03656000101030001500908284029041c25801c0d03100d042d05460f666115aa4052000c0044030011600e00321460843d041031000400380034203600c1c1c182c0b0b504c00d10144c031010301f007101c0c803a507007100c101c8164030300e410b8072140240c8030711002480a000c2800181060f520045041000400c8120b4003002c0d6034606080d2400b6250503510003001c14140041015103014031110300004a40040341e1140c040008110880e000c0e01000800d5102c10 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 676462598 1250 676461348 676461361
    0x90f0705070c0605091206040803060105030c1c02070308060108070207051909180311121c0212150907050c2d0d09030219030506041101031b080103020315070f08 71
    0x500700c0703514562205200e5041e40e40c44034081c3c070580065140602440403401300b819500380c04101c00d4400d681c0014514216200c00b40110b83d95040242036440d0b218003000780121a00b40e062621081f03403526480503945403403a16000384085000b400d03a074107101a40c014020071980204500082e04c41c252041c013144031542d6901600800668070041110740b805806100c990541885209074034007035101c0702401c0c0004070890360340c0c5d4244a00d41c2c961010921506145510509060168030785106e009400c00101b0040e084c180d050030740f0300300e045400030012004a030400c0c400c2140c1c40102c5003002401c0030903105a545c0c6900b0580307011504030b00c2e1001c1134800e007012800f00790781820031003080ba50420b803a08800303048603801c0e0105921030309038a607048071400d42c040b4114007074940c0080901126141d903640c00c071201d041c26031001d06040e1540100f00480201d40d03510f07220a000d0341c0c0c83c2c4405500d940141400e02d12035484100c0751043e10800c0103510368110003264628180e078a0100e0303d0380c0d41c0c00e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 676463848 1250 676462598 676462607
    0x61a09060d03020c1816080105010903140c090703050a0e01061d040516180b060322050705121e0115031e02030307080405030615100e01120207080301060206090a02090f07 75
    0x3020f0300d90b21280c0e031503400040c85d001980a51145464500c5441d95140e820744c103030b8080e202446907600190340c4c1f00c0b00b480010000d120320f0814000c0300040b213902018000004041e40011118000080d80d1802008200074981c064144001c12401c000c000c55400c0c070032517000c0c150035000603800c10082903000c1810410308000d01040c0e0304203241c0e0558480d0702c1d0403104800001c04d9070800200350034401e00c5080e614081d800c590059501000a010340856950400d29001d4503003420f6544d805a420001025201e002c100d00d411144500070f0046032801c600700032078443c0c20b11a000c201ea0f02d400d9a11035440507801c0341e0025642c00c00c1c01c00701c5550607144040c610261080b4000e400d400301141743c1c400c0190500240003556011402d407601c0b0f58403a00c89025008400310401c2d481103001a600310b0480c0035940d05d0180800602d0941e00354a410b813100e00986c2d214030400c641813040017004005007a4140000c580140303402029101c2304280e5000600b07550f0004e404a01d0680c1d928010501c028000d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 676465098 1250 676463848 676463863
    0x50106020607110a0f06020903070906050a06080c12090706020d050909060603060a1d0f1e040b18033906010e150d11130608120f0f03010f03061a09060d0302 69
    0x1042c581c4031805c90b443d00002039000404240d000f44240d80e804620341c4018020380c015542c02801c0ba01b402442c0002c100c9010a01030900580700404011803140c45402e81c0200d4410440d200c02003182c43d141000c02071a00448001d0395040000a1040965035558081c4054020700300b00c6044d600d81d203952001444003844c40d40722032030788885007403488801d14000320520f102d046584c0310f03003241d5510104000c030194100380c02210310310203c00001d030004070785203140d58122104501003802c2515168110389147d10003c520852044044028024910400006603010b03a9106040c0c2d0240501005960380704018002d41c41d25545a000041e4038a803841490b41c0c00540003481031150848d00d007001c104c950118600140608412009c40040108600030030081750340204c002e20030380a0b01200310070b50f5000024a45210300c01040b102d8120a18800a540a0403610802600c40392031072928030110381c002d12814003020110201340520380c0e07c1c0c8100780d51000d02590b641100311441e15003241071040 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 676466348 1250 676465098 676465103
    0x20405030a030801050306060a1805090f0a150b04020405060406030c020c060d021c050c070f0515240307030209010612110409060303020f0a0203120c031314010f03050106020607110a 80
    0x101d144100a040c0d10502031030485d0400d40542e4a951121800e00000c040b0030b004002030b900782080c0d0641e0080c40c5500c55680812080c0a84041d41c42c07164001c2d06000c0d08460941d40b03e03000f10b4545c0c41e00301541c410b0142003d0119821407800e883d00e00480c3c4980a42d10030103080c03651703070108940414024421440c0040000300500d9641045e00e285600035004140720a944d03005081d2405031000c1c2034071400d4000c1c0b03101d96803c0d082050a80e612201c80c048410200c0b9180a0006500440c40e1640d00e07040c0944410501160006036401c405140185010b010710703c02d51000310301b00302681341c12140341d040d17510520b3b001100307480c4100d0203005000800340980d5150000200003034040980e62064098912944c01e40d0000b010344a052647d074020407401a40c15040094840c06042110004102503a040310540e410321000341103a0751165601d5100700f0480b595885150b81c10b6134080c0c5031781003290040c1420481541040d00003507943d60000d00700341c1481801d00480121040030409010441e5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 676467598 1250 676466348 676466353
    0x806040b090c0d0f150c140a0903050d0809060c0702060a0f1b080405030d110601141302130f0902211e0901060f050d03020303070c11090708040209010b131802040503 73
    0x14101e2611306110034100900707070303204410032011060002d000d000d40c98228085907503821500130b51038450340031548611a01024450035910000000b18284000004415903488624261500740300490074040024201d070703241d11007001001c0051b0ba034481510100038071481d009040c2001107506130b6904040c070682d0b04095101c2c001100030444040d004009455040d8165600b0404c015401d44001c140664000d125070807100040c07041080c07800062143c10720040403484286106d4101e88201e0780705118200b40142e1500081c001c06054030314036001095403100462070400351115211038012844100015268004041540c40d561010b4510000348040388106032420428a400e00a0400344280c08032240c202c4000030781c2d8904000007108040d00b6801a41c515525020100c0f40002041411079207529891048040f68550740b03001403069600362140c04403401c0074010400e002d14140d120340840f01041000d032a40e410007140c2e02c0c04a0f00d0951a50b03501c280759183d204081d000302c2d0821501403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 676468848 1250 676467598 676467619
    0x1502032e03050c01030c0504170102040b0304062009030a03080702030d0c0207080708030a0504030f060f1b021507091a07080f040611060615031504020406020f0709060806040b090c 79
    0x218055050030003107a120b40100d071100408540190150340f10a1025070220320144400c00101c1d100380f00507500c0d416030740001032074a42c44001403111608240c0b000d03283d040d50b8200c44040c1000a200030f42040c00024021800e040324180001c3c6c1c3c503005081d0050030006503d000c51441402081924041650f101080c00103e8071404000d6582c0110703c42d4550307900c0741030381c0001c1682e03020003100c05048035a0b80b401d00d000e0454407509140032400780d040740d40e656a0503082c0b42021700c03889401d00802c488646005004071602c4000d1420b00d6010540d1000c0d0340e80424881d0140e0040d11000440e02107a07440020302d44000c1d03481c03446001d031140c0680812000034444844074203440051060359100d88424171100440869640c2c0c41d2000c64429030010303030190341c0000701c0303030540c000e07540c0b0000490350311065040134004601a42c210b9404440540e01c54800b14019110611040b4060a0301c09030401c41c1900e130041d0165900c0c0c0c040e01c0a46054282804143c1c0b0980a00407880c4584002e0030600b9074 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 676470098 1250 676468848 676468921
    0x909060f050c070c2c181002030a0b181801020c03040f0609080106030c06110f0d031a041803032703080f0a0507140d0f0603080c07060c150203 63
    0x26540300702404c4802e00300c10784001ca0302006588a1a0220104c86107445040d0540654440d12040c0a02108420701e05064046100c030710411600c9803044c009a005a00e9041c82c08400080e501000320161288001541400148a540e40c0044e03124011181e480442205044500d0080c82506d01c140c646000005005c51507224605d030341030880d140c0da42c450003a0340c2c2d00e01c00c1900321501400000e120301c0f00c5107c01c010642c030031f0162140c1600c807403098884003018071010603d0820078400d180301080d1035143d0007800c03144604101000e000141c1d401d003c00040840031121000354002c1c0181415a59403aa004100008045000b8000c2562035441c001c0441e04029207060012030325040f400451b00c1c00240134000ca400b80314042c00d02c1e03403510031440d910214804901e40143c040b072500a6602c801c80c00c0600a14001c5400440c09401003640e0750071400201420311329203412400902800195120000d41080b04d0120b075461800401a20b94482e040e0740304058035204082c4080e0048206c04904 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 676471348 1250 676470098 676470121
    0xf0f03041208090303040f060b060c0f0c0f0303070f02102a05060a060311010804080f0f03010311030a05120d06090e0d020c0a120f0c0f12140307020a0909060f05 71
    0x1501d80d00c40340307402e80d1207086413035881c8001c41d8010115880e910500b0300080d81901310030000c04005080600705800400c05c1450015040c20010490340801c1c1d42000070304084c1c1603110155000c1d006145000d500da224100304c4610303048002d010301c1000f0004481c06202d40d90305505440c0300744520b450b144201a80c40d45800400c581038810380201c5000c2004114a8842c0c40200c0340d2040400307541c0f40a10005455520006000396805031040006d84110f100540042203d41c072801a84e80c1ca030b5045003400d00303900391400d2490f0300944c00000400d020510000307048000d90780090b1807558903080080418064812540580445420860f1055803010041007028184007540d0840f00d0600f103040400040403038622075405d40083d00024100131840c00f4040d5100c042c010704030045240e540c0d000c4c0c1070800340260311008001c0407074007101c4200140052601c501543c800000c600340911900081c110141d0351003902252a46e4030003200400615401801000c00c01042c20445071030031100307548 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 676472598 1250 676471348 676471373
    0x210912020d08130209041e080412260f03090f030708031f0605031306091b051008010b03060609130903030b10081312171006030605030a05120f0f0304 66
    0x107010910100c0010780c0e541c000b031110540590000d12200d49074641c0c1d203130840130f40c00b10042d008100c01b689a000011a44e480004c0c0002e10820440c03614410076403c3c00307076015149031542202c0d00103c503820755072030f000310064488803004621500d6a903250180a07500c1c14030303041c80030fa00600000c1989010300c0a00005580f1840043d003d0300d25181d6140101090801107000d620301080b0140045544039008a0805480c0f40c8100000241c040d803a17160342441a0520802030381c1100d04850900c42414907210307a61426882c0d092600c641e50404554036403d0000910700350081c06d0104252440b44d8400760030405a282c0550104080da007203040080c003501c0040900390054602c0c191420f55107201d00740144c81610401100c805000e907a0f07940c80031010081d00a2010807500c03104442040c2c5501511500801c03000d000a851185401c60140c00c1d584c3d140d124500c40e400082c0e10401042d00403a180e000c0714090340500b940c03a6420030712200c1328084c1c3ca00089920502000f0001040384814685 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 676473848 1250 676472598 676472623
    0x13090e072d06090f12020a0e07031107060902010e01111203060a0e07030903030e0c03100209031203090105040203010f0c0f14040b04060203070b0105061c2d1b0e0121091202 76
    0x901191715140140c1442007494802074100480020400403004030884150b00511540f50101c0d41e58070309101240c1d03a4000b034000782c45031030707451800e4411036030043d0790400d407103a003800c000400d0002c030780340181c0318510615095450f090000c00076240380c1d500120031018102d24164000b09090106001380105404e180880100745081344150b00c10310005000e80d080f80e4000c0050040341310890440b40a50042c0780140d8041c810030003400c000c03202c840040c2d0b00c502c2d01032000140078980740c0101425684454041c0700700920b4905405007180d4001800644540c403410030100da410060b880441d5485243c6c48401144404200456000c0c2d003c40103044150203026558050303621442080610f2041901800d840070811410305080c040d140c00c1040c02d01084d0342d1180007041ca20180819003145d085100b02c00658480b00680b5002c1034245203c011402880c01e142d01c825002c0010b021807400c00007402e10a48003800d9071400340816041042c3c0a944000c031481d031001c1c0c604000c0e59030210340419 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 676475098 1250 676473848 676473869
    0x60f020d02030f0601140f040909060603213506010c0b1e240d030306030b0a0e10110901030b15070311060a051006050f0d090813090e072d0609 63
    0x80b003c1c2c45200f070064801f0b181c4241c00b02c5142c1490800700e00005c150781c2004840d4247c86e20f1000002c50101440f040781203481000380d2003010120400145002000300f0300d0b00b0b884c450308070212903082c1900c0500c0c01d1500710200003412910762500507a9003030881c20f00140010361020402680341210b840c4100445440ca0f800800ba40f00c00301d0b841a0b0820700980354202c40411035004026143c901e5003120904d000b418006002920ba450f42c0f11803a100329415a00681c540142d108140420800000c0d00182104100b088480c4103180d0340c058070400c800d01e07041645411201120f6940c2c3e40580c03907800320602685503102003525002c0c0c44130325040d0210300c05014800000b80c101129006481c4542e00359030103903510fa42844020f44450b00407000d0106a01002d119904170320501d4401d85405038001d00b00f00d40c41c0d60642c421008c660320160002c07513246082900310445042c0025400d02500c001440a0341c0c42c40180511540140b00781580e02102001b8a038001040b6411040c088256010300c0c41 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 676476348 1250 676475098 676475117
    0x12c0102010c03050130061109011b030f030203060613081c0f090504020711030313051e0906100c0b0c130b12042a08010f0522060f020d02030f0601 65
    0x10580072241c00344268035615860710402072110450310550091080450411b554103021070b101c41044451050700e4104560300094840302568000f001500c0b03694611058141d00300082d903005000040100c0d02c0000c0c15000f0010a0b60360341e030b140544880c84000503e816526035204011551000f004c14141d8103114405426500580300307001c0c5007410086074440c143c519140006120003940b09103401c3c1d900f50a0b850603074400c3c0d6020f1000b040c00340c06400a8251007800c02d000c000c1e12143c00b00b0100981c040189201841e40c580581d01640b02d101200c0c0741d411004009000d941c00075a950700102046902c400308448001c840b0090034068030388658a0701b0140d15182e030b44407140316008070130080da00c803000010f000855030102001d20030140008038060343c041c00d070030301d00410b06608000a0340c0d469000781e6060215500c5895400800c0c10710640440c030032403804011030320032000301900040c1c8031283c901d501c00780380d0111014644a41821981da25204507040802c0c9425a00c89000413175046 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 676477598 1250 676476348 676476371
    0x1207030210060f0515070501021201080c030d0e130f020d050112120311121509070504031a1005101815020c0904030909180f03050415050c030304030e012c010201 71
    0x80f05444d00941550500e49640044000d035801c454400c0300c00399000c2041c8081100c00001d01360003440000010300c00c6410010406003800281c070050402c10448900804c2e540e81c41c1d800843c3c1d580c00e0040700280d0030f0b10899014019200d4070302d0ac500c0c0c82c0d050200000d0460710503000c0c10b0081c0d024454068012042c0c44044080d6011100701415030302080c4400640d800b24882c5041d00400864120090031a0000114190f440201c42c1180401c1000c641002030150f00b210117103150040c0012104145480340c0b07145800d20b21400382c00d0140c0b0a02110611160040740702010211604540d941d2060380e038802c2c14124401241c0c0c2c0310040c02118980c04003030501800250159030f144d202e2681c81030501c4070342801800c147ca10350740300746041c1e0106001702e0301401040799140c0c0203507102a607e6040143d00d101420400d041c0b502004403c10000e08014400b005490304180c3c0b510382086803050090040300c40e102544480030841d0a04140380ca0003061110546454281c20f8000303111108110 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 676478848 1250 676477598 676477619
    0xb07021003020f040308160b040605060a08150112150516120c1e030902040e150603060106020d1b0203100606090f120f0317041b090204210302120703021006 69
    0xa500001030504240000e10004022001420047d00c1c3e05c061260a180280c45200306070000313807025105681d90fa014404541012582a0060205900207100400c003038a42c0d4a10038005208190801c08075007241410440c0c04d04004103840c5a071541130103181401100d500f0f0700500c400c84c0c100400c008201e41d0031807141030300840351344045a8943d04000b0400005009116441c400240100342e5500203040c0180d86d02d2140c95583da03000380003080484400d111040000344080c000324820b600c103100420007036900046034000706140d8030742411010741c2c1024108080844480013541405034025044208107d03600900464007a5a0f5544d405640c0341d165242c260f80710f0041c1050000e4424140c0b000c030751408040e5418500c01d2500035141c1034212100c03d260001501c04440d18070544030488030020121412401500041c8800c601e0701c1e2074010b20169007028075500282c50382096420070141030007804014010300a122240750b44601c54a0001d482c0c83e03240e9045a03115103040300200c4c0300d0084 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 676480098 1250 676478848 676478857
    0x902090a240206160e151e0306030105060607081c0617010e0c0105040807090b0d06051305070503060601050d0509070503030307050418090c27020414010f031a01050a03150b0702100302 81
    0xc60305d0b6500305c41c8440d000d0040035541e00311314585c100030070404001903140410040301c40381c191203801520390621408040c25034502034000c80c8900814003010012034004812a81945540c084d0b0a10810b80e0441d500c002c2c00c0250301c00c0b01a8428406d0900c99910103401ca0420410340d10190384c0d000e211030006541c40d014501450384a640310b01c205000b5040598099812414002c05402015402e0b55034042a680112003c10006d52400d19420401c070f0108070b240080e14040380900694030b8400002081c50190305400c1050f292241c01103104500c0601040380905806010f80c0e40e240b07440e24010340141d11500c40eaa0001e448500c0e0541c05480500c92603284035070200302c1e00403041c6007281d0301103000ca008810800100300f4200d1032070705016a100400061071170103245034a072006003002500103203104004500b41400c2017090354100318400c49a1040031024249070b9101d0310b40e164100c0080054064000e11024242d8000c9021203504010700152442181e00b0703c0d0504001d207044050303009 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 676481348 1250 676480098 676480141
    0x30c0a03050d030c09091a0109060305010b030c18090a1d060402030a080a021f0c030b1c03080a231501090815060d062405040b09010902090a240206 65
    0x80b48841d210743c20130b0031903c01614001e10000d80f120142e804541000700c60350111203072003402c44081d580220800000300030b0750038104115890000d400640b403000030419072659000140000b004583d81d182a064080b0140400c1403071f01e0041c040c0001042201da05020019184040c0720f1020000103202c1c0c4215405400341c8503002c010b544494035500442280019030160a11103c0d0010419000309000140d07041c0100d54007800460250445140000e0180941c50903501d0800c4000f043c04017800f5540e01d4078003800d04e80c8c1c03180c007200000c15081492000d18080c0c01c111851140100407114060580c03140d850150b0752100c4010740c0c0c100118807030200681c0105200144001600d0005684101e01415007803946100b980e0f00340450b0100c4030b030405c24416066030440c07400010701c200c5010b0441a1020400c2074411800a00c0701d01c1d0501c140488107800203044812038868a00041c018003503504802c040702120180c0050788010221000014801c400028405c4429610000b0744104c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 676482598 1250 676481348 676481353
    0x801050901022a0705150a031a1819020c03041401020c0a0e10032139080c1f0e0309010f120e03030a0f0e03070c1e05130902030c0a0305 60
    0x158003c44154145011026042407801050b100003102e0321144c444640e403d01725040d0640c1c81079210b070080c085943c049140c041c4149110b00e18a4661150710205c14103802c1e0403155101e694400f0300e6005000512070381154950300100e408074000d04e0001c0035009540000d030306d1a1000c00c004004980e60010140d00581c400307040f4000b0003d080d1034407005600094100d00e9010b9007920f070740f980c4460300441c42e180c08104000382c1c520107000740c1c80200c850801e1654071500e03140303d13808090036410030000101d1100c0d401d098603800c8100704040c03080392145103915042d078480c080040881c41110b44480c0031207248500b40400b002440c800441100c0040360143c4400700c84400d05081103441c41605280720302c0513036036400c1e50210142c080001c2c40c8140002100030070300a135034480c200d080d5030700310b0321440055000340140400601807400c208143d400c0580141a0b580001400036848100c0368802ca0f00807820002c004601150fa0704845900b600070740487d0303c4000c0300c10034042e0f640b01c0c5d84005403258 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 676483848 1250 676482598 676482637
    0x901090309050d030203040b1305010818060a2706022d0f0f090a03060b0f03070b091909060f0608060306060306070305071205010b09030d0807080a02070f051501080105090102 77
    0x10314164200c0c1c20f440e400391040340e050540380c03580308403a45d104070584c4945800d04c103010000340d0b07403020000381d00001c40c2800644c00d41c00c3c4210b05644e100054500300010ba1508011014410407810700c48060125050500118001e810141c1c001c0d44a039001032000e401d003402034007005442004008601c2c0b0010910703031601d5007030b03c0d102d050386d04801c40114033b0315820894600140c0e1114440d81c0a14000c64002480c038003a2010020341c252000c104500a401c40c1d6020081c804e20300e000d440e04005e0540300680006083c845510202c1100d82021240a280c00c00103c4c0d8844616450700542c3d00a4440701400e440c0d0104146d40c4400c121240e9600d54007180024000a209030005904644c0f18101107001100302c022000c16181c00340c010044c485030119580e500ca180030014a03c81c071002d03003041080760510b04001025400010314840000e40c00080c1102042021660013900030303000016644844da20a042c815211401e1141044544c04e01c408900c10401c18030031260741c00c1e480048a82203 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 676485098 1250 676483848 676483859
    0x2220b0a0308190311030916060e0d1b050d031e110d12020c0a05011a1f050a022103060a05030105130b04140a050604050d0c020a030305071b1d0901090309 68
    0x2c0c8200042a43c1099200c45071241c0c0380360140003450180c01200040c2c09640030106036a44480110780c00070f0308120400d0038404140c1c59944254140a801840c100800e1301c02090701102d4041030f60100390010b100494203410b0560101c2446942eaa50340800c002820303038a481210040c0b0300c1d6a407900240c120840b4122603c1c01408031214001c5080400341c18601526038440c2403080d62202034a65035128450180305000301c01d0f51076401181110a42c4484009490307031888503100d01400000e2100000d2130900d818000c00c82960746030540301d1804250000c440b104c40c0745e5042034803024041d00705164085502c0c901030060a12410707520102c0c800103096611250180039010703105560141900781807000c268001c1c409036000174099402040c03103081a241561400c0b00d40210704007000307143d2121800503510f40b0170b2141140e4042c54031944411441c1800d02c0e03d21140c40081803199041074002502c41c01f0182100d10307007011042030480a40c2d4418056090728501c20b0002c0009801f0700081c000c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 676486348 1250 676485098 676485127
    0x609030c1c140d06080102040f0e1308040e180106061707020d0e0f060c01020c0a0201090e0705040501050304060b030604111e1f11100207020a12150b0d02220b0a0308 73
    0x103040f031248011804c02c2d52080964220f9000f40c100004c4000b08260600501d5141010140c101407a502c0081152a00d42c94000e25400b85008a00b80e110750100425001031001c20307014200d900b140c008001c0250b07101409081052070449110300304c0045000a28614004540907034015000d40300c1600f8a4103090402115074910b00041d0b6004030184a504445142440070789040704504004040e001c20600014110104031340c400740320b6108850402080b1a40101601c04442c801c1c2401900c075103441c9040000f404254020f00d03010711400080000f488001d001c9161608015500c4004d51039183c000c10058400703d030141a000502240c0a1f4404071140501c44045481d0345044082115012030342d81c240300d100d040384140310b900810400250718007504d1440052011042079103504000c5d907078010200c0b01540705404507a07030b202502412903c8901c54000e00356401000354182d80890701003020700b880131180241240b46030082c1d40c515410481b040303500790703504844104d0815540712400f40 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 676487598 1250 676486348 676486357
    0x40f060e100e011b06050a0203060a0807030314070c0503011a130c020606190807180b0915011d040e0105041202070302062b09080a0f260402060405030609030c1c14 72
    0x6044d01081c072100400304585108290040c1010314003daa242013030010454400c91039080f007000f0750071150040001940140ea2803034104d0b80c1300070942d2109610709151075124015440746805500f4440c500d101070007014041401808100c070a0000903041288401c01c503014507400d41c0140e403040002ca0310629184501403030703501c0540c00400401da00c0300080783c24100c250b80040b422640c2040d5684441440707000d0f850518009440511461400b941100780c08031070b600406050190018200d000c0c40c0e40140e01600c0300030068002d10500c042c0c2d440440c000d02007110150b881e86244031003a079255101040d00403c5a800620302070508a40703009a05a9802c00e10b0540042010542c802252065a003e00c3d94004d011350300503901c40c03a20200181c0540c40701c51100f401c10504000c40c9042d419194400701c400354041c0c5841e52a0742d500c1c40441c81d0742c821a042140e0502c030300d808101e6040c00010050075179841c1c403816920600300d0000d005500103942c281d40004128024010f030b001003070600141 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 676488848 1250 676487598 676487627
    0x5060d060e0a0813181103010501120603060c0f030b030705030a0201110106030506011410030b010206010603020903151003150e0c010806180709061403061e01021002040f060e100e01 80
    0x128841c441540c3c40c00d00550286a6002240384280020002074002400415844100c0032040c000400086c1e50800c0c684414041c030381c148a01d00c100b143c0c826285a00a002841e4030110070400050f0980b000391101220000c070100003820180042018100031841030102d82c0d02400408038000a81c4c019605646200c036208040d41d41c408000010940401800c0c1c028140320444805400b0301d002480403a6802044200c10f041c00c182840440382d03400035a00e41100d0303040c0b50040e240d001c0d14000030b040030032807040c41458081004c14080d4403100c098414048903c1040302218880b151b2200401351000c2400100544c0c01c914580d05035540500e07961548402d0003048480e4400e030b90211494040015606030b800144001e00601807140c1183d5105040314085505606524181001500c3c0d040c100c45291540060040140516402040300390001034040205549503611203525151a01c0d082c0b1401000503500d004040d81c0c0d0900200056a4820356036502e400c042401c401501d800c0740540e02c1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 676490098 1250 676488848 676488853
    0x1d0f03030909190504031e0302120414101103100e01120b2d0907050109050d08070303111b1c0e09092514030601060f0e010507020d0f1505060d060e 65
    0x140c0c008100f00f842240c0c0f0881c03094581c20030444401c58001040f0701030301041c0c1c00f8544100004221401c12419403a030103503010016203032440c0788901d07a90030300111300b556a44c068105040c0710f29641c2e11001541c0320f078481d40c011244181c0e0f42d829044a909081c410480d03100c0c0401104070200c2c1ca00b0350031310780c04981e0f44410a0061101d080c2c025003407070300c4400a400e03408030300c0c14800d981c001800b643c0018042440c011145034104800240f081003000e40c004c000d001e00140b6242054065008900364540803180c49444203007440710000315801c0d40040340198041c62a100d5220101c05000d04a541c00c40c0d565590501841014011030490140503019140300303131030f005c0ca900c42e01607868466822240701c0081c1d46524050040c1004160039140612036000340d0018004203610900b80c0c4030b01011850301035859504040140ca881c07081c0200030b034000c1b201840700c00610005031f11007a091407250602b4028400c90700a501c0071030740262040c075441040040000701107000c036001024458882802d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 676491348 1250 676490098 676490131
    0x70206040f0b070308090303150618040606090e01091a06070311070f0914040515070e150a020606030a050d03090501180b060a0b070201080f090a050d1d0f03030909 72
    0xc00200780c01041c0d001c0800c2c0980040c2801c20998444400c50700a00380400540c21400e068006a02504a0303508141c00b4542c0440d40708458072440c110f941701301c07401400030411075440c0c8400400e2007a0342d02504020340c040c2c400001b5520124070070405600d044070f2003044000302010070001560f10130304040d03041200ba210314601c424070603c02c2200414441e0b44032117505151008110175a401c8400782801d1601400030007001c2a000f00d4000001500e5240d61400e0340c5c1c540308281c80c4002686060398000310401520b00d0305c407000c0002424549529002c0320340641d5035508042d41d502c00403000900c0c580207120304060540c060b4000c0b0304290710640001c60300d202d0308148608550300c119020b4900d04401024450725088c1134001300040e1a138071440c10310304607035500043d02001025002207204188040010700b00030060004e04403032a03010065460303942880030010480540360901e501c0c844640740d130345081031030501e8054007030420150207035080c402010700b003041904c4010b11980e80e01d032551a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 676492598 1250 676491348 676491359
    0x2030f03090d12170f01060e030307020d020114070501050906070914030c22150306151d3301030614030a1407180606140304020319030e04020a090e1b0d0207020604 72
    0x5503441019500c8076005d4030362411300014a911540750762240240c0041180b44003607181c40c4040000e0a4080c02e02c000445e601000c071482c1c910860802800039442c0005003c0024000b1036403500510b116a00c0001a9446e03071a007030307100c2507600a0681d2540c401c440106603420700c1058250440d50b0710304840440380f00303d50200d050380c4204040f041a5405800706104110283c0318000d0b541800142c1c0c0145a810084e007400211034034084020790804a0700064520a0070305000c01c1c14403101d40c20511010040030b0035042c55001041c0007404a824124041423443c01140e19420b900f80040017801703a0142a00d421102c0f1070766031080007560142060114402c080c014058980c220101e60001c0d980e85040d600401c915048440d07800c150030304006100141e5070024011008400420081c0d01a000620b0155070f118885003803140c00038004100c071044250401909002c65081c0000d02c07002c2d9450300240680881c610038180019402844400260318840d400760138802d102506840c038280d01c2e01d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 676493848 1250 676492598 676492637
    0x1090b03031806220e1b0d09050313090504050106050627040b061b0d081501081005130c0e041104150509041a03010c021c14040b03090a02030f03090d12 67
    0x3c0c454135030141c1d078030403c1110140440a140d480709054010207050b060300d01c1c0c0800184180d080058680d0349400c0302005121080c0f080351505016040018070140e40c407610340025100840e01078a00e9481e0240008603070031b00508440d00401c071403801e03003030450740506414401c0c0c60001e005500140d4400c010b2001e503da01c40240300500303082d07043c040300b0805a12a6407801441c0d0104204020110050000714240c1c0295411400300900700f50702e4a981e0904181ca5015081e40300f9540700340003101180d8101c40c03036485070b051030f1515921042d282c4204000c0c04140c59511007e1035080004000c20012150345007001c003980d588526280f0301c3c1050b01c00029003514120780303045405190010704400607160900c9001c0c229103550002c3d00c405000c9281801c1204444604441880241140d50301c640c24100d0485000d0010040020b8681c18241907a9a5034114400100d00a00c5a221440c40c40d12001080c3c1d056504024260480c00c41180c2d1694803c540f140d14420920080906c4a084c52140 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 676495098 1250 676493848 676493887
    0x1409030a1d0612191802060a1814010201111804020304050a15062112030c020304030c0806070e09190218120604290109020f0702100903060501090b03031806 69
    0x900d0000e0909007004044184220080d52507107425600c0c3c8094201c001d0341441d00c0042846e0100d034034a8690528450a95886143c000c040c1000c035000d650210f60307030000030340041d20000203a00802c002a120134004103140314088405140311461001d80c10149016001036520074450300581e180c2000f00d0303072642d0300001444100071541c0d4507220300303000c4160045070b07144054000e09051003030744180745c880100c41c5640c01d800c4020903481e00d0445c1402c50080049074025a4040702289050756280031854640b1400d440180004500c00c00007982813400d0000d0901444081e40340f008d08440d1314440100a5100b10070528041441100a000c559200070052400104441c041e0480345403070b1401c80103410032546c1c1c0307440102c0e8080340f071103107604103100d524192042003c0041e41c8888101d18000c01b8055124000d50040300001c4e000c0500343c0c0401c050080364420070007440702c0d90b205c605c124103480d20300203900c0c1c0650003404002030310104108040000640903013860301c5c0c003180d09102e6814020 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 676496348 1250 676495098 676495117
    0x3020f0307230307050a0c1e0501050a05010e0405030a1110061e0605031e0925080105090a0b0a0506010915030b090c0a140714150106031409030a1d06 66
    0x20000741d541c00c107582030b0309440e00035940c0000443c614a40240050024060080c1002c00c20803c82e0301e00b81000354500f18440c0110002d044441d440400b498124007030502212922100343c10000000388014092842d0741c06903a00001031400d24084110848401900004025003407049400d03000900301d2900c160780103005218141c1010701100c11703008a00140035403108003006020002c002c0d001880494080c42600002c603400d505e80c4030700d12814030f41001c06401e02c28050b05610310031105584400c644040f903203000300a01c40c40c0e0300c049141da100c3e80b414002401e41002c500025035400041d6200c1c0f0b40c40740741410140c055030f4030b8004c44038030512500d11b1000030958400880c07401d031805030701e40c0350710440c0484481c3c42c044002c2e40c010035500d40c2d649460300a00000c1800000c020100c0b802011301c0701044103c0e802100248189403100b03000380324800100746401c5003822a80da03a003065130320410741c2400840c5002c08249045070510320740e0040d5588a8503808a1800b190b0741c440c010403500d00c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 676497598 1250 676496348 676496357
    0x180e04141f022d040b1c050c070c060804030f270303020f072112110f01050610050712050310050915040e06190209180f01090c11030d0c03020f0307 65
    0x1518003801d402510310310f40c1e001040044200380c1100200c16002150300b5101c5090050740c580b40300c10340c10561486528403061515040408012110302401c0c007810a0724019060340510075038944080d10349200c00c0d81c01900044144640c607501c90f0140303441c0801c402e41c441e0943d0054002000440400f40740340c10490058200c0c5200c20042d090400480c0050500700c80c0b0404213080750b10019400c10541a001440480411345e20002c10380909401400004103100b90f5104100301014540281011a2410711034010711100c0c0034102d204405680d0856032042d40c451002524840c141c0304d035040145071404141c8801004202600c9080d0558061450170035102c100a104404210544803020703145115035101800300000002400a040446079902d076005950348101404110150011003080081541c91401d001d091001c500034181251071300701d000c014240a5800460311181c00107000741b5a03520502500300100001d5109101c19040c40c1401490403501552100403a00111060300100303 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 676498848 1250 676497598 676497607
    0xd0b090a031116050409111503090d0c030e121e010e120901170615030106020c01110601050d0b0604020c07060207030314041d060d02030106080d180e04141f02 70
    0x25411142c05412010782c070015202214024402d0040c005907441218851a11003100b003017404042c1d101d6602524000d00400449040103008170050390065031034076842c0c03140b401e68543d0743d4854024030000c203525a44030350034840c1807000c0152419480c05070300c14234043c0f04c1c40c00c207200c02d4041480d0491b1010354004500d9511800c0c20604005000070085c43c004c204101d400d2903680d0100e090502c0e2814920710048544600000c100c800102c0c0f40c42036103d8000100100b6a44d4002880c40da100c0001d84c1c803060500003500c4d06507102d000a116079600102c0d000003540014503c41c115603440b91303001e400142814054810f81d03213428580d5200c2c0d00981c005410900c181980402c00184072074505840a19003440c041800d805003001814050018524038045174861b502d6054002440d50000e009015407030f16054800d4643d104405c1c0b450101d900061421a01c0300b080d0b2414084582070000b4000395500c0f51961147d40e400d50085401c0e5010741d031802d50b0607100818803800840c8100c0f100580b038 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 676500098 1250 676498848 676498853
    0x40c030e1903020607050a1107060806030606150f161533060509030a020a0608070306050406050a03030e03070e09061803090a0306020d020405090c130e07020a110d0b090a 75
    0x4240d030000c0308440201c6aa5003031000720782c0000380b50b50000c040b072401c595203003e19001100c40c2103d000c08004180602c101c0010351a80c0190904c0c0155021001c1c0c4001e6200d0380d0800c4400b89451100150381c4a0034045843c45083c00c801510041780c02442074000b60f0480c0c1e84404005843c41118043d0b66911301c00f4081c91604107040e0352915030080b2900c4c12642c20140c0400410006102d0380e0100000000d400c1c40d01d447c24400303004115800340500c00c100d03840c1c1e500a0400c0c0700440b400c50019107003200001d107918003805003200f111009030005044da803c640341140d064041403042d03601403007500c070002180d100e1009034600c00e9800780c001d80003e06048038084100d070724641001a5a500501c20b044641d0b60b40e40814088903400f250041e0f80300d07051200c0038042d016550006070b12004010400225001d0400100301112140c50b0101c5040d446550f4084003980c2680e4000050b03000d08159400110400801200c40c0c9000f40710010003040d070b50305c200c0310a00460f1200c546801000d91a005c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 676501348 1250 676500098 676500103
    0x603030806090c180d0b15040b0418151e0204150e01020d0f20070302100804050a0f050106030b07030c02010c021b01081806040302210a051215040c030e 67
    0xc01040890381000307542005041c09455000341104981d0000c0790401a54031a0354a05c01040910341c0401c0401c26032400c062510054442081d0081c0a5410244071103000e2500c0d104402004908000c43c00c001c1c41c42d03440b100300e106085030204220341c1e40c2c0c50412100c60031215810740c908698007c05a40c0d541480400703d0030440c00700c2d1078414001d9070102003100d0380c1c000c1040c43c2c00c08103510744400401018841104c0b80c44020401c1100184060b40300038094401050342401c1e03034026079825088007800302c412904040c040318050322541180e018070300000d10b0f0000d105800d0f030003500089249900d0b40c41d4007050420035a80d0301d007c80d03650309480d98116020f0048040340680380c001303007202d03034400245410310f1540c0301d5801d41044458000200f40c40400c0000d07450304c100c0d01f4120780c00c52a2514010b1f6941c1c45462202d4200d0155880c10b0f200034025104440743c05030155611401c000d0320300c1a0303610343c84000d413401041442c0c1c0e038204121601d4a10074550310245607030700031074040b1003d00140d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 676502598 1250 676501348 676501351
    0x170c010302040b040b161e0c0b0304031704050c0315042102371b23040e030d1109040609110307050a020a1a0709170c04051302040e0106030308 63
    0xa040c5401840100481031441082d10110b4000b190065611640c03910002e9010191020040c1840002d00b10030b1840e000c40026822003e104a50b41510b00752107110b51860760008640003400244c0800d224030b60180303518503264005220314122010764041000003810f080f42c10200c500c0f00066002000103100c48551b40c6040d26541464081d02194450f00007034031040b0b80c4404c01684024054120441030440f12841075408484e280030303290700082d28100f001190925144c801181c00b000020680e00740645c0a000c14648009004900145060911000d091250741201c03644c00140072200c03290307005000341d404154500250b140e8403074036041003004a80c91038000710328840c40c041c2c2d0760a0031148041143c2d0000400d0528a0315106000c50492908146680050030541400f820780030004858580340e005400d1030720740018294440f01c0c060102c00380b084940f901944824007c0c5180c0c10240d004a800c180070400b5828140c502d074021030305480c5a01071212186c0e550b01d10030000d0580c0460080d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 676503848 1250 676502598 676502623
    0xf030418061502070302190302151908090705100306150906020d0207180e0a140c27060d083601080c04150521040b2811040305010617 59
    0x20b240700e028000251384504d01e000003030045a401c04d01c241d1200346451844000d41c1e004020380c04101d1502c20700340039038006941400f01841d0502202104a0040c1120351080b0380e120010030505181c00c0402c0f550004068150040c182d03546c43c00f20310303288000629118110140c603540800d91909400a18124081040200b1504402005d00410003541aa0000d031002a88041010950b0400c4242060b1a400004103031008002c0022021308000c150211141030485082899003001040b2040c000200c404500340c0c3c00c00e01c0300007105071411940e01e002c82402601e649003090103c080104110b40700d00f0400d00c1e50300144503044100054902184c501d8402803074400541d04000c01c0718907050003607000ea590302003131820b440901284100306030790300306138400165901c0c140050b91038110716100341c8041d00e00c0200c000011b998a5000c040741c010408041503e418405c00054030100109150862243c036040c041200101141c000d000711000f8004c13160364201d43c4611300c0e186603c0c040540094 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 676505098 1250 676503848 676503869
    0x2d0b0f07050c0c19050a0627060512090c09010609030b0a02090a05060f07050a0c0305150c18030c0607060203191e050a1d010b130209060301030f050f03041806 70
    0x2108522000031540100640c0d0948100b1301403800e0300001c007041401034000c581c011007542400151503610240140010140c109282600b150310f50010164040900540d80400c004128039604043d20f9214294420740d03010940d5940d02880e40083d000042c2030b4006400683e80c20014028401100701c1c00350843c419440440c508580700c0e0104608242e10300c00c681c4100c07004500780078024100c808481c3ca040d40401650400380c45460300044a03091404243c03030341e1051210381c1b040446080000f9014501059032a810812950107100c0700c421030401098040c0200c6042442d2920f070800540b0300f180c804d0300f01503180d14007002c242009500c0484a201031030300b40101031600d520400300110030303550140d0000c540c81d580d03c41f80c1c1c0e010b840512003960169481040e8566080010342c0801e044e00022954081300e000d452944038140d000d040301e001d901c480100700400001c2c0c0b86103400c1c04182c2c411416211020181e85000b411a001503001d4950403401c102443c908c041e45105600260148024 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 676506348 1250 676505098 676505107
    0x200904020f010509060706051006090b0c10020309010209090114042a12181109101d0411090c030402041d100509030f04120605061c2d0b0f0705 63
    0x40641001d0224103043c401d00040403002926014100d5146603000241440300b42042945107003614070522520000441d100030100307041c0b020104950019150358004e20391100c1c10502c100c02540060f10003c3c456500301f008924a44480050900a04c081402500d01240e91424003058424071a40c558a02c800030800706007203201d88140c6002c43c1d00915184103607003841d0000100070070000d450703020036400e849414420000745225010f41d0213001d45101c010f6032200d003460b005044060045030f60411040403024003040c0f90510350366020307002e080f00b0340b05d08075401c021685407082074480c240c01c44030000400041d410203000e50501c07000303400d80740010741d05100c0c4025150080e1090002a054a400101e2004042042990040801d542048c7d540d00da50315140c181d60520724000316130043c180000184580303051104010142d01040100d0703044a0180d640355903c0c80100001709200c00c00085810030310145d0a14051441d00ca5241c0030400c5c1050f81182160f08401800707001006400c00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 676507598 1250 676506348 676506353
    0x90f030b1009021303110102011404120f080c040918020a061115010e18070b1603031b0e0d08040e01030f0312090c050409020f1f0f0306050303040e040f0f200904 71
    0x900d10840c1d0300006d0074400c480c641c0300100c0c013500e02d0100e202c10030035202c010b1000f440209180c2c1401d07000d181c0c0b540340500a0b6820180c85c0103000b200d4103d54440240010041794009411400040c10f003003c10095248452303001540480058200b80002a0060900c602000040010319104003904580c0800c540c54900000301c8500d00a0101e40b45001d01020351901c244200a00000380c004140307456200d00307007c0700f040d48a80020702c0682c000707410900859801c08202c0f441c002d603111103685a15014400105015000d03058440440b0501402c200000303840c0c80045800f4065889040c00041402d1181001000140c05450100c2014641031680000905815681c0c048030300583d004125040d01b800025501000460030640000d00c510644c0d00d103074007901a540250390181c850031001d000c40340085040750301030700400c0d4240e84204000c0c807542c09180c0300264028843d50b03140392603803650395030a032420403204d104079041e18010142004000540d034044001c0c0c001070b50004160f180a4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 676508848 1250 676507598 676507627
    0xf0a08100b030118110702030d0f1b0b07030507050c0a03120c0203030f150f060d0903110f06310507051c0b0406020d0e06130b0105040c020c0f01090f030b100902 71
    0xa40c13040703110b542c90080030850280e68041e182c200c1e030020281d03000001c1c81c00016268074a1020000005003601234203940303916a070404510312a4100d0ba5542565580103815001814003a151406014041c403907004442d40400c140a1002c0c8030f41c1e5400c242c0e9212050480c1614044105c400c1176410510800c0041c020b46101075500c4031060f900e51780300c88004004242c0c0720159500b8141c0040e00000e00112000d62500491402846a50755104544646080303c1d244d0720002640c811642040001c00c1000d01d1080d03650100160500040030442c801124111607440812421100e17a00134503810002858950681011101e440824110600c0d242d0388441c444440100001c00090f80450310310403002642e408078825a56a004554141c01c00c9406001c0d80d0b060701030110b920004640000c00e05051a0050032001d0303d103074009010f040c03e144100090480044e490710304101d141c17500042d02448411603107000b03500801400e4800d0a11800c403008000c0380780c01c880c82481c0100010000103440 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 676510098 1250 676508848 676508879
    0x914030a03120e0d0e0f0a0e040f020f0909010914010507090b030c040b1c060501031107061a060f0903011a061603051606060905060108100506090103020f0a08100b0301 74
    0x145081c07a15100001d40140041800d080482528403035294950306a51708200800b4000c2d00c00c0b144003160002c0c0c00100032802c01e0a019030b51490861401080000c0c41c0e00b0366400c0410f10041c10404440d03542e0020421601c011103002c203c0b42e440e244d41030705100103c03508400700c000544c001e1119290842001e0301e010354034441c5ea14070490000005610589820607a4060300c0d01042c0550350300305a049000007020000f0b98840078501d080c0001070150b021b84140b540019030078107814102916600c900c0020441307081100000200001850581d40d01c807401000f0107080b48101503211030310f4009041c21a81d0280004951180e2142550b03150355500064a0000044002c520798003a201d01c0e088030940031342070542c2e0a12000c801007104203d1150001d405464500c0b00c10443ca035600340044658900c2a42c00d42c40c50070f124101800a8101b01d00100028101810301500e05015466400450792090410000199030f0000f0310480d00c11940d2841c3c010503e0480803801c55040c550305d43d40c0703c0f030b9 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 676511348 1250 676510098 676510103
    0x10303020717030909090d1106062d0d030210060e0903031f090c030204030213090c06140f07051e07140108040606080613020111011a061602031207030914030a 70
    0x14142d24825240400f0003c0b11313810040a091001c041c1400440e1554a90425451310007169071103500304e10b039039400120b1603c1142c000b010010f1924850a104040040c0c2d20102104000805c2542c40c0c240c4607084401d074001d2007a401420b400100c038620301c00315a0b05ea0001c20700410745d4014081802800004d41c1c0c2c0114a040c440180d02c6c040d010300c4840c2c80c042d907001c12029030611212031855501a0b0107441100c0c001d881034a0000310400041c0211501480c0007001c0e01c800d042e051050700d128188070010070041c0c060913481c20b4170340420040c01c0d03000701d0302c11100780c3d00c100c00380380d903244044202d046004404002410440c0c02c050304054410b01d4194843c0c1000302600003e814004e50780c022500424001e01968980d060908010a4849000405a02181c1c80310341c140e0200300144143c490030b032050140340410305036010400c8203580c001c084000c10003458a5079140941e07400d004900000001040403992040949000380c00130f1810b5000c0002c015008654402584002c03489090895 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 676512598 1250 676511348 676511369
    0x1812090112020a0921111c0b01060c0b010509011206151802070606170d0e0a0e0f09010b0613050d0807080a08090f01020711120f03042706050a06080c251a0103030207 73
    0x4800c50751f80d10003c505160050503a40390b100c000218503030000d075080c1c03105028a035441c140ea138942003880040b81c020302c1034280d40401c0e44001008105554040e49843c5000804130640c0c0c0c0d0b45040501011440c40380d6449007503030000d0007004000c880d2250100800540800d5000c1d03503900021103441d0001c14000009011890a220803103565110710840689a484030707014990800034000b0b511028100d4040150b5881c2c000c6c043e603070340303080020b80d61060340b10009601218201800c0c00003248800604030307501c2c00301303000c5070002916a41c05409a59401e69983c25140303001d0030310914284030039160541c0e0364030411045000c542d0781d5940003203050080d9040c40300606420242443c00310011001d040d1401301140c046819080f00301ca103203200c00c01945600c4034048440c12481121524403607107134040840b13007082251b10300403010503070b01082004055007410a01c59022030b840c4202c2104401c7c800381c0c207106800300900d61b40c030b03146840c8107074420042541c150b55001e543c40710180205803211 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 676513848 1250 676512598 676512619
    0x1050108061c17030412090f061407050f060f07030e0a060902030f060a06050102070503240402060f0c010902090a0c0c1b03020a0e0402091812090112020a092111 71
    0x140c2e051450342c2d1015403024204441c6200307465140c201c2c0c1c00a03201140c0050701c0c28140385041d48500c0b8100207403603664242000a40c90580c0540c3e84002540b00c207040404140b00e48c5c00418014071400c00700042d030601402d080d10b04007503444480d0400922400c140b5103817095106070400300242d458200c07640080000b8441c041e60001900e0542000101c000e9403040408100303c2c03503120b400810072243e0070380885501075169420507442c0d642c8440160440c0300001c0006801d40d9145c24825009400600fa0924000b015045a84d96500035160140340345e461707440480c214141030150980c0004070703000400c90b0483d138050003012407003540406480400011030b080c01c8000080040401941d000341030600059403060120300c00c1408990a0748510602c00024000c0100844203510107140358000c0c00507603078a032034520100d03042095a45e040158000d01d40890100d40c0c0300401c0c00105584405007800c0c900071340b071580c1d910060903044002e004101e0500000360300712140c420210003100c485040707 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 676515098 1250 676513848 676513879
    0x51012090201031413061a090f07050903070f050901121a040212012d020903120d0603060f090507051509011d1c140a0f0204021804021306090503060105010806 70
    0x140400491204402c070104e000e2102c3c1e02d001a130081d0400c2d105e404280100b001036100c00d600c0c845d02160041e0441c1c0c600c40042d142c4181c100f6065072200860900a017002d0604010034076044503074000001250b423180c030900a41ca0142c0c03031580185410400c1c401e0641180d55201c000e404111f0315101d01601903004031b030071562100f004600d0020030078001c0003441024200446a005d44c50301c6460074000d0070164070300701170080c0201e03060300c8070180080465400c0310b0b03862861944100c02c2c0400642d07442c107010000607030a000e81e80301c17600c05140208604038142007a034244015a030140c3e100d000f25a130007400c40c05004054030010702003420440700b58001c0110800124060b4007820b030f801000d501c26210049c440e0700703a5101450040140b52100c500b003001e0141e49010400c00500306004101284c001480c0c0340c1c000f00000d080034103400a0180c01d56001c1407c0c0c2c0c20403c40b0080013070100c2c3c3c01348002a400341c100130052604030300410181d490240080c1c4040d1014205a001d0048440000703030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 676516348 1250 676515098 676515101
    0x1c053c19080a1116030c0b030f06090702151618030c170111040e01030b010e010e0112030c060c020d1107153902090601020102120a02090111070b03090705101209020103 74
    0x301c0a11004e480010161201481060800340411036003800200c8010414140b02c5013070341c2c40f50724080c0e0b080700c0545580d0208822504010009003c40c46401c085009484030200d00902408502c109100f14107146000685644175086030008200340c02601003000c070707c450310a00704551042c100054014141c1000b10b014284010140250650006001441d080900b0200c1d04890182040b4030309642c07192810800d1000c284610701c40040081c0051040c0382810001c2c200c400e01c6070402c16010000f40c0c1d074603c15110006410390158000402d00007040b50010340e0004da035035001f409080c210303041443d020f0180c8065501681001422402d03038208418042c0c0c000c1040c1c800e081e0b454000018018006801d40100000700e015003010320120701d06500500a94020322150302d01c010840ea03d0001c40c00080d00b14020f4981041805000c5245908040c8001e4000d49114041c1c1c0759203184c50319a05161440541c03080f030103813200305501c8104a60054180912034000c03a0041500d03852400103e0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 676517598 1250 676516348 676516367
    0x100e07030c03050d0305010f080c01030f020c011503061d0a140307150605010215040b040b0c0904020d0209030f0c010f080a1119030e0c1c053c19080a 66
    0x24001e00100c44003006200c1c0c00500032110300640e65007032120b07a8a551a52308161141d210b80c0b00302d644402508480e648c00780d0014a40d030720101e20b005080c408500141130070340303051455958184c010b2180510500180c0d0192001c14034811004280400403034441a0b500c0c10302c8100500004d10f80e00200d41109030510440f005a40c01040a01e5419842d42c42500100300300c5c401c160141c4190f4400940d0703a01e01d2100c6074410780e00070718a04002e54a039100d505100c00020714188204a08100c0140241d0f9075101030f02081d0b009180c0140c66195041c18146000003001004015a01c400741d0b07040c00d6030344009100c4020126180004031920381e0103802c0c0160010002e01182e043d000301d0030341c0c0c502c03000361800d100a44145d6001d001402280305110340b9841d0050005402000c1202c05e180c0003020501d017205103600c15021161070030503901c8401555011061202c940310359203034400e241819504500708902008101810780d600c52940520800b0310240340007440c2d10000709990b0060780c024901130 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 676518848 1250 676517598 676517603
    0x6190303032a08180111120a0b0a0b0d0b0625050a021e01020d1815141612020c01080a0b0f0d03031506030506131e0905060a0c05030702100e0703 64
    0x1160450030401001e06440e00490b2004078605103a11300a104a20500a07100d040d400021000e24000010312050410038004044861b42c9899000014103070710b4010b01e100c000c4c5002c50340140c544a8a01c802401da60301050b01c18803480061203e0484a008400040302d0110300b8a45054020402c0c90400c2c05e2480c0560081e60100d101d84c00d41c000500c0401680030b0b0030209070b00340c81103152140c10030740b61400102005903540c81c60007000d101140782e1504240c418622420503808140038079040000990001a81c500d070f0288409460b010010f024000344541141800074002c0566a240003d015400041034169440d40b18043c018458482141c0d02d003803840c01905c8012100b1250802030040d080e18864028901c2c802c0d400001c8582c840d100d020b0003204000c14403000d41800c0761b00000038182e006440125a245121202e8290070144212100d6903c61400740c07800e0318040002c642102d544080383c0b03003441010401c1001242e404550080b502074036440000c2c0000740c00448a00e0b00c81183c100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 676520098 1250 676518848 676518911
    0x1180305030a0305060f0d050a29011401020c0a0e0f1810051f0608060d0c0803041517041a04050f0109050f0615011d13060612050619030303 62
    0x80c0c102a68980c2040c1d105805c160744060707444000c00140a181c0c0343d00e0b20b014159400c21604040016403d40c0c140184a910015403800c4054495007003400140a80c8568101851040701481c556014401c074180940c0446811030601c2ca0310803040c11081000304100346400075880060040c4003044c1c0703490070148050040314440c1209401c1600186000e80d4900c02143d0580740301c4c12600701942003c400e88082da50b400d070039034840f035007441550a49420201e40c0240400408510b1400c10405400100009480742e0801d00001c1c1001d850400a126898503a1030114104400b0425a42c403c42840a003ca1030311080da4550074003e040440300d914090b01d035400c2c4412002840340008140d000f034100324050300d402c3e0b11907030174036020002c03505140390100d6030310000c070111494061103034441450003a040c00d210105180c804412504650000804142c0c40280840c6a0507140324041d03202c842520303100f6030080700c085640314500403817200400300b54680844800c80a410940c5402c0319a01d80f0340b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 676521348 1250 676520098 676520107
    0x1104060804083f06010e0402030a06030f08040306110f031503121b010509010513031206050d0c0936050309040510032913050c0a090b031e07050118030503 68
    0x24604403d0f1240700c41d01c4003241c0c0d0010401d00c1d00c400700031102e02444058403801840800a010321019420003045400d40310780c4c0da1400000709000d5040e601e480351185c01c0c1e8a990740d0640ca0f2400031211810640c03408601c003805100c003080722000407070f030300542c006551148080d40301c40001d02e07041100422490b0390341c0c0481c8003030846018900309121510418000c1c0455550b05400c2401c9401c100c85100160811042107808280102e11503590352022820100f12745490302c001c00d103202d004000460b6a100014410800181c0342e1040f00407a24130406218600d8131408602c0c0f4500012902c01111790003010000020042c0420440f2403134100540f0902952030844201e000e084401e203c1990311513074402d14464440c07000551141440c9120900303184a0b100c0e01300751800c19030718050443c0c691069041c501015034641c107084d401000314000c041040c0344040245820602c040300e240c00c40b081f205c640c2140711140801c0f0340c002c1c0d40080c40c103102202c0001c04400e1a4692661000d4541c2c0400603 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 676522598 1250 676521348 676521397
    0x150301021b031818010905090708010908120105030c010806130e01090c031a040b01090902061204051e0a0b1801090804080a030f0507020303030a0f0b06040f080d03110406080408 78
    0x9401840d451141c5210b09a40d0700082c4070710003440c000040e84d29041080180101d03401540001d410400c580103d0384029110b4150600b1030b4195942502c280382d01090890481000c500c00c3e502520054003d0b2500070140400645102c1001d403120f0310810b0b142c052426035000350b03031014081c4404c10000340250761850904103002000381c00181c80c801200b4072880e0403980300301c92030740c0216800322048140303a1a15030070600901e42540e00b240d10881c10454040301500d004480380c095401000a481c98004981c030307950b00298207091202560f00450b1414001c2100e441036642c0c00111001d928036440d101c0115240101842c100040c42d68030f001c1400719010340000f410451342446038403011000c0985d107009503a0782c012100000e5140d0309c204005002d4002c01c0d008124a0480ca840110f41d10004000041003034100f60003c4817403002450003004400700400203020321082c035003030030844041501d03425401c910030303801414240410301c1d010504004010341281e660400b480e0010140e0880b00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 676523848 1250 676522598 676522603
    0xc0d080103060f0b06040b0f0d1113060305070f050d0e06040807120905150703020c090c0d11070b1f1a0301080d020d051e0705060103050102040501180608150301021b 73
    0x81c002994264589062003510340744900c01d04030011340c0148061b044c1850040c40500550003071184001088040c03001100f41e07040c1c1c0c011908d00c21402000c403601d8180e0074000c62840d9907503501410801d4100000d001da00d42d005a10700c04060024a442076075501070010840c054004024039010f180b00b140200b000340443c0701b000c0e010244c4148400000a00b040c2c130f04803078500e864041c8580c012103008540721180000001481110310a006450841e8080000a40d94140c201c503016118800051401c2020080f80300d004440145030b5900ba0a110b142d03184c20141c0b910042c8000940201ca552207c1c1c00000700c00444001c1c18040240b50341c06c4a0541031005513007084c440d40e0039610403030001a150754000f203034500081005079509414810074003880304980b0301c1c03804040580042003007480302185003406000d000e5400340b0300242c0d4840c50a00014a03041d00d031102020803d242c1001070007007075402034605801250110000d51f404800c1da000030700911444481040b400d00c58126030302001400f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 676525098 1250 676523848 676523851
    0x1e0604080c1f02030a120e0a030908010b0d0f060507020a0f110f0d02093c040c0f03051903030209120d091e150c02030d0207050a05040605031b060c0d08 67
    0x2d844401e02030151100021000032095006009608103009840b0751900c905a21629520001000716a540542052a060450404040d030004103041d10031702241809029000c005038041e0b8a01900750b26a469408840c1041d40c0d0050030703070340c8441c0810304039482001200b0001c1c1d00846401140108d51070300011000f1a00000b074000c540c044000c0e100307403034042d03001b4000d280c000d0405000780d640d0034022004051440200c10018020f40c40e09200d4500b50b0b00e145901d5642d07607851441030309043c01c002d500c004203a1b1103020120105034040c0000354000c11040503050201c4900ea40c00d5034585804c1d0041d00502003495040b805804006060010000d01014116080e88890440c41e40340d07503007040401e41d4440910f003500346040081003c228001d441521203c000c0c604120580b40542c00a0304145008013510010f0f0b00c44039080c0040d25140c13a01c00020b25048030100201490940820703103c4415034043e0011541c0c0c110b10b18920f4842c50122070001e160403007501c8030085e0f407204c00b4006500 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 676526348 1250 676525098 676525123
    0x70c0f0b090906040207150906060f03030810050a0501020307080c0102070b09030a0807020f2817040905074e0e010e03092b0804270b0f1e060408 64
    0x30b0b85011480341d0038a44200d68556400240385408805050740c451b001d04100c0c04200c0f000c941d14080040c040c00702000f090f0245202e03aa4441242c103242450002010391500001c0c424403404404011030ba03000070480396520703800710900b074980d4a5090000d0080c0503010016000010f107604101c00380d00d000c40105030710f0038540c5035040c9544680708200c0c0d0300d415401144400c1e41c842d011940c0851440d0100c0038203200841203c1d24524407980c1d84081c0c0d41c06668485140c200b01140c18090202d490246175480036041c50144a1800c52111882e002480e454220001507a180c1c0d445400c030888002e5040c170900c1800d808030f01a17070440490001005c1d500c0c2460410b500c3c1c006000d0300624040100c0c0e80f40c3c48000c10304d00e140f1481082c02c90000c4406410f90f030252846160401c00140901c1c0680000d01098100820445086140a08230b2003445000408a441c0402c19403995a03503001c4038580030800e44100000d250707411050001d2000303c400c1150300110100e80002d0081c0300289242d0004c4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 676527598 1250 676526348 676526359
    0xc0102040f06120b150c01020c0a06050403021e0312061207030b150909070317120703061511060106030522060209040e060f060402130302041805210906070c0f0b09 72
    0x44030303c503d40445034100000c03a840b00c1141c01a68000181001900d014092800014501b03d4a409107030702c0c22020007001c644150b10740c4100300505406000e14465485a010321842d040b424201c503c0e1648100400c00f00041403103404102d050711040c4503079654904480448083d540c484c10601c500d802c1c102c0e2441d403041c1d81440f00c48500e0800c3c04806000d00d400c0401050750780d0a6039205a1001d1180d98180c1c659103041c4000d0102c2429800818000c4125840000f1294200050030151b00400507100c81070140041582038a00301c0010704174111a900c0c50001103544668098002900d10000d508440d010b85042d1174083c04070682c020b14074038000315020481e111540e488a07445450071503001e11882c90610004505041640080c445d03203610684254007035440351700190455101208069812004440070700400408100800040101c0c1c1d1203c02c41c0c110b18440941107100d000c40e00d84c002c0b00d012440c07000304181d82d00c85002410a400030100242e44a42008105400005080e031081 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 676528848 1250 676527598 676527617
    0x3041a09070501050405091f1212030507050d0914030703020f07170a03050306010e0a0b031b1611041b02100c0c030507030e0a08340f120303020c0102040f06 69
    0x1010300051810403140180c4a040c20f081c540300400054960080c020a450300105480c500b0b40c0e0b1441d102c030000761080c0415800c000d151030070003411070103128240009041c5880240607400e5002010b46400481001002c120741a4501d403900f81a031400b00260390510001c01c5d00420540c002c00c1d4000894558400c0764015641c0b800d61015003620f0041c010201d411002c007920200380f1880c000c5a021606061201c001c481c5000410489405580702c520306580c00700031710641c02d4030b06081c2040c00101d0030403682030440c00b484542074903e58900c020076840c0210740c1c00d0441c0d00c86402002000c500c01018105501846102a4580ca4500c3c2801c488914201c0301c03004c1e003405403200e0001140c16070b44850a10f00c0507901503c038801c0c1c408210b948a286040c1c0095200800c101000e40b21003070040d24000c120041c040403942c1120f000d042c4462035070544040c0040c0c90a00e4403601140d001d501040c0d8600001d04090f0024401c20000241550001401040308802c801584003241c00030303a40c55140 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 676530098 1250 676528848 676528861
    0x702010c150204210b1b04031b08010c0c08091201090c06020a1209080c2b0804050a1a0a0818160f060e0130050a14071407020904110603041a 62
    0x3280760801008094241c09001b181601c10760204200d0501d44180f840d516280e125115441c00e9213500c01d03c0040850300c44401e03c404602030040003000541410b00e01e042d060749585112190040a07100c60090700300c6240e51103841425041a820719400030182c10000da110007009483e070719840400d0743c049000c04008281207100d0007103901250054400341c94020400020805855104c04070010019048054100c800c0e40444c1800c902d903100340f4440da40c48d86002c1c02d10084581a602c010448000c3c11038021101e149902200c01109242c07400b51000d590340242d44054104071800d414891188400103421802c00500c41c00903100310100398054159140022100c3c50546131107140010000b001e081141070118004c21012058035004d009001000d41c40d003c01c4a804407641b029060705c82040381020002a4640b0707401465515100074480c01807601c42001307102c0e844c8000e02845201c0000303801d12200900030f002c0d4410090a60741e50307003007038201110705880b000000900300c0f0710080494030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 676531348 1250 676530098 676530149
    0x706140108010c08100311061902010c03150503070b091c0c0801050a09030c02090403032706180f1b05041406030610060e060309010f0c0c050105090a08030105060702010c150204 78
    0x220340130b5520a8285d003415940c039520790368581c44040d500500c06020140008401c11071007180342c080781c0d00004121401a800500382c3c0d40c2c0c001881c80101c1d081c08140110b0300d000ca041010b44040102c403d07591803d0002295200009140200040c0c00c2410b1240c2001603145041d01150403c1c0001c1c0a41e44800f000c40d011100c55440c001c3c0410a2284200d00606003906c060b541325010b0304000a902c0d05d81441a9450268581d40c4a403c147c400b454104200c141c3c45420302c1544814952401c640d450354903d00c0300c003c0f0840c050038940180325201c0084509004500280c0b902910600c80e0054401e6143c15031401507900d941309018030070001e41c200342100ca0160841d0321558910030007040386800d01c041a4406098203442c0e54840705601c3c02103a06015411140c802c035a0340010840181c100542102d501605c146100c2d04400380307030004141002d00b41c030705440e42125600e584010510060302e0001d00200d00801420050150640d412540d502030403c4410500456030300d01c40301e014a02c07 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 676532598 1250 676531348 676531351
    0x190f090b03040f15020307030c14040308120c07050715030e0c1f020a12050703080109140c0c010e01060e0a0c0516110a24030f02030601020c13020706140108010c08 72
    0x201000c030900004002c41c1c42158021142801510b041e10070102d1103500b001603034001c0f100e10011070f445920801c4256032180c5818511707000e240c0c065080070306568900200e8801c400c144030400000c0008107031454907144c00c89106943c000200c0740041c0e6200c602c94101300404600d08040b85c40c010789820f0000300418448807090004003461502c4103040c0909581040c03140f00c0c1c404600c11035642c03000041c5044040c461800c201d491b80d139241c41203490700614003401600161349084c00e00007012400f0030300760101c070b40104486000d030343c841701c155002600411200c48134418070340c00c1041c0060401c0c01c5407a4140907285491341442180c81f1100141c0e61445142d605102d5441c882403180c0108101f44582c10130800d000345100300c000d50b5804603407240301c00816643e0381c0000441344614802e82500c01c0b4108408407074803d50952920030000b0303444100101c1070a018102d04141e6224400380c99040319543c0368002c8080000803682c00d480311010109004401007503191813404080c407801745d00000e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 676533848 1250 676532598 676532609
    0x2124050619031d0102131a0a08040b04030c150603110f060906030402150408030306030c1206190f150f0f031e020609100c0c0e010b0a1d06190f09 64
    0x11110a180c044101d00a0180307003c008102d07501105070901142081c0010240d080824002a01c0581050200522480a00804100ba503001c002020071240c00000301075202d90010300600c120f50369400c00f51949011010002c080d0080300710701400041142e40032006681c01040081140c00c904818011b5142090f600a94080303414420030206280540c0110f5111784054200700d2075032804400d49541e504950003400840d0030220820100d42400c0210070000d803411510601384511a034913060b2104009000314806400842c148440a00d0b240c2000341040d20000040000b41d10790001815074041c1c81c003071001c0c14142c0c0071000440400d001d01c1641540c2d04034035100031442404005214804680c001240c01c1601805079520541d43d40450000c009503e4940381d0044605151000e0b0b2040301c0d40201414107901401400010f40f0101956034074001403c1001c54803000610300991003070310326806039000703000045286071450802a40ca1185201c0c0d01c881465000c1400150740254140c000e4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 676535098 1250 676533848 676533877
    0x11100c030216180e0c03030c150906190506040605090c0903070f08030a0c03030621020f01020d120b0a080d0309030813020f06070317010b0301150507050a0321240506 73
    0x18036004101a0b40030704105100e00f011282c08210742008281103800c1b1643d0148c1d01c0d0032001803c1d00001c581c2c0052640143d044010f48814036002c4104034104d03120400080c015070380d4400080c000e0b1501e03030003c4003821004142d00000e141c9201c0c40303900c0d944100c40c168042d00448900003102402605200151914140954100f429802086881e00c084031400d40400d5100d280014400075850345400e000300452003036a02074a424018003400541d000390250440d801581c290407641e07032050b46104c0c02d035100703540400e885800c100098110030f40c9400280d55030180100d40189190954084c446a5202c0e07101d40ca055503036003213490740c001501440690080c41c201c0c00c11100d80340c42002400180d101c0d041402404400081d40070078640c00b44c006e80f0300c2500010052000200908285519032014030389589803400035500e258a4010001d0700405000100400c000581e12448890029645552081245040c240c0182e000240340c650803481e40a10081c006c200e60510304200c42c00e1034045400b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 676536348 1250 676535098 676535129
    0x501020c0c0d0c0302060c150702010b120d020a0809040e060f04110a0e010e0703020c03070507080705030703080f030702010603080c1506121e160905011a0310090911100c030216 78
    0x7840714644c84240102024001d0301221511500c101030305a0091859032b0000440010403c14081e4030030304401c820a090340140c2c858510b25038001007189001d503200349040d44494040f0302150150103010030403a0702c0c0c080c450801184440705820244980d0192100e0703045401110240509003103e07000364404540104010712021090700212a046142d030b1400510348174000c04818156003080e00d0440d2180c05c0514100800a41080150081e20b4118042d04031585150b5828001b84251101420440808030010700703924001c0d4400c000464200c4401990ba00d8108111a19201042c28445d09071802c07402003121810701080010101c861071004202d00d00030021104c13a141000c42c0c054810f407042c4801e15041003452044000180302100c40400e00e54144820210071415015408044110910801c54000b400c1646101180d402410000300d880d650b09007180e898200c0880150002401c02030044059070000c0b0398601c0e903029a081d00c150f05c4454260341c1404480381304918aa208400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 676537598 1250 676536348 676536353
    0x9180f040b46060f1a04030203070605030f090d1b0f0c1d0610020a03050c03040b1620010914030304030605070807020d0320250501020c0c0d0c03 64
    0x300258000404603074a68150714650034401400c5444264465100d0050281d50042c01551140365240c00841c201440442d0924460107000c0032240f01d004010300901008400031a244c0d800c85000d190003901b61028107480344405030295100b96414811620540f000850b0220085110740807030107241e0743c800142080c40c94000618000d02d03016208484550310140008102682c00790040450440300081359009840001038100000c080d00d002d4003248074651a01135010619402c2c00d50706041c107a4460600c98855465806290409144500e000504040c00308400c0d00d081c040034402c440d1b40300014800030034103205588601039240071403440c05050004405a140d01a261170028081340d051a540782c6440096410980704800412800401e00031a143d05101d28070b05240c0900b4140101c81805140032490559009030003824040415152426501150720345a001c03403054504d540786401e810620b000358490700b0010020b00c2000c05d401e40c9428030752a861505500000003004452858 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 676538848 1250 676537598 676537613
    0x30402010c020f040509011d0c03030909370606020a0b01051201021204150e03041212030b060c0d020d1403040b04080f0a11070b19031a030a03030209180f04 69
    0x26000b02c1c0d000046183c0264152240e115045c0710743e681000105903a240302000a10340601002042056005009820413540340081165503076002a1102c0000366582c5261600a61401d00d142c0185102c030581c100c83c8010350309509410110788082000035036079a00050381c0d9544040401012004868010422486d10f108030240f12200700002600d80a01c940261641d0641110b040f03d5513503d01c9090103c5c03016510400c3e12411002c0002e45c98241807620340b400046c0c80c0080148000045241c2d042480d02c00d0300040d020701c0c00504215180c501e00c05141ea00d030302ca40d40e0080014030400354040b2205100e54040710160040f42000b030b1958031b440d03c4054004000030300030b031041310080100e104494501801490b03900b065543e0050039400000d0401d09040e01540640340080c4103021082442406040a01b0300c548030742400504011105800201d601c4500c0c0815418028a200c03403050607010307001825208011150310350095401110400500004c1e0f407070042000703a000c00500003c860 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 676540098 1250 676538848 676538867
    0x533040f02010e1003060e070c050a120c0b091015051539010b031f090201140328020705190804030f08090f18060105071719120c0503040201 62
    0x40c0f4040d58141c40940100b01101c07180102e00001a58500c02003017a001100c0410390450f200d1314080c681d010342c0e600c03407907580c20440d100031344050003441100d1025030103900d0300f0b49181c3d8040d009207000c0c0b42440e641900c660801c100d19103501e0130150340c1440303140c0c1480441c080c2d8800a19241c0401800f04034901940c01541101082c0107400c60309140110115514005025079890a420a40038040c010b03800c2d40c11880040d802540140f40c03c0801401c442c0d200c4c007604101e030700d000411140ca400104c3d080511038505503000e060000620408009020006d040d4680c80005161001d1120700d11201f2846aa4400352040d00900512180301082102d1100300394001c1800d0b80c10107442e40c03620319525800b004201c0b40c2c4070f00050a0145805c1c844032107101c40400301c418401c03414078a5408090070300d000740500c0c108500046c4200c2000002841d4032a21406200d07080d8440e40c091000c02c10081c0c4c058404000328a0712103d040c0d030f04415014002c5041c1b00c0340d5819013540c541d6401510741050 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 676541348 1250 676540098 676540103
    0x706030c0207080610031a071b081c0e12130e091f02030a06060c0c06030b010513080607021c021209040f02030901050106090510050304110109120533040f 68
    0x15001e000a005482006198003c0101d42d0849a1062662030709140c142c00c1c003020031f0016182c0104000b81641c00001d46401c00c441100400380f910315614007051607105040700100943c0e4040140103002e07180f0b5001243c0680404201c581d141d0042d04400224010341c50022040403003494107100b40390240410503000714408044408030f80a0021000b0804540041100015800f00400203403462500510b0000c062070308125100c03c87d03d481d4110080c070540103c0c0281500c411401c1201e92082081f1510301600000540c0c41586413904a0b80350f104c250b82040040c0b2440001001040701000110300b101040d40080c912000340050343c2c0c0041d000b9001d6168819603601c04031111580301e000039845898000000100c0390705040c1d02605442d2180c00960040c0e85c50700451400c56009402c0300d4000350131240801c40450400c00488550b4103680084814101c51958001003180c002a81e54002c0b640c4c0302c098010f00790741c0d0306800c1c90280b825000d4002d14190780c08a0701040c95103032701404507030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 676542598 1250 676541348 676541353
    0x120a020c0f0304030503070308070c0203100b0112110c0c01171612020714070902040803040302040510050301110703020d020312010608180f0c01030b0301020a02031e1603050a0f08090706030c02 85
    0x40d00c1d8000d0943e04954010355280c1c000248040400d035200600d0303503002c64141014501e0b4900c0e40c020036500c01982d170f081154190344240d12000d0768000c900305401d40c03d40d44001d02500441403551070468014075841d000611901d0b14081ca558081d01d011418207180ca454441c840e500c0e1003d9411016442200005025240d030000c01c0e00241c030700042c00302c00d02820044013032040c00c0d20158079110160b03020b0008988180700600400001000716170840f07404580100e0951a0840c0a0000c06a1a4001a0715600e044044203241d00c010700501185d0b0b0080e001d8841040d0921410390f200e1003800c4081d44090250001131050f6809a4080c0d0b801c44000c603420b08044428507429440c00c0c01250040c0e20951241d28126138969240c01100010b4105600079428003841040180d62401500b61130702c4086403c08050400c0e00005040d200000030300802e8418004050070080c203240d01403a0340000260549600c400308501500d4214041e6030300800410381140707020002c4000340307800d5200d5000c50 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 676543848 1250 676542598 676542613
    0x901120b0f1b0307050403031b0213110f07050c09070e0d060c050c0d030b03100204030c150c050304090c0314040507180e0715090e161211030403090911120a020c 71
    0x26110360019504c14005600c496940b9421820080d1044001040c80c107503510301000c20500688035178051400d00c082c0e41901251071210140c84c058540601e82c20852800300228080052040c0001c003240180c00c151800c1540d40c443c41d03000c483d652040601543c1101074100700400003202a4015200100b15161080c18064084681030600c600c00045000298541441150900c1c081c0803039811580d00e16411450b252030769032a070b21110020b10611b001c105010310080c09481c01100d904509590200580750b445032110104001052000b2803900001d00d4941e00000d40c945c580380c26402180c0080051102900d00140c17241c01140c08a0390b15603c0345c44810000c826042045014080c00b4100010184c0903010701c0020900025036021a032000460070a00207038a05550300342c0001c240c9450500070140402c020240a0b1428059000388404000104000c0c5507004510038141d840442060190350401480900d5600400b520764a9480c031801c00f06050001c60b81c020303c2c046040d00e082d901107 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 676545098 1250 676543848 676543891
    0x10804031b080723010c05070c0512070e01060207150f0e15160f1e0b01031221020310150905121e0d020f0d0806042a0203090901120b0f 60
    0x11380e10070541e0b003408800840d100f40f804082c2070050001c2c010f028030b0072604210b4992940c1100f08910300c90180910280d00d02c1c40750071402031180a0280152042d420403550f52030100030750303841041c481c2c0c8034400310182ca007000c00d070b105041c0c0030b0090074a03940301c1181d145244104205450b46400e848400e0707804010900c1e11034907a0034002d074501c0c0920f8510501c80000d00302040e400303520700ca072070945030301c01b0850b480054600c94049056a4000c6140d4100c4028410140c0301004801249010b14006009140c6410280d400862042a07060143c1c50300d550744080c01e14001c0102240c01c00410740f811070620442c11b109810703540003800b420855004231803561300c0000c55201003003503401380d8002804401d900b540422030704003005400c1c0001d0046c5201c500005005507005081c0328421926030144460522088991541d1b40d1014a022559226000ca01035a02d0340040c54040c0620601c800000701050303200384500110303810100401017552100102140c62000401940421208007101c820 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 676546348 1250 676545098 676545113
    0xa0c0606231507030c0f02180103020f0102060c0301050d061407051308030418050603010f051510030b062a03070c1706091e070e190b010804031b0807 66
    0x80074607522040d0300c0103000030810349030040545694051082594140c100d0003141044a1085405181c0117091620030b2500d034070441619640a580f04200802c054145054000303603a040f80c0c400c070307040031405c0102c100591301d4490031286103421600c140010040b40c2030905d054032800d4400c550000780303500d000a1140f40b401c07058808100181c404500b403a40c0100c2c404529000d44182002141490315281e440c00c081d01320032055003400d0780c82c2c401081d440d49094205031040c6002c040d00f440302d85810160002400d80302000c5501c29401400c1100f2024000d04c50b0b219840400380601d4a82880081040700c0c0d0341640c1d00d080c01044040040f00100340c0705001030800715200c1c020240c4060310303111100100030800590316003290020b00500c5604440003031003c03c1d00401d140c00b10003022070242024100680d43d841040542e011500b00859508611074520080b00107400811420000c2c400459694000311030040103e45804041466080d079480359183c000d109490341890110240d444a0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 676547598 1250 676546348 676546361
    0x100504060f14010516060b15071406060f28030510020d140c0702010c02031204031505010e06030d081012050c0111010507140918180f120406050a0c06 66
    0x8030408201c40d091007a1201c80c1010304208109182ca00d007410030040c40030351814101d04004080d10394403000c01405840350100c440c80842c1c00d0240716101c8070b40d0b0400c90481102c01c0c0c8884102e00607a00003a83c203103002000d04155040103422002502d031a1780782701d103014804818002005030300500000c000b41c010412507079034bc010340c1405629000013007202e030290748034403c01d001041030b80b41c1008101368000e001d40ba4030f50303024a0004500c60a5001203401d03c2010582c22aa01e040001c01009114804118040e00d900e19102084680c0c2d0318090034000083c15500c45a05420203521030880038400c99500381c02440211040500e2690341018a4850981f0742c1c003180d81c0d030064200000650380048686104800160007448203281c4a03000800c4001c0000210300c4c1c1c0000410004429110741d50148542e40a18040c085142001c0c44200110849003a0061041c803c80030b030216a15004110f542021440441403802e05081c582c0994482d0001442c0304d0411490702a4140030400a01544 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 676548848 1250 676547598 676547609
    0x9050a0c08070b270d05010501090c1d030304050111010e0706200706080610030b040c050405190e07050c24100603051303030b18010f0501030c0c031710050406 70
    0x11000da514002109007810b15039880608024001c0c02508a00d0000640c064810204030600f03000a85403000024078120071140041e0080d8600800800c1c82102c60b8400e00c031204c032640b990140107108001d0040420394100682d50550820b210420055001d01c1080c1840d9601d1000842d80842e0042082e103094400ea100200051003a4000688091003443c00d400240d981c070050031066007400c1c1c0103060b06001421150048074940500700c0410701c2980000c00d01c4100500c20300040e140c115006080f604940075191041201c81c00f11025040343c8007103402210390b10405004203903190030003a60360b41c00a0071118483d010f1502c042d04149820346001d0b0b0044600c02d40100c090604190804c5882c405400c0041450314040600c59811006000f035281103505290105d1002c60b80d00100f01584140d181c1c0c0b4201a411000208a810410340c02d80161002a41c0421982804c01d408441c421800d203806000315900b00042840d0445d0042440da2040c810113896018650b030704041401ca44540e40302c0b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 676550098 1250 676548848 676548863
    0x40309030b040c06110d02071e081914030a0c0b0c0c0f0615030d080a09060608030408010603121b0f050f031206030f150a0203060d02060403050a06050606191209050a 73
    0x20300540740c20451710044030089030020f151700800964040e507101814058840c4e010711041d842a007004003002d28102501d00c04042d2181c1ca9514515010300700900b0000310340c41c504c44040c4403000e640000942c1c0708001d0560301c200d102e044e551515041040e001c0c00c03070492040e08110b040e003c0e2408010b03214041c0704034070060a592501d4505400c01810800c1150300c00e402029605a1003680800d0198004a440d02c0004140b035061400c84000d1415070f11161041c0800b08000810010660000c0704481c020454825890740f0000c2c200c2d440011210f00c11808500c007130010000c68071001c1c41e0312200b4464800c4420800c8103100b00c0d455a00702c1000321050b42c00003001c011150074144031690102c4940c4000700301900880307801e5031315180700502d14610b0540c04000074040b541c40d172020071800fa0700a49140da4a544a041c81c1e80c60f2801c119041d9000341c280000300b140e50401204446188000002480c42d050300200202d45c040000f1781568401038644140c880814404d120807180303e03115415 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 676551348 1250 676550098 676550123
    0x907120305180301050106020709020f0910050a02010f0c1d030708070915050301111207030b0603070504212a090e01020a0206010b0f12190507050901090b07021305040309030b04 78
    0x600b485580d58190015000b42d061100400c50f00703800103038001c156001c5000260f15028006540d00c0180510303020250b000d01f0f40603628030b416411200a04a00000f580240b050181d44130100c000d4032002050000010900c40191102c0a40030b80c0303000b4208801011789040c6ea0b519248107290a24903042201c90359603600e12170284900d01c1110030f00410b8281c0c0240160b04a001240400e03004041d802071074000c0c40740000c1c180601c031303910104a1450003404030783c407070519000090040d04240a480c85691010b11985031000c0407109004003d58009a500d90105002d515015540021888121004400309001c1034508031400b0700d0048800d0031000680721518484024a80394040e0b02c50310200350100f00002240c403101e0120740741ea100071182e401d056229000502842c0089107800031200e0718001c280221940e2080042c0aa40000d981d1040a00d40300d1400022a102e1950000e41c41410302800410040150700920391250203800e0081d450b69603500c0d980c121107800c4070200c038001e0a010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 676552598 1250 676551348 676551367
    0xd020c041401050603040803061503041a1e0c0c011514190f0302060702180411010206010b0427020c120a1d0d0b0a0e0109030206191b080907120305 65
    0x1c100072003a951108055a29450040401c00520010380b025040346400000500d01340c0f03d40c0d280398000403541140030365914107800c10340115030b4100220503240000d400824083c80c1d81c0c0141c0b000d402001c40c3e03080410b8640094100d4150300c8090514015520784031b0103047c0c100204100c0c0d00130a8070524001d41d80c2d554104000e040e1851881000410459000602a40d02c1048200d010340381c4c141d038415038078441400082c2c08002e841c10465050341e8280200310400c0b0f072019020701c04000a03001c4588607601c0b94143d00041c0281e000303060603840c160340c22111081245840103002c501050f00185844c406101086c1441d113003c0846400b0040000c1100c0c009034066503043d0700a842c009001d02054100d170028510f1048103d025108042c40340210f4000145640140504da0b07040c00200950100b03482c000e501e802c1d0498079030a8690b01c0c120410b000c1a814050a8034001444460015901c1c0203003054a58210143c5032003035501c0342c00e101251810889104c101028000c0d1141270701c500d07198 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 676553848 1250 676552598 676552601
    0x31a19110c0d081909030c02040c1d010f0f180803040303080f010509060607020d17160308010e0405030307110c090a060e0603120315040b043b1c020109050d020c04 72
    0x103030700010801401808015000a02640348440100320b13010110741c65040c1c0c201240c10324042031019500c1803600402102c3c05030090107032035a50070b5954850148200c1e403001520a25807030141e010104181c2c030141210342e4031518506110310700d040c02140312191140c16080c51500b040e0402c03404110180180405104041840c600403c0203c4e1703c1c1015141060110f007840c010140024002d404001100c405c00a8108035a80110096030017642c0f00d01c00d152800b04060310302c20094010601c90700000c2005040c198200d4410b41e005402545141c96050040b51580b0303c0f50001c00c0756003d4004110600d64410405030b0240b80030a0001c5101410600514011070000d4610b41c4650300030342c0824103102e003050541ba070050401410540a4413104086009031000824060303000f40317800f544252000300070b00f9201100381080101801d4040c0c1c1c4014000c5000880e083e000c0c02c0d80300d01080185c42a0a901c019260b100d02d1001045405907590303190324014080c40010096005080701800b2030804d03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 676555098 1250 676553848 676553863
    0xc0603051909082b050a0614010e061e0d05040312060b090307090c09090f020705070611190609290a020a1403071404060203031f031a19110c 62
    0x42608220b6031409a41d503251501c644000075140d0940d2101d0500c004050031010404060f4449051080b490480480c100410903030144410f0b45504496001040d445101500e60600020701103d00e4680c9155150706d031440d50700040f0590b00c804004088038408a03009440c00b46100c0d40b1807075160421581c061007503031420341041a54003003e1128515568000540c101190285800041c8904212000f00c42c0b626540d08040b5906062901e19689040194002d0040e01e01400503600711a45440e0f0444075004e0444c907480e220740c404116010070180f500c4405070740602c500b200203041d00e03c40e0f499118101804440000741f08070b2050440c0c0c41104040714940c80080a4011480c0c0103901c00040c3c20307802200b03045c900c1c0701000b00004240c5e0b4055084c010700d202c070301101c5588450341e80000954030740c4100c0b00050810000780c4ca0622141303007032100c0029258020200002d40410065014000100905040c60700c0f12044400c480100c0f0f40c410710000410800d0001e03550710500310f405203400711 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 676556348 1250 676555098 676555141
    0x3050f071b060b0301060506040303050c0106210303050709030209041101032414030a0f0804080c06091c02150423030724020307170306031506011d0a030c060305 71
    0x4a07080820301000070044000c10041e8481000a01c1d01c8080c000f01c2e004001e641c11058101000041c04014960000041e245036584e510003441100e8880c0f40c1000a00c48081900d600300d03105104200010b402600481d44c030407260b1405a407190782d42d40020321a030300203a4054628420041c100100d82d41e050040102c0e102c081c40b1a081c0c814220480100107151910aa1050080203501122a541d05022900e40c2c44c8e005164643e1401d02400c00c00c0941d8000e114002d19481900030021907400c01d001922480c08000f0300155100ca920000380c5d0b9201d1545404a0b8000c0189100c803a050741c0e00750240014040c0380c5e00010303110143c6404480e4054207001c200c0e00c0ba030b01101040104100c040c10340c9254070101100188400121a400c2c2d1940c01081c00c010b0205220744594000c160000011b1442900120704861121241161028101a0513220140019a6004004c10140325007805210a010107450030b0100f0342c0e0b0b5254800102129001040060b89400c1480056040c100b081c412845 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 676557598 1250 676556348 676556357
    0x1b120c0c010615030f09022d060711090106020601080a0803070c02040c0216050a050f0622060e090c0324010203040b0304051b06181504031a040302101103040f1106070303050f07 78
    0x18000e0f000180800101d2010020710321100c581042a0405040801235045001d406c554844865162001400100a0710301c1d008001250000a503d4400240d0a040351308440141802d01c0c81c40c0c0301d91205501c0100805d040c400c410007014010b881d24400d1130380e0729006501508036003030f000c1050130081d000c6a1002c0e105680c205410b0080d5900c114101a8009080b00c60355540ea46120120b840702e162040e5260b080f9003144400250355410010300301070a0300840d1649103a955841d0501385902050b21008000d0003844d12212007000c00840801d8150f80500440b0308050343c0341e10044203540b048030203c8640d0051400b0042c1e80a031608140c80b50341046445a00b4090910300300d02015000303c0d8182e1080c0142c0003d00c1183c0c070070904881c05150003c1c0030360440c50a130414454080000d45d4100c005100d180b50702c10061506105106915180c1940b89103541c80d10740b1400c0701e0640311041960000344811600c54940e55520050034203500c251070218261802281c0303022003802c010070903000d10 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 676558848 1250 676557598 676557611
    0x30308011e0504090f020d0c050907050a0c021509030a050f0d03060303050f2b0e0f03130605092b0507060305040c0506031905090a05061b120c0c010615030f 69
    0x3407108450300058980550300000c800480c2d0074650000700b400c4102940150942801070144485881543e081c0d440a5031101015110050b040b40c0310301c07600c3c41c0310000400a00000d001450880c101c61403c80c42c1c5003049050070404000a07007012000d180840c1d16a002030082c0a00410612060b084004941410000c191840e02e014006215503480c1002c035502c0010000070f00700d5445032149840d4031080795026613020381011140104a140d01c5d1454510454221405560000086900c0c0d0001c140460840614141d415103041e0041c500c1203a00040041d5441003c081100300880117144903545000704052508010f8280800358001d04100342c1460200404121000d01c0b8100f1110240c03100f954a42d40c503210711003030042451280103c60b0804041c00b40301440080c2c0218414003440503900d081d141d007400035050070660100d212105005000c40c020382402030b054503a010201090040c80c1030344d080109800c4800c1900305400f100400f00440300807903854480c084003011022000c000ba03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 676560098 1250 676558848 676558889
    0x21b0603040b2a0403020103050a060506091201020c030c0703210813051e161d01030807051005010e0a0606080603120a11060406050109151401030911060d0603030801 73
    0x1148801000070b4440d08908010072220745940c5065161400030301e01403007509501e20300303540c0c4030790203448142d0000341024046403d141d11880303800304445004140c68a816403041c24054501000420030045560078421201010780c1031000300340200101300909030701400e601d00000da080352a2310300c5074101980810a080207401c00340319600050302055041402e2500e2078403c2c82c0ca0b0070100c1480c000c5100111064070210f00044000109410700c20303175138116886101070221000030100c00003200140400410200f0340200c000d1010034083c0d030560b18809100c0004c1d0054800a078445402c1070f800e4001c114a1845038071a010180c02945402ca10509200700085d41d141c1c0321040250b486040010661140f0703001d01d68001c0358103081010b44050746410300f4100c0041c40c00b44554010b0904000020b21a9029842da440503240503200c0c00488100c0080110001c280342c01d411036005045018500c0d040d6150b20103820020041c4001091540c2507207002404110184e10a800d04842a01c26205 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 676561348 1250 676560098 676560109
    0x70b130c0603090c031b0501120c14030a060b07050307020f31230108010b030109081c060b031311041a0105031b07050d081509011202130219021b 64
    0x1140c105180100d260600341c03c001c00704d402142e000070000c00c45010380552002c0030074154401c40f00309803110b50f516001255120b051307030120402180043ea071800800141740303502d009580c220701d41c080e001a499449400d2002d20341c6c009641951160300100e489001c601e00100710910641003a10111200c4115000005040340390622200c0c0c00c500130303184100f004003560b01050382102100e0201c20803c0304003184c0110100c01b03008003007180d401d0101d0808542014080d80d10030f10f512103e8141b03011100200807603c0e5008408404d00141c5070000007440d20a242c0146000f41c0d1410807402e04106180b60a40b0306000c4a203071a8029401c20800000301c0b20081040c41104100307080007030756540e071988004100ca00804c95401002030100e10780c014000002085411040313a51a25543e07030321000a0540e882c10541e6010f035010000e600144101902492502e03000752001d0043d206410800f0700100580c0c018248411441002c00c11100c504d590411842d0316078044000981040442c10000c0b60 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 676562598 1250 676561348 676561373
    0x70e10300302010e060115080109061d070504050a0303050307170f060f060d090308040212010213090b19061206060302041805070c0b0f0115020c0f01180506030c070b13 74
    0x4000e541550800d250007904000d6281605601391141c661312014888194003504075800c0008403042e0011840394070034844c190070350b20340703044506020b001985504503100340104a407040001c14000003039030b5180d003158807000c0c1d403080d15060f80307903d006038000b0040b007200090f410010000a0500039140742c0c54400d035800080607100e904030984070b0070215400d489000d026004640c5080c4041091540c03208038039010303500c02c0302c04030107814070f05421600303078003c001d10500106200d501c100701419840e0b00c4103880b03c0b0b0180003000e00500c101c02120030410194440004601180b4050740e51945902c02c940181040d1300341181486d05102060500340c505198640d0120350714400304080342c0c0a012081034066100c4400b001d00e00d0001c6030190303003680a210720189401088070311019280046140d085004c2c0c0500f03407a00c1390b02903500440d1400d03400310803003203481c824070340224071a180c00b4000c601c90001044000c1da6546c180c9450020303500b00601412100d2490072039500020305039012075 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 676563848 1250 676562598 676562669
    0x7030c18060516210215251e080916320603040602070201030609180b1f1d06060304020d14070b1b0606030f030d1d070e10 54
    0x703a48821002c04040e0700c012900102401120340d202015600c0040c0020742c2c045001250700f940d46181440f04203002191003550321f01d4030107055041007205041140c041071070f003040d02c1c40c064201c50030005500d4040340030680071600043d0312000300003020000700142c1c500310301e050501c10100d40c81c2c001034204003c1c00310704144500300c001c07034030040080e02c1c0b510700a02d5450081c040c550303134101440d04600950041e00100d010a061850005001e00c0038030445109906c1e03180c00440c140030036507403a0742d05500108001d00d4a518408495a160110004007006c0c0c160749050000684069201026071000185014890903041040100503107800c49520122503100541c0016522038035502401c0c8001c45e0428a62040301240d0820780c0842c81910548080c100000c0d44d065868100a150b103640b00404804c50541c01040345440c0b4a1444d44034098a2222104d0f40b151002a100a50b06020f240c0c0c0c0040503481e203090502030a0204001d250000344405859034003d40d0000101c00040126030032031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 676565098 1250 676563848 676563857
    0x15050a050d02130e040c090203100302060702040f0c02031215060703120905010f09060b010c0302030906070c080d03050907081609020730020d05030c16030908120307030c1806 77
    0x155114150181c850346403000030040040c031345650b61842441003c80701502d944080d40e10016a001880c400c6030300502c204a00d2003285d40c01d58091082c140c0c00b070602203800507581c81d140c1007031410910502d001148268040d41c2d54100c01c1e1000483c0c44405010041400c030740c506c03482215602c03081250840d03a4981480f0716603945c8044100000c00700284050555403c0c8001100001030aa1080450320710400d801c00c400d0088100442d025001044000c0c05a807040000100501d401805003900324442c0300070401d501c2c0c6502c8018180f4041c00c0d0702002080c0c450702031110b480414007810000e0f00700e400040800006103246150742400302d104003003819a001603d4001d10411621090343d213002c07686001902c03001400b0170462101c400091200500030104a00d0065102e001100d008220380140942442e41400c10741c901900b55803411010702c0104c20000a558506000c0c0702c04034000803500c0c82d101d190540014056a200785211010004805154802c0101d5140d20b50140c0780c0305d281 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 676566348 1250 676565098 676565107
    0x150e0705040e070302030a1b0801050f04090609290c0708031510090302010206010f0605030103020f030a0b0903040311060f030403080921040f290d110301080607080115050a05 77
    0x24195058070a0750050500400c0c2d036010410001c0c0c064009501600b2804d90400c24110002d180400c20003016115500107882140100178034507041e00c600c407007c0001040050169017560360300084460480f01190f207000303200c60600031003001250030000035101c03c02c0315000d071500c4502040f0704d125540c0000e214004c00b0000c10340308003c0c4bc80044d01c2403406046081410b420b2174010300303040003620003203005200d02d00001c1910540000c1c02c4089440170703191181564215420004c0c1091119855500742c4110172010300030808401c0e42e180214841406981d0f2a4110f0800c545859000320070280211420072489280000c410100d80d032250301460b0404e49038039140d04031401c050b1421003036001c141d0440e036490bc070101c544008100b19a140c182040090746d0710510319040030038001000d0421a208041455141d0052000700031003448400000b4203082701d02c51a42c0340303400a80200740c00d070b40203d0401160f07642103142c55001d007000202c81124250a00700003000340c400c803680502007102c00304 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 676567598 1250 676566348 676566361
    0x206070b0c070204061404052503020702031228030c1704050c13140a110405060a051c0606020d020c0603150a030b04050c130207021302070201261603150e 68
    0x250b864180d8010414000030303545840c4840d030602d5094035284501d02e0540454001040ca820a45d801c00c440343c00c00001c1c4000d0306080c0e0007500523130b00503601400740303003c140c83c16983c1c5802044000e01c060b1400304002460603d010303654206000307030b00c10305251000d0000000d8011000e815044107659031115560703128900036080ca80c510b00e80580042203031000818070a6180c004402001810313080c0300322a52081c2c0341c8025204041c145e548405070401c024043d03421701200510306040c02e41081403400e00380340140c5805004600600160540d50007040c0601603045c00401c002940301e20051422082404c0054240c2c4006440d8200302d0b441050860020740310001c01100031900f1032030342030341c034501070030b19644607454020340511070349802080c21250358180c03081e0b8010b607401411410300540d5031580c8a0096102c61400c0c1d050083c1c85030505c104881002c061402c110040e03081141c0c50420b500c44007482d00300b48049606050030030f280e09d080f40c01444c079030303008540a20411795010f84820 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 676568848 1250 676567598 676567621
    0x110a080301301113051306020c0f032106040209150a0c021306080706050406050f031009022b0b03300304140c010f0f08040804080f1b0d0206070b 64
    0x8401c048010309242c1d150505201d0407006004100d542550800d8600f402050184102e5401300d49114203000d0441002012464940c041c1c921450041c00716442c86000d00d040314a140c1081d00701c500e01d5440c0804c0322041e0315151069503008a02a02c040d170034000c6071800030700384c7c0c1c002d400a0082c09030049001202c40d07100d9060400c1c0f503500a4042e41e500d444a4041c40094840750065007603038440d1150005100b445241240c044a00c9a50342a007400c240d0648070381075500103007051425406d0760002041a14051005100c40342484140c9131803080b410381e81c580b0669201600e02c0e5803a15000c600381042e00c01144503405020070b0780d40032072a9200710803150b04215099908000001c004410001040b0382e503a12040c1403002e0b203040700c104c0301e07a00c401142c100140b2070710000080c1410300303c1d000341406450013a421600c00c00d20181030a450f8013040d40780014050b580411540150014418504060350340080c0c3ca006032444540102c3c4c0c4d8010902c24886c0300c40c0180307510344240002e002103070304 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 676570098 1250 676568848 676568909
    0x306011218060b120708030f070606210c0b0310140315090714030604080d0c0c02031b040b0a140108190c080a0b0907080c0d091a0106110a080301 64
    0x41d02040900945080807002000e0506440740601920b030341114802000140b11340403035070114002c5140800c5518565015040b4440480d402501c2d00d002140d030035010100c0d4203161403007040c090010201d40c100121501c0c0c03140c1c17110a080004005110380c080c6803884a800b543c4014540b44603120b82075000c82d1515046c14052100b071649001440f1000320041030074000c4407003400c071300036070308031070b4010140c03141015200100704200400c10141030f0241604415a4400503040c0030090030459000701c4c1c2840c040c0064410b078460907240035082e514251054070041d0b03600365441c0d54058203003103c04000b0200d4411203418401c1110014027245c80365090310141c83c50444050060031600900580003501c181c40e0498202d041048142c00c40c10240390040c403c080c0d558900344503441c0d14400280d07070fa001c0007045010b20f0f00c070f881110110b10b01c03540c030683e0008008001500d940c5040401040f040b00380610450507040980380501241e174680c1601d0545141030f000c03c1c0c800e8003d5056000585c00b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 676571348 1250 676570098 676570121
    0x13080102040b130605091c050307020312031b0913150b0a121404021818150402090f090706120e010e010f0b030c0a14030312180111030c03060112 64
    0x40c010507060b450034042c221600f0741c15029440079440c1c5405440c10f00404910b140c00404200d07407481450903203140c0b19410743c001c005582c5004510b4001c80c0c18551070410f0807080d051700100f4840301a008200c071030f4a842c0c100203060f09005900300001c007031103030309100c600e001d07610b565070411001c0780e40013142c0044c00640c81143d81c1e20301c09640503003000d9503402c0701d107601480c204690302c005071103c40c8140303d19401020350360a146904c1c01100c480d8400750a80c5082d0300c174905d6646161038108040c00f44134a01c140012018030b8544100840980b004080030203500342c0d01c040c40701108c1c000425406a40035030510101040304095a4001410120340050b01503007455003a114003141980002c0924501c800c0900c06480c028060603501c08810100580000c0401c4040100c804418400800c0c124003c0a5a240805070082503c0000d8241c1e80e8500d44190000c11000141007485105202d11180c403201e419850300360180803450200400a130305002d030b0101540c230703800244d602c03c03804a02c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 676572598 1250 676571348 676571351
    0xd0602130e04050d0f05040b0924071a0618041205090d0809040b010306180504060608010e030d27140f010e030a02070533130b03060103230606130801 66
    0x80d00f420443c1c0e0382e4001e01c20b480081440a6048100c0c18410340455040c1c5441401480ca0540940140102003144101078481054150301c0204080da64000410034103004e0120700780d508810b81062041920040c1040344900200320b8820944000400b4880c0e0007038105007003001c0c0d001d21803400e403128460307240d0250b40071400802200400046002500b020901560100114002c041c015021150725014100c51390003004481e51003403c4540286078441e10440e4085101940c402055003500c8500c8001036042c0c00c085a81248040103202c0c031484c4010800c05070480c47c24082006100013640300000c2c00304201048900100901002411380210305e25000f00b141200c05014191a5000341450a0060040f0940050186064070850700c01c0d250031812a04e004040c50b40d28441c14211802d0002200014404120746000c405500700080914111203692442c1140006044981d00e84503445224020b800350509070310440c0715540d10180544c0c00c640d03200d120712080840101d01350b00501081d03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 676573848 1250 676572598 676572601
    0xe010b130806180d210b03120f0a180b04090903022b0e01020a1a1305010c0203090f04050417031f03050a061b1b08040503060a09140102090d0602130e 66
    0x9060b801d580301c950a0001e0644401d01405502110342403110140c124405d0a4604410100e420552050b800c184000302240d10091090b1414803d641280b08218241e03000482ea180005d500400310103819080713800070302c030703070b141060b1814099008901510390034617500d1010a040500030010030318103ea1200c491014030600c41d103030000c903200d04404280004d2942c080b41c1925400000d00e220823540c020303255100c0003c4811030000384400181a94410400d211051010070340a1007a1100500142c0c0596550303070420303080c06185907804070164000c0e40303060100400b0511031030b107401c4151845a11581da944582e4403100303c0f00100140400305107201100002009400245010001e00c50201803000d000d580035200d90998100d24000d0215400420010b040310302040702c103030f10b00e100d00d441d503007042d8491000c40e26004046801e0340d00680d540402d00140547e800307004501102080081d0324001d03000c004652904070030b1000800240d00400c0b800100c03060b102080b0080d01406500d050305 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 676575098 1250 676573848 676573861
    0x17150405040b06030c04020c07120507051002030901090605070b0610180905420102010f050a02030a0b0307050f01211b0306050103090f080a020106150c0302060606040e010b130806 79
    0x40e82c42921241d12a102d002d814000905145c02034440750240740015001c038602d4607120802d5094500780c11038980c05044c2000c152941e42011510800209030f000390313214661100094900c11454100c81c040c0400dd00211002504449201d81d00410a80b450601c0118059055075403040494002c55402c001003008206071f82c96030701041c85209204034081400001d41002c894005009070310840102c5007440a04510005802288100e2010701c00080c1807000540d201c1c3c101c91042c3e4180c08501c2e0004280660010a8002d2104c800000c070040e0580c145040c00164908800621003814001041d184081254030b03005041550b45092005001d0b480c58801b4121a210341d00d80e12101081ca403100c04183c40d4864882c00450035440100e8113640c01a580300e03c1c4050308240d60500856480742004650101d00202c200f683d4074464803160887c5043d407a0280c245440142010b000b14414401002310b480d02e0008a41100ca100345541d54400b2312902100c581c203140d8000b000c1300d10035602803204 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 676576348 1250 676575098 676575113
    0x103080a110f03070b100521031201030609020102100e0d120615030b0108181b28090c1812032309040e030712080a06121a07020d1715040504 62
    0x4070300d2041105107641d50b10000301b0a00b50f9414001c0540001c2c56000c0d100c424004e83c03001000c00c0d2012003c80e03007401c02c006550100319000340c1007140c003192141085811542c04001100d1640c0303080800f40075411034a10087d03030300d81d0f036100311404200f507581d044091001b166200e034010b00070319207104010900f81000500a0030705000454002004440017032118840c00303000c80c411908090140180710000e0048020ba00d410640342a840003620076480000703503821004da421070000c4ca281103041f13441e19240c030089404060012003031140b008001d03203c006441140e1002c0d5816144201c100c600361341030451300c0700c0c2e00800a02030f00380a030095041e42c6411302c0142950f003400300d40500c4103411a4800716243c0c012000000c2106c090442280700150180121a6101c803150b640019104e0f600c04040e4180c600000c015500066000e40c07038010b01c040c0c55151680030701280001c021581980d480185001003096480c1141070702e07107020a14002442040d070960003402041440141441c1c1040704 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 676577598 1250 676576348 676576357
    0xd03140708043312052d04140312010509040602071a04110a030203030d0504170403080304060b01020a330f0b04061505070204020d020708161403070b0103080a110f03 73
    0x44400c0300e8000705800803515005800c0a1228603558100c0c07012204d00001e014003005014020700120710905c0c0d00403085041443c0700300781a81c40c5d00784090b050a00307103002d001c3c48421312480703d50800c101c00d0120f0043d050100d41100d0055a1002481d42c03603007841e40080c00b0310320005040c664410201c100318980d84448134010340c02001c1e07100691001c5810060b0704044c910001390550000e000404c41d620b0305600980d413041c02003450a021140b4056030030384a5000350800c54040301d012081c00f060040921400502d120b00780000c044e01490341d21020807801c498820280071a044200d003c1076100c0f1002440084d050b941400d02c100343c05213002c18040c041039030380c03640514500391001030203a0340c6201c4803452010a40701e0500c0c18845409003c0654843c001400b4055000c015200004041c10000c000600c43c0400c128810416854004003caa4402d030004c0301e980140000d10116901d540c2c80b50440394440101c86e9503401d411819101c86c00030200c03a40040c00307240d0748242d08400200061 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 676578848 1250 676577598 676577639
    0x123072d050d02070605070c0b070303060803031f0e010b041a0d060f062c0f06120c25200103140702030a140f04091503171e090d0314070804 62
    0x3c0e00c04e56214407045486010f00754003c2e00d01000002c00300004c0ca00140244012802842e0200360b66407078803034252079070340255090a00300e84c0d2218030509928540c04070314003514a01b130305d014055241c500c40301c100b0300990161060388550448440c61081c0000c088402025104500f4083ea80d0380e4000c51080307202034881e95010901140c450081ca1903416120000003084088166003481a4000c2c05089168a10b0341c42d0070200403c1291214000100d2140c450a8000060b13603039080d0440c82c0700141d011108500504903054080340001072004101d0001c2d075500c8902c0c06140f07940d84001200504031038984104115009024032481a0b4084020b206004458403a0004c2410804d1152810300c10100c080c1c60101c0180418001d00d2040e40044c1510307503030b444003242001c0e101d4848007034000040718087c0082400060407914031030040104241c0e68074112045082280c0032011480d0300107903050040401072881652141400100142d51840d500951925121915140d80b21080b0780d404141 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 676580098 1250 676578848 676578853
    0x1d010c080103111f0807200703112409040207060e0c030d090605120901110406260114040b130f060905060d05100e0703021305060123072d050d02 64
    0x5943d52814400f54040707200040c1c1c40d000001c503180365401c403100d0b84003505400030070000f0101c02c030704064400c0c01c1691914000e4080c00c80603286241c104001821040814000d88100300d4141e41070440c013944081000d4568070341685c49002d44005030013803040b610020505450003a400b0b0b490100081c0c6c6c4521081d060741143c08a866406d000d44850002d441807a0005004100000942c80c1c849032043d04400300b40004940c0c5903030311640181c203400c5a044400001c140f800f08003115800301d00114610182a0318400040d41444100080c1d003508107001806036131150030810079911460030150309800f50203010051074218046082c0034000f58440c400072541800e01103586458403042c403030025603005000b86801e80d00004000d003c2e108030682844d080c05052000405a21500098030130641b4a07240000c40d0b2074000c0014082407060340c0b071f4925220400c030603100d01c8111a800c555070749400c508c400d816540b80405020600b90b4131061a650080400c0c2804104030000900a0b200c204035000d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 676581348 1250 676580098 676580123
    0x30f0806040b0a0605070203010207140a030206150603160c1b080c030d0f0804030309050d0309050115061d030304050604091d0610050d0203030910090614070b01091d010c080103 78
    0x208402c1d00c2d0100d200c194041c400120070403000b40654002c0038440e10240c0050300703108050716094662140c031860071119400108070142010350511000c2c0c1c0c0b00350000e00d03086880800700007003040b03400f000308540c00c11204202181d46050180b000041c490f41e00c04a00015006296103410300c40060b0301ca00300c076030710440101108620380401c2c844c0c085001e0307a682818041d00040201c03000b15002c2c20030341c10325982d0005400420390078007107140900c20640300802c000b0032f146045802c446040c0900b8507580350545081c0103441c0e210110b1b034462102c0c600d00700c110401d0f8000207400e621071940504d601c0580050006000c0d40660089040031402e010000600c0080c0590b042d01e800f011507e0200d60450440c1c107028a142112200007250300107001c9030308060740000420070028900032514007240e518481002701607030003107240e0003898244407820704121045e43c410003080c0047c0200700c0300036124601081d00d0001501c0113454001c40303038000d0060800c400c40c043d10500c42030000b51041d92000c1c2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 676582598 1250 676581348 676581361
    0x60603060602100e0a2d050a111012020315031f23160309050a0c05031903050d020c120f090906010c150c02120a08102c090304030807030f08 62
    0x460324004c2c1075044003404414045036a110302c01d0098030503602c41190340c0340030303059504201da031844806d51142000b00950303e00d80c282402510004007226110341030305202e00c0e400076884076003905030120301c0201586a484140c501801d42c2c40101c0d001e17805205650603103110b80790f900b901800c0c2d10302d608405c2002303e00d0486655000c0c0445241c146d10440901c01003181214881076003a00b0f80d1081c03a001603010082c1d42d40900f80b0040680580d80b40c801c040b0184020700d000e021010310300440c004100020f0410750f40c003030403d00130031205044580e40465040e060340700c2888000740038601019141e6491612540e9000d154200701c00c1103005101c08400901503502034600d0f11182c6801c0f844680e920202190030380080c1100240325002c501510368070001140705000a001414181c0d103490710940351184103040c602010b5403012510150360409000d9040000c00303e00002e072028504400700c1d65820301001e103188119800200101ca0019800c81030540c4121011013102480e03640d80d4480d01c070070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 676583848 1250 676582598 676582601
    0x318050c130c23041d310f020a0816140105091e0d0213020403050c031203071b12030212090a080405040213090606020a15050403020a080304140106060306060210 71
    0x9240e540100d00c81004040b0000000021004000d800c030070007a25150310f60340c0c850b00f01764404400d0362004090b1002d0102200070340307000d801c940820f40350102409800019103a80b01540c014041d01080c00e29070040709544900b411000504a501c04541105e41821180681100c15100d10460317000107040d0900298828030881c3c1142c0030081070b4403220305c454081d9111210384180d8155010141003080b10040c0c5650a18150101005100503221495820501d042c104e111100300c1c0719412102569803044d9001d8181d0790003a40a25055000459032000c0310300303149005402811070443c004803040c1039903044e0010604403480262a042c15212801c00e00d1b90307030b40515070081041c98144414006824541e014100d100d06d6107031038820443c0e40b0720b00ca40485071140c102d1001270b04108902004e200d01040d00800c03011500d4030800251600e514001c3d110b582044c8018410039000001c1014800040c42d001203c0914800030007511fa601e00703025004244912600d00540900340980f10802d049 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 676585098 1250 676583848 676583861
    0x60905010c0206181c1d0d06020405010201060803071a0c040e091614150a02030702060715050c030f0a020a11190c0501020a11060f04081218060a020c010c030318050c13 74
    0x10710300050034007a000e02051b9120911000c0f41040d20610604d0414a82ea50036851014130b4000e030001a5240d09240c0020300b9940507810100307032940700700b16400016902050040400c0070b00c140840c0c1c29100c912000c0b2161003564011910140c000082c8074400c100400d182c4910015188104101540c03038841c0402032100311107507503002172990b10760880e41c1503020080440014600c1038a203018840c0e40000c00c035070801c00d0140c03003a2081415000c8002c507036114141d04204d40c1040385040d858100c0392101ea404008145004c0707590041018900503014040304040781c08050156460703103000f201038480e41c0500e5602955060701c56000042c65500100d004407a150300001c10300d03480b00c40318040c44915403120700001000381e420000060050070511182c08030240940043ea030b00e401c94040c03c140449030b00c403014491101006400416074001070a075140c0300c000e00b03109808216509095004140036030b42183c0706502070300d007103082000104d081c5c412010700f2240d0107251819055110200d070707170 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 676586348 1250 676585098 676585123
    0xa2606010515030a15080a0605340c030201060f15021c0207090504020a03020303040308041728030c020a1203080903040602060705160503120a0f090b070c060905010c020618 76
    0x400225500056540201d001c0c01c02c0007110200390340e6a1300c030702032401c0300c11103007600d004c9e6036002031001c908064070007044d421601c1c0f0210801c02c03941944040e0048031198685090010f406034840805000b03406c442c00400040444101032076541c03c0120160091802e4040140203680c000d07032600301005800e00d401c440c00c5c0e0003400202e04001c5a072004150140060303030720101c0c002340040143c0d03042004001862080c407099407524a400c0c1c00005600180c85100b055070031070110303082c15100704c030b200c20410b11005143c40e009400b2401d095036844401c2d003010350018040d90380810500d0f01c1441c6401d11522070b43d9040e04613079401217055160b018a0190b080180c00840114075442e00c50005041020003003203400501911560f01d041c41c6521156021407190482d07010065904100e205e80d522001c020401403041c0002030762800700342c2c00300a020f1024081000820414014030340d1102e014650b01000810051802400103076480c0070031a03a416200b1194400c0038100d500c0800d6010b031560 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 676587598 1250 676586348 676586389
    0xf11090114060a02010b06070c0617070c0327090605030d030501030c0b0309031c0b0f060a0905041e0e01050a06080d0507060b01170f0f01060306060e0f0a26060105 72
    0x70059001c0002c0e95000158800456480344842862542d031180184a45441056003940d0b007440d00002138089100220340300c140b0581041040300094100f440070440a9043c5080c4e1180c80c2500800811420754034a070310407e003808403010400000390352100055038011001c0760581d640501b030071010743e03074240401424000540c4d000c000000158000e103030000b940e0741c00c2e28100780348900f07400d03100318140c00c80da070003180c031448452843c0c1403103801a140e1090a40d0300324580400a01c000c2d058500501ca850300031907840c09010004c0c4081c180510042e0300078a018400c06d00c408510318080c0000303a03800044103260200010f1040d03400a921500c003002c64803060300303102443e15203100400c41000710b6030500c40f0580c8088062a840e1444038411080303c40050b0b40ca0500c1150406c0f0510141c002d0401e03d490014240403035508081080740c0320701c00325440d846103009000400d80e40705180d40100070041c452454036150b90001c45010743c0030320100c8110340d210f82e80c0f0380400034042a500c0c0c400c0b9542 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 676588848 1250 676587598 676587629
    0xf090f0c0f0d140601090b091e0912131404090c0608150d060e0c09071d190608040302010b220f0e060a02250201050913060b070f110901 60
    0x241041c40300191034030401007840c000002030f900e6402e03495030846510040750300050014002e101c030a11802c1d0b08900160b440320500d203440002c113840412503050030340740e000d00382c0c0002ea2055400c100e0005000070b20284140c8030540c0c9143c0401d2103246028011000c0001220400301d400c082c810050040d811451140d1403070316015040e50441d038060009a844603071847c0b901150b84605d09842e428504c184400500408035649913400e00418592903441620800c06106e0700644c00b45451044800690803006a0086440051403526624165045c00601c0d080c001171001c0d04203214504c541e0081c3c0092009212990420040d21400c005100b117842800003050890142035116a001441c040b900044980c001c43c107003446d00303904681c00c001c0a43c0025a01c3d501c040780d4802c0c0f0350003da003200803110f95000380c0e0018006009589645010381580382d1200c4000c410750b00560000e140c810900c640d200b0007814071b01140048580c0036100d4484800b54640b50303080c00c10442e4101d89403421240002d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 676590098 1250 676588848 676588873
    0x120c03110a0b040b191409060f01050f280815010902030405070608150916120b060405191a1b0f07090c0309062c0f0a020f0a1d0f090f 59
    0x1050160210120baa45c1e0a40504424135900ca000c4c850b0f140549100c6091500c1141c2a2400070b0040248840d102c04100421036601c0e45410324102d00021501050054450041681300040015205401c00b00380c200020307201c500441d0720103d0446140d45004244e803035601040c140c3c4070640e0004c025a100c07040c1000725034800d2109580004507200c0c00404071905a000800141d07061341c40c00c4441282c3c1c80342c403006903045106000d400707607006004e0001d1404c0c440050b2041c003032031040500800c461201c8100980f503000607640503200f6a04152071004d0103074961501da4000c0e125a40b0034081481c400225080b0010344c90400602240003000d00b1030a010105001c0d040c000c0c01e4400789030b180c3c40301c43c0005044e8047d010841c1401c104c0c603842c04001584036244801a2002c040050300320a0350b0030200040800c1703000b0010f40581c1e10b19980010040403c03c140c1c1160720140790385c40c20b5400003c0042c6030f520800c3c01068a26104000d94032031705806911101c981540c0d415960118600112 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 676591348 1250 676590098 676590113
    0xf0406030e0d091a0408010f0b030c0f1518090f010303180e04020d0c080102040b0d180c0905040c0509010e0f070305090a141006030507030b091b06030a09120c03110a0b04 75
    0xb140c260b028102c5085c90703910010542903649152420800644409040300d8506041240e908490000c940b1507120b05410004504103028940c40381d00080c2d030020388201c4103001503c80911480015003081d0051034a100c3c140340e290f1080c001100051182302c069040e00c2d000800380300076160a40c0c0031560342e4586508000200c0020f01c8201c404206110340041c0401c000c2c80908000c01644080565411241038000102d41c1c0c060100541d0401d000000e00110f8116a00e003400c1d540d642000082035141c83c20440000d01c1254803031030340040101700105442d01c820100c0c1d80980c030882074141c501c1c3c4440100303500340c82c0c040344d00c04a00da001400351030100b0001a500c40f40490105c003519004142c40a003202558184d42090b00c260380185002c000700304202030941e920111030f1780a02200d21401d640100d4211082e90312602c07072f89002c03010400108040e48420510703940280018001901c0c0c21020b021200b603031000b540401c464060209860401140c01150260b02241d4101c0c40d0303030b0303540d0b82c1c00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 676592598 1250 676591348 676591379
    0x5011805070210050a0603140f060112170a09030b25030903030f05040503040503150105030706051b2a0906060708160f0c0311010e01020c04050603030f0f0406030e0d09 74
    0xc0440c824140b090b070f8400030a1040500941041c180480d4031400c60500c000c81031102100c6034502d40c066000c107101c8075408600c8034152410300411b600700144a04011509071078903c51180106c1001920b0001103400230a103404036481b40e240150980e64003841074084031200440010b032110492010b0503442c0c0b003603216040307941c0710782400500c441400720507a04403034084808640c550710000b0244102d1908005a8181c442c070951082065070511002c80e480e10003d10810051000c0450580001d51201441650050a038401c0358184412115052041d4031402038030b0382602c00c50b0003401800d0801c03d080511401002c0c02a5140005c15564100b455010b400409075180c0d0080140340051401091702c80c20340c1c0a0626107030340c2030550401c2443d159100d0401030500c200001c0703a40d55a60041008125024201d90000302690b07202e0101e410741c0304d200303d8020b01e0980000d070184c5940002c130290040c1c442641c2c0821000544606961b030f9070000102c01c0700400c14560040002c10f036450400f4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 676593848 1250 676592598 676592611
    0xc06040605060d050f0a141b010806040e01020c060402041803230702130509100b09190b060a0210050105010305060612060a0b16020f0a0b0a080a0e0d05030a06060305011805 76
    0x10003541c0b944404d41030009140e0007540a8001c2c454240911072611050451141001d000d400e949610014029214600034140c5d4184109507001031060340e11584240c10708813446c4000c1d980e525401c014540c50300411141284524503082d0441106107030401000380e42a415101e0702e0300b01e203110362901c1803840c00100c880c403840070800010006842d405041701e410604014045501d050001126040a50300c3c0f040900051410282c1881d40d038a0368100c83c3c00005103c80e1201d000e90505a00780546581d1601035007103100040d02141c595800207815203c04200c0c50704101c20b980740e10044040c2c410664015600039000e01c0708981c03070305520003030b2500003030028410310185a891441341c02d039421000301800700d65658654002582090b0752a441801130481c1c050221606123070441c115030007250f50103020464100000303000c2d00da040e4851040400b101c0d003101c845481000004180340d100b210301101c40d500f007010002d400d43c00780c0905416544041d101140f40040e0124120003008000d00f02d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 676595098 1250 676593848 676593859
    0x302030102070b10080d0c060f14090703170a080c0a0c0b01120b1302090a0b24030118110405060306061b24060d0b0c04030c0902030609010b0c0604060506 68
    0x698003440104869885640c015003246014065041881030503840440c8075000b200c040c416481c2e02c08445038209910001c0010386c0a01041c9a03401400350314401284d80d500d0340305014020310006900001c8911824a03105140c5803440d04942c5c41c0100c1c03136081c0100e881c04011406100541000e003440c1440d44c980303005c0c03102d540e450782c442546080e809141280400d22442d0103005001c2d5809904c40c03003001c3c001410900c5903000c07495140c4003c045541940d5225030358445540c0c1d10001000e034502154001107050300e007011403081d0713510a114540d00c042d81c4006003c0300440342d000b141c08a90361050014201441e040920200d076200070041075005408200204844031036220300c1c000b2204010003446200661403141d03045e080200c1400c8802c480c0c440410080340c3e6000d21100000340c4c8800b4592131611a480741001c1d601803030300001c04141d0103604c04501049561b024600c0340a089950400a903039414500e61a480340034001d1149410a00019012a40d9034111a40001001d0b04 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 676596348 1250 676595098 676595113
    0x5042901050c0f01020f072028030204050405160e010e0c07141009030f170105040c03061203020c10080f04330b031501080703060b0f10030527120705 66
    0x218242240c0c0406c1e1540355040d40812503d00380032200b821522003400c40f4940d4448802c0c608002450201c2d128640501101c0e138104c0015a100e075500510011039000d0300a01c0203040518050b40c03070328003040c0d01d10014007001200090303512841c1c0c10541202c0512091202940751080d02044070b0788918000e84081c0c051051004104208001712164000103620005130510b0924004028101824041c000c000081454080401d501c054460440e80300702c400041c1c0003038140741640074003619440a42c0440507840e0f55024140c0108414000f403404441ca42c2c44012546410354507a802500c282c0450400780c1c0c001030000710f1042500c440701002c185506240c0510091000440904000808419440300502011410f0820101c85407004422040c840340d0b04100701d080e1303600032510002d041c540e00c2c1c040303051482c1c1b262512822000c401400b05003031291130100c043c0240c441174413428070035008400403840b4010141c4a41c040e000740b40d80039144560317041e003100d0141e8204480c1642c080c001d009 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 676597598 1250 676596348 676596373
    0x4030e0d020a0308090405090708100213030b100305240a020721030e010501150c030c081e041d0903030610120501060206090f010b1f200705042901050c 67
    0x10702002c0210f100342c60140e40d0300d40c071405020035075070080e01c048110b40c030103402841f04ca80301090383c01a101050314010b032a503101a00403804940e65a2016141a1954040c1300c1c0002400e16503200f0342e40103808590600c0d0400650510001130f980c2c60030050709205000c104e0010a130780060030713854090241d6021203541c03610542442d80100c14110042541e4210141411100f801000e004040c0441c0f5040e20700c41031030000d0000f015580d801010010a00c1130102040b4051003664000700742014208665881c0d03052500642d03005000e03071001d00c1c4000c0c0e004003191303d0401120b8403540c0d41e900958115283c4905100c81c05070000b9010050100140e8a41000c1d030700c030300c03c046c000c00c0c50754006d1140341480c01005041c0040c50721700001c941d040241e17802c0710342c0700c0300d20103214404184003000b4003a904d04401c9801100c003280c2c0e410a41d01c010070a42070b2860005610080c1c0d10111400c10600d0b920720a02c5c20003c072150680008034100104c3d004896025402a19845007080140c60756a034405 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 676598848 1250 676597598 676597609
    0x16080d03092f0102011d06010e10090c03020403020a151409042301030c06050a0815060d1e0b0415050f0402090d03020604030206060d051005090f0a080706050c0306010804030e0d02 79
    0x7095190700748120201101944c1d090041e5213602641660b40080785420810340d83d220341050040824024103a03000c81c0d0a0320104840e00c0003480010801c205220302d06500502039441444240d1050800560108041c40f40650405100d420b688804107111840701520741603402a110352540b141c2d0320b2805000301c056001e400c620140800000d040f5941c15850b003000c0d248400c2c0c10403400c01c00180b04e40303070700340d5045010240c0058144012540301d040c9200024200e204e0386c0c02d482219070a040802d01d80c1040c0d081e03405501240080c0c240b241d400150240700450750048400c04404e0f4030a40100821300b0444240448940040d001610b000e0480b00070039440303006072804900680c446410001419414000030342c0002007200d0180c00320101e170702d5040d0340d81d11105003110f040e5603c60115100d82e00402c004440f03c2c2d6580b003540e031030003114180310340250000d82080d00e0050130b250008100d00c01c0c050460303120780c005071102800c0740c841351401c40f40420410a4680c010901e00841405039a45 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 676600098 1250 676598848 676598903
    0xb150d020904060608070807033605150921041d0703050115050415020a0c080d080a0603240b030312090118121b06060605090316080d0309 61
    0x24a0015903600c4000050004a07006507000c0c03801c0000030310038012801c0d0720104481d0040e800b0f240104491042202810a0446035605016040c03603c910f00300d00c1d2601103621142c081e02400641382e022446c03040200c0d002800b20340b018501d4220000b10f501e40000d92205043c00744070013110a08090701c4585000402c0074001b0359240c90000702d0200301589901d130081601404c554140000000c1040401a080c0d02543c00348071070f44c44016029040c024401c00c42500001c0d008440a20080e95490001c4d482d12403c4c90b03901e0000304400d0000d4243c804d20700840089903030080345490f007030715094105031141c0152080301c01000e46480c903070886903404101401d1030002c65100000035040144900f800c440d0502c40e01751004440008040121b42d00007040d1a03003041c242000d150245020f00c2526124084020080106107032480100342e0359845800b03000c4100c010b0f4205c6001d09540003860200e104a80306082c16540041610010681f1130f4000c00003151284400800508101d030741c844c000c005 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 676601348 1250 676600098 676600117
    0x1502190807021207050a050906040b090c03100f03050d050901090f06020303060f01110d0503060616051506090c0406030c05070203061911040506070f1a0906040302150106020a060b15 80
    0x441c5010541c68030100326035000301a80d000701800c41c54000400d01880031481000d224410040010b80c141d06c85811100b2101d200404141952403c0d403800c1d05e45400646811030804c0c61020301088106603070011074251794001c0014507114940d0780c1d08681a5000c80070441c1000402d2800107030321204990f10b50050700081e005180c49107400f5051100b54504036220320b041000704843c0203103240c804501c20f04080d000740f03401980c035601c03207020515511810a0142c1103040151008050000c0425198241001c03014442c41c06e803030b031404010072180c045e26404001101008200203d601940c4505008951410100e0804c12640c00003410008220340b020004018a203903e1001200d5110745100000c081c20302d0307410715003058049005402481d000130000c000303018004041c0115412841842c071040100c440351440c205929540394402583c089000d88289401429034011001c1203074180e5115a004066654040d20b440b405000301d0110f264204420b0b05001c04d0944100009100184 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 676602598 1250 676601348 676601363
    0x2090109080f1f1806090201091205010b09070c020a060309150504110102070602030a21110c1c02190f2a050f100507021315090c030509010e0601150219 67
    0x5a04a455440e03900d2501c03615a001e28002c0c2090200c600b600340c13003601e00d8000e04000b403203030300a100607107401c0c090f5045000004c0182c03868808010054024480c20f50701a0307280e5030540c4846006641c82412500300a50007504e000d800d00c185480303544001400c0b80204110000b07220500b01c2041100d2041e1400c2d96200d10100d0145942d580410802004200900c011417030200000d400070218882c41160b1018141a410400b0710801c0355000403440414606156503101110303c600785d0b8602d4282542c40000b1110031022040718000300d0481071124850b101c0c1c1c842c5480b207a55141503440b00307040458000700c1c2c004074640100d002d2103806440e0080300f80006840d0303080c1001c0218054034290381d2807140b4030031001c2d0090240d000707055452159068601d1080054400419409406202c5c2c01e450500780d0400002904005c42e00411810015510100480c1e29441112800e80b06050502d9103030782e101800400c454602a0700c0700340c07a120103106032400c4070640b00005041c01c161a9080c6d46e800f = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 676603848 1250 676602598 676602613
    0x1e03080a1205070f1d0621100b07020603010b0f0c0a0b06121c030b0a0b2208030a021e030706110406090f060c15020c01150905070309110402090109080f 67
    0x29180700ba25080001410b10242203c0364a0303004250007441146040000103e08240220391600c105941211203004103050080400301d9a400b5042c60444e50111104651100050900b44484c201c0745029005414030b0300c2c0d40e00304484581142e0101344410b066400410032188840400e100d0040300c18401c900f0f06815081042c01c02c4418001c0034042080c0d42c01018007280c8200c00c080d500075410b1035908010403001900c50008901c00115840140800d200107802a4003200c50064291942201c1c1e82c00344005440f4214944c2e2801440c00d04005030b0312806015001a0280320265165851101101d25000c00c0d41e40d01801d9401403110b61010701070101d003d100140d04184c03003001030150003880f1103951b8034140c03000b00001c4011401920b12142000e81d12080701940d0101c800401c41000240240d61081020000300d64030b920070203200500c0c220116143c01e00c03a0049080c41074200c1105a030081920003000000d502c43d10030903061000002c00001c00407020b01414040c40901c0014010f00c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 676605098 1250 676603848 676603877
    0xe120609071a071217010306050702010c050708070f2105031b070c031203140f0601020c0306070906080a02070c031a0f061f090810150801151e03080a 66
    0x701105500144414922500c04010801d090302c240d42e02103130000044051207080c1001503030346400443d0030040e01ca018000100c14041590403203030003950725600801045903000003c43d4140509075006090500410250001c00c03141074031300c8141406100c2d0f85003800101d4400341c40480401e1038030703000b25801004001c41891248452444540100c1c0180d1505201c4d544824100308580401015000d2685040c03540e58403d6008414038043d40700d44540d00d04104406001d6408100c42043c0144030b0f21400322040e0030042601b41c040c081e6070700c44280c0641001d400380d440e600000c1140e106290309200c10004105060021b100941c01000c500c2c030303000b00309040c10130344240081c05d011f907108004051081c261190260120140022000542d0290418008482e050f5582e400403c240c8580c40c0c0d440740c03040c000c0c0d0200460320480c10011a615039030f49003540c01c1e122209003d0b0345410610b2402c01c440c0d110132604e00d0103000300d0340005410540320750340c100c035580004081c000090820142c0185 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 676606348 1250 676605098 676605103
    0xa1212240503160e2d01031a061914032a0a08010b03030403060e2b090f081e1c080a0501060516080a0c020a03060c02070506031003030c030e120609 65
    0x41c003412141e02e1222003400c0c03843c440c400c07400240c84030a4200c64503a030b50015a400c01c0f1959140c174a0880b031103c140d40d40742005041382e0f100b002c401603070442e44c4010400c0c5107409180c500362412418510f0700c00601e80780603000380301e00b61501980c142c05240f0104030000f602000902030072003200740f4110140011418004071004541040325560715118a00160350740020640b8105ca900c85c8000c180814444180c904040c01042100140000c038140d8032600e11003079500c04640316180d0b507004100c5035241040f500c0c10b0998030070f42800b50009024100f060165840814101102c3c000302c508081030201e513000c201c9540c08400d000140b21b0350a0240112441c06114014040c920300f4a08100352000030200d00c0b50351110003050500000b03610144c503401107a02500c0c0784d400512003030741c00d5a0703800d09030043c0c02c0c0e201c0d1550050150040c042000e140c020700b503901810b10b000700c0310708890079994169801428120190184541481d0b000007903520400744c804125115809005a401c00c11052071 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 676607598 1250 676606348 676606363
    0x20c1e250f0f0e0f04020a03080a11060717150d0804180b01170f041403120f0f040b1315050901020702090109111606022503020f0a1212240503 63
    0xe5402040000c1043d804920744041d0031446080050620303407a14800500c0140707480c1d20003008a400411070100c0d06422400c801242d500d41d6050700c81c00d035505001210300165520007607410642450100c2c00d43da011043c140c1d142c1001a00e010448042030b11240015000303a0f2088020100103021000a00118082c3c0d008400003030034448180c441c0500c220380a0035004003181c0c07281d518a80060309000d4100b0440442c6600102500d41d5040880d0700c0080310a41181e04100000300c035408190340e404101c070068851a001140444075407221800f440f04403100030025030742c003581340301d441000c081c0300c0c802c01d03000c1d0038070300d0005903151604c4c03043c00816501684000e59141c5424469001c0c1180007085079498000c40c85a5010340011780b80640080c06071403002c400041082c40c0c54a44038000c8604601014069000c41e107000555089055071201011401002c42c034000e02c04a151074002c07003d4a00014404d0350200d2010742d0044010f4942840703013102c2d1203c01560000304610f080034080c42 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 676608848 1250 676607598 676607609
    0xe13060b1930080301050915040204082b0507031b120e120105010501080109091a0414060c0a0e010f0c050f03040f0f0b040e04170d02030103020a0504020c1e250f 71
    0x501c42c00034107032188802d50005100f001d00803605000043e41090f184a0100340b00000108115161601c558065a94100c50f4240700d11098500c04680d031002c1c50000c8400d06844640d40d0a403078400580c1d030861b031420002d40150003491171840024001002182e1160062a059031039200302e407044800c01400b2480d0b0a0800303616450b0000521803030341d01250240c1500d10007103002c914070b0482d192450b048030711042120020b5655206110810002044050f0050b0382c9400316800c0da00e882c10032003498070890100c600411580512101e039940141c0b151408558103007001e030510585915806e040c4031405030018181c5d0400102440ba20080b82c40d1400034080031100310030f1190611000800302d204501030b115420318401c0c0050304201811406e0407249020340c2d48583c84015003e8403070040d402c05c0c002280300e21039680b00401d85003860710946251202220013000c00c401d200703030300c50b2180304000c03401500e038000c9507007943c01010703021203020101d002a5400d003052458409100700c00342154025 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 676610098 1250 676608848 676608929
    0x504090c0f03050f060108070e21012f07060515030307050d020f0706050d09081c0902010e060a120c020f1f050606030405100f0b040c02030705070e13060b19 69
    0x280010341c1d90220800c3c2d449048c0342000e0b261010318100155041f86003220295920018a5600400b004190080c0c111001d000c059030044003242c940c08030580d0200f01e03100c0300700b4005003c400702280490304070320b030085042030460184040c80c4010909540c48440c007a034603580545400103082d641048546400788069011340500c50030040000c04030300c50555a00c942a40f1121102705011802040b552800f83e1418a0812022511110400742c4401e000c16070120f01100d45090300c1d8100b0381d04880240c07907030780e48100c082c22a006044008107034050942c1d00718400d140c100c00c00b42030200081200269501541d4222048031400f100560310001c00c2030b801445e0500500c00051800544082140d00d40040801c1e0781c40070300100c0000740b02c840030380c0345d2150404103004070054000c0000d085490144043d41c04540d1243c0c05954403250595441c0c40e120032400740f005c003298403503101020180c1c004100f04140590031456521158442d080307010010203000078550000811182d0b850b041550401 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 676611348 1250 676610098 676610101
    0x521070c02010309060b04050718080309010c12021002030c0c01110c0c24040303030507200735060105100e01020a031b0b09010c030e030702030c100504090c0f03050f 73
    0x10054540d101009040c103807109042070800c8030980000c480440082e10401c02e51500e0f0400400032401114204040700c04140d0204001c2c2d004011120301d0301d410384444e0009880c81c1e0354109860032840c1480114020084804010780a900045018011301040d590700c40d400451400e0848669841c04407100008110604414401040c0d2003d5014201c50103e41d50001045110483c030345204120810f8000180100405405030f02050040d803d50340d802900d425415240c840d4404542c000900d6548000010002000c03240701d09500100650281080c100840d0607071840509101200319158000c0d90040c040380c00d19401011203c003180c600342c80681807810001c0e4603800802c0f8051304008107642e1144a00040f800b1540509520142801d0304d03161103010103000340000d40b11140064104241750300001e80002c292400c0d42d030010003600f000500c2d40e00300a03240f8a1281c40308180401807000085010300c0d4801d91340d40c5071b9161182007140c0c0420b8801000c0f03520081034800840074090 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 676612598 1250 676611348 676611361
    0x14101707050a031e08030403031a1c0b07090f090e010e071a1b150103050f0c031e120a12051003080a08060103020f180a0911030c0307031b0521 63
    0xd000303e98000ea2100101045248850b010000320840900602c800105120801d42d1550010358079006200303032001071401040030015406800c0f1440110341241d074032140c0c0840c02c00c0e0303401a000152400c1018100350b441c9070166901d100390340204541a6501122020340e08280a05290b580a10703001e4094541000509561101c0950101ca0b1010001c200001d010112a20024034001d002046565074412090a0000103501f4002200d050040d464000b050b0000042c88202c1071600401405e00700e405440751980d013001040c4010036610441d090b00740750300c8814004058803603840c0d5403560410410a02d0200380c07040036089020142450030204003040c010029a03420440502e00507145456001c0102c01901480114188508002500046040004000300f01c1c24005a8890034016600e81d40301c4125079080c094004840000c10001d0840c010f400011a80048036060002e140d240d444a018070440702d640c20100480c0300007812100a2844200c0c80d0b01016508085010a2a014 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 676613848 1250 676612598 676612609
    0x609060c0d110f1308030306030a0303180f0b01030605060904020a0504020c15101d09190305070b15030c041e1a100509011206030314090102011410170705 68
    0xc0100d4111040462a8080c00d101c507041840c154071440d54568031030741d8100702c0b000c0300e50040c0c81c4619060b110700c2c2c0000b8034010100650380f2500008002d0304104440d6202a000b0b08142d00c80304016010520300000001e61f84000800c10602a01c1c00200940c118501035080303440280c40f4520401e0400100700042e900c1e01c404030282c440560380542c4a02d51510054a842c40b09140c0f08402e12000c0c0070800151224141d00c2e00b2200304550341440490380840c4c3c00005241987e6150f032642000c1e14803141c19902d40c12030220203210b481c1440c58040c058881401801e004e845074006080c0e07000d280400b0b440d041002c06d0541d541203030200706142250036065604032141100c001c2c51601d68250400303140320020021181c1c040070b84144071410005100030030a90000c0d421502081d02c904515030010310074807540b82236a0307158407951036401c1010304500305508106803030b0741199242d51341e10200c0c42c1000401401030031641c204290381d5041031440d8003081c115181030141ca600c019403c20865566 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 676615098 1250 676613848 676613851
    0x81905011503110d11180414011403120a030b010f11060f180106080604061508030904180f050109110d03210e061603110406170a0b03070e040c08060906 67
    0x40b401c00140d8074400d4491164240108051654a10f103010500702c500001100146294407406000c00c00d011181d5003000111044141c00c5061792a40500501010704000c0840e505820024121410044102d1242070164001c4646100003511402e4a032420f50300100710000c00515810410001b40029010960341c40d0300500c04a00806800302080c81006421003000c0201040d80007403081c15144c10302c0b10b40d20a1f043e9000c96043d85010800b035803903450044004240c030b515801075440c0c080035034100809000c0501c09001070003c013110340d02c0011280090f4107002c0c1d10800c00070a0089603810581c1200e9003912000703006d441c0030724090000980c0300c0c80c0346201e01c0e0b46800701442c1b0041c80c00d01300000c20340800407030321a105810900080a0365030050981d503807069a01440030840d0300170344240c51b0040c0d00c54040401c40098004042018071180c10b54031034100c110004040000c1000280713040303002d500c034010803000c4105000c14468041400d10241c0424002403641d802c1a021680ea5881c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 676616348 1250 676615098 676615139
    0xa020a020a060902150403140d020d0207150201021605061008031602012d08101a043f0501050903070b060d051f06090b1e01050d060902040608190501 66
    0xf82c0d44010800c56807580443c0b100c18052030b81603610b580e105c2c505582d0301c022007031b05070903188900c400024581744001400c078110985580600326680c0303041e0101045446500740401555000d0100e0b0091039007110890601c07038006e80080a482c28000802d0810f42140e8001003141d8008002d00380d1400e5000d0512081141e080c64600301641c0010000b1b0011026046480c90b0101c602842e1a07130f09500141c154011851010030350100d507520014420701c8445c140510700011000e20003001010120308801c03800b03842241c403c1c08100d480b036a895100b002d0000c00790400c0c0032000d10240c00d11000348901c6610a8240005520b88081d03915080c11284004100d40d00c07640c203640940d801c000c01806244400400707280f243c3c0301a0381100003500a0400c0303000b5a03084034500204180103107020394054006134200740d90f914410350440c004450036441583e4111034680c071218001502da500744000c0c0001c0c80f80c1d40c3e905480382080c00c103d03510444000284100a800d10006002c1880c80004010000d203 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 676617598 1250 676616348 676616351
    0x16030e0a0b091e150304030f0c0c03140f07170d050c0703021012020c010606080603061b0c030403081303020414091f060e040308060a0b0a050d0f090b040c0e0a020a020a06 75
    0x40400c4030980d24610010f031034009020380000b01041e169070300654040c601c2603c0704441240c40030011078884004410161166a003c030080000c0780c060812000440004803c0c0d8400707084501c20540f610760554807424084088448451140d03105021280c0c101c2418070304585840000c000e001e640e0f481c81e00010303115041c0a2130b1038228070f01400c041c03400e40d080707400d040d5180c0e100a8561030082202c2c1c0300794004603880d04000342203440c0104035140700b40014070300f64103410b02064505c4595048480314022600c010080072000ca10103c0180080c00c903245641c1c65190700310700c10b120030340e0f40d1b40307818540c5001c0c500c1c01e01c01410f90118040c401c00c012426511788103101500d2000280072190300400700e04410105010034140c1c052071451046c403007540e004c03050070795402e00c000a9100c0c110a810008400340181c5001702c406400046080400450114482c015901c50640600b4203440440300c418a0101c20400001c90074801e83e8071a08401c41103003090b49840e0003035120000050000c0a40d03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 676618705 1107 676617598 676617619
    0x30106030f060f1d01091211032704020403060e01060f06080406110904050a0e0f0c01020c060309102a03060605220b0d0e0c1504050d150216030e0a0b09 67
    0x108d400802140b810004400c0c031035240d09070126a21441344040f0b04020a50f0341d81c00030308043c5000302d100080020304113190b2800c403a41580918003039030b40300344c007002130b00d4000c0036841d0301ca80c20010100b6558900981c40c021886021101540a4500780501c0b0468041d07600c0100260003c10440b40308142e440103543ea10702c02082005e00580c0680030f21543c50030038401442d00040301e0360482d40d0914410204c602500e48070380424038040b01041d9800b4501d02610805403140e42c00c5e0908200f410304225005106d8881c0d102002d0700401d00c0041202000e900b0280c09005101400312241c44003100341040c00500310012081035148180604101a4984481c4d502c03401c0c2c0903140e40740d10f40751425042c0720380d19505441c155441144114100304000d818001086103102c3e1000040d003d01d04c3c1c1c9030281c42e0f41e0100b002c031800307a201d00c0810310000b51904c0403504d101008403082c4508 = true := by decide +kernel

theorem cover : BRFrame.Cov 676438848 676618705 := by
  have h0 := BRFrame.cov_init 676438848
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676438848 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 676438848 ≤ n) (h2 : n < 676618705) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
