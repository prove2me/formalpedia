-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2659
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:21:50.215172+00:00
-- url     : https://prove2.me/submissions/2fc5b738-e7cd-48e4-a432-8393a44980fe

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 478057553 ≤ n < 478237410 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 478058803 1250 478057553 478057571
    0x3050318150a0206040c050405090c0103020c030d0908130f0303020712210206040c0602010e030702100c05030a030b040c0e0102250b0c030301030b010e06010f0309060b06120a0b10050904 82
    0x840c1c040c9209481c546084640d58040200c0003510381100343c40849281c092284006407034541401414000d0031184060801d00003014010750003940300110307040141c0000c1c42118110301d6280700b510a90382c020715003603580f8280742d00801102a1250850065450119000d00120f54001130400507940c88402401d11b400311820120b81480a50389414145540d03016070701c150550100c1c0182c0106e201c2c01c0d074001881e0302c0d080300740c0c280c968540300385146030300501c284009031400d8030307180220301d2007800d00c401da0107030300d4030348030308660040c00d0360f0780403e841c0e090b030081900b0140301d10800201c443c0b909150369413401000035103030081c40740200c05440032460720480004500000f10700030000881403980e101c3c1382a80054aa8009120540e000c0c51144000039a0b503c41070080c51281c06c05a59842c2503081c003813020740050001e481e040d54a2036883d040c0c08101d489610007800084a1154249140d240c003104000a0301c5248188501442480481c0a8099048400c1e202a141c0494002c507000103 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 478060053 1250 478058803 478058809
    0x606050f1305041a04110a2f0d1d0303090901060305040615081b04110906070528020906030a1e0519060912020a030206070525110a0f03050318 63
    0x3115006281d1061070111034019040e0300b040c0e49541800181d400b84504180089103010718000e084408005c211202c10941c0c04040d9040d40a08d0580b03155200881150100f60b41407030040d1002003000440c02100c18054400b110344004061200e04800a41c549800c0f5804100740320018400d40052640310307c0031504000d6181c000400c010825401c0300d5405940d602020346c3c0e6403001e259058042c11040118003a42400d01074051a140c1e81240d1910b000003a074180881c0354881d020903200750154000d422400391002c00034220f400005124429440501d00400501d810040d08052183d84009402800102072491a9a000d885406449400901800c02c0c5081c0036110303a0904010b0394107031201041208592101882900a4030080404200f141d0240e03a6641000405009a4400d0000510440c4500014113080c1003819201c1803420501d503070401e502c150300008507a440c213600b8140b036141c200064088010050003503290300e041c2c40c54454503101d02c40c881d400f0b152052081c0030712581391 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 478061303 1250 478060053 478060087
    0x402070201110f07091425091d0a0c0315050f060c01181209030825050a0302010c02060c040f090207020414090a03080a020306030c01081504090c180606050f 69
    0x24060400fa00c14580c800040e95403941c0c441d0041001071031402083c248500d1480380302da40304140c04201d41841188103e401c0390078046615500040021204c008140d011442c108001c01040c000158001c0e030501d80b0001095551803420101010b240403036000c542d560b65200130040383c0c4140c0d12001105e8169011801510410100100035800e0243c1c0ca401e080034007409903202ea000315000700e5549044842202d49504920000e05001003d0010420501d80010041400c1c000c0030595001d451990340e945080403000b00c2c003900542d640c0d40e028503842e501446900e0b400141c1020442c0703801d0501c0c1c01100300360642c3c045d0440d070f288d0102e0040210340b01c0343e1101414180901c0085000c0c80d15003455582c0f0702c2490800c40024444031302060742101c1500903a805113000a0103401105000b80045031000740092007000c90814458080e01c1c03d1f03d651007414a994010300303018044600746141c0c0d01c0881321520741d0404146c5050030402500380e202003a0391000803a40410742d9141d2000034505103003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 478062553 1250 478061303 478061327
    0xb010e1e06040b0c06090c0904030c03050d020d06081c0e0d150e030c0d11011401030803060d021c0606080a030c080d02040b16060b090c09120f010c09181a0402070201 73
    0x4581c00280c16100c8000006840384201e0031441200c7c150041d042c280820f030b01080d1001404114414040c0000902403005043c1a4403d040010304000c84440104207850780ca0317000c500c040e0007a4000c1d40c240e080e44507070f008a4601c941417541201380b5217004034908811402c0d01500c039071043c2607038401500e0b07160462103103121310800716910381c01220745407070b150708a140740340c2e0100300c510460503101401809601010000c840d005400c0340e2a50b11078131502e500040025074480c01403c00480180e0300c80464103e400f41146440c100e0007814901141120381a81107001d0640c42002ea1b0000250700c0500c1589036a40f009291b519140340f1000c150190046400813800d171800882c00301c1030340c0c400b10030030030a8a000e4101400240914428440841030548030094500d4040020f11068200144080c2082541d64102c0701c0040c4c60300d07005800c640c42c2c42e2400d0005203010100304000c00041040300e10044114404010502e0f400c4107005000480c031800500aa402048040c1568045c40c040303180 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 478063803 1250 478062553 478062569
    0x70603020919031101090e3c070305090d05031504020c12030a0207150b010f0f0c060614100525140a0c080d09050607060b060f0d0507030b010e1e0604 66
    0x55244c1c580501060800301210f400500030240001c0e40420841419010b55070176810245103030100300d08038203200b10022400e01c029800d100f0350195207200d42c4565100703403da554006118103081c50007506105161071b023601040f07001d005209100d14040b04400380e1300340c01c42d00143c1d14120524031030b00b80004e4420407240990b02004110300502160010443e03244608040104940c0181c4401c0c121407000c1c100c640000d07642520101c3c0603010700f04c3d0903d60031941c20038070f00f03202103503459a0a41d4066004134071040b110f03000104060603e000400f110100c542841401c02034006000c101c07082020814003801d4640e00d4005051220000d03640e0b00340b001c10001c0c1c6280400509129004100902c0b4241292180304207207100e0b60303c515208001d0f034100034a03151800d415601c80e50040c01c40000c1d06503001100704000181c1c0c0304094001d01d081c01a036000410309103000311000d4115030010404505000d0004d6410304140d440782080c0c14403e005031041c1111400f481c000c54210300070b54001d41d42d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 478065053 1250 478063803 478063849
    0x51903080f030f070c0b13030203310806010e0c09010e06160c1505220801020c1605090f07051c0c0207080f0706050415170103320706030209 62
    0x22501c1000001184685445550082607803141300084440d00c4102070b018024642603004a04c41ea5280e2145102ca24001d20450741040704c0514848082140d446000c00c1802c0159103c103c001e90b01e140c02e100400480c4058861f96150514005c2d44035001814140b50010010302128940e003c0c0807030f5805100d0180580d621048040d03c0e85c000d00c0b25400c41a03502021812001403402c510640101c86500300c1c0d5522410320300c040c50b080740c0204491303009c0c103500704e200140402d86420034809014082c41b110003d01c90b015100d003a00100140c142c000c0340c02004042c0410a10110021855030031505a00e8944d42d990004d029800b1502044121120b0036130402040400700d5030b00280100560302540280c071134402100c00d000740d9500ca02e215050104600348030030011010007461106043e1800c0c01e2054444d0b0003000309044810b070980044580c200031102440501c096041074180e0045226640300402c2801c0c849107035035032010712a040805400140003182030b00e42c0d90380066850070003140c40e5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 478066303 1250 478065053 478065067
    0x9150409021c0b1210200d06061b0206070b0604140a0e011109030c0f0102030f0301030b010609170604020910051206090111130e101d01091d060105190308 68
    0x1001c1d01c6070b03011241c41582060301e0001d00b840c0c030352107100380040d80e0001462895103e0880b1000741032400907441e038046070a90740701150701c0c0d04001031651000601c07001880030704050001c1e2013810503042030380724503002c09280d03801600c540d403c44042a8210802501d59516900024082c0401d40d1141a810820b07106001404500350800000d012040c0001d00c10400b15026400342401140002a4540c4c03014280302e1060600191102c100c05061041ea4a00b014400c2c50900e01c3d0320131f91007103c104000c0c900400c52654030100120240c17905000883d55400d52410301559004061b02c06481541c1c8440030030301c24140c2503510001498081c100401c41c024855902d0307213a91003190b1305a12035080400b005504120b00c400c8881d092b401d0710a40d4106410301240c003503502c0c0004c11030300c0348a400300300c041894116104162445907840c0c594448a41c1400540c40945603d0207a41d6258194113020415154011440a054070420355406e880c142d4540c7c081616521242d0000d0002800041d040c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 478067553 1250 478066303 478066327
    0x703020c0109151b020f06070809040b0d05100b04020c0a05070f0608040c090e12030a0515030102040f0b090402090604080a0c05031203040209060a051e150f0915040902 74
    0x81405110036203a0802c03156403410340070303052003900b00341c00c000483d000c0c0110302c8604030704101c0c0320f502e0010f0115580d620500020407142d52107500f013540c03000e5011407043c1040c5480d00518020000645a2034080c0c1460b030703121691507a56000c0001c1054580800745001e0310b9030743c1a46d000150500440d101c10780107091054a902690181c031503039100422002c5040c034062400540500d6008411440c500d1a20080b41c0051050303140b41c00c201d000341a04224441801e201a40c000c48491000040c3c500b8140c00c00d03a108012403401c1400390b40180020032406032070070803d40407108403100d06642d8842c4200001c000b485001b100c5540054040390203e0b010500180316598503100d0000d034850345880c4c00c02c0682e10315410001c900002c004200040050034081841908420064a130881c500e44402c00030742c20809070114528141500d442c0c1050602d000c2d0b0f07580b40087c103002c100524001c00f50301a04200d100b80190f25014500c1c00003002400c0403054116401411164000c64542c0ca00c1414 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 478068803 1250 478067553 478067563
    0xf050304090905010b270903160c0501030e010e0606010c030e030703060c12020906031603090b0702011b052502270612030c0606010e0604050301090819090b120a020f070302 76
    0x815210f81d072a144485420f810140c0c030755820114124511480640455400014140e00800260b680e00060204a00441c00c004440b08114840ea941d201d030a801c0c54001401c40c2c2001e2011482a17041a050301d50320000490a560055800c0c602101045040d003170696008401c20b02203505482404c60020a01030030b640204001a070682e1800d941c800d01d004110285c1c040c07d050603031b004104102141a402408484106100007420042010300e40ca0300c800c0c500f01421103d42c1e015035112807111450102100c403c400d604114100b59040981c016400541071900042188000c10f1500c0114259902c8401500059085d01c031200e5007040300304180441101b055a000d80682c1c542d4080e021422004001d507940d518a0800034006a170715040116010948150070316080b01d030420010407170740c40a00a0b035400038000c40030380f40d403403110007420901c2904040d0f020f010070510300c0b001c2c4083d031200d80840300c1c000030752a191091a25008140c000920915160340f81110000402c401050340202d4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 478070053 1250 478068803 478068821
    0xc03040521150c0d050a09080703020d081e010311041404030306050a05100503070309030915030902150f030106142106130c0c020618150c060717040b040f05030409 72
    0x984030403000701030b2011021401039580d407a07005030500c02155001416481075920001d400808202c44006131a0703800181d011440550040c7c0101c8005443d4035002072803144c008080c000740e520002c10601c22105c03e5403060000900207204404100c510350744030b412202c01c0405400d458410f03810146809802441c0521a080c0540d81110000900380b40a00007084044d80f9038403680e1850303841e28011001006145021020b1200c0c0044c0440c180301a80b03262002c510f4a078400140c010118010032200368a40c0c018084450700420071700c140c11070184182c2c1c1c11100641070150b814034610004d00703101c0c00f46044102038550031512031104034441109280c0240000d880b8840101c22188000080e1060b4241c6103020510440ca1103005090880082c002c1c402d156903810303482210903001640340921010125190f903c0441e594061500074840b85401c1240b42c100074144614131002c81203051402400900314441c03840002c0e0034411140c2890582d1540a01900d60701c90b00d9482240041a04903 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 478071303 1250 478070053 478070119
    0x30703030501060e090112170d1a03010b0d0b041110050301060f08090d0e060d0c03020c0706081e09031c052d060d2a03350c030405 58
    0x1442070054541104061024011005582c00d00c1c107a003c5081c4807031411140a42a1011280e001e0100c2c40900068821400c0200b13a0086921120158010152b0020300c281d1402c00f070003160750b60340711203d540d203548649143d2240e502d501b03040074003914003607a03907400c65400c168244160758442c00031410384049854440032030740450f10441c1d06003802c40340c02129500120001c02c0c0da50250500501304a80100005d14040d814000c0005a58005000801098020031078011342c0d5014042c081c040c0c00b4030300e0484803074075003041030087c07042105030000c0c5c48002e4140405c41482c3d00703204581c01c50003603405412501600640107401414220760b07884020000c2400c42104c600c0e011000c0c800d12601d03015900a6072500c00800180002009003100c44110064041003c1e4030183e0615840c41d10481100480310328604001c0d4904003284010380f80d00c0d1340801c01086080440c200d11003d40750031281d00361550401441e480c034610480d0444d0f5030004800da082d6400450202c902241c0c03204032 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 478072553 1250 478071303 478071311
    0xf03110306030303010635190b09010b0d2901020f06090d03020304030e04021306090b12040b1512072448060e03030f040f0609080304030804200d1704031403070303 72
    0x104900b09c48240d0205540961001b0040040308a85d1001c0c0140d500040c1c00020036100d4480b902e0005c2d410780b0001e0f0602e0700d120b00c8890b99507805000800f1081e410f0009000c05203080c0021a8451003840103810905502002040a062050208009208001d0006c41d91400300305c4240144c0c4080744620000034500d0303400411018858810f8508105526040108548550b503650310b07244030040203809804040101c2a100d95604605a039168540d5005005583d00f401504c1c4c607102c1700c03c40103031000c482c00215200e1080c0e00803940c0101900b146c084460344d02610003d54040c060304407001c038510503c039982100011880340600341c001c1c0f260004001c00590002e00584078041180c01070640c2d41c0e21000500860b41d130480c02e01c042c80c82444005100b40c2980c6e9150340582051301c0543c0006c44050070001080a1078074018003103d00030700c0c03603054000003000048030001d88120007461000040d00c02c5100348404020340d07028580c440400403001200e0580199660401107040d0006820 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 478073803 1250 478072553 478072591
    0x5160b0d0b0303040f093b12030f0103260a090618060512100902040e1501021b0d0c0503010c050913020403030917030702030d0f03110306030303010635 67
    0x10000c01c460448480700c4e405400ca61610286c40001c014070034440351a46011160900003021440440380710411001e41410303050b81440300d0a00c0d28111000404d018002001440359101d807410b019811280c0c4100050021f00c2030201c49080092055080d00721150301045d00349040360480c032144150380a5603590010718601c8407401d00d25600c18403640020410411500588020720b200c120340c0210301d9002001000e0741c480c10907040364003a0707110000f800d4150b4180612044030112212003075809100801c0585029101080c1d0301a1945540d441110154001000c0042d220043c000078800107000300412001404007034581d91000d40c0661107202c1c0b0010400c8002a03074400c0d42c0549800d40d440541e00d40c1040516441e40c0c180710000900b901c4184840d9005a800f00003041511050751b840c401d160803e190050203030b5a04006010f000801481040003948000040d241124030518104c40c95040c000080301940002c050b14604c00171440d4107600c050b01128500c5070040c1600c0c24840d1031512 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 478075053 1250 478073803 478073809
    0x1504050606010f0c080f070309030f0302010c030f1e050a0e150106020105180a02010c06060b071a0703020c0a020d0201030b060c0f07050916030b011814120a08041205160b0d0b 77
    0x2842d004010a1045c0906c02d052000000a1301d4240e1103400c08100d13694aa4558802c1c030f4190100440040c3e4540102079441a403601403410300384d114803401d1124114044012520a580c0c035078806d0115500e100107135000c1c100d0380001512191070003d0303403c0d0341290f24140380d1500c0240246400341d0b080c503010808020003144014455082080a01140304803540110b076000e0203080c2c1560700988401d03001c907210303507034000911402e48502c5440000700c0b5003148401c182400108503d051602c1801007050f03060300440d0701d4144541c101d82c0425040d0041c801a00100b00c00c6c0c120540000700032906403003400300000c0503414000c030744e070880d00481d43d20010003005502c1111b49a20020f0f00641c0b60744443e000360010040014141012030a42c07201501c0e0302d5882510b40c0c041c8600100c0914140e0081c01c098020410754143c50f0702800c2c0d58922911407910070f2280348540c1e480c0c0f0340b090f00d404040c001c0c2070060016400622843c0c1c10415035400b00e140381da03080300d422000440d150504491981c6 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 478076303 1250 478075053 478075067
    0x1090f0f1a031605210108010203040510050603070b070f170a18030c0b0706060806070e0913021f02120313030f080910150503032b06030b040b0402031504050606010f 73
    0x1941c040384108007140c0280840d01340e0881c4401c018030458481c4a01400c0142c006024040d14060000686924050400c40d02d09030442e081c20014910340740a101a40d1000b00300c91096480c00c0c2d054070f80c0d60407545480251400744c0703c000740106004180e01406011044000c2110000e19640d0a0b0342d00c005280e04151100305110003030020340042002c01c9103044020141004c0c0b8081c20000800a170703644a0a8208502101e1480008108881030b40c10380c50700d1381030b49401c000421045518404158003094142c21007000c0310400100c0c041c80e00b0b090603c00c00c40c00c600b0b00c3c8200d1100342caa04202d24420031b10480c001080780450606050020200d01c1818540c0c07080c00304100420240002a4800000f8105085444030610900201041d142c80820050000341d01003002e01c0b141c824889141c4842d000404030b5004464180383c0c081021404288a441d0000c0e00060100c1e003944641c80080c2c50500d216514401e4807450000300414002d0104403a44102c20a1725070224400300380300201c40310 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 478077553 1250 478076303 478076311
    0x90213080105061c0302240105150f0403111207030f02090c120420180906010618050402250c050a080f0604060e03040b0d060807051503070c0201090f0f1a03 69
    0x1c002c0c595103001c0982c090b13520040c45180240180c81485000a10914064882c00e07028404468800010400303400d0010002e0101001d00f1801c1e0704206035103ca10300c45100b0742c800548122404004588030b0b176107407a200025405c03c41c046030089940e03460440308010f8a41405e9200d00c0204002035450142030049500c00f08081c1c100e6891950340340d80c0d0b8011640102104100101c032041c40b102251034464446071880c1720802600000e1602004080c40d10f84141c110204000220b102418000442500c810540c0d2007140e015032921003a074150030414034040e400c01c0580c1e01c0100c992007800400b40030682603402c1070300d0841e085600d442030281d85126900b0070300c030241c0c270007070004010924540c040d419000c11101582e190541ea0742d8016896085076414215407031342c4000c02c200b402000c00c03019009000503510000202903200454809000051160301408a01642d0700300b1607114030740410142269174503c0c0e40c5241c41d140941c0c0f02810074002e454004041d00c00c59001000310b4404d5902c5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 478078803 1250 478077553 478077559
    0x9030606060f132c0f0a050a0b040e060a060501021207030c08090d11030601090c20150405060907120c1707081605190f031709030604030c0506070903110d170409021308010506 77
    0x42d42c0c480c41b4100340208030040c0720b8160349960301110000ca070f48030301903130000001140c002e0025040c240086021102d0070f900c010b0640d03000c80410035003003d188082e525000c1e01341c1041d02c2010301c01d04180c0b0045c411030700c40c40c2d4017203142207850303040200e940b07103510724040d068007241e90326a219140e40089a0811003660040340e040d01c4200401e55802560304030030001c0740c0541d4441c4d003225a4004000b0f4041d581291150011405c103d514003040050304002d1100700c19401600c1e0781900d82c1ca0320882c4074028090040802030b8007080c1000108900c1008007940c1c02114404d050049100c8000c0c1054010103102c0c207040e500300720b0069040c591520944000c4510010010711390b81e180f6061101e1103104003408078045c0300b0211641d4061101ca0720031030013500c5a4120707808601c0d00c6030522030010901003c2c0540404140b004c10300c0e0302180e00c0b0b11281901e480301100780710b0a0000214051010074081110009030210b11701c3c08a030040c2c406400000c0780b45602035161513180307082e22000c03100150 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 478080053 1250 478078803 478078831
    0x215120a050603190303020c0a080912070302010503061003150608070f08010b12060a0314030307140715050c0c070f0906050d0b04020103110702040e0109020906010509030606060f132c 81
    0x180c0040300b070925845241709080c0145440080e4200c6810000540c40c203030ba507840046021011402c14021784180c428058000c0c11501342180c1c0003070800e000c043c050501071084021046090350090b400041e1000c02c140c6a0856240c0d02c12008160300c00c2140e261000a20355071400c4101c4d4042d80f641411786e107140070481d05200ba10103950811000c01444a40e00401a54001011600030404519550b582030050b40d51b924002c40c014205200c2c20070040040182040f10f1780104071034032801c203000d0380030060100d05901c407000454a180540c02117601680109400041d0f14101480a50229010014140482c96450041222034000550041d01040c451000100158446d5100118a00d201c013400c60904842d034010604896505201080d40c0c0c0d5588540b10951401580096200000b4179103246002e415401203503d500c0c0141604d8000d00d004111f600c48056a0700c01d8580080c81d140809024a94464120310246c0c3c40c00c0b0042c0380041c6508242000790381c0c0c0b1001c280f1030072220300c00917 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 478081303 1250 478080053 478080073
    0x10e010f02070b0307170408041d0606031f15030f0c0206070f0305061f0e0102011a030a0b04111221070305041712180a051e1003090215120a050603 65
    0x200f45580010512010481d185040302c0b041281c00700a47d00413805040c446485504220744901e1561040e0030342c0103c8030070a001c001442d55548112540070008540f65006030a80511090b0051065002400141c502081c9000c2c142c1c0e1660145190300d038061024070081014810503629048155904400102246820000d59001c1d030030803500624082d004003a94812541d0501c507100600c80c5650000304511002c8a0640c0c1c24040c0c10075940c5038103461241200c400000035510501c154004100300903610024040c03204c00ea00c0712003400c1d07003c3c060315080070313014660a8a030300110840c42d50030041c05114603203074a001c8050780c402a500d40c1343d070f038601814040b10b40220107207514504900d00c5441e141c59000c1543d0009800304260403c9941541c141d600100400d01c0380d26008140501c40761507541581e242c00006000e00b01e50162140c11400c0030b080001c5024040318000690003109100603842c980d1014402081844807400d20005180ca5140170181540c90503107900b81d140c0c1c8440980 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 478082553 1250 478081303 478081319
    0x21f08070f1403010b0a0f020607020d0f050f1605060117070302041d1b0f0301021e1b0f06040b0705180105030a0207150614090705040909060f0218010e010f0207 71
    0x5400c1e800d181e040400ca02c03a0100001e841c00d83c0b007600100c4ca490404079241440e02d8214440d404c0b5144140003074280380c9042a0002d5803108a18291801c210041e40c680c1d200600032001c540354240b02c448283e03614480403410146200f420030301201c10340301d200000500d51520459040c108507496018011552135602004003070550b044a489108650320700c041c8448400b0868451404611241703404544407810401006c4030314803450354040d900400010f00e059414041c40ca044520004182d074841c0c03040c03501100b81c440d8803078421400703100d110103280c0304100c0003800d54400d40c403450502259a54444048409009400351404104840c02440b4190f6024502071544216070050060802e9202d07252801128912081d14480c0e0340d65440074804180c1401910100101c00d0f1281802d9040c9044c006005210701d00c601c01e01c0a60b940451802c004040c0c10185980c10016419919407441c0c04a0b003064100c1c0d401490301250a94604000300d500403203e40f03072000c13420f401038a204d600d08002c0e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 478083803 1250 478082553 478082567
    0x16030b1506160f0224030a020a0e0310050f071103092e0e0a050a21110d0501021b010b1302030c041d040302060c120412021216021f0807 60
    0x51503400641841042c0c8184a21915103040500484100b040450140140812400090908034a04141001030b11410502004894108041103401642d800c0c0c2507030101c6008010300070160380342c01411f03800d4405000d5908150b004a00c1103046000316190b600741074a00d41085540c50825400c1403180207214903102001d100141d01c813201078500101c01001c00304040b240440d0010201c0c0f8015103c030304500700301d001351001d440280c0b4158071082c10008100540e00c0c4002d0100d9070300c140f0010301001c2041c0e91008000c0741314054519659141c0f14504680130790840304220b0200c4c0d0002c5002e4590201c140122030368030300b000d0503080310102c10302000c4000c0e6000901c03850180b5010440066013035010544030040e46c0d0304035034025040c102460020f05116010309044039480090082e16039428007072203601d0700716a10440b000081d40c6002c506a080207030100c2059121000801e81d0042c0041c144a5098407610032900040070301d40c5000b0304800c0e1010200c168000030310800009a181e8040c0030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 478085053 1250 478083803 478083841
    0x615090302060306031f14130308010e091c050c060a090209010b07020105040305070b03091c020d3002030108010c020a0c030f0f080d02300c0d060e010906060216030b 73
    0x9581100c0f103019501c0e0001014010743d030050603600c919407e0f40c1d64041c0481600407038411840000c0c42015100101800e0040c020035807141030401c0850071003103080114021880c1c1c404010384c1800c51081c000780c06600070403051801801403c00003003203880c16100701151603074010580c020341e07400c1400c44c040ba60410041241030003020880800420400c2141c28000c0841c0010640d80303240c4030a4079400e22000c401e01000c802401e441c031035103042c0c0100354030540201a00e00703c2c004401d00603100150b205140c803101045001d40011103401c5000382c0003181600c880c1c0000b44082603c1d88001c0740c1c2c80c0903114000c0c0c1143e0300700000740300082001800c0c0440f40e005012a110190321904c44070810390140c280b01100540c0095114542c160300c289140303030340409404500a40c003e0000c07040c4050303401051b0288a080005100b01d0184a541c1700002801f00c204d4024420368440d28450010106406004054410600d80e4a04072280c129100180d0754403682c9144940c94400d900080460216 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 478086303 1250 478085053 478085059
    0xf0c0312060f09050a0c0503040f030518060a0809060601020a030909110405030d0f0e09040f030804060f09150e0f070306020d0902090a150902160f050f070608010305010615090302060306 82
    0x100700001e801c0c800424040241203003800000d40c908107640e000301103038041c1584005200d01030040001080750b405200c0f0b2a01c0d09400c140f60389003a05200b0b00318181d81c40f00c0b07499100d44d012901400050b4009507191040701c0100032200b03075480b0308006903030301d40c031200c8001c0010350030001c140300300d00c102d8018242c0802d880d400030342270607129030019081101100d09800018144442600352903841480e03a0300950041d210004503041c1921205c20982c2e81080c0681441021800300e4108035043c0d000514032001d6104c1041401407038500703040c03110540c4441c1d111981c141016004107482c04540c12202c0407000c00105841480c6035140c001030340080f84002c0d1101d540d500400096240c0301c524910455130244d0010702c21207606140103074260550007000f8030a10500a0199502813040800080c941010089040859030315140c2d1030944c11704110b540d14040c103c40021401d40140e402130589100b40b00030b0003000e8858041ca002c04660308180700000b10048401c00c05802c106c0300030b540000000d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 478087553 1250 478086303 478086311
    0x50406051b090120010203010e092e150305030a0e03010f0e0706080703090803070801090e0109051f0b31050613050718060e030106080105060609090c070b0705040e070f0c0312 77
    0x134042650890700700368815840300b400ca108000d0300040c00e001070140740c0305a030a01c03460806004a4201080440c542e0600140d030b5804c4551048290f1013041e42c01564000101c07590755000e440000c3c0302c41042c00c0e80c05e00941c208003015a40b60300344d0081000b6220418001d19243d49005c108030f541c42c8010748400189030362042c458001c035411340d008611a0804c3e40702c56823154500f10501c0200e50072070842403d1a458106001c0009201042d2030341b481981c00204015010384444841c010061040aa5440300b4942441c0ba40038018180c444200d652a280608070340001764038100c142c5400b20380e52984058a01c2d56003943c1c0140e40e04c980e400006901d490b07070b03210072850140e034440031003508540040307481421615501d10b802d0056501a00512000380701d182044401b05c1c41e64080c94010600c01c100003070001d0150249201550780c0d07280c02001c2e0103058140210050881e5120703000b000d12001e0038600050203070b40204a01d01d0085442d82da18081c48140e510100c46015510301004025511 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 478088803 1250 478087553 478087607
    0x215130807020d08070308010e06040e1b0109170a060509190312180f05061e0420180103020a06110312060a050a080f0c0f06040915030b0406050406051b0901 69
    0xc1000d0f2070030342e1180d11447d22075418500c0c510040c110007030900c0e104505200700348503049000b00d60f41000c0280f440c4403514075105070f00181d80c03807041034011150618004020418480002550780e600c24000d00c003c01c92034070b6429081f61100744202000110701c40740402240082e218082d81104060301100000e0360b0200700c0342c80d040c0c0030110bc2060307502101842515040c0312084c40450703003200048071031600e5082c1c6041782138034500d1b0080c400391a06051004032078100025030590110b6040c0100040e1100640c507489510285082c0801da0041d56118004036410740076450100d04c031818400210b05000b2110000c3e45000401092180c0060f00c03800001601c1e102c140b001e1001d0315a2a0151860400d068051072404000b0420944110302d00b5224880c191241c404603025640d10f8000807640201c82141440000b0036580024200b00c0480e04110030f01940e5803129024500c12801800f00e81c40e4480000b1140d191780054000c001c800f08400c0d01150b0150305564060301d080c0038031b408150700c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 478090053 1250 478088803 478088813
    0x3010605060a05301602070815090724030e0a0f0204020c120309010e010b041104030b0405010b060703030c020c0d020a0504090204141f0618030605061c120215130807020d 75
    0x14541d40d00c200c4000109003400704201490300526410446071000300081450441d0b08c0380e40e11440e02084044903014000b003000c1800a01c40ca8025014900c901000840300b8401402100140180303980041c2c607101c0072850180700840d22940b21901b000b0135515070180354003044025031102d18180001c0c880c80d1480002541c0d0540034602c51103c070000000d1070075501e030415094860310140d4078032031440c141010f260005581e09039803d42e500520010f2148d07860780f800900408144080c2640082c0c007144c0300d010580d0507000b25400d1100b540c00e440c500c001100074020000d944810003903200040103814041c1c0d00b030a40c002c03842180000c2c0b02103424440713200c1421070508152030303044031841d81614240e43d4445425042004103c546440300552803119002548a440c0e808002c04294868010404a40ea18500e858401d039050000180403000c0c0d141010601a8042c00c603400340c09009160700e1007925480105200341c3c8c06201d1f0344a60310455544211507070004804a80c4402d41c01150742c081a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 478091303 1250 478090053 478090117
    0xc21020d141c021c0207050a030e0616080a1d01020703021302070c0b07020306060105040e0a0b0d050d021006090603030c0b0402210d120207050a0b15031204050a0503010605060a05 79
    0x3240e80d000051340c8600061621411000450300c076003840703004000040004600140c5203504c19058600740303581c2d56a0310000f404a1148098101079050640e001c0c00500c000e11700203203800d03070441d03d800801d020f50680c03001e401110546e5150141c4c101a41c20030160a00300342507289072140620040c0b400b1650f5407548052a070705d8021358188800401c50340110300381002000d4204a0900b4014101841c10b01103045126000b461141c03450785500380b040b02c40d210440e040707a0042d4410155007603a00d140b0130082d503400d0a010324810290429a0001c0c01030baa41c0b0035071055a406540304c5481001076250b00d103e0f0400a03100b260400500020b0044042d0202c1c08203000e600ca5002030180e81d0200380d4024800503212030180080c0c0d10400a400000c0d1000034031404c2554400007180c150360343c20000c503401c642c1401040381c050292422855440d50510024001e584040b90340010154803001031500b2100180100c80d00704108105042c200b134001c0025112000e208880c8545080840300901251 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 478092553 1250 478091303 478091347
    0xc0709050114090402060f0d02090a0902030702060114030a1b050a0f061d0916140c0c030f0c10081503010f3305011b0609030c21020d14 60
    0x41580d0300d0041c894600003582500d100300003255049901c2c00c00d50005039841c46a42c1100303061190010b801146009940c0580e50304680007410400700c0c40c0c0d105c601c5c10281d4411507003200140158030022030b0241e1000f0b407008080c0d6000c3d00900300000300b903417200051090070151045001c64071200150340d503521070000000d031102641c0701c0d883c2442c00101070410b10403001e0b11000d810b031108402c0035a0310355030708065101e04a014620404060300105403081e0160700001602080005042c0300d00180019007155001003d400b03d0755920324040c1d01c4c136140c1d90904002d41d0302c410300c8841d49081f540311f248120703000b1070000c0504202c80314620001382181e2980c2c0010040d50703169420418465a1040303822400d0a821405141c40d5a40c10302003006507645000c0c55040c45074082608810100c68070a4103a450350140c03040152416a04020784a202c1c050000c86151403201e1540007120302100303010f006a9515002440541301c803850903240c280a400c2100626070b000d2040021510681c0f07880d01c29 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 478093803 1250 478092553 478092569
    0x60f05010807031202030a02190807021008090706050306030c0904031106040c03030311070f120306090e0f070b0c071512021c0506010504051507020406030f0317310302030c07 77
    0x40b62443c50b18000742199200c4504c25034006000301e1441c01c0d0081100354541208449134881e030741c1d1502c0c14800c0c9000d000d40c06508101c40000700e50809800c0480b00b40198071210890304180d648450858042c0b104a8550382c254116049004440c180082c0041d045071090a140444098003a580c0d80f42c0b80c000c840642c1c2003101d030f5508005041c0c0504c41c08182d5240804000d181c20545d4480807200c01d08120001c203400c0001c030030501000d11030751100001d400761380c4080c8003082d000c080c0d01d95a401c0b501540c2c45207010704a00003d010030124100d40c5040c50b4074014004591400c03440b01d66025491503c2e20a210308064021429246031004084120361850161500301e00c0507035800813a4401410b55060000401045c0019981c03544040400d03c0f1001003075540352014404980035000b1a8001802d140c2d040840030300705034016070b002d180d40038807401d001690398684031110300c1c007140e090600080c40c0a0b4040d600c01c0380b1015110292213402401140e244c400500c103410310742086503011142c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 478095053 1250 478093803 478093813
    0x9030a0609060c08040b04141204030302100f0b090c0901051209010905060f06010c080f070204090507090f050c0927010f050a0e07050f03100f03060f0e06011809060f050108 76
    0x820060648581100f0619514000b126031410380d48001e11008040e10140c0041d6425408a914950800c0580a10344200848a4a50340c1e44d01c4c021756201d60440701403e86605211740b07114101c255114250000a00525600c01030301c0d100ca4020941d4014502c090400004001043c10851036000a42c007800405000064000301e034203041e07042500c054144406426034506002045e0390091b000101c468202c14820741d1007401489941c0d01c4d105901c1d009412a0404100c04140300010904030f0031591b045009103d02030304540403000b2510704403903031a0403820a0040705800e0610b2a0154852a00005a0041e00300490348014204509034402120541210420310046c20300c107810600130448006591020305001c10301600500071520503080e241c00210014030700d0340075840c00ca001405030304511004941c9034201100070b0f060a800e10a04035091074440611014001001d034120340c00c22081c16003050007011a01c02400e100c68041c1e42e1240c480b0341a6000c031460b480307203d00070308811000f00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 478096303 1250 478095053 478095071
    0x50c12070f02120616030b01110610030b0a0e0d050703030902090a0501050307090b0a0e0405030d090602091c030e0918030c0618070311150408030a090807090608070e090309030a06 79
    0x1050200b070240400f511504820144403070682040499000014682400304a803031112004a0744200920035103401803150b68280b05034850702d1500801900e0107012060780340c0d034814000005071071300c450904626501412454810314411320261540520903d0040b4180300c4c96000118251026030b580da00807540d440040180386030410070302008022179a4284003030042c4800281c0003500341e00c6480c05c4030302e80d4400078041000c24022161020f0044030208a00815414808000d40000da5414004c1ca4441806500e003620301405400441d07141d5219221590824140003a1510240041c1141d485c020806010a0f000f030000e0010603580f07000504961509450b01326101151201500700350b0040201440460078a0721181e128501c10b0b1400b9001140c840755099640c4602d40c0500c905000100340102c071198000701e2481111054000c880e03187d61a003410b00100c40c090711130442150301000c0c0c1000030121044a9035804950803058a0605980d480440d0606500036000c40b24030b0780d600c40c02 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 478097553 1250 478096303 478096309
    0x2a030102180a2111010306030510090c0b0906030a110c1209030114010e16180e070e09070f030908040e010608071202090117090c040e0f1b060901050c12070f02 70
    0x40002c06414540f5544001c44100b4109022242c502c06403001d00c50120025443c4d019400c148000c42e408012295442c0c0071406601c020718080d64103c40c0d58915820016113071041d402540c4151070000c000a14544804040d2001014540181405e4400c1448014240c200078800303400100c0e18100e8141e5540c14840800d800c5402d240b01e05464509080010b0241c804181141948100c0703d04810401904900e01506c204183e001c464410343c00404000c9803e906541e0700d203000b594640c5420551858420410040d01401c68214001801049013440014403039000000342a000b000d41030b1034540c4402d085151924241c02207c08240e0890500ca10240d0048104140c008000e02c114205040b81c00020200d090350390b603440011115001281c64400e040c0070782107900030300800401a4100318400a502c031b80006543d40114002c040f1540404010080b44c207000701300c024017080ca031800403801581c494016002003a441c0c40307018000c844901008001b0100709003e12501c0032902e0f80d0b8410 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 478098803 1250 478097553 478097569
    0xf0706020102040f0b070c060c0804030204050a0603020306070c110d0c03020d050102030708070201290418030206060f0d020a0302220c121b0e06180901150906112a03010218 76
    0x20040380a003001b100703002c90000f0040784180c1c0ca182c41c1103203a006542c01c008419000301e030000b0754042d251409000d584c103aa40e00c40340840e4401e406540e180d43c0e81c0002a41c2007030101d80094000406a444600245003910000039150701c1098280e0150b62240c01040c17812803e58005c030b03496036002051103000d640040c050f5034002c007684024000804a0088401c40441105010f04448545420042e0039515500440801c59001201c000001c2440c103000350344500c01e640150040710504c4401354942045060030400b0780d006891070038107901d141e00b404640301c541425142407c503045403040300c80c0c6c01802440000203281d91646c0d140313149901204101c031440c940c021a1800017030034180c9401d42191a032420b203007045906035101c0040c5412603220315134845645034084000e00c008540f00d08918000b803403d4110382d40e8500826102d06040d69868100703040d106040e803100d131081042e0040503c5500740e4015141070b002456841c100800d09a8011a400b20070a0fa155040e0303039200e041c0070762 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 478100053 1250 478098803 478098809
    0x40e18010e0703170a0c021e10180b09031608010b0a0e0423030d11040e010906030206160627140601060e011d15030411060a0e01050307020f0706020102040f 69
    0x944070203851135980c2d9280c0608982031041100001c200400d90354000c0111000968000d403d04050190b01c0b0340e294030043c180f4200b181715a00340e09011291905c541c8000c000403070b0101401c0140c6003001128140c40c1c000aa00340da140c49403001e030b4102400031181d160000c00b04140045010580c54040002030715154018261022140003004046030220302801d484410a080301b040d01c15903811010308622407004580c0c0c82c14109010b0b5001c891138031008000b100d88411356205030784d88417000c0e0f04c29110540300103503101ba001d01901c80001c4008010700d20032440398100007542c80000b10b21002d10100090b910095440010300c2c90140440141000d2200c2841c2c00500a507604145002c1d0140f4015000c00c2d0401285441c21030751310400115200355050010441c0743c03101898a005885c541c0111000c031100c01ca21044000c1d1401d14509442c08040f168480c1c1c0d055105007001102c43e86c00c01040101140b1131645440f40e0389406000f1000500b000fa030015a403917003411002c0c005020a0740c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 478101303 1250 478100053 478100081
    0x20c100f0510050108100b04060e090604060308040e0a20090f030d0f0c0305070515061f0c0f050a17090a080604020307050402210c120106030504020d021302040e1801 73
    0x420080882c5445540c10256502401c1040e074644801c0044045613609410450000c07600040100e03886401103c2004020012210070210303958003024007080c3c0d00c00c3d02c00101225414001840f44142c0f841d036456000c14004000540048584082200842c0b8244071906001000030701c5e522600341401820112a4181c004000702c11a00c0c0000344404690801242088103582c0c0000c2014411707030480700b8082d040790171030b0681407120800c0d840c1e2100030f44160b84905c3c4501c3c1403416481c104105446036420640b2034070b500c01d9503511010411841c40d001111280156080040084d4450b00301001e0180e0095085440e40692011300c40d100c42260428a0b1562207102004010b0b600000c802d0151103068030b0250302c44629092164000310941c049003000c54051003000b0080c40008050032251001109040b1203907030ba5071080d400c0f01c0054601075080b0244840741d40250803c1420f19200500c4644018070302a0380b0310403100c200700f041c0c83c10b0340d4a42c0d0850b140d000040d001d0240c919901c0a00e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 478102553 1250 478101303 478101311
    0x1b030a0e18150402030603011811010e0909150c0405121b060f07080904090b160201110414040c020319110c030d020d0c0302160303080a0606050f1c090204020c100f 72
    0x1129503068203602c4407001e58480c44e0000300081c1292000e4211418078559080c0094a4580343c0c601102094035640041d070020301c40a0a03001e0503e46650707428091002d00000d07000c0401440c5411040711002405110682010080001c55880d6001c2071265030b694040030f40b5003444011031140c8210740e12100203100d0f01c428044070145610740300440708896441401281d458000901043c054029258050316042c0b615080000040302c130743c500f0321844580e030300130000031818030f0003403100b030142e800b401424001c440c0c010301990070198008100d003d070303e0044a0134500c80c400b096200184180c2c80b0000241c039076002e200e20070010007120341041400c6028000080750740c0e070000c0d580d1900a030000c1c02c02c25900f000343c09260081c00450590700240e600000e1003500c0f8117001d010340d0020746850722407500d400c400040f40d601c40c0c5d060f1070130b14480c120500e02d420b03900c2c11850f44403002540c4104001d81d4400702140160346510003406818184405000520840c0c8400f004498004402031401420 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 478103803 1250 478102553 478102561
    0xd021f020d0f0f030f0b09090a0b09011a060a0207150201061e060206040b1e040f02090a110a0f050c0109060b011706060d09031709010e2b03021b030a0e18 68
    0x480c00d90420301d03c03145000038407229180806406400d01c3e240981c0c2101c503000074042040030104031070310b0560007200c01440c0341e15814402402ca803280305401a101d0f000c0325101e80e40f440c09030010f052132aa284100c03100140c441e041c3d44141c481c00140c40015030b64684c0d041140b00e2410a280030460110200081600d18002d006502c84100800c0204000e200c5030020304982c0060050741184004402054030614040c42e0a00703203024002c0b0240d03c610700990020f20782c40b50324000d10717614140c50207910341030010120080c1c81c40c601e51920801070010900280111203801d1060780003c6010311004120200b0820001d440a90311101000550000c5010811552955001c46656202d41302c0005a40d207254141100d140c100d0804480c4080240018400100f40542103c148145070105440340810307110b150043c0d42040143c180704c541030032005114403078025800b0b08503a40383c0c0c141c40e148885c5207141e8182036501040c04840403450180084101d800c0840c42000701c0d500065099140d810 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 478105053 1250 478103803 478103807
    0xd0801030809042007030302030a050c030601020703030e180411120d140a050f070b010315020a0e1e06070c0317030903121f0308030109110f04090b0d021f020d0f 71
    0x4940b644550159440e18100310b80c84100304c8024241c50b402140d0b40341c896442e86001400f0350b0003540c0d00c171012428607010422400d2141c04490140b48141c00912000d45156003e581504c0f0b01e500507584000003425400d0584100c44a8510a40c42546224051a59101000420407031003040d520158001404a006160042c502d240c051103406100754491540030710481d028481d040480030000e00200c0d8810030040305410703040c1601d01ca40180d944c20b0036401c81c1941203004881c504070000340320342d541200301c0c20b015828181c2c070300d02051002c4501c020b2002061480c1e112510464100d034005008006010103c4540783c80000b05d09202881c504207900959640d010342400c3c4402600554080342c41007516089007a0a421032030465541103940741000d5078150024403803400d207181449a50140c0d00d55000480306240c8510040b1420f140c240351030500207200117042d19130440c1c08240c192001d0f95426502c141c0c1011014010022440d140c44002d0524802e4402c10341406548859802c88035 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 478106303 1250 478105053 478105057
    0x302120a121124060310150902030c04050a080d0e09070c30020109051510030f2907031515050a0c1401050f0106090f0b0a0507050106080f0d08010308 66
    0x1101c0c0307810600091035440c000e003040c020210380c3c91140c2c40c8420703d08154858000d030314480c11086007603d50600794043c6020941d4410424440c0c18507408500b800207050030340c042e681045441c440507044c21b884101042d01d0010b240c20030380f144d50009111103116940904c10085501c81614039204606025101804030343d003001d00107001181d081007049061050300c0181c03c03488040208500040100f2034064020701d41000c0695182c014034a01780a03c8078020800c60280440011008081d45075031620440c242e13242d18215003200e001c22000c602400005460209591681d540a0320740c18480409030441e00000c40040c0501c580c0f08040140b084203402c3c00a42d40101c0c00d00c3c940d01c0e020000304540200000c0c200800855032201c60241d5014158002407081e0a41e000d140e80d50b03601c406007030300c1d4440c0d04d10541100c0c00d000d40d410701204035060090510140e0742d04115050644e5540c403282540c00b241c00c515160350103030f03040031102c2000300301d134600346402410101481d5045441c0c3c202c01d8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 478107553 1250 478106303 478106333
    0x5040b13110d0204020c010635030306011b05012a022b0221040e010618060507060b21010c0309051b1203030708060a0501091d060609060a0302040302120a 68
    0x99404850b400c0641d200c58048a01c40940321008100503a1141070306000107044024180c1858040300110101c4031440041c00b001c041144c00542c215501d00004403480300305004400e4503950240d40c00d20000320300740118030440f9144480340c4031812081520880d100404e0242c401194002050300ba00c150340305a290060310304940c1010302c00024140240c2c54000d03100712080081046036060099900d1400c0900300303503454000f41d03c2190740e03240700c05c0380c104a0012000a40c485004020030605000304024501a4410700340810105030400c0000c0901c0c040d005e00d1468081100ca07000c2c9110400c0c490341e000c45040c5d0600b00683c103140e407602e554503402d42d528820403040c020844001ca07034a801d0048500107990044940c0c03464498801000581c1c02d984042c06104001c1c0b01007110340c0210184c809981d0380076240000403002c2080c0030800d5402a06213a04450204007000c56510b56a000740171100103a10050390f41c510f54810701c50704013600c03020220640c001484410000b20b030000c0c46030391 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 478108803 1250 478107553 478107559
    0x14032109041508031c27170406030e060105090402010203030c1c050c0d0e010c05070212010e03071b080c091501090f060507030909050903030105130b0603040f23060c16060f05040b1311 81
    0x1e2401b60340380c10304404e00032210106449401180c0054440d5040c0c128060b0207043d40103852103a43d80c5d800780030a41c0c00998000340540c0050002a02d60347c03c020180018041c910001c801c84100b00b44000d045070401d564114030320700001407900c1c0601c102e002c1c0d521502c034030b2002000034400038071000303069004100e4028410044c882060340308441c25002882c0c20700c0c88000b56540c408051600d0700080a1400380c004032904001c000048070240031460082c0301b00082c0850120741d880388071040b4548003038030f4001d0521000000200701040711211041c00f4001603103549076113056a083c003600304240c0c0e07404135008a0a02c410070011000200c10340e8110f860994011508018501c151005400300780202032700030300080100014842000c0c10148202c0c05114008001c1c90b1190b0f94000440c0402c580b1030355644a40c0124880440440c001d141202007141114110842c1c0d60325441602c01d1200e031280029254020710081c03040300454160080700d668032800b08911241e45800c40e40c00ca0404d240c0c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 478110053 1250 478108803 478108871
    0x40b0f10170f0105071e080105150d090b0f01170304150c020a1a0301090e0f060114030a05010504050c0126150d0b1014032109041508031c 61
    0x1100041040350b846211107500007032040780781c0b90302c00810180c4c884900a8004c5906c070a50683d06000318210f07130603600050601d40c0d00440c80c01d19400c265100d030b07800c20300003940e0710060800f00703d081d00c80c1401005c002a034107500703514268117041032a1442400c5642c54104010030002114440d000c40103a103083d003020815040e1500006056081503804401e5928420b0411091004408000c50581e42205010098a051003511035500c43c60103660003d25444580140034488140102e4190b03440300500f01e07080c0c40302c580d44190075144103581c01c403950703407000a20901070341e040000d0708065022403125208401800c0342100040303c4c050444a022510000303621091345590515410755600200d41244500f881c089151003080c00c0d200e050f103c5034010440800c58600481c9040c0c0c0401031110b95070480304218005212135001802c40766102c1d5a0301c1810210b03841000a00c0b00810041000c4e50311400888044e88511901c0d42000207820300e0300c40c2c602c045080d114240c058074010350500031 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 478111303 1250 478110053 478110089
    0x9090102040e040501090201080a09151119020105040b060102030316080702032104120306050a030206030c0c0610081c080a0207022b060e0105040b01050108070e040c08040b0f10 78
    0x900a108039086003030800350403030802041c40f00540264201034400c1ea030b4801035544503c0e0384002c0351601c1600174900040c004001c41d203032070140c02c041c2a0301c11810140e860140c00100412108042c162400c0141c0d441d001000281b08405081e2503001034280003039842c0d440c105419210f01c510f014420020702000c83c5c003040030743d4804c00549884022840381c0c2c0361005200c0389100e201e587c00301c178100d414200038407440f0307407442c4240209000ca910113040a10348605642c01c100325604010401c02841314244070b00c005103001000628066081039204800050814001e40c2c140744601070701d540545105801c801c20380b43d0244495501060840300103840c0c02d170b644005207a0a480c082400340d810056015241182d1341005943e580c54461042040704400b00040142660021107010f440c00f4076450040143c0d501411b40301e81d101c080c5140038266036004078002421244010001c8000614580030081000402c149080e0803410190403a072a524101019902c582c40b60f00804403a9480c0351045 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 478112553 1250 478111303 478111321
    0x5090703032a320a080a051e1201051008040201050a080705070f080a0318020901140a0308120a0f090b01180603060e0604020117040b07031104081c0e030c030a0209 72
    0xc861542d0340034030340055070750807004004101c040d40340d03218030f59440e41c29216180420015500070880c0e8015101030501d00d500c3d20549168209200c1c4000440410b00351150098400c0e004251908a5a081c04070950500040c80140c507841c0003021b041c01f140900740405030382c0103001d507000005c880c50041d0710707036070344030360843c4d83c1c0c0200c010081100c15402c0c21401044510406840105511703a02004642c1ea80c8800d01e07024400c112029401100c000010302c20b4100070100e0708180c440240124500f10340d240d4076001e09600900e0704a805548420521640c5005401a261007490701c180912510881d5100c1014240040c4030743c40d220345400c00744203425541030708448000c58008000300112056042e82d40d4076590102c400702c5c0010180418150080e1440e0394080c0900d41203540c9030010b0340d5030f4105500400c401d40c00000510307c06d200004120380308104103507481e04e10108801502c440550702404c2602042c1d8450320940040b280301000380c40c006215142c403501103a0700c02d082d458040078 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 478113803 1250 478112553 478112627
    0xa05030406020f07051c08070f0c1202011104080a050c06041d0402120d09050f0a0605030f07020106120f030306170307020409140a2102061501030f2d0509070303 71
    0x51260041209002c0207411140700481b15080a460380a1142c0d2284011909074001800305c07400324041151000c0031505044245000111a0000050480c0d1181c01c0c98101e400a5000f60010b0b13101c4003000040210900c41d4030200c0d0301c203640c0030b4205070816400c100c2d800c00c1c0c2d00c41e0240d002c02a800050a540c0c40360080701c4029844021f490f10061443d0004011a08074007a003070180c42c002c4900085428003001700800c9560903074034242141c0b169034500d86040000707081807003151740b215004280d2015000c1d900d5040740c4a002c010524034800d281c06001c1d5407803030f44141d07100720310700d403071f1101881c4080f04480606034125000100c0d100b0b14940011140303000541000c0e02c1c410a040e000070050039401c00a4144050300c00303a070a60820a50032a924402100c1c100382c6034070707800901c5106502035088154201011800422074100380d440f070020030701507049a00e0788400f445400714440f446a2080b150400191409848260b0658131302411040c8035003a040329038401e4034004440600036002d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 478115053 1250 478113803 478113817
    0x1404091a06040b07030e0315040f1a0a06060e0d021f030f0507031e181509060c020d09050405040f0807020d08030a0f0605040b0310241206050c0a05030406020f 70
    0x80c1c191110b803074464080c2e098028a40c101d000c511010718402051400041061075182d140c0400c5086548554650004601f000b80842c1e2002c44103a0a9595407440400c0901c40c8030060400105985000c50040000705064411b900503180620b061000d030b25049043e440c40810030a554202c407403410011401441c626403003414141c500004c0c415031b540d058200e03d030045d01140703408022054580d21001150306090750184c12030310900d80400003130035088403000b0309689507500003000401500d03141c2c26203103d081c600d070058000b091a40d0342d064016078814050304003a502000b261406e0b175590000703200100d5018012420103d440381c11507546856021505521000c2d080d00c0c0d00f841e040c80c5020784910b1840c1448103082105c0461141003502c2001311041c4000c0c01412400501d00e04907000340942255084000e80782c041c4085800d0041d0603480080901424001c212031720f40c24071000303c4030050013a543e84403040100824080e4032206882c1c0042e080702d401039480f422082c080e40e040c49820 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 478116303 1250 478115053 478115059
    0xa0513030f031113140901061404051c05150402091803030f04050a05151b0a120e0304051002030909102301030b09070c0b060f1c1a04211404091a 64
    0x1011405c07000e14500240c07403030300a4441040300d988490082d5600000b0700c4614a405001b0b01c410001850201c54840f15005290f003008164641502c46900301149108422044000c3d207007400118100482d405501504003041c00318030f41c5615088580324400900740b001c84006100c0490b061000500c550b1000301d03401000ca404518103900151749440f41141d40820f20031943c2072003100b0900150072204070f102c0d20b90b64000c4051180ba07400d40200000c030f0495804c2c2c4002d10002c180c1c0d03110503128400c4060140c0095444e003c3c854200b00d000340c4020150f40c1c441d2100d0340200310320f98120b0301c0684200c0010004d41440b0903c2401200181009003c40d5031000200c0240000c40c2c0c0c0099140e802980501000380d2540c0d198014490002c0462000d260000c00354441c54400d0b030514a19144c120384a00381d240c862400700d028001c030311274056505a0b190382c01c0f0104603138141010840c1182240c25030400040d02c414088100706a80610312550703ca96445428008454101c0200000811002 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 478117553 1250 478116303 478116337
    0x330609060a02070f0b090f1c05010f09050c2b060e070f141e0d0510060b22050a060305330a0602070b03160519080a0513030f0311 57
    0x1407400a55908142c450102d520302c03800f40100c0c000038214201ca0400c080031f010b08030310f01a81020301100800642e208a804206500c250303000900a010382103145035401004504d451035400c040f4102100108110312030648120f9894000700c030545c0d8081042201c0b1802003a651860800301c001d070042680340e80c510300a4640220752820050200c0090742e940d02152440901c001c0140070703c0f403407151003500c0e401c6062403080300b44c0d2422045140006205109070381030044480d1005040d100303e038000c1c005603080800e00b0445032040c0c0075501c50028091a24051051030301c404140c40c452140151410161500c0006a040310b20024501c5040e04000703503070b174009030b40b2605040a600c010815910070502d071080090f0003440010b00c4400d07640d2601029145132a4140054901406602d0600c2444010312254069042100031001c0014041c1c8032400d00303103460514141190030040074501d11350400c4c000040404e600080501c00e06200d401c1c002914100304004c066540141c8444009401030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 478118803 1250 478117553 478117567
    0x90203040f05071e08011e0c020f030c0304060e0312030a23040506010905070203040806061002250e0f07050702121f06030b07080108100519110c0633060906 69
    0x202c021805400040d90000d03102da685c0300c281040c281c6803040c13100340e03080103c0955501441025400700301104218011a20340d20041001503007543c02c108815100d0350004602000360700d4110041072030500f0b04a010f0080403d042e40c0c1d0708502d0101400c41040142c1d240150610700d01e0710007012001c250900c80c03d54583c5080d180c000d94441003409042c00e164140b6003c110072500000a490544c1d004001803c4581c3c2c540d0309104954088985850461080c3c80910182245090b0660050203003410300083c03080c00c0140d880c4002d030703002e0300c010003803500041001070596202040d12a442d5040b00c0c84048004072210082c584500e004d201d8011400302c0300442c81c078154a030f00c5941100d100b00441801d555800d0425902d0031000d1240b288250480c40ca6880c0448880e404607901030790f91114441a09003000d1010126002d030300008010420016034908003800401000c1d5001c08171043d008003001454401102d800221004034000c5000300702d0340000b6540301803d56410f440c0c00b030030a50703ca40c4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 478120053 1250 478118803 478118819
    0x30504030c030803041b1202240f030403020d05040f0e090703150212101401050c123006010e040b130507031b050301060512060102010b122d07090203040f0507 70
    0x2005403422144031100004c0c6d00890b400709040344084940140c0760704803800d460740074483d004041c04072240d401150803d18404c0640101c3c050f10486001100c002c1c1c40786003501e0041d240000e00d089440603c00240320801c04030141104410690b202044980f80035101d40c21107620788040d40d04000e100b6a806882d9480310703c0994040c002c5402c20300b01c400d01036202c0114031405210341d4000c001d0f0401042c45000d0495005400a1030001880e0317044416900d02901501c4030354100001c004840820300e107409007815000800d050800144e83d2030310500703042034400078043c0f000d071141590090341c640d1001c400da40e40e2051070318444401c04000b40b0076454880c800600500c83c9424005d076079107410411410603032040040d641a82c056446c0c05180c60140b100700c5030300403130040c0020b0443d920740c0c030461560b0b1540540c0c8928159854020b0040d8021541e8404c826500c0c00301e040307010a80e0044284113040c00040740b07800c460510382c0050741c90f156801e1030442c5040d088406009071040301c0c1c0026000c0c03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 478121303 1250 478120053 478120057
    0x291602011b05091905090727030b010e011d0117010204030203030d0f050f0103030e130b1306030309080c0a0911070f11010201050609060904121209080c0f0f19030504030c0308 77
    0xa00c0868131180500385003454a6015250342c021070350410003040c001000300b4040c2c18002c130103a62280c2c0d0810185c2d402d08070a03a054500e900221101c4220000421420304245100390140408020448101d82452255030749400b05110300f00d0907603000c21010701105000e604940146401a00356503480fa09290304002a0080401d84d02c03080b45404009a031101c04c00c3d06481c1680da16580c0c0a0360b8229420400c440c05e00c04c0d05590000c2c580e1740d00050600e584a0345084201c1003124000700d0b101d4614140508241d8140d4401403c0da00601c1281c1320540e901d0030610191914454000b030b020030051101c8460b80660b540c000d08821040e0318140a011949008004c454002d034028805a80d0740700c00d0100480e02981c107590040b44442c0442e000908504270a1003034001454408418020b1080b07080a41c1c0e0740b40e2060380e0709140098002a4890207024800d41c0e00c51640c0104020642203190958800c2c0b030710f03507010021a2203070500c004c051261003210015600016402000e60702e17420702034001c2d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 478122553 1250 478121303 478121317
    0x70e040210091d0c040b0703020d11010e0309011d030a030c0615270b1909051006050a120f0213061808100e0f100603291602011b05 58
    0x40d100411481145071089014805640d02104002c03d0500010f00f60100c160b8040d051010507007003030002090f003d000c20080c08409001c2d500400152445107030262903207028207503440141c1d04050051200f804004226000000d0a01c0d195120781050f4410f8801400c1a40d2a5a8580181c040410030b244c0d00000c14a07071a801404200701e4440320004164140c529849405d00c03110303520000c0c100e00701c54802402051350001c04081229185075001400380190310b010426655000001400390b400d45100b001e52082800c10641f0003541003003170107041030003154410003c021203280c01d000c001103170b0740144051003000c640c00e540368541400d01901c01403140c00b581d0001019041040c072a804644c2c681e1b0b084840c114060304030031010b6440c1c840a0640420b641c1c2c07007840f07981410000390000f0800c3c21b020711030080000070320500f1417030005a0032030210704600e088290884445814000c40401c4c03178104006202d02d03c054121380b40180e0150801c2e416910021203021002040d00350018010066 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 478123803 1250 478122553 478122559
    0x6090e0d080a0614060703170414012f0903071701022511090603070b2a0a080409050403140a1d06040b0409020a170108010e011802100f0908070e0402 66
    0x1580d07000a00b400300c842070b116480031078294110706400c0781040d00040c01030a000345072140c042144641001c4e054403007520115440381103031140034001030082c0f14000c208a0001c05140102c8610b03141415034000e1190075031782846000403402c02c80c2da0200889e00041201e2a032101080390189c409034000d40100384e1116103000d01190344694910034800490784c19500c00d4000380c1032081074041c06171440004087d580c1501c181c0a000c101c2049460141c803003104a940c0d100d0308040c030580f07001d29040c48500712240561000000c03800141804e0281d030183e83d200c48002400f9500d078102140c1410352040340e8421031800141100c0459400310a201c0400341d28a91100300005c10800d0180380e1040340b0510884000511007401208010b400400024006141549410912120501c66061b0a030b11000c511b03075413941c10f0032581c002801041a881e01d00c900007244103240343c000c90a28070b40c401c0100100301741c040c903014079540140617407405040140201ca20164440c0403100000da019070381030748 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 478125053 1250 478123803 478123817
    0xf030904051506070b09070b04090f0b01030c1b06060509190606050a020d0806030c0a0f0e100f0b07031106090a170a0e1012050703021c05010302100c0606090e0d 71
    0x20850341e420701102c0040036080920304842c580300d22140240242004004d07000c0e407040002c6d060312810141020700040381d400202520410b148404540e003c100380c0341418140040340905541103808400780c9044810a500310486901e8070b48018400c86c0c100c02d0b400344120b814800c10b1000d010fa080c04503802c0450401c41d40d5140c050a954a003d514043e000581c04a440464503c0c4120020b40c2c0104010702244d01404ea01c83c00900400d801d608038a1040c4140c80040000b60329070403003590082200900f140000e8148800c0d00c1408147c2c0c0103041810f100000c03c0d40c2014441c000c100ea0281d003010503150541028070344941c50f0980000155141902d080c02e001c1c120245104940407180c06031140c0f0b4000504000717100464420649a03020f2000040b000815821540038151180d80c0c15a0016902c5102c0c916030f801a91450119104203840c1c840148010b0b00d960011100107080f5003000d103044031040c07902001504460b00441c91150401400c5001d0740c00c00240303907007610304503104c01d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 478126303 1250 478125053 478125061
    0x618101e11030316090312021501060509030309040c18090b21060105041d01050c030130020411040f0b030714030f01150309120c03030c03020405060d0506120f03090405 74
    0x100c0441c000195a03540c0d8004002003641c0b604005521280543c66050282c1819501d171201038031500220717201400358000107400c5102c070580740403503409060703d420102e00340492035000c603540380907011000f4040c0d035441100d120401d0140c0c05040c10303a8048070440d5070050301e9901040103861010300b00c9002d84050b907118400115650100303070700d01d0b0b8418002c00450f842c0108001c0036040e08071201d0300f1701ca0384881c10140c4420a001c0c1600c1040907130320103541e0f945805070742d2680a85504002514403c0d40e991440c20840c801d49424a01d50122404504040881181481441140d00001c4c440010703ca0008037030041d82d000c5c41c418982c2d40c542c144043d0240d40300400500c130480f20880e81c3c2c1c4124005104000e650154134481344440c0c6000149844641d075900c0300341e8030b0911848049101c510700da008155050041e500c10241074502541010700d00f0340890483c2c011541e07000d103650313200c0000420039110100441d40700d420f00412508216000e09038541ca960103038101d27074010b6003040c0c001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 478127553 1250 478126303 478126307
    0x100e100f0305161d1c0804080c1206150a050d050f010f0b030307030c060207080d0b10030c020d080a02070b0c0703090e06090703020304061d0705040515010c020618101e 74
    0x3110020584c1350022004080750085000d002c01c04407441d841599060039655030350140c83c03003c25061252504580e1a07051910081c900500000030301d00ca080548180c400d00d4201107a0190482e80f0718070b2120410450f180010800101c54006d590084c40540c2410180040081c1e90000c2c0305250000700840620180c45800782d4804011194041d441003040c0c00009204004140420340107400060a01e01240c1e60404a07034480d00382d002840d910760401059528041007074200301043d90808200300800c0c104003a440e1440550301c03d0900c28090700207070804e051a01200d40d4644c0c4580c00038074074602001c14000c5a00480c4003640056900d607008210032904d0001c25000310340c003c1c0b03c1c0c1c0340c940d65040d04502a61001308122112600c80d209180b17100d400085080c00d000c40ca101600701a0304000a00c000c94500601081922480107400c412698018000c92611501a204155034071a510442130740ea074044441c0035004103030642034000341c1c0e50000c503c2000300c200704540c0c403600d01d4000341 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 478128803 1250 478127553 478127581
    0x307081f1503020d140309130203060306090c032806020c16080313090f0b0a06020717211605031201090e011b03200d0b030601050d050705100e100f0305 67
    0x10080d001403044130440c010600100081c004068030310126441c000307407200407607017a8841d0b0840a0501d5000f0082c0403d03450b0500109511003c180d0082030040c002c000041d030381c2e00383c4502c020700d40f4107c18007210310364040960f42030701c480d0001d405541d10700000703500c80d44ea030048603c450b402e40041480414103110200071103c000800e204034602e49030410007080c0013408034182116900350b03103c040c903a8a07115910351a00800064000d04002494074072401610061159000000e070802e18003483c008000f03089940c0403500f82d184280e00d42149602c1c0c002842c600d860054010710004c41c684558981000c1483d06032040e05409100501c000701d4818240c81c0c1c2030707040c0c0c2c5c0014246612016550b2299204030030903004024941d010041d291401c0340640c2c440401c0c43c4a041e102c03011010b050070100003ca00400c03040c5e0350304d4841101d980310035450fa941c0c0d0040e071340324140d40d894442c442031203541d485850180c000e11492402c03100e003001070450f02180941402080c20100055241011810 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 478130053 1250 478128803 478128809
    0x2d0a020703120309020315060306070c0c1202030a02030a0605040c060c110405190f02070c0503031207030f14070507050d0302031501030b03160e011706060d110307081f15 75
    0x3403a00604542e50030660351114030340a010190f840b90300c0005640d080000f400c05121501440c2001c0c103085d0241402c06e44000c0802062000c1c0f103811000050058440da8201c2e01441d02942d10808a4800641840040c50010390b2501c0b44490300d20520401c1c0d403065000d244034901300003c007541d0314010707140d2144560000e0000110550700e11341d941443c2e00030a50101134507401380207a2021003408000ca900b001c500500c055400b191030001c000c0002c0f944005004c0803002581000c20394801e00c060020004c01d19000c0503183d090308405185141c10070090811810790110591404060044c031503008800103603008d108507103210101071300a2088a0089110354007043d450750075200150083e00700316840940502c01c4801b00c0700b005950440403000b038043c080084d2415454103003001d15025482040290680162041c00240c1c0c0c0c1d510400400b190707122414085280701680081d003010802d6200d41e10070700540407480070171941c0030451845007440d0740301044200c03072840c0c40916241c8140 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 478131303 1250 478130053 478130057
    0x206130308041b090c0219020f0114070210050a030c030c1b03020a152013030303110d060e090d03140711280b070c0b0c090307030203032d0a 62
    0x1001180441e01c00e0107a258000c1c0601c0b01c1400c00310001240141d2524241d012001d001e0344c1c1c0c80100d818a506001d4258460000f03000b600c1e20385629000104032a08e0311819070b06010162000d61884980d032000d48041c0d540041101a07908800762024207194459048031002925100d44540d003580070307204142c15420b02e952103c407648266210601011913800081d01540300303060310000003465001150b040300502d10030114498950300d81c074403580c07240360700030244803c0c051000b5265003400152580860b034243c5808130b8280f4400400340440d10483c03010081c11070810781d01107607580003502d1050103415400b0440f19204030640040b800c461030007210204140c00b40c03010030341141c0325500d03e03401c0c1000d060980d202410040604e001e4540103240c15810301c14405050420b00400247e2580d110116051101d00c030318096a82100d056070003800c2170b6100b40040780c110220303182080301d14081d61780941126030303411610038459000034450701c0003211401c0705810101c8410341c0c403041c1c4e203200c1340781c0e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 478132553 1250 478131303 478131331
    0x60901060c0c150215010f03050c0603010b0d0c1101360c090209121b0405070f0f0f050408070f1401140d09050a0f030c1104020310120c0f03051506010206 68
    0x1108098403414021aa03c110320400d0403c0207807890300801c40d03000301000764004103c1491450800d04181c94003060710b00c541424401007000c05001c1045840307092441c07800280c00c140316401556180d180c0082c800d030075860101e414130150b0fa1806440c3c095004000c0211180c500561400c4500c0501c150080c014070708084100810745e41c940107400300060081c01c0020399400030043c41c0c43c002c03d5031181d03150318012940c03099140c1810311502c1c0e0002543d203401c06840c02250300141111440300410010044c0880c1100c8030340780302e14203480180c4a002e09480500c0d546688580c01070026004141c0348081842c415089580944426180700440341180c41c10400180c0806d8000d040b810829120342c06480e2000d40014003215030703500f4642c400d803640c2d46081740d01c1c180b1030512650712003c503010314810018011018005019442203070403c0400300b40000305e600d4080365881d204d900402d5400044d840c007004001d80421180b1040e403c000406405654803c01240d443d101964030a10070100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 478133803 1250 478132553 478132559
    0xb04060f120c051c0b100507060b0d02010804030f020106090e0d02010f0b01020a0308100302040f020c01050a0c052a010905030415050304021815030a11010e0904021008100f0e060901060c0c 83
    0x45104c5000b80c03500c40210000b014440e440101e58280c07454070300340000a000107489000c10a09105048800720280c1e01c00100c0080713030780044c4c600700d4060405000d004120017110241340c0300f5000200600030055040c82482c45040c03006a403600282d5108025500b40700564404003da48110200a88164014104001145c1b07060b02c034440058541c188001260030080096181c900400050f40031540005aa4000342c8d0f40d0282185c4002e4900000b85052210b4100f60a078800c06440801d4446100c1d89118040d200424900d00501801c4c01075550a2880010a000e4013101410071a0036401e42080c00550000040b149440112002940040c1a98000341d41c038841c0a50ba07540000c9175506c003610031902c440000c1c98510340300c00455042c081800c4000c00d9583c0b2500110300d030b00c410383c0e601601c0d0800d903000039529500304070740302e08020b04a000581a4001092258014008080d0200c005034403040d2150501340220f03003260051a406000184052040400b010066001561001c0440c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 478135053 1250 478133803 478133827
    0x3016060c1a040f020109081506100203090a0806060306010e0c0a0302130b1201140a03030203090621043c171b0f1c120b0a0b04060f120c05 61
    0x600041d00e400d9654a00031540c071186088580c0610f014003070200e00c0381518400140108100d8100c03610542210706d0160101402801240c1c01070403c44044402c3d4030b2102040b0b245028640c04180d00003541480000d81c03550110702d8034060141039081c2c50442c5e0300c0e18030240300c08006954458a14030308004807801180310f6800f41c4059240c1f581018241a40d40b5401c40300c0d43c018005c0e01d0a03181d14000100f00401d01558880d001e40400d54081848500d50b4801030b45901500700b2950160100084d0203005c4078170030b444403544410005400000c0d007454204003400003501c140045920a91800f20b03a4440d006141c2d41c502030545c03001c070182e00d0300b00d59640444400304285280c4008800d02c2000c500301244600c040010b48010300610900d44e905c20040d01c3e18602e5580c0313002810444000c0310300744e60300442e805008103a98002103042a00400403880c505010b9004565110020801040d5131782c0c043d890581c0c01d0f409554014441c1c3d4042e011600f2141d06030460030215004010a0074821 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 478136303 1250 478135053 478135067
    0x2e0507021302030c0d0b040c0e06070f0c0b030403020d03050424111902010501120b0f070207030210051801022e090807060608100e060609040f02301606 67
    0xc0c40074080c1d52a8005001884007030740c10564410440c0c1001003016205148248906c500540c4100d805004404070000003600c00c1c18101c50060003020001406024010140d5030003400a03402010000c055544444501f00c0750010fa40440060007040d2941100500c0b0f40561402503402c80048080ca1761a89990504500c45011900100340ca0b80c203684207201c0404060a0072402d0f4080c4003842a10382640242103500582103c420380341310440840106144000c0142e21003a49040c00c8950b854032003040c0d01d040032540c002903201c03603011100c42200d507000c005030851078074545a84044c1c2505100680c2c546800714228800b2035000340e4507080c03000c2800700000c54145e00c3d000005a0350700c1a00c82c1c0000303502c40c002c240d0b40d9503100c4800700807840003080501003220000c1e008008541d030f814003c40d12054040d203054800d40d1404d000c41d083c01819030740e43c0c0080358014207403030714400ca28560712502c1086041d2061081e0204031143c2d10700d117020486008100a40707003170054881c1840001d403212 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 478137553 1250 478136303 478136317
    0xb13290307020118030809240129030c071110020a110a0f0305030406090f08150a0b060d0507081302182a04090b0a0305150c0c0d08062e05 61
    0x542d00c3d00c15840d0032603401500703444000e0003540d46c50722a1914001881c40c10602e89150b8141c46911281c0e48021005400c8060568182001b540e88040024101c6030070a0b0030030407048a00310001040c8104d814140d40205842482825501e10b101d038203800704150101650342c071801507002200300724001000320140c1c0a0305d0500030f002d520070544409801306034111541044030a0b83c030005041c0300d080c0d08034410130002c10140d20101c481a007004509902c900401c10541c07450940e84020804002554005080000c0050961a01c603c1102148005090300b602d0240101e440080810032040fa4031540038000741d00644120b00b4038a401701720140111000b001c0444181003446055100b007040030700000a2150f000c4c6413510369051204d04400c030381c43d0340340040c45000c00c160208002940440c4007045111000d0180c0100d0390354414640d080e1041c80a5140c0030700444202c443d285070480301d40b070302540042e160302040d4105070078a000e10902030408066842d0405103010f403003501c14070050001c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 478138803 1250 478137553 478137557
    0x51233091803040b040905060a09090807080304031205070c0209091b220c020f06090303010f03030e04090c060507051204030507150e030a0b06011722050a08040b13290307 75
    0x1405a5502131043e098000d9007000c84601d8440b4240070551410100c4a40504400032040204881d01c0d910701c0703e180304400c0001e204a40100c009018103015207a44420134812580c284464517002000804c40d101c42e203c124810003861022543d080c000041180d9420504080e0211046000d0200009100c14005085c2d9004c204200c02c4102d100c1c9009210442c20680c0040581040c2901a1030506100402424990f0300031300c01003080c88a400c40943c2101c1c0c044c2862213848800401003000b60904420140043e2038810b400162640e025004018050142e002d40f042d621920890b0030307480c0306030701c0080d03d5544842c0003440081c03542d1035010381e1400e81e800c0c0040304030345031400700781085040c15050704c0c42c151080400c00d403541c005120040034038090400000c2840c100120b114540c03440c16102c2814881843c0c101c0401c1810009501d0b46504801c4035501c6a988104030b28240d4001d60805c4482c031301030000050010380c0c4015076076424010900201113815180c0045105400040c02401 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 478140053 1250 478138803 478138807
    0xf04030503040b0702090f070807030c1803051b060405130c090e1f050402070f03082208031f0f061404030204050403020705040b0105130e0601051233091803 69
    0x2181007004100400646440c0790f21800307180100f00303441c20001d0121707292040200c100f19100b9131000301d03143d1181032403c000031116a80381084460000c42c17071a0680c95408000e021040c00b0001a003041400000c4503054445404641888510302641c40b4680c0c0060000e1001030201c2c0c001d4100300300d040f94500c2c29480e21070ba00c074102c0302007178415601c1c25038000c490070030030082160000120002d04410348095182056541d900c0020300340800307000c0e003002803c0c1c012500d03580800c103554410710286107441501c10350f00c1c02d00303800d00d900550f01e1455003c03880c1c10600f000c040500c00a4121030020b480302d0746070f41c9444015502801d002c2501304c0072010400020005136107a2040c940181e020f603008200c0c140c141401d1004581c011003030707075040c08400c0c841c0328200301116561105441c3c50b03000300542a01c82c00c0042c0e941d4010010a14149040c0d24100040c4980b4800380a00501c05035402281d41803407503620125007018418035541044a1400081100c490031a411180088a0080340c1c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 478141303 1250 478140053 478140059
    0x30f050a0516270b06030414060106030b060d150803070c30080c010216050c040c1d01030207080d1b171e06030f010204080109020108060a080303011517010b040815090c04020f04 78
    0x106286c0c41250202d6841c0080707140c00141040410819003d020395080401c4008a69000542ca60207141103040c111501e541c079031a040b0300300301c0086008004041c110380d11200c0310700d06124404218006d01181018a41c102e00c808419441346126840c800103014007294016145da86182d400300340d04001640d003c1007185403c1120f21b10201c2003034041d0000e441e003a22010100801d44410004503070070040c00480e106200c1003920310a0040316000d00b070069440801d4684031240b8001ea0228209151078080c0d0345080d0030142441004502e0650354121451a80c0078860704079490664800350140b140c03603200307807821041903052600700318010b003140c0e250a44c04020509a80c807641040f045651944180b20440d41c204401a400c2a41245d034260709a0414005a4ad607010511901d0101c0070300903d44500c25004400354600001940c000c4000c56849540c1035001d41d201d44141d18a030308c00c0008102c022021040080e00a00106001c1c0907045941410003020350000d0180d90680c00c3c08001c00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 478142553 1250 478141303 478141309
    0x90c0a110d03060303030506010e130903030915020705070905070c120e040606021b0a05100509010c0501020313140a0f0219090f0c090602120a0315030f050a0516270b 73
    0x5400500440d80d40843c0440c01d500e0010306540015001b0b038144a400d09450115958101c413005085840d540300150000d0281000c4000d412541405040547e40b003c40d5201c4c1d4526800504c105400b80084880f42560303080b0380720480300105c80d96000070303010400c120000761219106c1c500e00c0746140781c4484142e50220000e01200c01c95401000960f011046981d207040d045030390045504000c440c0b00700c4044c5418045140c800e10f03400002c080040000f03100b05503038040e85100340d1050304900219203d10303004945812669680c1d00aa030010704030038081100141c00901c0d2034a441c0c2c0200f901003075081544c20b0100f8107051082200f4418005d840110300b075031452103445200004240c0c0807a10206007203016202b00c0b22900507800f15000650394003c9541034808440d14541c06150000312614001c11190114106030802030845245403100c5091101c000360a40145004105a980d070610000700701c074441e0a544103e84016400d45246400c0d00c14158441c861014001c002103003485400b000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 478143803 1250 478142553 478142563
    0x40f050102030a05040201031518020a0c1205030901050109060b0a080a0e010e1c03020408070b0f04051c0b16020c010c05031902030409050f010f170109080f0705010b0f090c0a11 78
    0x25403201aa500d0307040006541c0d0500070750600740b5441c00c00c0c0110a040101c00c2b1210f51203501c1d9900e92036000170390240d94034401c2810241040c1c002e8420040900c2200000b40582d000b621448829030808001061040c890302c1400304079540403201c14941103c4030b80c10303604001d00601907005140e413083e009079a64000c1c000c41c941101aa405002511100003100c48180c03400e6450380100740c81030005000c1c1100014140d81503075804070f0441d85800091f025900c1600c6070380c10542d008558880070b40d100c0048014041c00092250000c0390035541c1741800682150122464140143d2220450564550050407008003450041042e01c4c680444000c3d4081403254a03142d85005a10004040140124a114541c0c010b2150820f01e24554581850703501c5195240c002c440300e50350031454551148100358001c1210940c04481c0545481c95443c881c080c035005100c1c142c17030755400c20003440c0e100e1501452904d10442c000340b40840340d807a07060318148141c0220b04450b05112000c01641c45022007086 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 478145053 1250 478143803 478143811
    0x18090213050c070213050c1b07030602040e090c120705060d02040911040303020f070302030601060f020a0b0108071e050312070c0b1810020f0c191a0703021203010608040803040f05010203 82
    0x40100d41e528800e1040c0440c80207000017010380f20b840c0c00140b1261882c41811202c5000750803048030601c9074298422401c1204950008144510020700014a5484862000d01c215010415500b0740c0108800b0701101255515141d00c2c03d8000160a000f6407910030060010007d0380800181000e031250f241ca021100740040384140b0300c0000c03800f00b08151b41040072051100b03991024200031444e56020a90750b03401800b0308003e1290707200000e1803051080100381c034050f4101104480559503070905980b226a135001d00d090002c8405411000c80c071600f504041280ea0143c000e2404011905154009d40c106c0c02c8211004045c1c0c1c1c40005445030100e01802003c0c002050a000150b922030811101c3c0e03240042032000d54008060741030059202003120710000e001070b40c440d0b0720892030806c0da1604070a2900207031800b01c80c0203c14204d0907017000241c140d052003a000c40c1d8503107a5814400000f8002403091300d00080071800040d0000da0300314041c580042c400c0050a24000441e5503040c02c0e600111 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 478146303 1250 478145053 478145071
    0x501020702040b0118030f0609150905060a02270d0507060e09150f01270f03060c0e030a0807020d0f03030506041104060c062007080a03060f1809021305 67
    0x1180e82020741c546880349005040003400c01c12801c0040e486000034030000d61001070b095803d5810420280f010540000692650000d83c850001c1a01030000c80102881c5000340e81507c00c0500040c03140c40540308031800c03012440b481d041103610f10580c0840180c00312141540003081b8051700c40c0000d904003c9580a4441521884191118801440750f005401419900c415107900d0421607951501000341c98602e00070300c0d04004109008074501d155264186e410200c80322403400006841e048600440c054a1080c1c03028000f2030b9501d0380480d1170900e0019140d80c981c1201400340c000514110041002c2c0d0f102401040c10303285a511030003681c020144040e00400c0d01c440c10001289024495100d0400065120300d04050800d14001e0502e40d000d4030080189582c3e8000f50214071000f030b100202c140120012035500c4000345403845036900880380c40400b10f4145100443e640d58220604804d03291142151401d69107202800300150000e07810036608005c0081803001d20140070701030984114681 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 478147553 1250 478146303 478146307
    0x20c0904020d05070b03090d0903110423070309051b103e15090d030923030715050408030402060d020c0d0906090608130f050f101514090c03070203070f050102 70
    0x24081c2d00c8c28407107402082820042d03550020302c0010352041032550243c070f0a46002516036150248003c86000c40034080d480e50b810359040041c460382c0350300454025840b500075a54454480362141c00d40e000041c070001d038041081500c00300ea0b43d00c512080460014100c100d15400041000c0c0c4050391881c04684802c013412400342e034111908200090316102000b02149102454140802c3c0e484043d40341ca0742c03003059140d10183c0c0501c13211040d4400d01d0181801590709501d52041d801e552a804548100c8022071000780d2038038a00240d110341c500c255002101107280d66115801c204941e0b100c17150104e07a0650030302c604001c1040411100c004600390741c0758640f0300d906260001c0d1a0041c01d40c8802c00304000e400030010550003100a003590301303500205a001c25030703061920380d08141020380c04143d14402c640c4448443d00d0300d030b00051840030a200141c0f04450b140c01050601d80201804940c00c0940301d0081450460400b00560740701c00c02d8410b0300d042800759551043c1d402d03034041d03081d1816900 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 478148803 1250 478147553 478147561
    0x50c1e07120e0f091605090127031a07020d0c021c05072610110c12040302100f0804121e0c05160f1404110f0325020c0904020d05070b03 60
    0x32030207018404000c1100c1c8440f2616040c80311600c1064817060510401101080c88002da9000c1e800340b030303684e901c49503078061100121a01040f0400300c5100549440080b0482500b180c45881003031801200c2d183e010b45007011140d0820341e110311414001300c5e007009442094800d0401091003240c0c03518461000703880e44c2c40c80c141c6001550000319034111501c006210138104543c0c000102090354840d140d00c00f00c1e100d001c3c4012590140180000c0c00140e018480e0400413500341c10f40144152442155a503c1c40c248419040719610081012035000c1420000402e000c01c009131038800006000e494140541c905140910700034440b40b82e000000315402d08286810080c00388803030b074642c0d9001a4041081d518018000884403800e100d071100c510000041c4030115100c5410a01e54000000e0f21180d803800103000e03c584503070048071560f001c800c903810321400701c84589008404003508d9034014030340207516008001603440060002c030380c0042003225900c00100d0500a0704028030ba000296a120300e4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 478150053 1250 478148803 478148809
    0x60c0304060807140304080d0c03022a10020a0c060f180807020301060f060c03030b090c0f070302100903050408010e011a041e090807020916080403030b01021627050c1e07120e 77
    0x4509c07603c0e0b605160045c04200401e9014081c000c2014091480000802c10701d4107040d810410a17950961780180002180080b01303803c40c408011403882202c0800c40e48405025003402c03035162280780c0006d0000700c1042c1002c600c03080c001e0030713a5500080c00028103d94414140c030340c0f40b8040d8405804944c07040000028150113124000041a041c0d03400b080034900940c2440e000d12a08806c1071030300c0c0b0049005810306d48200944103181e010020200041d030141e0070081c0c4aa04544110305140d820700c10125585078043c05110a100b104200400e8032408035000c001c050588208000703800701d0703c20302903140311106015000390580103c0429030742d403005005000c00341000a05030780320003011500c448607150f40300c005a41d000e505841d0001d0400d401d10b0040341008540d1400d0f6081e280e6000011a0007500034a4418400140e001860400e403019059103069602c00c88441c149030f00d050028844210000e0003040000000c00da040f0319201716945d42d0104d089400d07200d00f001a00c00e034402e00880c1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 478151303 1250 478150053 478150061
    0xf150f0906030c050118080d0519020102090904110d0f060501150206010605030c03130819090801090f0204021806040f1805061e030c0a17010b060c0304060807140304080d 75
    0x12210100074041603003180c482d019014001d00c2000d04100303d040000040c410001070000c0505410300c141e82041e160360701d000304541c100f0114200002d15481d070036520240144202c845005002d042140a0b51300c070f07190480c04030902c0c8419900102404410b00000300b100c0406004988030b100300081c0c81d41483e8805503091581076100c4195840800140702507030f0401c066036401641d211501f40d0380c1d43c0d5001070158114003a070009000c110b0110303000c130f80c501c070344012000003e850395a080d40381642c5800803800d0340d0003014090690505070b0b0500d009420550000c00e20032211040806508036004040f80695110381d0003840c003410780745070501900590940e83c04a031600c1e08001e00c00d90410600041884228080d88021031941e540c041a01d40c42c28001134080384001011407041d00e55814036850074440103061083c02d9460322400e480c031458001c00707503600da240210042d4141410503400b621003e5014001c01c040c02a1700e0302c00c10114850100451050380702d07119094480c0e8005007140166 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 478152553 1250 478151303 478151309
    0xf270f08070b0301030201080a0525021f111b031210030506150a09091104020d0609060807080d050a090807140112092f03060f100b03040b0c09040f150f 67
    0x1103400f0001000542ea000c040c141d041215070b84006802d071501d5034072140407043e00b0030b400c0109202d11441810150045015689002e110303104040c80503c8404000845640404404681500b400410b00010b03064401c2008a11414226450800c0a400c15206a80c0440d51490b9024041d030042c0100320090000a821030b102c04101303440f0140e10000210f80740d00d5030040d29401c40d41d400380780c0e0038414101781d904c80c0548007400442d13445e9612200e20000e4600c41c050b107041603003404000604014002640d02c2241d0002025018407c0d08100132101507000310402c8040007d8006c021a103401c040c0480310042c0458058820312400f01c0c000585540c501c600401c12041c80c0400281c00301340050840a0131095010540e0f0a040040e000c0d50811088000410303014810302d010000080e003407a0398180100c031003903514160503030764982c02201307031200f01c50082030414402c000c9054038007004054941108000c3c8040f45807008941d110088404c8424085601c41d8651801c0203c400d021f8040e4010b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 478153803 1250 478152553 478152569
    0x60f0106020f060c0313020105121008010b060f030a05100e092406100f020a1506060305160c020d02060408160501121a0609061b060609060604060f270f0807 69
    0x56252500340d941e20b9000003410b506d000c14220050604580c070a90440d8040340c0c000c039660400342042c5c002081c2c2c089082c0100e203020b6283c50704921072490f0000c2504e11403815400300034903541c0c2c1d15807020058500540340c0c0b020b5801e40e040200c1c02000140300341d0b10849002000740000006a070400c0c0c200c60458031041c2c035074265401845041d4071689090800c025040c1011100c8800c01c660882c600864003074040c00600c00c4041990380c17040b0381d40000007220b416030b4090040d078030742680118800f4403440f00c1e80f010400c079858501c0181004c0800c02c0503540010441414070b5610708501d800c29145120805030101e40313070411b101035a08043e0b1800d0014564100708070303203103080e18109150200481814480c05012500d90030f5a43e0b01c2c0b0840c0c1e40b684c000030810784180d42842c031855540301c1c25100360344129030740d030000361041c1058016202100e1351a512541040c014500660320381081d00324030300c45003070102e0030310b18007211680303509005200b10100350f6070541c42c10030600e00f002490380010007 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 478155053 1250 478153803 478153813
    0x6080405060402120f010c031d010c0512091c0206180f0a110409051203010306060518070305150402031005011e050f21040c0e0a050603031803030903060f0106020f 72
    0x10104400240c440d90140e81070b07420050079024001c1043c07810701c0000b074043c001c0d801d047c406001151b1640107001e040041001c0f00380e0401001c0c0d20710b07080c1d441c4003080b1400506c0c1408a01c2c03151030165515500824454152442816501d0740e01101c0740c0010342d0a030242e80094284900740e1004ca240806c65603601028040b42c0c0e10b44010715454140d0320b00060801030078280010440c2e9038562040c6801584402100d21f03028036038600a625400910041d03800d240342840000d004d040c1600707102004a105210074550355146001074008241c0a41803201091402241081503200c510007940181007030f2504005103450003000500c004141610220380d0424081c04001d900d40000c141d804000c0c005080607252921808000f150784204d24405082c50081b4042c0030900c4000c44048081d03600300240300f5216520501c1c0c1d08252602610701ca40c05504c00c1103882070442e55807500300740f404401001ea9140000b0b00c000246444020740d007001e0701030b8102c07004102031501042040b080010f02d0000d81 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 478156303 1250 478155053 478155061
    0xa0e04050c0a14060c0c0a0303081008030a0909020708070c140423010e19110a0305060103020903150a200a030506030a030903080d020c030d0c11190609080403080d090c0608 76
    0x401e800034803c54140c003c010202d0300d030600b0f10091258180c0c50300702502d400e61060b0f0702e060043c143c071001e40380141e45401586000c1220304c4080110340050300d840c3c5406140c00c3c582030340d80e0029404440c0940e0240e00a00440e000100c54100b040300400b03a04001c40440c590030001c03c4102d4070305142e845034111120742001e114809101006d811903014881d001c059946070100030041d1a00340c880ca40c1018981066420b00c1c21200c409000f030801295002c2285548001c010f4003244100e18482d64140d0103941040410088080307a950300203517281011603106034091203000e000c0c11041001c4001a8080340e500001503041c0b10b82d55018904800800030308600340c501402d0240725002c06441100000341001141030b6a40480d22448112000c89507100841c494040c01800ba580c0782100042c0d07000b181649201c0c1c0084c3c06217048000c00c500b9000c4a0f01daa50390b02c0200081d810445010400307020010102d442032004d05a03e210800011502005503e00f001120340160807800c1400760141c144 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 478157553 1250 478156303 478156319
    0x6170309091303021c050301140a06050d050714130801180b070c02011707110f01051018060b040f060e1804080a020705090c04061202190f05090a0e04050c0a 69
    0x105400c400c20b0b82201c4003804076420102d092040140c5240d481296900520900a03400320086040b507001e8400009400540303000c10039455031a21070800050010310031101c185095501c1182c202c4074508101c0b0400d0010440801c060300b10f10000301281d030004400300f05c8814280600c1004031240c0c80e020010341c805d9a1004640d05001d02000c04006040c0705000840e4041d2040005003d41c00151010a00e00100024441c1c000041001d102d8040d1400450301d070101400f409003d4510390b00024026818001d0302482c5c82000d4410b41030f080d49404000036441d40c04001130000d84440303420b00c2580390074a01c020b803668030a0700319540110341c4207122a646c0e0003089045a0442e500000283d0307a0100c5030403c920780f0f1b1003030b000591310111090500803907094100c0100204c82c4103407111040c0460900b0003070224019524138540028200c40c040042c144101107070003000e1507a041c104e09048803480840c5010119410581c2c3c001d00b00803e00007401410407084254880c08c0320000245410070640e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 478158803 1250 478157553 478157569
    0x30e09090a0f06090b0c0408010b01112e110919030b0c091f03050a0c02031216180f03060e01150902030903070212061e090a0b041401090606170309 65
    0xb42116940c0d002e110104101c60f0080c0c0d0003180c00c060592603c1c10000e52030b04a40d0f10a101d200c605600e440051030007940140f8224003401c0aa6003d004034160104220080001e0b10f10b507002d90540c8110807642040c0f440c41200040c001c420f0040345c84000c040180702d80b0012402d4a81914020f02c0000c00000303880303481c481e03407082030380d000162240c1454010425046402d001095620804005007651541c503512280c8141002c103030502049203200d1099031248100c000c04480c2003a040001003154a8003088208100424039140400c0080400140341c61200f0341c10114401d201d110041050001500034201d56009410007005004900a1019085401d078401e103204543c003c00041d400800c140f060b56141a0050091809450f0599410b5100c80c002c0f250100d072418294031304d454000203001c038281301c3c100c00320003042e041d56603844203002021f000b4402c5030341c074903001170007441d51100f070241c4109607101e480701080c294108049004200c2c04900c0e4441d1070340c424810f1408a07551121 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 478160053 1250 478158803 478158823
    0x140f0706050f1b0109020301060b040305150402030a1a0712020406080a0b031e0c090f07090608040c0306140708070e0d020402071502070804090f060e06040c0c1e030e0909 75
    0x51042c0c0d1400590100c0c1041d01a040b1040614030091100b0703403601c0c50641081c00070a2080b4000c21a1640b10b405190700c600031400301602c0c9a01121100c4050f4a0552100f5040f500040032102d10000c1640d910880101141202003004054424440c48503013111752040c2c1d204c5002c40c15403d060610100030040100140600341c00307621091800078a131400d00854002103a00c480952600c1c082142d9035586002414806e03000d0510400015496074800c0b1150340104401e83d64211094a40b0308115404080640103503108600940000001100740c40f0310708006261a4042200d403070030400c05840708034000c0c182000c4c030804511240640d5a0b05075003c403e2681181c0050b01d0b20a41d0900035009a1107100050a0610000e1620180440c103005002103803880710017804418100440030080e0b688a00c1880301e035003061408500149019040300340e500da07051414100c83d0040e511a102c08100c0eaa0170f10760003000e0f4005090a0551100c400302c0f038504250786800325800c0500312250354000600b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 478161303 1250 478160053 478160057
    0xd1a0105030609070e032514010906050708040803030709210506061002010609020a02031c09020306060f030a0c140424121403031e010909030905060a031103040f140f0706 75
    0x100044d00540540c1c2c42c9030700000b002c0c003207982d0084050828a101100240d0851154110f41c000051941c100c0c5007102014206a481e03003003481c41c1c084162040d421110341115030000078070010070401002c0025510035500d59581d295803904e85030004180a1038001e9000a00c00c0902c40e90020031070024084c1d801070b17026104a0034108603954128018003254000301c2c031007400040c8103882c1c950b000020382a801580542c2c40d200c0c0011b07415103002c41d106200000e4043e0003190000b1030714504008012401400030b41601d04021103903440f014807031030750f420104081c5081120b203e264105442170001d506400400303240b14207114151104002e1403132240c003030068400c02c0d00204000210032081d502e5020704084a80b40c1c1032000b507030010102d40710082d000c1d105691000041024880c09954a023030340503240c1140450030b120501c00150300c04d106281c00d054558000c0140055030b6402144264041d100b00c140700405031526404204200c111003036180e100804481e444000454800d040321068 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 478162553 1250 478161303 478161319
    0xb01060c120e0111070905090708070303020c06090409080307080a05061815010221030603010f020921010e0a03030b09070509090c090a05210d08010f0911090a03080d1a01050306 78
    0x760b8012030710b1900c1444100ea2a000314100002c04000c5a0007090044a02c4400e030ba01e10340e1181d0906a8500711844064016403152500a0260030940b004140d40030003e8408140c00500307480c1d040080c0e00c00e030b81d400f001a07919820000d00908034401c1c9504104119200092020007411800e103a81000c2c2c2454028003d01038030202c1c5030700800c615880c0010055042c07111014550b0300107030309d0700102c801c039019508129040e90310485d94401c50380c05000051003010b044484601403101c10071400300f5040159662190a02760302c00811a8502041c441c0d540400c2030301b2141d0910030b1000020300799106102c1c0c24090180d071981e4249084d03501015002002d910707404290000ac50301d2003d83d0010b50401c80c02c0c0140c0b482a0500c1000100d218015402c4a4050400a80840301c2c0c000921a100501509800a201c17444150b040154007800480720130f8109400c1d500040c6210751213907c101c40e0010000b40d04240b0341c0d1940640c03000788070003256400380d0f00742ca1300c00a005840000c0005104002c8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 478163803 1250 478162553 478162577
    0xa030b0601031b020706031d12070308090705180a060e0108010c020f0307020a0b0d090b04032c220609020d1b050a0801120f120801090b1c1e08070c030b01060c12 71
    0x203100352000080d90030000c4420b8110040e44011441d4041040bd4000484041c0002e1800200181e03110071100d001d0840e008141c0070307010b803d502080260454203240d0b20b07a803002801c03003984417505020301902070000580c440c034014042d107045003640311810540c0081c042a0056034a03c460002100c400d5081a940d50303240d03070103410080070b80c000c0c02015050200280700a2540c05842c0c175104c024031205000c60f030b00030102c8015500344c081034815407003a9200200360443c00e4590079070b4440d030406440070541c19201e40410741a27030081c4250350101580c401e80000484203a0202d00c0d0780045a00300705203404c1c2c0d40140101580c3e014003c01480d403410792110000c020015a241c0051900442d0804a003403c640300140011004c0c07103003200300d81c1000c83c10403162030a0348468030301c020440601003c2100c55542c1d08010340404102400f2840038440d0b030008180e10b18001c1c8840b91046000c04012401c1d413420310316221040c2c002a040180c4040d0303c50002e8061540110b0345c144c242400035200c84 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 478165053 1250 478163803 478163831
    0x10f1203020a140c130207050c04020c0a0203011b09150903020f060405060d150503280203150a0c03051311120111040b0d0e01020a020d0c110a030b0601031b02070603 73
    0x99003603402003090060000707480e11640c0c0401e100002c0d20044074858109102c501d4001d042c0d000d50100903280d90054427a110403032800d60300500300781c0b9248007614100190340d00040d007110314503403002050421b680b9a0840c211351240c1828003070311003030894600003c407101d4020101c0e0310301d01000b4000c25240304445030b1a500c00d000c0e81c00a1000070405030b95221a01820340140003882840030041a0905001c01c4500d0301080c100b68181000d91414581042039200009811450400341d030540115500010601105d8000c0703881485895004034403022400401401c60340c0080c020409490700c580000c001840741404d4002134582210300c0610340300c1c41095940140603400b0f030791608541c00940080c001001c034021300009500f0480401c1008010881503007030344130700c01b44000160890301d00000c0c00760056400c002c00c0c034003802000c802800c0c08408183e83c501e03070350030175582190204104504c0d0360b8540140d0040190328101e40c3c450107100ea90103036642c00540210010302d5150701901000711 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 478166303 1250 478165053 478165063
    0x507110a0b062b1110020a0308100306020a0c0506090109030507081b01060602071409010e1603020c0604140d17010b0d0e2e1404060b01031404030f020d0305010f120302 74
    0x104000110039100c07848580002c10011560b0790890384003c4522041404d881c109402c0040426290041c0100030041d507002c40b49a4402001b09242c1824910040080303030f03492020b05082c444944400c0f01000003401c10a14101000f84814900e038102540e0100095121080d00d103100d500c41e805a4940880c1101c0d90f41c4809140c146c64055840c000b8009122076000544a04075666072401500c0101d4010602103444002d00915000007460800314280500800301c000328107006240040c240501310201c0b43c01e00000340c406417020050402010301500741440806005000c2d82080d49003040700b01c0350081091814481d0681000000c61401c003001845e8210721041001c05055860b00b9180c03008803c0c0e1000744440c1d10249514025001030f251a40d440f50000304c0d0380495a804d00d41c0c1c0c442d9542030180c1007041c000303410076403600b60304410750a003102d802d405540b00c0e894144480005c0e41e00203203007010761102c04080508040042140f0300c48000003006a0b0308244080030480d449083c10fa10305 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 478167553 1250 478166303 478166329
    0x90c1e0c0f1b0103061a030718210212011e150509160207080a0c050409020d1a010e06060702010c02040e0f0a0303020903070f03050607081504140402040507110a0b06 73
    0x1406455204001c202d48001c1070a030380b00098a00b085216118107150142071501c0720b010329000070030804107602e2406070099803564041003110511894031050704019444042c00c000c0d640070102841a021885d000c41e044c0c6190b202c9a00800c101307015044030241c0c032154600403454050f0344071100202c1400c02d00b40d03030018040c040d211544070b08050b48041c0c01c0d9124045200d0050040d07400c0440c419078082100c8500a03000905140c03a0b03420801000000c128402080340d0054904109000281d450640114010000180f42e1701c1c5600d0200f124140e107100500c914401d400c00c1114200507a00020002d84041d01941c00080390050712543c54039008040003c10424441d0a54850402d81d054000384500f00c825401c0c0c2d003a80e5900c600111100c0480d000081c0280c000c040080c070325602c039412150b40002028211445001c01d070b40442c04442061601103da00c030190200400e42c100780c0140c43d00808585081c0b0340c900c07001300c230580d2140c90b180c2d002098440e1034004202160f56540300c0c0104 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 478168803 1250 478167553 478167583
    0x12021011210c04231e1008070207090507050901030c020102090616140a08030a14190c180902070c050d0b01030f0303020f0d0518010e120a020a080f09090c1e0c 70
    0x195603113804100a500310500c201d8428408070300420880c0003072a441040a00318000390308941000740c4111000805030421840344010010f000a26402590700074a25910343c503645001041c001410303241011000c405580c010840112a5203400f01201c030511010007400040d0450361a002002c0e400b0400c504106114400341130f01440036540003140201c1c07000d00304014070a0500c039284030031241110310700f160038091190355001080070f412442050300d162030300d410744158040350b042e404003003500080f84069000c00c014040110440c5000e000d0725048411644180f2144d41c2c4c00d0400c141400010080086214004200f50107038050315903800040300003e80310b914802c1c00600901c411211540d084485502c014013400c01840f45004041469000e040121603404070704005511503844a030443c0300da12090f00200705281c000e4400388084210090b56081c8500812486d004c003e095028102d0081103401d00100c2c0d45403100040e00704d12004203803590b030703000860341c00c1040f45620110 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 478170053 1250 478168803 478168829
    0xa02030601090e060f010501021b18010314100207020a06051606050a15060c020907030b1201050903030a0b1e041806050403030c0201110405030c0d0f12021011210c04 73
    0x30104100d810070303480700301000203c880c0d1744c0c1e4005850310465403e02c40c281c0580c00600321104200c5c840d03409070070907681c05031004030700c00800600107480c3c6c6400d90041e034000c40c150204095000f014091034259201d10501542000c0c0076400050300d48110384601c005120303002490505a00c07e4903e44018941c10030070411043c90074808903800b402101050180210841d01d0214803140142c1503119103540140904020345d503004029002400c80c1c00100760300000580e0003100f8994240a20f601c61000140030310388070308020f00b190341992102102030348191004201c60800400c0f070a031390b0490b400201c902042d80039085246e030003d01c10f50741000e4006801e00301003005044d0103800101c043c110720382c005c00400c9400c61140b001c60103280a525415000007031580000d151000881c2c001d00e01502444808451603030b01d031031141010b20444000b40c2c01500c1180007601d400d1141c08012802150840c0ca00990041c2104800c0070b20840e0003141949100400c050a00c40d60640e00540318031400d5070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 478171303 1250 478170053 478170059
    0x71221030b03070801240b0d050c2b0c020f0d030519061e1e06050d021b1b0612010e090a0503040602031b010c20190c15020f0d110a02030601 62
    0x1c1c046d20480c5032060840018040c802c011010f10780031001242c402d804480e0502d4860081100600070145c4042c070101d0060000d241066801c01262a010302c103205882c080b18038002c040301c169003d0140e0402550060120031892000108a40e455405240340000321303503444c085080000104400c1410690340b610300082040170109a000340010a0b5888152019507a81305121241044840c8400c148000718010001c660055024224a0b0701d00e840150605107800100544010030b030701020b00c258400403150380000558100c0c1d02d49110107a41281c501038000c624001480b20600c0b6000605103036100182080ca0240071410a29a0101c140d0783d0741d6a80750f0000b903513500500c42075000da64208a4003800a00c05105541d101039040e141d42c1601c90462481c200e141404040850480c00740d4081e40614030b02c9803800c0c481c414860300c0403a2001c0d040090001c05a00c8500c14070007550f000007828003070b2140014500403000140c0c5022072000b0980100c1504007070b2021070094043c4103060000c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 478172553 1250 478171303 478171319
    0x2103041707200d0309150c0f0c17030304080318150106050d0c0c0f0605061504080604030311090d021c060f0219140a0c06180b040203071221030b0307 66
    0x74041c22200410030000742422a0100b0401c40a0300200402107017041c80100314000540304440c102c0380700c074106000d1140c0b807038480300703400103075031204403090720411000744003c85107101e41d01c0644072141c00841c10340c038003552202c03030754400581403090071070800241011455003000381480302c2c1c84100c656a4296510100900150000b90300d03446810f0034001c0c818007891140343c1d1a011150000805502c07031040d83c44074070042401504080d08210900c0060b44400b5200c0000c00007031440c2c2005180c280b43c00d040080841d10030440800e8000d00402003009207642e8484910000c0f90100c0b10b4003500980b003840c0107012400100000c04a6080c1004401402099405010240f940480e150020281404201c0302040110005400980c1c1030000c00a06841220100c81841c480d03c400591300400501041244480703a4049a210624130100800c504090000000400700c2801e09512175000f03070740e010314161201c540106005501f0201d500c1561083c1c108152005000e000e41e6400d90b143d01503 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 478173803 1250 478172553 478172573
    0x30806010206060312040b090a17060106030b180612011b02010501031407060819110d051504110906030a0906060609080106150516050a06060f0f082103041707 70
    0x29560240c000d0000092507400d010500d544000104003150b854030b4140b10301c2e4481c0c0d402200b0000d0b0441c42c0e2400118454048041400b18116040010441d1f50715040c0000d0030780354088811801140d03c00c00b150a0200c2d0344045c40d41101044442e803145031040030020380141486651800c0c002c001921030705e41c154042d0301c400e061320300880c202c02ca00035120244039540c0ca2503218080004102500040c0400051903109405141d03200307010418040f1120340c42c070a5043b00c001649600d545900b8400502182210890342d440d0a4800b40201c0399010301c008054080c0310b000034050303100000050802d00c0c007507200c0c0509650101c41081015241e45008001002e0ba000d9200151b191980103d00b01416000015440988ad550645444a5254000204116031134102c2e401c0c40b90310042c90019040303024002c00b511603e070386071051503c0d200e1360300c200a030039900549154000c2c2000c081c0c1141040c0c0c40d41c80c40880c0c0220980c0c0e0ba00e6518001000221f0344520100001010529408000301084 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 478175053 1250 478173803 478173811
    0x10b1306080609060405070303110c0301060303050909070311030112030e0a0e0919050a020f010512010e1501030605030a06150909030309020909160314011104030503090405010b0a0e060f040506070308 88
    0x1c2140c229564402c06980e03251415500a001c2ea8001002000000c0c80350711001c580e004010306681c0e0001d00c450100e4252070160300114003056020403a50114200700000c10742c4441b140c0b07410f100c10305c15041020103510040c0130b01640051210041c81c140750180486002c4d4280190032400015543c20f8548814801a5001c000034003441d9812010416080451012503801502400000c401a42080107180f1a4840030f0b041c0700d030074440303502c803006100b4440e8000e02218941c1561031801c080d82c0c00b03402424030000343c145403801e00184115140004d10212180e40700700b002800c860215184d2a04580b154015544582440078020070140d058200c858030034802c0c0d0350204036440e15541c2a489103140d104011220b203943c40c0400c080383e01c6408001c170340580d920001803d88041510f11007554400d400aa4941c0e200068800f0107050030300c5a2401071028000b018200045800c3c02403da0800688440c8100004940d091102e042c00040341d00411b0000c0c0256a0303102d80b03240160550804036 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 478176303 1250 478175053 478175069
    0xc03071d1f060c060e06070c020108011a0418140c04090614090a0f0f0914060106020309011b0606181d0d0e0618100816030908160203010b1306 63
    0xe01040d00c0d5003940390318982184103010801d5405040001c210389a4142030401d440b4944c07120340343d4650340700920500c1d0003140107640d100e600c2015800003518809060340400c103021444a201607122007000107480a8890045403000e010028a64560103026008080d058600d0788900303001c03010724801c0081048814003441805800d076a1141c1032400000c200e4455045424100010880c085e00d42c00a40051480500002c841056a811404886c1d00340000c4a58030301c0303407202c050140d404000182c010b140e644000c40c90105400e000901140d1b55202c140001c0961203c2075003000055000040900b440301a4003002c2c6291010500141284107590407208401001d032100309900802c11910301c041d0b41d290a2601031401c81848011b500205078108030740d9450041c0400c1d40c1da00c0710f03145019540c90341e4016841c202040c3e08041c4403001442c5038249440c054010000540103400d44500c00a441001c02014225001190150001d1102c460788503008a19858150180ba400841603d000c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 478177553 1250 478176303 478176359
    0x4021c05010b090f19080316060e0304080d0507140d03020d0b0409050304050f0a09060312080106021b060a110f0115080105011d0711162408070f020c0307 68
    0x182c4810803440c03003410070345900540102c0c5501e0450400303031391501c02c40c240203041e40a1259141419415078114010408003000a244d00c502441064001c43c0a551103410245250078506000300c0d41e24008103d2040a1050226010040c400c00d4207990140304100c10075550441c07075459000300254031241c041c1c240c0341c0c5400801c401505080c0305094959030f104c0011440c0908000c10400e51044540216510544201000c1103032001c0c0d00031080214403540c0c0002581c07a140c24054903800d0b050300705008660010308400180c03c0480c0c101c8030350341720660b03410382d5800f03051404580180500c0200543c41c41a0818440c5d4800158419420651708613200407070301d034907070002a081e21402e1042180f44400340c0b03070210220050b0301800790001d19a04060640e40360004000b0305203030741c1c580c449032410301c10b4000302300c641d0751000e800c41c0107042c2d4107501402803106040540301ea580034104c0805c0000380c08415095900800c219001c04400504440c2c40d107554014605480241d04001500d150b14 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 478178803 1250 478177553 478177559
    0xf01050f03070807351003050a050c04060e0c040b09010e0301050907090c02010b010203030a0b0307151205060103052202030c031005010810050603100e0321090f0303060d170904021c0501 82
    0x4203003102c801c01e0b5144003803100081e9003102002541c0360146c201c08008000b00703800400a0703002c02c040d0410b40c0c820001341c03004014040800c811504181c1c00724107035403861000c100901a040046500f915001c20303003684c4403d0b0410040f0b0300300340300b034680ea6015840c082c14440c15400004056007141d410400912400031b00c0c0004900ba6190703032580d103001d6031040c0081461011550032050102d100641250220f5a40d443c0844243e40c80c800883d003c0b03620008030345815056405003e41c800c0c000e0805010a090412039868141c20915001200040501103001155400d01c4024606a0018200d98000e0405ca503500000c1c4400e1145600c1072294001d002c901e90000c1c09281e202e002c00402030546204140c520b18090f0250111504050004000590061441d103000712441801e408020702da87c40c040340700c1850300c040c03140d1709082076005100b00708079551903030459050240e0118008000c40c03074407407011411740100700c02d4507407050000c50b12030b28694421000d0703012181003150501160341e07 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 478180053 1250 478178803 478178837
    0x11202130e04060207050d0e030a0f1502120106020f030910320c0609010608030919050a03060f0c0305040816050709050c03040203060705030603060f090a020a090c2303060f01050f03070807 83
    0x208c0342e200c4e8060b0040d055034004103c0c220303002c81c0e085014000050742c0809030001c4100300c2c0c1c4001040120381c4510700c01170044580c10401a00080c0c041c400a601d00510600000d500c088148141c1081102c0a400084c85103040301449009465496086004000003000c40045811000341c2e10054842d03100080c0100405000e6882210000b101440c83d08207410140a00010008211140d00403d444005000d0301c924005030000d41c0242d00000d6130307040d03000c8820241c81541621808043c00c1c40184000306580c0011a8040c1000580d020384c2000540381c07050502040e64022000d5a1420b400c00200800f444c00443c4100c1c4200c042d82c84c150740d0810103440c5808156000b941581c05100010901082c1c48000351b08a08001e04403a015403040c0d0010b203800f9440d80201040c0c6840c1e2041c0240e190300400502484890054200d1510040000d203280c98000100600e200f203030320060300e0860f640100701b00c0300019041e505003a07503445c060310050b11024055807100001100700b03040c060303100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 478181303 1250 478180053 478180067
    0x20d0603030e010e030c0d022b050601030606091b20070b040504060803070b0f06220c020c0103021608031308130e13031d030709090303050f0a0605011202130e04060207050d 76
    0x81b00030003280f0740400c0e540034030070140391205604603010646965000d171510350300520903a10703200ea4014001e560543c500702c8280c2d6200d1748224001d505004603c41160000361484204003840e1a01424064085803040c0601d800940d0504d580e0048050100d5148003440041c03041d900c007a00c0030b009090f47c841c1d600c2d40d24402c0c07060203400b82c80c034200403d072440d40600380242c125078010003903440c0d038141e0980b0100c0e807204051b030f18404079a150f104600c2c042d01030299183d00182400c003107040c0000d85c411f4024482c1d6402004041d02000000508146040043e580303080e0b40000d11203454881140003005000c8850254014803c00d03000018540c88020440c850040d5140c0d4030100c401804084442c102240d0481c3c0c594580101c690110328500144a40c1e50800d0082e0340101d12401c0c070888003802e00e00060f03e00400c03c0d082c020140080d0340c01002024011b4041d00005a0311905070190404c1600719800500901107103800740828007000350013500c4514060b506440d83c0310713404041540c01c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 478182553 1250 478181303 478181323
    0x1703120112060f06060527030a06050a060e10290906030a1b1205361204180b0f090105010e010c0b0708090f07060512040303020d0603030e010e03 64
    0x16110040061201881180d42858501d218241c0820031101d81a0000300395890b0f500003400051010440c0003000321840700c05201c0308140343d51283d18482d180d0100340c4485141c0300280c4100d0311880407800003805644000020840c00b41d000342e07142407880c1c1c83e101155081c8158654010001000102c036007001e800c40b012210501703215450700b05060f0500c0203580005100c0058a80c0c1c41c6030040001082200780c7d0b0348c2c00002e560711484a0320251b218800c803000609420910b000554400350603429002181c0c0811400086140d43c0043c030320003003840d0400d84651142d268901007400200c41004c54180000000c0e074040a01415516100340f0091a040c0400c0a42c40340881c4010070495004803040241c100061611101d030340a20740310143e03400f40503604080002c000340204508090180701d1400d5420700d42024090a030315060009080380140148184a0988040401c0806009604940120780072040c1031082c40e50340c0c2000303000d02d11200d0ba40d60102d0400aa51301079846c01084455003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 478183803 1250 478182553 478182577
    0xd2a0c0305071a03072a060e010c031a0d020a080a080307080901092a0b040806040c0509092d0f0106091d06160e03161509030302061801020f0d02041703 67
    0x1940d0303e8910444910b03d40c0c550141c9980584480c81b00c101c001e64003a203800c1801102c000c1005420102c0c10750031035400c0b07900c8104051524000c4210b590076150014600d50048a40312070001d094000206c00c1c2000d58000845486410080002c0000c01006544141850340b03442800b5901d0032146801c1e038155040040042050541c0b100c0c441c4d080d152000c01c54030f48140506501526824520403079406504020344540c040c0040004004038044100f01a01060340ca020407400c0c040341103035940c0c018911390050051100000305013910b94420b2031005113030f031008650300308601e20105402007103e4000c07043d8050800d000d5005490b00c001000380c21016071401030000d42e5441115000d040303011011282080003040761041d07299400c00680c4410466156070402c0c00749440201540190382c10702080034012030b0941000440e40228074282d1001c140d006040b190020280e003103009100382403a4104d0398802003820003808100d503010b00f056901090811101a40096545549010b0f40740842a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 478185053 1250 478183803 478183807
    0x619050a0e10091b08030403050f0304032d020414060f22020c0c0a03080d050a060b0304080a0c0606080a03180b1b03090a090b011b03020d2a0c0305071a 67
    0x40d0041607500010619018111030040400c03000b8040d440a0300d245d0085005910114051043c8002480812051000c0000942c030306480c0d50341d440c003240900360384681c2042c0030b10504200d140521074190280369008204011f0043c0681c0c461012840c10380381580240f10310032454010382480d00b00c0c48065040c409042d41404040c9004002070b50290f1243c414a026410383c048280d1240040c4101440c854942c0075222049108568211340340242154070a50900100f00680c100c501e080307076040f5411076882c5941c0d08443c00240c4490200c084020007840c940340700005d9111020410007c540d00c60f81c0c402d2130100f681154450554803078001c0c071042800401410343c2c598803d803851740900340079006480c06c0004c2080050b0740710115600202d0304c40c1c0c6030100390115613407000d800d00586181e0140e144a83d002a28003c0d51906100c0e0f82006000d0b09080036a8040c01c180c001c00c6046441019840419030a850500032400152008451500c100d403c0818050301c0c0d119060000c3d0541d800ba14 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 478186303 1250 478185053 478185073
    0x206150409031803050601170106060509010c02040212010b270604060e0d05010c021f1401061b0f06060317121314151008150114030f0619050a0e 64
    0x320051024000c11424812100740d5031010b00000d14220000f5400381000d40220361400004081000110680c91400e0b4540030040c081a500310043e9034002c4028601081c22400a1011074028400c034200384403010381034000003800301400402411709148030300004440e107400000040301320030a600c8007680b01c1c006100600c00d4a208211003601040000c11201c16941291030707140c00c60f4a104402c00040c1c20464502120203600d00808000781d041c03400c100a0040e0650404c0d14110303060040d1010401d4912104508814403e01d0184541c4c03c090314941c003c9a5140800c01001d030352000f101d001a514200a500c0541101500d001689580d03c0c0f80d00340c6d503040c810840306000c80b0422691002c1c40381903030600010400404e0700c0d2401032090750000d41804d0407148202c825030750000341540d01640e42451140070120090307044035150a4401c0208140d0400070f410182e800f000408548a86810042c540356080100e01480030000c0c8100469220703a40704009544200e041c83d5a035030700c685521 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 478187553 1250 478186303 478186309
    0xa0302060405040b010203160605090d260a02040f06050702031b0a12061b02160e0709060e031c02060f090102040f0506031003020306100305070e15013e0d020615 71
    0x2c0102d904c1441503915052040300804002141c040701a2055995601001001d4804201815640141d401c0ca00c03a45c07581e05809241c480750503001000c4d941030715000b28450001680580f005403400c1c403c03d001c1c0c00d8613450001d000d40c01421082e4460b10801c1261130345c141c010798094a0382140601421442e5040400c01180803174002e40440f00990784204d60700c146e405018610054280c1070380584020382d80552600502d42c4190440c0070901080814054020740200c44030045a00c00c1c200041e5110030040000c1c140604606a12180711025600c5560700c0c0d070114040d80b041d2424910003056485842c0d10324200c0c000d80c0038400307801070030003c14405440c214010310303402040c40e0030710720700c194482d40441d040203400c0da100040c46840b10310610030440e0500c44a4003a140e11072002c440c6240c1700b0340400c0e40340c41102245041c000b800641c10040700b00c81d96600d100d03040f90f080b041c0d074100c0c0394081d06080080c4040c140009015454112406501c0411000d0007007034201149110510a5010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 478188803 1250 478187553 478187561
    0x2030c04030b0403020c1801060e0306061f020f0106031416080622020a03061d0c0d12050c1507030609051608060f042a09030312050c0f07050705030c0a030206040504 73
    0xf0940562003140c071044190303a114943e02c0e100c008032140500da0f6503d80300d0050305070060000304620a4101b6000c20500d502d40800b58640c851941111003203030741140307006906007000044220443e5080c981c010061240c0c3d406902d0340810310008035040181d4804100d13040341c0392030142d03144079004074010880800c102d61040c0d0200c4502074074502581c040b0b0f03000130b8208500e0741c0200d41c19034403000c814605940a046660a0824685c0541400400000000c94440018100420001000d8040d100c15441407055030848040ba40c00c403400c0140b45a419210000c044840c4d40000307051031408925014103002d00ca01a5014116440388900c87c98801c1e0380c203d00042142d41c01641d07518090950b56198060403d5101d00c0b207409001142600130b000551008200350342c418000352200800009510180b18881601c54000c00030766a290714548004c144149501041c501802042c84001d0050202c0d840d4200da06c102c3c02c4600d51507ea00c1030003038504491101a500903001c2c4000c10407801c09800c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 478190053 1250 478188803 478188811
    0x170c030f0a0605030d020610060c020f040e01020708070f1b061220040b03010f0b040e01030308060d02041b021015120c0b0307230306060a0e010201141f0902030c04030b 74
    0x81c002c540d0741d4590b40800c0c41d0000001c50300b4010b0744140180a4a07080c617a48010151820340303002c0f0000480b03900801d800c14080555903010704ea490104500040080d415a0642c0b45e00070001a55440355040034602140e00f1041520415951800e5a103c0c0c0704108928040f548141c5981302c451700d109161100414540290b2400750700441041080c0000340001007005d4002c0d0f070210760300e0b1350401480c4103210156810165000303000300414820f100400c1c1c01c450449605241c10b007119038401000c600011f078079510003501306051030b07490301400d0310ba21014681001d40ea0708035520b40c0e48000c084001d8a4070080d0b03074166000e52540c240a0000000f08501406019414160003240e40360110700c80c56008681040008500c0720280d4101c00c014030111388030001e00318001d030950a02400160081c0b140200b06001d0142d0030301d00d912164001e40200142c20441e00344026940742c030a0b401c45442c2000302d910624644220030204c0c0d814110710969002d42c00c4507034003d0810f400c50341c60200060010b0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 478191303 1250 478190053 478190071
    0x7020c0120150106030e060901090201050421050303040609142a010512090303040c09021309021b0f1e0105040503090621010801140609040b06040203060a0b0d0507170c030f 76
    0x101994440ba56006a2500905030341c0d8000514403582c05800d81010030180c81001940d062590981c0540c5e800420784050b102c00c0c140303e214425118008902c01c074030341d540050150101004002c2272001962060161900030600d005190180e244070545a11030182c03819003400c0c5491220000c141d03009840300c901581814840d00e0044007880d0150035a0701124680451b074400400c005c100104604920300400d20801c0070b41c04c2003003503000c0240c040301c4c9010f000c1c00654082403110352500d050041401036078a40003620f421040e0b205015468100104ca404415032035550062008501407041612480d0441c000c0d40c1084819420000b444d40b1142c031044400880d0503001c101c491312998070b140209034190000592032001c48c28954003500080019200e81290410071011400507215280d01c480115401a5030b542e659002840201980c0c1000845000c0413a0640d130400c40c2c1c1e80082d0092020b03480c0c0b41d0040c20900c1445c0d030303010800c51300f850036400e080c0040780481882c03c0d03889802610340 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 478192553 1250 478191303 478191313
    0x903180504180b0924060a050114030f040c0e0a0501170c01020c0d0501060e070207060f080601020a12030e0109111e100e0406031e0c050618010c0809120d0807020c0120 74
    0x30104c0134540c03112080c0c40720303c04c4011086c4041850041e540310300a0100f828010081c08403070030f1043d4180801000c607003050302e5100002d400c110300300b446900035100910002c05503081c9800703900c0081c1424043c46046a5500c0700049007010001102d000d40b0005034010551304c0035000c20f025014020000882d110b40d00c501020038203204c0721090910811656000746507440c90301c440208652030120f00001030105607400e000e401c0e6804111400e05c190444841c00740300d11101030031001807d0103c2801095464a4031038000c100031a40840315104044039110204180304c450707200200288189282c1c889181481c01d100107014607c8040e064100600024005580781c482c0300c090100c1c4072425115104070328980c4208807810765000098001690041e040c0500a2080c030f43c035246458045041c4036a140b201303000c010348102200c8003900c0140c45818628240402559100d9108440001103405200091070035403001440d4007841205039100d009401042d01721b01600106070030021114090 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 478193803 1250 478192553 478192573
    0x151404020d02040b1902101a061303140a0c0e06030307030c1502030f06241b011e0e1506090103171e0a02070506070c09020307050d0903180504180b09 66
    0x1c0b006001791015101003d032032496500c000900742500c205140300d0051070080c210700450100130500080c00c50644103143d4440908106000d5503080e0f80c4001d005a01811b42440315080104e00384550034414000708464540316100750b01c0700203003110256019401400000e0101f0311070340b11090220f00910400c18800b14102940081e644119800c80c49040d020b01401840d0600c4501580c3ca07804454020b8841c90454070203403d14810720b446091b524120840c1c40b132510b6421b5225034103500015100700303c401304a411241c0038100c281203100d1035001d40c2c4244010101c00b654413612405005054040303603801d40c0d40d0105055840345c0308401044041c0440003981910008610085061200c69511600f42c18002407800140f500041d002e02c0007401121300003502d40c5e0444003075600000f0b000d0f03225950300004480c0350040c6800f40c80c036075007841302d20b006154000402482d40600f01c2c0a8a01203503c0d0340600c01074034034950b5071041105807600403074003080c05080240c1d041a0460180d8104100c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 478195053 1250 478193803 478193819
    0x11010c0f1203021b19030305092b08090316021c08030711060109110f0304032303091504021c0804091409010609110301060806010c0602030108010f151404020d0204 72
    0x4182074101d80820760004c0d80c8032601905080c081a4444440700424242c0c800c540c505404000d2020010241501c80c4003184900c0418072042e0ba04603000360210002c1030b61100302710034012102001c400030940e08000324130380e404003000b205d580500030f4034001074200c040d60a106502c902d14072085020484e2400000018040c040258010155544d82d03080c10b072075040807141800c106900075070704175152010a20a0346003500c207640400a6500c1c04a899980350b040507200e078241c80d0030748480d00021144040d001020701010754003c003404002c40f0b01c80500500f00100c2c07100c0035240a5404000c0349210181c070124840304181d610f110f201d0503400d2540d122509401c1d070700f6020440b11480b1402080141c4070909120700d10003441401001c3c07080d98100040d12000d4031040c001c110420095030005940ba900503078001035401d61104086680e5a5a070007018020081c0351450f824107400e0148440000c1445980c2c00180c4007041d0503030b0350038050441044000c0d4001111080c10076000d10000a07491 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 478196303 1250 478195053 478195073
    0x905210d050114011101020a2c030706020d020609160302060711090132150a0e030604060903080603070602070b160606030825080307031e090c0807050306010311010c0f 74
    0x84074014040703084424100140410b40307440100301c0c0310b87c414410b44c0403865000041095000741c0159a40fa02180d94002010701910780f80c044e41c042c40303002d02c0003445542c00100226607007031a9003940c00f1922080c0300f1a0700da0001039606409540040b005001525007000208103040c0301d07100903206c40c6025004145502c400360b0003041c0c402910070152641506040e9182084000c40900040b43d0403580d0005090303070200c40d03070b050044034041b80300f41c603250146601407540c200003421034540780340618001010704044c110440008550740049162802c00040c4082500c19540280210754101030b5000b200b40c00c000d001104550249001b00c000c5030040c41008061030050606507510025070b841d0100544142000c020781ca404d000001d000b05003410140c0e5040075880ca80850f00c0d1101240151101d161020070703034220303498600b944040010b074254290480344508140e41da41540c903010903455110900c00540326000c02810095150304c0343e50301c10ba00314400c404032002e680041c4c54002c600 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 478197553 1250 478196303 478196309
    0x20c010806030a02151b210a050c071e150210150e0f01090b010f020c090601090924060f050702190b040b030a0542150306090702010905210d0501 64
    0x390000241b1402517001480910200c2003c00f006040800300e0354020101d0301414417000b03952201c0400c0c403201d00e0f485041240c411345c811a08507003100d070322400c003400d010080043d181c3c00c0707101300300780010407801c604500c0090080c01c5d000381c0350146140c4c01c03c00c00703008220703601c1d215001e0713805000c030f41c076030502c0400c60040d4082d031607820080d03050026a90484030801403a40c1400821050300300010360000d4011480c031811748076210503480d12801a103d00c1710a810400c8143e007040c0f00b040c0c2958200364070140d40c03128004c500e4602562900107403003108142c001040020420001080036007090344070000070001d80d81e42001401d580e144e0030f10854000d034000040e8008008184501201c66001c0c06801c4820950020300b0780c030b40865550f29035150301c40b44140c0086002c80043d665822191114401c40c0090b140c208900c070301c10745080d0b0650080f034529104101400205110600c14460fa010259025004100440c04020aa07801c0301c84030010b840034100412480384204424003071a402 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 478198803 1250 478197553 478197589
    0x111e010504021003090c060f09051f020c15070f05030706020f0a030e2b031d03040513090c030807060e01062309040c061202040e010602060708090607020c010806030a02 74
    0x403400c1c2441040b1400e850410301c1e608240c18640c00c0d40104a9418150046a40c107050818166495900c140c42e680100c0c3c1c4100d03809901c0155175041400046c0710301e0521400390782a41c0d4018010000c101e00f110080382c06020000003070001c0c03000505c0d0080100131190240040f24113002003503030303044240c0e40a0070380d0004400001c1078040895805004074180701800c600034045440c2040b50000c4e2512401c9010309c0e540f0031a0301c580354400c3c02940034002c00f0420700341e10301040352140902943e03640940b007554040c180220b43c1e981d800c41d10380700b08a40b1660001f001000d5514540314000c00d900016000d139505560b80245030b110010902c40d0030010155070900204042890b1034183c4441e00200034280248615070800c8000342d508240901a14030a0038003651020545000c18001d002c1d58200310703806038004001040a51300080c4551140d0801e90f03031403206581d10b02c0040d407920700c04c0c0d403046c01580c000b05600750150300a000ca02e6000202034111010100039800180001c40c071880c814007 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 478200053 1250 478198803 478198811
    0xb1f030b09011406091003090b25050316030507090f03051507020f0607111911040501081f05041103010903080103030f0c050a080702180c09240901111e01 68
    0x500e0038103030021401000702d000343c0107401ea00e003800310b4468842d0744941072081d02d14212218109020782d00c10003580380c0044105085240524038101021800f0400e108100c0300b45082e01c11044c400d1084a00c184000c8081c00b803282c44082e4140c0c00344c203020b0019003c2c0900203401040500c250310030031000350f0180f8000c0895142e04204c03410580405010301e01107400c10320160f280302000041b01500242e01e4a0450b0702c040300400f0444c01d0441a0240c141c000002c14038880c10701c2151011084a180f0031101000b281e641d030b502c555a03a00007102c4107640303000c49092240c0001da440d40030a074014050300703500d1040b400c585c00090850768000001ca022a0903807005200f4107a110541038400c8410b400c10845c0c80c0e602c0e803140c3d9520b42142c0d900805c510310018154086441c0c0c1a4002404400801009603a040c9880c41040320340112900314000c40c80d9007441102c003004814084411609503a182d46008004401112101400e200c0702c1d00782c0c465000d510004649680c5458130324200080005 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 478201303 1250 478200053 478200071
    0x6080a05010b01031125030908030a020c031203100308030c07061b0e041104050402070503090d030207080607081603020703030b190614030402092d0c1209010c050d0b1f03 75
    0x14040328200300c13140740119824001c3d580560b1441c580f200c8003200212180141d2446d5240858a03043e854208201c60300010412050603900012940054101181030301c403c0c403c0c09501c1c3e511808100c4005a40e001036a41c1000071960640040d600201c1d00c0800c580b40020130b4030727650150f8889102d4403a99080100f400b1006590060b554150981d00304d83c20f009402c81c00e01100030a000d140141c0b1f10031903000034108101725042007199211340014018010b02ca81c6410702940703808140c840c1c070903180144400034081038400c24107c0e228104030381c44044404043d490840094000507803c4040c142d45070005080c0e41c7d138040145110403580562030b502c00f4100600106080300015100c0d5210070300b40103001c0180c1e160040b560f401a9650007881c0182541c440c0c0c80a40404480200c21f620000d82c02e0100009441d801001224081c00002506840d850011401c8401200101001800034000c00c04411802e410003808550001d02c90480e04d0803541c8100305100740c410140020030358030b030204 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 478202553 1250 478201303 478201307
    0xa1e050d0b0915040c0c021905011e080403110309090906011e0e01060804020d060e06040b070509030c060307020709020430080f031018090b1003020a0b03090106080a05010b01 77
    0x440c54040182c42c811000c2c1064491a4140c1d412081128452030f03c031000c0d2070ba0244552120000d0705d8009080040301016000581d18014490044a0008840c994550030100c00c00303441d90740580342c03a980d030021035441da20101c4c1d15200d510000c0406000400c1114203c0d0303100b000305402980000003601716035250944c04408550001c080703003c61810074804000140b44014050704481c0c2c1800d211031140d94030b100140208212039801040c0700c2c03401c042d4040c4102c001460601c00c2d881102a000d06071507140c0180c1c0d080c022030804582c15030140c3d07108042e40c202200030759040185801154001d6484440000a0380c01c0707900594448031500c00460450400c81090f4000410744115261350f0b240d060301c504030580310303000d0411020840000441c855103814441200141400440c8800d08200200c03120b01030880b9130810340d41410302c0340100303603081e952218000807030303034010442a00240f502c10550015080200090a00c1d56100c0c4c0c00a6150b07002d000c07410500340f285000041138580d00d000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 478203803 1250 478202553 478202561
    0x406020a0309051006170703030206041401110c030d0623151b0a0b062209031b030c020111010218040509100603030909061a07030309060e01060902070c0503030309060c0a1e050d 78
    0x302081f64000982003020030780105106401c2600898600c019641c1c50046901421040b090035201040002d07600c0b64440e03011000e00502c5400380414481c0170381c1c50b440d1462084001484401040c0c076111070401a00d46a400d11004407006009581070650705501004040c141c01c400b942903800440700c030001c001f002d1202c9544950f017201c484104036aa450489404054100d00300801d90303131014160180b6000300031003d84c1c071840d8482e00c0e802c1c007100d10307008001a4114008a01281d082004100100018001d54180002c1030400c9988480a1410003000c0d00e00030340507907018060610f8642d0030703501c18090f6030041e5019883d2528841d203003d042c04202c94295010042d100c18101c0c40c150800801c1e4111104182c240c42c004c1140986400e1400003040501c851016070340c81c01da0000b882c010a41c02400141e401510034100309075660046c591248011240c00c03019030404000140d030040c031080500000304440c0351841d81480c1010180000407010b0030500d0201d803000c50010840109401 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 478205053 1250 478203803 478203839
    0x213022209090b01170a0807030e0415141009030503041d0f1506030406020c0d0908070501020639070812160210020d0f0203040807020a080d080406020a0309051006 72
    0x200b10100e803d44a09040b0b00041c01803d189400468081403c41030030010131400a41010b219543c803185458050072051481a00e180540d040510500c21121000c544c10211203003460741300d184440700350802000444c068415814001c1c015404804503208001910144c140e00d489201402c41070280c0202d540d0000f0110b80030030710702104000710b4880c9200c00c00320800041d24050b4580d1228500280a8003440e015880f60780b047e80c01c4e900015602411500444900409a40b08183c07184e004a0b100c1d10129951008800c88042450b001101f05d03045024416141006204204030660b5204165000d1181a40c8010b808034030200111807051001d0b8220743c010280009101150001a4454080441c1e2410596020039099460780c81500801e1604289030011942c0e4601840c10292541100358280d0041f02c1c40c22000c5007584000511800041150322100125a202c1c1e4403400070754030034081d0030205501e86409100041c81040600310301243c0c1000410514146525020351103000c7c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 478206303 1250 478205053 478205069
    0x7030834230309370f08130f0506040b03060616051002030103020f1c060b012f060f0c03010b0708090a0306020304110109051026090307052a090402130222 68
    0x80c880c03060030441e080c1c1c1c070303502403801366458940f4440310b0810110100026101401c14100050383d2443c1c00202d1501c8000d03194000360000c5900c0d190301c14091580518050540b4500c1c4c1040814090b1034420301900d40305040b45012218104103544070f9080c0840844901903240d0080014400c6103000452080042d2054800c0c040c0c4881051051004910342c2e580509581c3d590b0080140c0d03030344148201036030b4811803690700020116000080d01c03031803840e1503201030714094000800e810403d84070700070b40100f008505250540e400c007041c1141c03aa008500840340701d0002c100c0640903840d107d0030710b0000c1d8054540183c0381c1c0b81c142880040d201d1054030603070401507819003d204694030410b00030700c20101c6190144141238422140243c80300d41d0ba50000d040d1070500300b002400d010002c002e00321203210707009503071040e088020a090030080380086884091003c0580f80c0c85820400740e03503680540000d0407880704880982d0507174126449001d810001d07001d0204440c0a40d81c452940d103006248032 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 478207553 1250 478206303 478206343
    0x602281104110310142b0c1203031112062e031b03050108030406030209030a0204050c090a0608070c060e16080c0103060602031204081b0d0507030834230309 69
    0x1c0006480040402c80c0014480109014a0170a8401300c6c5000c417296001c008256404c0d2600034244029420303640840003c7c0c1007885044040c21070704151002d40b101e404949050352202c0e0200a481103c00800f803507114503418035010b202a1040e041d2420340301e184c0300010922448108040d00400c4405c81406040c1408010806044000222401c5404030710b40149c5850707400002030b0908010f5034002c2d51041c03e24081c0b1440303d03000401403092905c11039191204035500c25040e2000001214064007160140e01041c011804503080035030740200d03070800e407086003460403918090800e03281c001c28083c0d4070125100b0295605881760902030683d0380019410f08080c01303140031061000900c02040a4004036420500003160500e0301c00450060041e00d454840c01c4100a020b60808101030b80050f17040000315280c41100c00d12900c40c0c0071044210004180e64401c0894850381902c049000c0142c1c04103040d2006c1158501c0322100441107202c4c942d0380c2484022503241c50283c0c00030f04003032580 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 478208803 1250 478207553 478207589
    0x516030f0816020c0f03030c0a08030f0f04050606090c1218010f0e07030f050c09040f1703041e0c050d15060602010507050415051b0a020a0602281104110310 69
    0xc0c600200c80700485054820f917005002180c00d45c095001f1050385481034104c8542044a023001441c424071803d654000c07540c0d1004180c520031601a10050640d420a20120708079040034400c5a5100041c5110382c3d152a1046820054007c41240c988090301c8482807920142807080c013907006021980c01043c8205462400c0c42c6442d110107120051100301512078200820506001c00682e41e00c0c020b21440d42031915040c0780c0079244d00a40d04945580b000942c5d8106a1400c00a07280075503004001070084c507000358115040710504440540c2c40f0200c00c0030000300c6a449590110400744610b199155a0500c10740c0c20717085c0c41c1d55030441025641040d0402c840198071805880c102c800440391444814051002035500d8450803840c42045000740e101d108000c040042c81c00d400602c00d462020380b01d5910b1000720f1f11800e00300c1501c05401c095400f0f1303400f116054160201c40e80e018401e00c02444072424006012038540e460100031550000c802c11641e040703110140d900819805c030311480c00c0c3c01 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 478210053 1250 478208803 478208807
    0x403330c0f050c010e0303010e01170a0f23100f0b09010303230c010204091a1522090513030f0503010f0902160f0506061c0c0e070516030f0816 63
    0x1004005620070048041004410300b8001d420500c5d42c01e1216050b81e41d656111180c04200c19424001c0c034070180030000d41000c2200001132029412908030038040e03840e075007540d500441004105003161103a103400d0304a9981c82d6050103004030800000600140300c50500d4102010384555014092007141c040c40104082604440340b03800b03078010348100000598071800c41b0203d6004a100f900f606610218010a1002d03040d0312040c521030320140e03442540d0700c0c8501044084001e40d120003190030000c2c400c00300b1500d00ba01c01c03010042882401070b80030315114a0203804498013224440b60030180c040c4c08105041d001744610520185a01d0054515030401e000091355117510301c10422003a6001420109103000003801d00811540150a20a17142040c10182c0d07880c00c096440e44d00c1390850301c8030b060814915011134035000390b108100510462a0001005900300c0040581c1c1c14810300708440a6144001c3d407041001c2d07440f039241c1c400700c65503018001344a90030040c2a4914000b80602c030605050f = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 478211303 1250 478210053 478210067
    0x30a0e01090f0b130b0c0310080d020c1e030115170a030507020120151006020106120602070f0b01150206061215100f06020601090e010b0d0f03050403330c 68
    0xd60019000843e5448060f550b10100c004088041d21003109401448490300d0132600440c01015841d0041c11002d40b19807000c2c0c0c030307241002441005680202e60320300880c10035a803100000799106000e50a0401444042800d41e4910f016a02c01c26040c031006000c2e10380b488000612030000400182048030a85d0703000780c090711904802034140018020280c0300402129121004102c3e1102940c00e901000346910f81030311415601069451300c102d401003000d520512a9500705d50403282883d08044039a2a0300c0003e50101c1c2060351400c0380074600901090700c1d281d07054020169031020f00310311203000c40700a09240e40502054400e20003400100506400014500812045260030b10520348801080e0000ca852a6105904c480940840064032030340214405049441c48038003402041c2000120307900701d840d4406516880b544920302c4901103000c44003a011494440e0410034074040d1a61038441c0307a00d881c401c40b0221690b035100c1018081c100380742404491030200800f400801803502f4050054 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 478212553 1250 478211303 478211333
    0x905100516030e1f0e010801050405091e030912030d06090603080d0f06050405191d03030f0a091a0a0f0504050613080708030a06030201110f06061210050c030a0e0109 73
    0x454120f90b50344846040182028004000000004e000604085140404d0501040f07d48000003140e041a020f03051251146e080541007000c403064130b82c00c0030680306200081c184414800c00c00c441e1200342040312444400c2c002141c0300d5400980510a42d0119000345107070a0600c0410400180c01074161606880000070114004965a03c0c09009000d42d920a65100f400c0c0021722031010905091076082d0081c2600030f0010309078560f20a07025809484040c0d909074002c02c00600c114155408403034010f03096031000b241c0c1c80410b8580c00141045410780c0e280166104050140b4008035202d0101081404c0b0418440d0340707401c0d1078080d01c2c0c00c801040c0400390240c2200c0c2208203d852005c03034420590003030309542c40e818211660001050b49000480c01300c0c00714013103401d12007000120074444901c400010b007241e0751004240305441044001d00d000070710420700c82d501000d0450242c0d510a880700d0003403070740b01e00e03150b400c81c0c1c02c0c0d030361107444600c4c075905d068002804646104041000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 478213803 1250 478212553 478212557
    0x28020103020a0c020d03030b100305092508030301031b0501020606030c010e0f040501030f0c051905041503060f0b030111130e041b120b0a05011d060a0f06090510051603 74
    0x8448000c2015503183c900f03060b0081d48030312400c1d001400c0640580c0301400c140c0702035910208000c0c1e241011340c00c903441502d440c03440351303c003200810319000c2e60090608014440c031f0182c0703d503903070faa0505071454000780c00444003102010700580703d41d0907051040740142401d200500460902d000441e46600281041c2c50400240c0c030000d40307160700c406120f02e03c2c80c2c0303000d0b00c208150349c1d6900b03111f6910003112078116015000c20400290720300c0c021400c0118544094108540e9514010401009261000045a90344410030340007010030040e109072244240310041c04075440080908060071114001140c04441c101884603036181c0030203d2845e02500c10107107800859880c0d5050007d010f00085041d40f0706032112082c08036510507250340c2c2c1e0501c180300d08441d440796150030b1588015660240140e0201002800b602c2c000c10a0044c41c039604100c02400750319443d40c980701c00380c245902d035412240104110b944100298106030300b49103000320142c0750490418072004c065200f4850105000344c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 478215053 1250 478213803 478213807
    0xe18060918120c0f010204030b1501021212070f0206130311070503120a0e010c02091302012d0e0405011a03280906050907210303060512070302032802010302 69
    0x94425040808401c1e01c02103a412555201010b00c4102c0c15a4010310103142d00e4001d019590744014014029201542e40c00422040c8a903070b0810200703c140c2d010701c24581144140301c101502c4030001001420315031801540190b0914141340b0180031566101080c07011507111900300909003140491090005900d8a008000040007040c00e81c42c0500035004640d140c00b440300340c40c1d0100303000c400904600e40f603603c401b0300c0311091100544001c00b9002000e500501ea4100003030601603184001003580f40705050400e090900840151400c60714400c0203001012100254012103400500c040c070f4040084605100c2581005543e000d6001a03900200320441c0100c08200d120012000d03030058061400c2c01e806900d8a401149005020701d03280945805140001041000101090a80540301c10405900101c0c1d0700400c0c01da030041201130305030109551032001140994424100701c0c80c4582d040e00030448103085004060800c0000102c4c24518500000b0003d084009201c0d4096880e4090900617 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 478216303 1250 478215053 478215061
    0x5070f020d051608040906031e0503090f1c0605010f09050402300f0105060918060705030c040b070501020904110a020c2e0201050709060504050a050607060e06070206070e180609 78
    0x3d000702007549000f0300c0d4590120f4081251080c035401001101c1c02026a13128400303040c00c1003140900d02d600085c0140e0002c002e41d82c1641080300950755404000f51411414080d9018003003200307415203d0403a9100c0c2c42c0d0004001801c640e130301c404003500300702000b0041ea003415400154002054008010b0001c80100b50240d858021500c1130354403a501425100c40d001144041c60083c00c003210700c540b00c0c504250101d180340c020030128400c02d0154000611740d0b6101c03914280c8054000802100d0710b010b017008003148110500d0068174042d44140009621403800000b084141c900141c0080800c000a014400760300d507000401000983c019036825056410b484418102b0800081d210f40d91150700d032006000d0300381c0c1544030300e102c0d1000740da46032445515090100c9051280e485035a52180c0080c0c4140403520303041d402001c41130321038400050741c610300321519401c00c0000c03a40f000c0980c02060820201c541c01404250075070008940f0082c00448030181c001c040c00d805806640240390400000d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 478217553 1250 478216303 478216327
    0x8010c031509050c04080a120219030c140f120310050402090d0305030910020304050a1112070b0313050d08040b0108070605040308090d3503070e2701061205070f020d05 74
    0x71742c080d12482c0181c50101401c0e041218007503801c4c0356094010710a180e004c901c601d415104c448605a850340e12001c0f54151601c40c101400c600c01c6000303455000c0d40440c180b000e0010008905500c1d10360f11100c2d02e902e80019031842e42110f980c4440d000318010032040c1d8250396101d00303440c252075241c00c2240d120f894840006190207207136050700904501c00003d201c244040040d44c1c1c68010b104094003035000312270340c0c2407080d000c4401c1d51710107190f8001001801800001e0029580c8030a856007a800d0501c00358032000d1411313548400c0703103000c11a4007050000303216014080b00c1c09094003500810401d840d00708001d203603210341d04c405015600040f840e800c03aa540d40c200d088006400541d109881424000c2d01098a410038441044945050011081d04088a000c0d00e1140c1c81645a0704600d80b0b00c442841085524035414031151705024a14180c05865401c83c24060304103a5252034420740b2003c000d00032601c001c3d0100c01400643c4c11648001a070016a16400040d0b51030460f8607148000b02c8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 478218803 1250 478217553 478217557
    0x30a14010506090139061a01030c050a031112041b0b04030f0807030e1302180307030f0305090d0b0a0c090501020f0a020112020c0609160501090b04031704091508010c031509050c 78
    0x20880f070b0742d180c078041c03828807549400151002c00d9801047d24103070354100064040b01e03107214501001c20402d20482c44058003030b80c0240c41e11100482d806140c22450340d240300340310030203c5003200d130b101403c0c101864800e8080d00080c094503800841750b182c50304589a410001181c800000e0001c280020310408040c03207090048040d03000540100caa181d40d010990000c1d400010540103500c03007840f02940035150008031f00b02101d4103e40500400c00b01d640301101c690344045141034002c00d484020000003060008643c0c40781106800000e039500e0700344d0005040d46502d50010303045502c242c42269200f40003040c503810740da42c2400c20700c450550789600c0d100070b805000e40c003407411301400e0304100c619a00401c00f698003601324402081401d85980055441000c1c600503460020303002d010a10005001c185140a00e06003c0340720340c1000c1d03413044203405991010104502d10640c0600c02c0040c5e900900600c13440b42201e0909011103040b0364404035407800d2501c51264516100c1c1c0100b4002c03050102 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 478220053 1250 478218803 478218887
    0x7080f0405100e0310111c0902060a03090b01090e060f0907081002092809050601051204030509090121020d170f250206070224030a140105060901 64
    0x10451910740c81d0000540701a2560043c41d020740182c8120032203c91091040942c081a54807100d82090840480851040d840203846144241d0318a42ca4016907a03100c0645110046a075007c65460018a405594808180d00c03850f65030f410704034900b1440308046100d80d8000c8172204a604250f54184c43c10380760002541c400031030b501410326507050154440d0003e05103000d080c0d9695881010006850800000010324424020f0713030300205100b50211b60700800e80206051410341d06280d8040706034020700742d058a0890105900040282c400d04203001450b0042c44219500c01804084004010070b4800da00310003841801d00681d044200011400000018102400b20b2601d130604080f144a065002103242d2a4a0110071000400040d008440c16461035000c1e051a0070901c0550a02800010044128080c071210001000351800b5141c00355100f908000c0300800c81084180c030302e0311400340681003580184010001d10300980d8020001c501c0b9225844051941c0d082d480706505201c0035201 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 478221303 1250 478220053 478220059
    0x5070308031f0b0a08010b0d14101d0402010f14070b1512070501021506310b0901080a12021501030807150203040b2a0c060a2007080f0405 61
    0x210502ca520203004041c481002c81140c0c000c0b040d25114008114070f4003640038408005951180180240ca813050003429210b28001800b00d080d5203000a640042d0000310303881130800c1d032460401c002025854a00d11003138244914001001e04250300020043c08103841c90000b0300c01100c181d0a00604007070116050385400054107042410300e4000d03e00342c04e50890302d2611951840c888000d0030b100104d4004111171051300186032101140340b424061810003030030705501c10700310041c03040a003250109402c054120079100a01c44c400e03400340e401c12074000241c820b028402900060015050002e2128542c035000311400000740a9500224034009a12a0390911030b0704141c000001c01c002d22000c0d00015201d1600302c0c421050b0f00144204900007210302a0211540901254003c0c0c0300440c07a100e049140034211a038100c8542d00c0000f2036000d04807205096000c074041100c0401d441c8203e152a20b05920340714600101003c440815000700e030341c003618a81c0700085480d01a440c11003140c005201c06 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 478222553 1250 478221303 478221307
    0x120f100302010f351f05040c03020c0102030901151d06150405120d12020a1d0307081b0a05030c031c0921050d02012f0409050c04090b01051c0905070308 67
    0x4400502e6054061800000750f801808280640c40c001306420140c17480c449412002482d1004000180c142c40c030211062650800021501c50030a000540c843c4600030300109400c03461a01c0456465000d40c414044203a50f401c2c02164241480322458001d072080340c0700600c4e4000f081040b10300c0d210b140c0c021507002100c03680c20391749401d0124540160070b03a6600c0742041e240c1440307088002e0384124101c8a001840c42e40003003800c10703580d0061001031400a8100d941c115103442d030700c902d00200703d2031808402401c101e412420f032038000f0000c005005d0527400340000308034201c08070340d1b50001ca001c2c0c2211402801c003202c100510404229000b05840b0000c980c20245a85d45841c481000380025902c0e400303030b41d07a1416070724014044c030b855019640c2402c1c001c20b0300c034290030402c2d885140601c0c2d032028020000010b54140e903015403405420340200041d616464801c00500300e9007045456418848148100800307000d000c51140038291800d1008103d03c1078515146050252a8200412030280 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 478223803 1250 478222553 478222607
    0x121a0f130c21021908040510060f08010f02090f01121413020102010c0201060e010b0c030c01020d06060f0804110402030411030109110a140306270d0203120f100302010f 74
    0x100c42d03090b10800303050860b24541d10280795034000591007184840c40352003d0100000b140e207032241580c01d0740640a00240c41c15040c8001080094854640c06070b000344142000a01c90300d00c080c880c1580600d19036804625210401c40403134850350850800130b0501419000c160000d120603040052840c20100c00c0c0c1005141207101c1040a030000d410a90041d8a00304400d811240141708101c00e031860200040d209a18120b40c044450784600515660307400103001c40040c41500f40040d00c040500c0c8180420b00d141000c1c001050400d03141c100c8005c21044506020206020481440c540380044e078000d60707245d6950400c0580f03088544002901980381104100030710140209110081e54101c1c1c0000680342c5d507030344902c011680701031075541c5030700000042005a4403141c8041c40803010f100c41d001c40480840d141a00780800c151412000d41c00019904d0304c00c03490f070b001103644121130154070800c504049842d0081f503a40c0b40030007414401c0e070980900095005030b00c598602e4402c50410703214062 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 478225053 1250 478223803 478223807
    0x220b0d050610030c0e15100309060501030c030302010c0807140702120a060e010f0c120213030c03080a020607080717060a1a1b06040203100c1e0f121a0f130c 69
    0x102c5200c25561070005542c0030881015020205008050400380351303010b910b038241007241c04848080c0c00780505035100405000143c103800340900031030040700d140b4813403442c2d418083d0945010030101130821500004100c65960003071010741219104001050f00c849091010072020740ca001c00c0d43d0302910984480e0400c114154000540d081c424600034040c221066180c242500c03000c0041c007000c00d0116281c00718880d902e5028100104007580d13483c9015940b5110071410000b01e81051310703036540c0016500050b40c0c0401056810460f50316100302149042000280001c241d100200d42c400203603800300c0c0c250f503203040441c000307801b2036080c00000c03910315603101c02d060340511003501071810112120700100304085038503449160080c014100c014100e48450000b45011410701003030111a686444110080030740030f25005c0c00a1f02c500e43c06e446481e0000d02000125030b64008002d04181010101d240e00411a5075400002c0e07904800c1e00a82038000f44812a170b20f440802443d03c0e00d80303c1000a6 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 478226303 1250 478225053 478225081
    0x21140d0b0102011d031c0609060303050c06090d051c0f0e01061e03230a080a0e03060612100c111212010b0c030901050d0209030601080d0e220b0d0506 66
    0x50400d030001c0040084948039403030103a550340c01d82c1040d40c01c14886441941c030b0503001b1150542031004002441c644403e003180855125400c103600140020842142e00c90f0304100075034220700228005e054101b0241030080c182e1241400600b40c1c11a18103440d00742650ba608000411500598140700800280b9410341c020801d0384610050042d100e086208400c1c0c00c0165102504e80104030170700c1c460400b0043c80103032031522502c485540b1031000454045001d40d03016110140490f03481c15154840e03202050f1800740080d100b1403040c807014500c103450810010ba00c10500c0002e50003c2801c0c90b03105402e64507000c0d1540c07488118041c10011051030a040c500500c00050145101901e1340d89840c550302e2a8098021542401e9004106242c00c960050b4083c1030f06a01c8050301620380036800011078203010003039020f04015449540340150a5070070038840c0d081c200c8165000c0c62036041200d4401c00c890100c0c1b03c410b202c6680e81d50300800503124a9020a00c5039000341c21a1402c1c01d0058a07848070f8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 478227553 1250 478226303 478226321
    0x26070b0a120905063702070203190803041208070e090720070e0c04030c060806040609090507050406050d08070b1e0f01050a0f05031005180a030201021c02030421140d 73
    0x3015650419a0188600c0c02c90380101c1c2d1200c82a1001c9441030b05c1e1184002d40c40101d05a034036204540c0300b18908408406074003200c92183d2800c0c0d4880c100741c0341110800340d102807000188500d0a08004e042da030b002038004241c1d60212508205520740310030179511054000ea1204510403514503180c2c080c48001071000403549143c5618404d5500e2101c0340390940200c0c000101715201e540420040c49120f0102c080c1c00c48001400081e0075a0389802c1d010491700c030080100e810760041d074810815440c01d4400c820041c1002e869039180b0704059030311140c0c0e074407400000422828400c80801c45920020100100c00079842d5900c1384039091403108004c3d201d400b449024420305803044089040d41341c40d40d440003104c60280c0140b2007038004100e902c02070603004000c03803907200020030410080c100030810b90240c0c82c000e800041c0d5881058500041d80c180060a5400c128010006d100004100750010303000114030700c0d0035841344d414207038040342e034480c0c07408001c501c43e44042070b50711000c8078540c451030300 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 478228803 1250 478227553 478227571
    0x703020c0424230909060115022d0c03070f0b030a0b1c300503070c1506030312020702150f0c06010e090c01021204050103020a12020a080126070b0a12090506 69
    0x140180c3c0001c000072200120743c00d04a40e000600104407804c04100381801400e0580180e135080c0102c20104000011a00c04005030b02d110301d1803446c40d840c401d005c038640c562402d6014021460030b00c681c0486900350782c89410001e846c004000340c60b9240a600445003d8002001d181800a15400043d00350f00840c0090307814260003d40c4a140d404401c004c05005403900da003c07900c048a0900c00d403065000101000d042c000054542000592640c0308021803060308500098098110300b40202039419240564103c58030400500002d640c3d10b500301046056080c0341103660721f280ca20720410602a80112080c9845a00b00210f0110748211001e88100b00311b0080b2248590070340012070f0f40e4900e0080f070b45040c0c0420441805154400e4004041342c05140c01d00824900740c0300301c65000ca03072102d1030040002d00700740d006012041c1c1d954949420000700304010350303294007125080394840003a0300c01e055203502e0004450342050b0007450701904440c1c0805c4100b0040c00c6604040b600c80c0030894035000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 478230053 1250 478228803 478228859
    0x213060608090715080c0a031d07090c0302030c0714070b030f07030b01030903091a1b0616050406050f03041403120105151626190e01050703020c0424 66
    0x213800f102403038035030b412413410755131105151900251007501d9849440b41d6010180c6030380000c040c4404951030301040c10241d4005015880c94044c041c421529078540d100c08060040050001044059003550040c0d07400049200c10071000401451034403e19503c00c543e0740700080b081103446200c50b90306c0c91007410180c0b0103121410b007003401101150401d582c01004900d04803028000f01c0341900e040300000c0d12141c1901e107800f900000500b0640e08504e0303244281c3d0700c20301c2000a0340314082450507100e117a9050003070801e804c00c0d50140550140584c0584090000f0000805008500d002c0c40700891600301525a80c503507030013000d4614202405041e00500c221b0182c0e04039615024121446445018552002400580d0790702d005220010030410002a894a121401c80d040500510002030015200c0501e10300c2c0d044050183c4c042468402d051000500c00000840e8000c1800d03c100361741240c00080e0030340e542011841d0101400d5040110001c10080400c20030141c1001d0907031381c1d81c0918404 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 478231303 1250 478230053 478230059
    0x6050c060c07150902040b03010e010605030c0907050307051303020a0602010902090c1611060c0123100f06030f200a08130507060f05070506070c030f0801140d02130606080907 77
    0x1c1140300d1080c0082262819058034400c40c040b07a80100d16036440200041380403034005001900b5a5a60915200076955801c0c04001a103000c214181d102c0f942138854144501e40304201030204d001c0148010144840041c440d0400c1c540c041078030f0040d41d8010700d403a085940b1210001e00801c1401070480c0515420700219080002078416240000380a0f81d1107100d203102651101c906004100d5801c0e0418401e1250482081084c001c045503080c03500b9210303020700540e5254041042e005019040746aa140100b40052941806c0d11000e50781c490a01141400d40c40010384c0041c0780b00c2030403210011048101001c0100c81d200200a02040390b03589040c16250741154428130201c07680028850750203854100304032800741192421912080c240642009155184e0505000b0116080340024005001c0e020030503401ca1015010705860b490302403401d40c1003502c2c4802d95480020245e2261000102000440d541c0b580c0345908c0c820350134028840c0c0d558070071000e000c0d050192860a20f5014425002c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 478232553 1250 478231303 478231321
    0x509100c1b180911010c0c030c0e0f0a110d05060f040507020106090b03070b030403030902151801031d0a0b0a06170705030d1b060213080321010f03171308060106050c06 74
    0xc1c030f0442c0d07000403114084000e900019282220f40d02012941170420280000c0803450487c7d071140103101c03011032840c45113851511240344c220000c0c20003e007140780c10659440352540f0429180d04c1c075092140018070b07455490008881d80190144281d0140c02c180c10803e140341d06401042c200d40b1012400d210b01c50030701b010907868035028080e847c9040424400074000c02e10941189070b4650016003504903030441c184502c4918ae1244152100c10503100d020f240303007035074148100d440f04205081d100d101c0135410000c07940c44485000340034003c0381070800481e540b00b4545d8064002002010000003400e607040342c1080d03d852580c0700b000d109002d04041c02841c94001c0302490b80c20145c440d15803240700c01075540c3c07200070b4002d15640784241c3c0b035042010424080401c0184444a210000003100b00310021003c944000160490701148540303080070400181c0d001d0320300d044401c1e0180d405444040550f11a0000c5070300340e21840c000d2142c000009446a00300e030050000002040558aa960711a451 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 478233803 1250 478232553 478232561
    0x50303180f0d021c110f010b100504050310050901150806010806250807090b0f07060e16180b03190c06031e09050a200a05040605010509100c1b18 64
    0x200003d40c002d0400c609008420798204680b260041c02c10f020220300c1551210b16010b980c003c000f89031382d9100a880c0c024900015000a052018586213242c2800c26020030745600182e14903034800340d01c44c408241c06910a42006407901c18901844001d9903076100f500703a442c002881001018050702021400d9140101c48a541403071048545540f1506c024100b114000b071f00030000401c2003425580030921030300201c0141b109004c40b150044c1c071a20142071900856082c003440c100180c1c822107902090210203030b2404201c80c0d0010308022002008040d1a003d401e41c480712641c180281d000510501d1b51405c000c6003030741d004070100d109243d190b0341700b90300b2240d15107a43c00102e92941006c00d00c1030080d800c805100b910440a50780d040545550380c181c050624641daa10441905542c544070703081c0351070980000e110440d0180f18980c54200060103620842d0a820f000e03500240742030030b100c0d020f1b1603c1220b031980107591404100b48141c50718083c1c1180c0c000e00000320f20f000c00c6115000700c5809 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 478235053 1250 478233803 478233823
    0x130b1305010915270b03100501030c090807050d020118030506010314071410021c0305160311030a0506030a0c1211010c03080601081f080c0108010b040b190507050303180f 75
    0x445204c40d0042c1400510a20081c1c4070040204286090100d5222002c0014500401d071401042a18504010016080c0c40c0454510300030880180404c0040f4072000480a04440f410794002c036064115000403075980d0030555499220301000311000003007100015a05040300d01030312032f0100b070307101100b85251a8021449581c8000d20b400c2d0070f603001803400b5040080311880500440308043c25502c02c4084020404030110003083d0b8407002c21038a81c010503030307880c59000705107800c221900c91545840051b00010301117440c1c43da9250b00080954500b00810a03207240c00c07540c1c4c03140d150b9991915000346420480e040340c1040003002020b0055024009440503150700d91514459592400011184900002c04428802001d03c401105214540c0b0f0594003424414001e00f0640ca40900003401c0d1640691181b20003030720800042025014400540d100c01103102100c0d407200e1404e5004549900603e0f402902c64080001800310a41c41c000780104006014803d8079102410040030303540b61a0211 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 478236303 1250 478235053 478235057
    0x918010312051e0a201e0307080301150302090a080a290604050a1d0703060e0601080604030c060209060d0b240a03090c0807030b070801050d030507020402130b1305010915 75
    0x50f0b04203100140c450b014201022140c6852420020007850541c40c060019a55110981005804155001003500b9400310f80c55150011403030252150344400984c80140308165104150a04444065200740c04031008504001d1205c04650340301c1c500540c42d4400440101c842c1498410404403009100710921030701540132007111000d6440c0803e1001400004102d041090355515000002c020109940246408102c0080400500350301e000300490300502803904041d48000c0c0100108080003c400d40d101d94903291801c034140d410b02d44000640140c20400e80c0c4000d02107030096200d21030b03134807018401034201d0700611810300c91043d1010f40c1300038180000c001c15041009243e4107002c1d41200d0600c602ca4000d5118066940058030308155141d04202d5000c0d00407018450741070b9010300b40b5805010210355140341500c540c0e0700540f03c1d00c500c1000a00498000c14800114410108020001d1490106043d41c0d45440c103500300c40e02050303000b0240032038005000132500002d4610f40966450b619 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 478237410 1107 478236303 478236337
    0x50d0504031b030209060d03030213091a040506010203030705210c1c1107030c03030f0c050904060801090c0b0f0f0705160501050a1211091801031205 66
    0x4a007411009070200d1103080c0050303501c00000c21b8000108844025002c42c2e0382c64207038068007806125207024410070000203040c0c00c698011140306051904820340d05d00044d810402292002d5414030b005910500c0002e007094064001800710762410266480d0310000d040740c0c00e09000007100c03e844022130100e0034009600c83e001105070b0000c03218105002d90b075455040024180201e03a40601048070340102e45042c180268040350652850702424080980150f0010741071342d01c41c0c04005c0c0202d1422800041c46c01c8188608d0a190754480d040045091034411103405941184031490500700303007040700c40c110600300c1006020702c51289001e0a9134606030206038440f000e1070b5000c241444410400b600d03501d50710524249220a049000080042e11003041c0c01d0380303000394032806801900c5845100d80d110700840c4100c1c102d0b8441c81100450f0800a4400c450a01900d80700410382d041c4 = true := by decide +kernel

theorem cover : BRFrame.Cov 478057553 478237410 := by
  have h0 := BRFrame.cov_init 478057553
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478057553 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 478057553 ≤ n) (h2 : n < 478237410) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
