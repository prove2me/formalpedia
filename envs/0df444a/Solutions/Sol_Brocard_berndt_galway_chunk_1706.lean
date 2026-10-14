-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1706
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:22:33.265666+00:00
-- url     : https://prove2.me/submissions/e555c43b-c450-42eb-963a-f43aa0364958

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 306654676 ≤ n < 306834532 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 306655926 1250 306654676 306654739
    0x11060d020a080609070306180b030a0c14030607030c0e06130801060e10050303040e190f06170106090b0108070c050c031203010302031c050d020706200a080106140405 73
    0x15903500507640e0103442d01200362030a9000f80210030004044520a200340c000b503c542d90250701411650007035500240c18540301580c2e15000341c8049000140281c10640010705086109280c0c408410b0209424440014807120516060030441da110307130b40c090040d00c40b841041340c0c4d164032080b00c0c41007a90940b1441d00036050030740c03800d800802e06100003c0101d129200016401031459110390901d903c80c06a03205102c00c0442d2440850030704041a03581d43c9000c0030079100050000c03621440d610590740720340e114a03402c041c20390328452400b00c2070040e140a01480407050003050504800203041d103400a00480800c02c2040c0903104002d03040c400c002003100002d040b00d41e010300c0b84103074034010b62082c40704a21911401d020010302108040080c1e54401481e21440e0a18601c0a03900000c0c6d4410601104c0e000d90f69900c11203540d81c8103002c4130090640c820071940b04c5030014005001200d06821072802d008080180048920301981103505480d000e4404102103140c0b0541c0d040308050440225 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 306657176 1250 306655926 306655931
    0x3061b16031806080108070b041508060418080406030b0406030c030f021201110306040c020a0b040b0c040806090c090906131502040b160201020c010e18270a0317070c11060d 76
    0xf0040d51001c0303014160340303c180c02e40c0c050b03075a25805014036200300c0c410107020240401049819500030f581c0c503a1f200c6800340004c9092080e0812041001d0030145045030312610204051104a17410b04c2840d02049056a04005103415a103130b2282c0340300244401000d45041882804c115290291001082c2080c28001d04c981c0d0b44988070790072513400481d003142c021071900c6002c8031100d1000440303130714a82c0c001c2104030031a12035840710100d4110080c042c522903441040002206401081514810500d441c054580e5082c0c0f101000f80d0307000e01a106005646c80700b403d0003000040c00c504000c050760700218008141845102c07280c0680181e502100782d510000c120080c2c2d403410070820201c420301c00d9087d50107035a40322005580000040c0420b80d0410345064070b07400665600d200c1c46420651204c01d0802c00903e2444050748095407411b8880d154220510020815400a9090300080602107400c0030f0740c941310781d00901400c0c0c00400500f02c84101811065140c6800044400004a10105 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 306658426 1250 306657176 306657179
    0x906090c03061b0305010303320a02010518060f07030c02070510020303060301110c03221a040305010f0b090429282a05040e04060b03061b160318 64
    0x1002c001c000700e6448800e003015403000345946620922a141c181d9916468030410a13100904100544030000082e24440a4030540c80c041c4146a0001e441806280d42c0007040030700c4c1800690501a949060080c40c40d4080400c1c081c1d545d00d80000c1581c0305a481c50002860015054228649a0164000e42d0040388101c078500307035641e02200452042e6015070081c4040f400032010310f606403140300c0c5040881c0d0030911020440c1200e8540c004031250140c02d0320000e03e522800b403003d01c40040b180d603003001d0400003010410003600b0302580d526003904c014108808081d19001c129480402000281580c15821605481c070040c1da001401ca407030280700304c1c0114a03100021141e4101e000d004000f0050800000c0610182c19008201d1514004a000301c0c0008043d0580b2894044a1000c401442014480403d820100a48032482a03014520211f142009001030506005002c3c10010600850b00d2102d2948041e020403120817411941d18016a003100d4141100c20f100ca80d60070307803880040c0360790 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 306659676 1250 306658426 306658433
    0x1050f030a090605010938150c0303090303161b060b04090c060e030114061c031209050c01120b09040b0709030501021303120908070b03070509040207050d030b041a040906090c03 78
    0x40c85400c0380301c000c10001c1850812880390702c404084113018440210211a450601180e1123407050305060700c142c20140240d0070141180c00440c1ca4282c264804004c03c0308a00c9000d55081b410003080c281050580302100103044158110340d8098045c44d01d843c94a929038481340d0100c408150040c48000300c2c5512640d00520314000c02c0c980c0c40c0b03e0741c02d1144001d1142e0010503080c2c09244010261084c0c4a10a01c2c03d042c80b80503c0030640c01c0c48641c0560586440050240840b1107105001402100c1c01500c009004901c2943e00381d01d01d54640b42c03106501d611450f10707443c0c0203174000d05114000d5071194000c584003462030300001d0040d400813940d80d001440031411001540e11400410640360120001200c2c010854881d68031b05501c000c17401c01144000030000e40d040f049520b401d6280200d510003043c180c1e80145001c490b0f56025054203005298548296140185e0851f0148800c1481504082d80281c4c42c1013001e11807652a00c402007086041d030300400c01150b00100b9501582c3e500e06 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 306660926 1250 306659676 306659681
    0x71e03060207150b19050f01170103030203071704180f18060501080c090609220812070e1203091c0b0117060901090b0106180b0c1f090201050f030a0906050109 70
    0x42071030f00401e0a100f600540d51400041e8401d0100015400e07100703051404003001000340072080303130b1410b00280f08a07070502001024040c5010358000c1c0c000390b6541707000c4e00c0d10b064590744101200c0c140c408144018404081224000c40f6407180304c110100714046e0364680a0300910b2106540021815400d8020b02000003d801082c12142c0d010240c1308030004650511074842070440312194000e6407040060601e81d090310700100c050300e2481070701503044060354135002ca036400125000c949040507400c00040d40d40c02a6502d07207072a070035200c8a100451003c5800d41c5d070301692021078032400300c0491340c9c02c4850300484010151a0080901c440c0781d69101c2c4200a858804080c0c50340354090800040d5012105015141520303030f01c8018503006a280007001c940d115401261074550281101c000a610358a880281c034606032058064440203180600e84849000d07802c00b080b6115003441103d101503030700306059408004804100580d03036a280415200240030411b002002c1c2d82c42e100010400d0350056 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 306662176 1250 306660926 306660953
    0xb0304150c0c0302010e060f0403050f0408011812030c021c0e03030d14010602010c0e0906130f0609060f030506010b03190f1b0302090d081b060109090209070f02071e03060207 77
    0x13500200f01070710300c09000d95268102100c029104202c0300c004200080e200e000202015110306011504107038440712182d094840c2c0051900d45180c104107543c080c0300da541032400000c02036040c2000f442080c40c40c007a440303848100250118041c0511602e5405d030080000b940c1c0700c0c40c000d0a036581c88410551100050600c5501040140e881100200c0d0705c1c0d0051192601e06091601c940c10f2001c1054104010721310b0040019030400150f00307252061280c0303800b500b9025080c2d4100030884a0400704d03e8000c403a165840a003101164103410004200c1c00302d0208c0c15075007502d1b00d0701d90301d40d99101e41580c000c40c54411407030b4040c42c0c55001d104090f0240c2c08001b50b00554a01d070080c1d44105601142640501e90905901c1002c0e100c00381c0000c3d09a41c0200368010303a0f56000049284010310050801009901100800d40c03100100c20452801c1869944e1000980c00e02d140a503c4450000f0340e502114000d141441c40e00c142c0c1294251500100070004561000d41550f6485440c0342080051140 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 306663426 1250 306662176 306662183
    0xa0f0f050c22080601090b010c050307380a02070c03050a080408060604022802070909150606110303040f111e01030605010509280504060b071106070c0b0304150c0c 72
    0xc401000c1c0308500682d804882500e00204038503400c2040c00c5000b0619141407605101600d00d013500003541c28006810840d015210301c1c417103001034039400040c40e0082510301108500d00f02000c1200c0000303082c110b0300302c5500c003001030f2071383c40600d400c8002c0683d50b04003502920031008075004010030741d0000c0c0180d620160035122070707448110502060740108042802c01c10100d03009204840c11007080c6111a101d0b61040f0b0f0304840d0f456074101c1c116910088203858540d43d0080020040b4035501494004001920b070420045400084481e200c0c00040e0000700070110041210003400703c001009400c0200003010301c11007260308850807024050188805000c030f424440300062a60045d4140c1d06c424a020f0003c6810201c0010386c0800000d80154681c01d29038594004200d50701c0c0c52040c1000b13000742c00c82c000d030350300c4050502c082115507102c546846650100005400030750310398010400c0340d2286103466103d440754600005411a04002d020360645001c1a000d100c0d9402009031110500 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 306664676 1250 306663426 306663457
    0x3050d0f03090c050103020a090f06030f0e03090a23090a06030201020c0306040203100e030f040b04031502160b04020f1917030403200111240f0402090a0f0f050c 71
    0x40ca503000e50a40300394041c00740000c85041804c010550081e002007202201c0c92900c5e000140c0c480040c4042c41d02160400c1e03000070f503140ca0038007030403800303115a18a86180000840c18000a000050500d6800b4040d1b24094214483c0900e1040d070340018180219000070070640d00ca2a20380465401402503103c05d03401803240c40001c030340038200801c0540c003458000d00603040c4182c1c8460038002800440c40c0d00c0c045c5100812000107a4100b80c0090701c007500607401d1003560399166003001c00d0419040b01c548072100d8410407007038082d541450002d01000ea802a400b60803680c40e400000c01b040401801160420417020560213801300c4200380806489088041000c0000b000243c7c60341d90141e80401018981071904100f40842219070307007002284140f510520500039450242c3c2443c0103240700d0755080e0114041240100481c11255a010607510814251440e20b0b0300012403401d0046c05580c54030b07035500304402418195400200302c0c1c2c0d035040ea044c441ca00f402c0103016070a9000d00304501d60b084 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 306665926 1250 306664676 306664697
    0x1050f12060c1c0902131d03040f03030207060206010810050a090803100e150603061207170105070224040b1506070809100305060a03110a03060f0902100f12091103030403050d 77
    0x303c07600c28104004d40260003000e008051503010301c0204001f940410104940069420855008100810140000020300c2c10298514500a0700c0d048a030b801c000f0540d00701c000184402003000074800a14044558085000c0c0ca6024013400280b46419000e08808030010820580d281c0f07080d59841201c0454a883e01c15943d00030950698140050b4180d44c480c3c01000403651740e2810814042d11004140142c0d907440d590382140492880301c00c507a00304141d441c0c004001c6a0f98050019001210300c915494080300c14014013941414001030000700075030001e9001c80c1340c00c8a19001c00c4840700000c1c140582c0d1b0030003030420780034903085510424403549050f0030351070803584640140d42c050900684880301050440e034540b0030007660080010b41001d03000c0030010124080d40176003600f0144220000071412501c4c0140304805071401d41c1c050a0004140c00401503d901c07104080c410800d03a00002179014403407a1500c00404508511603140c1f0010501009000000c1000da9100c00d1030b4441c20f0414 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 306667176 1250 306665926 306665977
    0x21040f0201022503060e0106120317060f0901031e050d090e01050a03020f12030c030d0b100f140705070305070f0e01080f1c120603050f0106080105090601050f12060c 73
    0x105441c0f01928101c0f80d402800f00005919a0040c1815405460012a100340c03203194414648020041c2a00090402000350070078600c03ca21040e000b5400340e484503010716407000407540c0e40c041071000504a190760009041054a139603440f0010302d50060540b4104641800020802c8d0303500e01400015602a000001c0c840c608040c1210449078081d2041c80c100201404012802280040030701487c08104030401c20384406000820402608003000100343c1c8a40c001c0c4100b10340180c02c0c2d203003845194640b40c464650060801ca624100c0072541c0c81d603411452402d18242007013584000d0140c840c0b030301c0c08180307490255107907001d2340c41c00e00103c0b5490ba681c03144a555040d1024a44503141c002c500038410302d64204040401a1030b4074203001c3e4010b0140c450403811501654815a02c6800c03090311442e00c2c01303003801400e00403c0010020710107820684c401c5034460ac0107214051141c103186013030750110f440d41c20325190009285c4007074501c107141511901c0380907440742d03c840035642025030100310307071 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 306668426 1250 306667176 306667213
    0x4030915230a02161e05060405030a1217090a06050601030b090f060a091b020105100f03020f01050f0304061d0703050c062107030c030b0405040f02220e010f0c020d0206070521040f020102 82
    0x858270014000d00e00c058081d02d402144005410343c84041200301810780320000d104c880c19601520200d001020124281d0505104849010b80014100f41c1003242d103036901d5032a01d41d005c0e00441e506080b5102c9403074110004040d2421984100640d60038800d00410b6003003029101a11b00109030001e1005940b12401a107a0403024015045014945281480542049500d41d104100e040c10302a10300751281d04c0080c241c1c0c10407603045a2280c2c681455020b03c0c0008004900c40306c000b1001010b030716065640e1691a411000c0b0343d140a0180841e401024262280084141e4100c401541c482e80c103101d04000d01600b280e80501000c40d0600c4c501042509051003a0781c4940e070407007107140c2c004407036500b00400003621080903e85002c05401002082c00350b445035110b865042000000c0c0200c1201c4c410065499020502040d500000856035085801080f09503200c0014a03010303598040c68003c410f019020158000c9600b00c2c1c0d14108410460b580b002c2c80c4c3d840c0c3c001d800300c50103540300c01c99000e403 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 306669676 1250 306668426 306668429
    0x10030b04060b1315030612110102010c0e1c060b0409050a1b03120c0606030b090705150a090317070b0705070302100c2307080304030915230a02161e050604 68
    0x140c1c0511010412002e41000030350070a00283d1715010958950b10411440c540483d20020396440d0344c2074100310000d680911440c45011411b003800c10b00024150000b68150b103d504a03100440703007580e101420072580d41c1c0706810040000700108000d01c1d46003012540d0b24540c1004a03443c400b5580e800364444405142c21040300e40c8045154104c1e0104a8121455000c10404940701038450101000290500c2c25040c841e09146009002a0b0b241600700012400c01c5418100350660400c41d43d9805035114150505492300640110890b14555424190300d04c2018005440e4803802c0090201c0d690b400030091201d24026800c4803550340190210000b201c40400c0310340089144000340c051210030f011f94410400601444060a20405460b110040d500c1160b040b400201f82540134045880218030090f000c03905450070400041c0400c441110401d242c0195140410010810503400c078801c020800610383d01d800e02d030451555070041c0e205038492200b0043c22404040b0b0340131505041602c1641d0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 306670926 1250 306669676 306669697
    0x13090507051507050c10050c060411030c0406030f080304081b010209010f1e080a060306060b0318120a0302031503030a020a150905100e070503071710020304021e0f10030b04060b 78
    0xa440c503885c108002c3c4101074610a40103002e4140700038038090a0620180b44160b00034811418441d0007a81010f00741607807028494800e61a0110038000300700300020800c5c00c994031042d00781c0e17a601c983c00e003011a4016a060b16022400024484030138580c190060061214282c8a0701e8840c010050281c9140e0300315001400702054280001000522801c10960020202840051480e890f80c58400030780e00076403c170f0000100000305002409150002c0c001c4003980546c0501050004038a0100180c401c0c583c25070704058010001c030782c1c0144041c1d090750f0080e0f40202203030364078500c80c64080c5d2190f0540c8425514902000f03014214403919010b0b000000d5030250107006106640000341d0002c0c07501c80303980781701c0b840f506402103032548041015501415010105110b24202600441d262010405c886420540103006100060b11a41010310500d11912483c032420994400800c3c1b01b28090380c4107030741c000f250541410b1000d806510101c400c41040d42c0038003820707440b02c03141111442504047c5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 306672176 1250 306670926 306670933
    0x70e010905190b0103150609081c020607120b120a0b01210209100503010510150306120204021b0d0309060510050d0201110c03030703031a040605010e0409021309050705150705 77
    0x303491182c0b6484802c56503014100064048140c0341c824500070025006800460f09000301440030b584200809043c4a109054070025040200340081d2110405040f4030240943d074144004429843d40050800c0743e40940100c03201643c1d01505651490ae6100035100220250004580310349189403a501d46a20901c0c00720254415a003841060003008151210522004001003040e542c21b0107528000c0d10011410105141448075200e41c0540c40721401c002d06280500401900d1a080692400160102c600503140c0307100b00403004c0a40c080f81c003041c0080c090a550212956016413140030464002ca40030480c40e07032104108000c4110b0f0380a4564460b400c012100015881400c840e40710702a02026a503005082001082c90341d002544120007007074541a40f1580041d69880c02a940741045405000c4603181000180c285220311840a0045450703991040564a8842c00c2c51400c030888082004035410346c0c10070680b252510b002c1d90784180c0e44c0e01e40024849025000350b420898110014 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 306673426 1250 306672176 306672211
    0x927050a0b0c032a09060a0903051e0d0f1d24040810090c091808071101030b04090b1812031f060801061407030c020306130b0c13090c050714070e010905 67
    0x80100c02e8007c00c0421040040e05103000c800580d06205802907406405845181000d404c85002c1c245552176402000700188800749048441d0b00c84503903d980300219600190a24170140424840f20407400c00b2030030059030400d01c0e4490403000d8004e00c207c1d81050180c4003401d200c00d107d001594440344015180312f07900310003440f60280950000f40308442900c00215185540d1341c441640c1e40000780c041da441000494055129601801074000740c07a012942080307c4240e580c0d03080410740014042c808002104406094aa0702c10009080b0900c10202020b48070710300304009601030b40220038614000e081c040c0000034242c2c05003149174140c1d2503580358030a901450403000c0b0b09541089005408005002c9409030258405015080c0140002c224403a115030480c100000b4100b405003804260f1030003008100c2c0c445c174004082ca001c0c0d4921803030204102081d250111414051148003420102441c1346031821004001045011a80150303003d42c5140e1f40c800d444011541c08a54031a60300c0030b003910 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 306674676 1250 306673426 306673429
    0x5010e060a080c0a200d09092319060f180501180b030a0b04030809010510080d05281e0c0206040302090613050c0909010927050a0b0c032a09 62
    0xc0c100c0000c44c2e143c803510380703d152041d01303400031965001c0310140c4c0c01030700707040c100350782d1000c0508041c010418090044d43d80d14000180c3c2440b0f0403441c401d0501c41400425021455051203440e604007401003800782c0c6849000901c00d00d0294842d078500c505544007090340410013801014121031460050400700c0b5008415000500004400c450749070207160b2105c0c0004080e080d04601480c020350341c04410346406651075084074406008c80000030b00b00f90b8204040300c8005075800d03580001c2e250268940300e541000360382410344045140c025804040440c4819540403130407100300060000c2012106c9a18002900c4444003800c019401c20800c00040c0090305004030041e8100c2c2020f040d0541f450218030042c400c5401c02d03a0519000c0c1d0300000c5148082c03400928250240408001c2000021140d1480c0d008016030320030003a2180220b503000c07109008045c0946c140c0903801400c030941529107201084519130088840c008a56196020035080b01c18021048840401164100e0301d003078011700 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 306675926 1250 306674676 306674701
    0x7050112020d0c0e040c0801030203031b07050a140108070807090e15030a060c02010b03060618220b251709010b04240e040f1e06020304050705010e060a08 68
    0xa840e00300303150200711048902920348200360b004a902d540c1d0f480c0300c00f1207100300b000b075521000140301001151001407016039008002c40e81452840710425036032490504116051060540c0100d074041c1070034400107400e4a13444400202c802c000d03610310704c45903913590007a03420308015201d501c00554402400d00c1600c030200506900042110001e40d0f8a460110000341b4100380258115110f507111403280620940901a05082c50400c4020342070a00d001c0e400714110880c01d419007102d045140020405100c0700c2e051a401c01e507980001c80280c00c01504105810250942e01c0c020f00c0715040342d0b400e92980034001c01d180149541e0f0741d0850340008110500120b900302414101065580764082c02300b03680c4901c00c440e1107810b000c141040880700c0300a903038040380c800c2d8412103550040004100000e0745e406420001da42c1d0000c40130061280e02c40b11036050f0240000000c060038030000a010a10074006011021204241d030759800d00002203040c080d19000e145601004285501c0103d1510000030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 306677176 1250 306675926 306675947
    0xb030112080a1b050f07060302041202060d15060302070c0b09090406050402210105150d03090e040303180506100605090319020f0306100906240c030c020a090c030b0405010305070501 80
    0x1450720001c41d20524031403d0070111401811191540440d0121030040c00a0021034004d02c101d040450030149040455142c0c0074605034003d2090000003416042c1c100c41e5841407509006030702c2010401070b03c03080c01400940c0042c205580e0000c0e96600011021134240071036200d5000500181e14039241e599940021f482c0141049070b1151040b07080c4c240650790390314407e100c621150b001043c5420210380c455003c1c51030b087c410b406902030360422004242c0110b009011640007803da80b4643da202d040440c000c1050240000d203100c03005800c0014070030002016406400c40480f400b4141c0d82d20801030b10207110702c04e44683c064010b0641200341142070034140d2185400980720344850060800080e050210403030b950fa0311030481080c188101c1126115a00140100d1a8003825161031401642500111080403070300704144a0080001c1602c500f140ba081542e014040220b40340d11414000d02415010f1000c1000034a0a02d03c010700d8134060092134100c0c2d800030050304196050200444900008 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 306678426 1250 306677176 306677197
    0x7021e0d0206031320011b03020709061401120510090c170a06030b0c0705100b0402130306020a0f090b070303020a0513030c050a050111070e0702010b13150b03011208 73
    0x84031104000da00c842c402184036580d00320400082e00d48919144094a4000d28a00b03e00c2008044140c41c0340d0300998001c0c0c05015154509040d4145440d0817845c3c1001500700007000ea04000b8000341d80e44c0c0c1e100da80030380010240c8409a180c00306c1e0301030404a41c42101c40000c071441d49181001117003003503808142d04090728036104180103440070981c204100c058621104280ea252002c1003840140714003135400c0b41019900c1441c000182d100c0313039912000c5107041840c06944180f041400e45d100d80c12036000900044603400015030b682040c034000e411070400b0201040341c00080d0ba04080c4120050400c1e29260200141401e460380c8085009401858119060010810810a2030b40c80080d40380000c502c1211a1034409083c0420b0102800c1a60f0200381404000b085100d418440495000141c400b0f00d0b88101300d6554500d0103c1c00341181015281c4c00ca01da8005080c2c040b5116000b0280c07805554440040181c3d031414140b195100910540c0855140800f040d1b0000e1882c4c002410040300 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 306679676 1250 306678426 306678439
    0x907180513060305070f03170f09100917060103050c060f0711060f041806060806100c030e3307030f1202070602040b0c01110301080c060c010e0d090609080307021e 72
    0x44031360310903280c4049900806802440034078208104141c4c4180b502c411405980041e0074081ca10a03401428090303c2100e501c1111200440d140980c8581c2a690003090008240100e8004000000307894000a010944481c020000803204034108881151001c24003e000e546c44c1c00b003e0341303d100b544000b100d40766034801020050f0a1b900001000688040c2294003054200c0d052403640312411141150b118405100040080050790359074420703060003214940c10000205101d5181c2215280d0f600ca03070746a802940d1481e6100240341880c1e1030440e051014000320781c5d0300c160000d00d2004d4003030800004c000925407251b510b03e0318885c1906090078040c2902c0541031010540e1518281e8119802c40d0300011008501c80d00540c1c000d003cbc2c3d4a0b064820b40409203994100155651120441a83c0e180144400580c00050240035800142c1844032001540c030010000c1030010a400c24610440001800e01c01001c50016000701c1151211540140703600341300d001c880c06014680350290780c041d51194 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 306680926 1250 306679676 306679679
    0x31b01022a0c040501051f030902060c03040501110c060403080a210e190803060d08090a06020d0908010c0e0418020907051e0c1506030a06060e06090718051306 70
    0x8091084807216034900c101d0100c0c1d401c0c840380d001d180411525110b449a0f081400411040c2c45035042002180c0085c034401d0a80443d220058014259600c4020b4200c1c0d8000b40d40e18210001101900c180c0d03109a0310951843d90300300c24a0780e68400701013041d901140403c001c00c00604040000c2111f010141010981d1003a4846039140c40d01c00310700c01140140d195000211140303000d0244034207400c001c850251a007480c0c0c5e02c03040980d000090150380110020081841840000b4054030810100109103ea40300e85503500251075554003801c1002280600d9070204841c10107001d07082040b81542d44407090001244100000340a2400100c8100d0080340d051f00301680312210041e121b81c01603200c0540d01e858444240c0030082c0b82400041101b5820700a84900d803074017040c000f80c80201e240500c465600c50000180c10400300d160014081891b0410003e4141100c02d000d0388100812240e1010300c3e500d00d80141d078040428051400d18140410061049242202011aa906c0707026070000c2c006 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 306682176 1250 306680926 306680947
    0x1005090f0f01020301030b09191203020d18060509030a0807030b06090d050d0908010603030c020603041103150a11071a0a0609061701060815151c060510090b0102031b0102 75
    0x20440c201840c403075940000041c07050007840ca0000350890030410051190000fa0201c2c0481c0c080c092000401c8100b007540358007c00d61094060358603201010700f0400c20320061a40d9091880507031402140e80c0360400300056624132020050b1400d00c04a0f4a841459660301e840c11001445a40c48143d440314003400300814039104c10b5455003901e4030a10042a1428136100040e040403007a503c100116810030350705000003070340804e2401c589035042c0c0b4072a840f81c5a0380342250a001341a02c5c3c0580610444d140340b140c5071b07041c0196a01800741c022007080714001d00061120144036140001c1c003000c1e808000100c280082e2509030f584200181070006050351520003500685566600c003a107480341c03030300703641d03900c96004c0c824500180a40300c0180841802000c11428480c4010401e0800b00307505060078009448865050101360b200b0b6008094401081c07134140006d1a003503034101c100350721800021441c0152841a44020a0140c004605203081148001380305030039030350241210354003031042003001c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 306683426 1250 306682176 306682183
    0xf1503070b0d141012061508150703061d0708040212010c17010b1305010807020a0609030512060f0303040b070507031b1a1e09040e0d030203090f01020c1005090f 71
    0x28007984030b800b0440800402d150b80c034903240030301040c00400c00d80c0d0301000019172038403072880010f40c40034020608198a0200c5500001280d22911541c0030350106021000d03180c200041c0314807070689040019940301d60b40314030401001489222100c18079404502468041c860099106100406110380718105081590941c0c000004c60341c04140302014183d09990154502e9024000205616080592404689130400907603c2a18180028280400c7e9007920901c600c043c06a0050740900c501c4203e840d00030484d82c00b0b00000000c104205021441c0b0785001101c00e03800010041c01107090609100d0040515804984100c5030b610171010004006440034036900d132070b00d01c01781c08611b00c103245c03802181031502724140760380700c16004020540327a00c6544040c0e10079891010a6107510f415030540807500401d1100103002c414883c0420b038510b51a450b40003540704004190655001075007189000b0300b42d00031200810740310380100032000100d035415884541c1c4440254111103090100d4983c4605 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 306684676 1250 306683426 306683437
    0x3010216050c10020c0f0d050304170601050405130c060e0f031b100804050a030c03091d150d0f0b0a06030c090b1c02060a080903092205060303030f1503070b 69
    0x30070b60000000c01c401494583c003904140741c243c0c00074001a01d03510380002c1c20384400403800d5120300002809481800002c0081e10080c222000c40f18460030300784004a5515042489803a114500306000500c1d4100d014954800403a8400825461242409015182110000307212900b0140c066548405070341c0810001421001c40284403038004040401d1041a001070003214041c022850705020001d00c002070742d0304d000380c0c0620b4207400f004114078040300d022115910100d15900500705c9949147c050809450060110440d14003a5030b980d0000d000c030100070014040c00d901d02e22105407002c6814509020380c0300480110000e000303030700c075070b100300c820182c582150a5640e82d4a03101040303818031240444444150300328070200e400e440c0e07000a1162003509141d4081210b00300201d02c5040c0100180c0c5c41c035000050000000504159042440c030300e0b10581c42d80030901b8040410420309010040320302405611195800543d148032541200300d41520f40c003a0180b14110ac00120105150068403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 306685926 1250 306684676 306684683
    0x3030906040b040503210414061207180608010807050103090602090603010305060415020405130f0608070602030d05390903070609150f081503010b31060803090f03010216 75
    0x19191400c180926107886214401c2003071a9004040004a0104500641c0c04480c181c0707041940790b8a0120119050b808ae80030682d029500ca102440070190f004046035155070801c1c101130841130340d00d4000302d40503c000c0c4103001803508170180920480d4800d03080074112034098140545001003034404a4484d5000360b00075101c540000050004103d94003e008030101c8000500f941400c0c14140090b00010140c110701c0341c01c0f5650300c6248420100c541102c4001c101d0030341a5918141d41704006502d80d442016101429403420001911840032070241080200b004681a40881552130b442c49021015405c081100c04082c050490259000c000d2039014269990307650708150300c0c0005603602d4114580440342400b107a02442c0704c20551000360715521100d0010308580a503c6100403e00400304143d810b03421114881d1440c4044c8a07400c2a42e2044803188040d0780021142503210007101c0490140401d650810448181c96103041441c8040141000740010702d400803006c00d01c5860400d600084 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 306687176 1250 306685926 306685949
    0xf070c0f1a09070f051302090103140412320a0504092408240c0c0a05030c0d26041505070309020a050109061403070c0816050106050f01020a110303090604 68
    0xc01080203003c03c0740100702100004511505000029415512186031149041c0d404180000c00342c2c40fa400000e29001800040c013164203050500c0c800100c50a041000459803a0045562031001450412291002740703000000040341002c0000055000101e82400c0003814400810285890301c0303158402414036040c4003644044005a03100907405900c24807140c1c1006406149001025540480207506000a6160755072803544402d00c0d0f016604840f001840340d61651020800004020004071140504440e60021004003c69040301d15903c14048188440c2c00b01e0360707a5012561242c0c0280c404d02c41000403000040e04081254012512400042d8441e0070410541c20030403018030183c2028681602400d0078024054102a04886032080740900040064091341c030402e03a0b4003003154080c10300c82c2c0d0794407014a4264011034412054071203502e01600001c2d42d2034141c4034103242000c10b80283c01ca4040ea130316030011400d0201001c9406001c01c0000414554860000340090402d0382c000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 306688426 1250 306687176 306687181
    0x30a090b010f0e100b18030f0d0206060a080a081b01090204110712030203070f1803050109150c0531050901121505040206041206060902040e0106020c03060f070c0f1a 73
    0x8400880001307480e0307403410710f0344030024051070317044508642060395140300490070780040101092070540c500c040807085009040e68010a25804100240075140031500d1150080e103e18087d5200d04400700b00908000c000c1001304c4820b00f0040150710382e04082000055500c155401017030590713007402000c03045500000740b14003c021000c1511583d4180300d207800c50851510b49030103002c21054000a1080c00503400d601144a252400e414000d50390020090100600c14906041816440006800b100c0e04140303060000074401c0301a10940c4e01c83e583c0f02244010004a8900715206014490070050840500410303941c84607030301750b80244000d072800c403e8a0180d040a203484521129080040d90a010a02c00542d90b03800548050342c480b20190b01611070545058030040c40d9a80c0301e2500301d4008280018852403c59080741240c600c0c3c2c082c0c410300610041059140c0b2011070303000441202001c08039900c64030412110006a02c103410035480c03421140c64120346d418004241c010280000403c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 306689676 1250 306688426 306688439
    0x303070b060907030c0f0c02030102040812030103140a02060d0203060f0a0e06040c0801150302220605071703071205090106050d080c070b03010b070b070c021905040b0a0b040b030a090b010f 83
    0xb065448840340c5030400c480800b5240c01410005c01905e1b01080204400c0810150354080d0304803801040c07804121102c1190b07411011409030424841900c6408025080b00c80401010035082c20042d07000740308501d4030104002d408029000a004103410482101e00040350b030f1260800d0002038600d00c000390034035141010802043c0c6030010407000030041c01d2401005150300bc24401050008a41809a00c40e91485a200a803814619a10480c035406000018001d5000380040c01030901074000301013640303541d4072100301a1100f03851810016854078000c00d005021540856003000010002040719941d03000028030710180a98182c82000c030000f080510418108001401800e0120683e802c40d8980580303d009800b611001914241c6140d001a07100e038401c0c00c0091120703038014241c040c016480d949841134400c03140511802945403130b505110f903181800003403003184e4080c84868642810502014500c0d000a80130441c1d00d81c86640b0000020407000300d45000c0e01c1d950480310f0890b4038091 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 306690926 1250 306689676 306689689
    0x40605060406170405240901051b1b0304080111030f0106090e04080706060e2503050115030b150c06040302010b0402090901090c0909022704020f031308090303070b06 73
    0x501551003904100010070660f500285a814a100f003251040266542c030b04107076080030411100102100100703003109440040b0810568040d00c0c42000030001503071040304020041d903c01030307460b400c20802c0c8007003200b901c059112084041401000d8031704083da40d5440702e09640350200b0102701c4200c044200b2291725100800d0300d00415070340c42d10150031890411107100304e0501a0015012140000b008002c0c08140c0d00700c9002000503800180c03071032612469841c3c50103418078604503016200d04000100c10f1103405102d041c0c0e0142200074100100d140410b50050003268141c94002540380007810140328044040c0c401042108098442c0380342030f2a00074210307402e600a0340e00c0b40b0b105100700003003238454801240c151114410b0000f07021107000c4040e120200d0543c001d00313070640001a41510000c0c451180076010030f00a43d500300c50903c40007000140e02075a00d0300240d00d141880001c0201100010b1003021601a441d242c0c80d1000d2034010070700359480004180d03880075803001070001504000c1c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 306692176 1250 306690926 306690929
    0x803100e071d04060303050a1b0b0408090f04060303020606101101020a0c0506090105011a030c070506040c090c0806130c0c050d0216120b010308180306010e040c080706050306091909030e0406 84
    0x103e500b08803032401e40c0d4010740f1a0103030000440030400340070b289900310440148100d05594005d840c003001c51905103494011035110580260040580c0300c1c2010003800e0502558058a44c50340180000d41c0c2c4010901c41c0741008002040100144001c500044030020b00c0145038044141d510282c1c41442401c00740d142000181c15801c140c0c0c905001082982003142c289a13010302800516996501d4003107503042d450084c2d50700540240110f0043c842001041c8840e0000c403100d2210038400104406030a031251941110343c0c0d81c01008400d5950410840c0b42d01040001d040c80c00d0105808603141c60b40c0d86410f00b00c0203500c000d80d100806e03200c0021800500a40140a04000c403421004907075501d550810041c44010246003001ca105050160f6100d4065406030001c0c0849055694440e2800d142030340035201611040c0070700c4004509401c010501c43d05494158440030b28544401051004506c00200800d10309a402242040103940e64041c04180740c3c001c0d9600548501980c00704011110706 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 306693426 1250 306692176 306692179
    0x60909090304080717030415050903060a0515180636190605010e01080a180804091406090106080405120f0d05060418020607060603020612070311160803100e071d 71
    0x50f0303101745c903c1400003c903401d440000c0440c484404984005a41d540a20101164140600c0342003113403440c09940b00a10030f848e10300444e081800340d441400051000c05600400d0842c0740000150b15084c40c0303d18480b07107039030802c05000c40c9410105145190503400742000285410ba81849000c2c440b659030304242c0c400d11002000445d02d0000040c1002800c80740301414045404001100c02d040d69000319041a03405200015080b464504200c0c1903010340110718203145442c101001c00e0b07000c1c240740c0b48110000380010243e070742081c2c3c2c00e4496140c01001107455124010441004803908409000800071201c4080d0b00c3d83c0314904540709503140180140d0040b80380c086c1c1003c506c043c1440c09081e294040c1e4416644a44c0f90030100041d01c000d401c0a5081070000500c0114589142a214802d92440c5d03000c220b020310742c40c03c001140c4945083c84843c41c0060b00d140000c28241e00084d9042030051009410940e0344840800c1c1040d0202d904401090101c001664885880c0c640d0107101c000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 306694676 1250 306693426 306693449
    0x1809030a020115060813110a0b0418020403030e06070f05030a11010b03060606030a1a04090c05130207020603062e021e24060a030f060902210703110609090903040807 73
    0x200300c0c1c010045c0c0300040104008100780740105041c001034003001c51403a00c02410510742d03591540c440d00328075805071081d0359041c032401500600c012001c0c420b99040c0c0740d055a039071042a010200300021500000301c01c0d10b5220040e000440001e1040005007810415601c541c40710388842800c00d421140f442d0469802034200108002d0140c0d12602100c0d0300c003500e901c0000740314103082c1c4e42c800c81940309510b040d045440c0c00c058000340305a04c07802c04202c0b00200d80142020f440110913030181d00034004020b401c00024404a20303580361214040b00c407030f03014042c0c0001140c08207800b00c0d2008100d81a950160300020742140b8041801d11f0240b0300007041c000103080647d0144203e00c00300c1c1001e000d20340c0d080c030f48a000c11403176a42c108a0b240210340000d502603202c640341c02c1500040058620891080e2040c2d102004405208403492104041c41000340c600e651840d110f1a0601c0807010003541e0240080000a245580c1e0903000341c05071a0401c011502c660801403000c0ca030003107a80001d005400e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 306695926 1250 306694676 306694679
    0xc0e06040212040b090c1305090f0d020a0201030b220903080703022a07030c080f06010f03260c0706030516030204150f02070b0f091306051008061809030a020115 71
    0xba0481ca400c19402400e11249584035580d0604201c10071308041e50004030980120110f450940215000d4603901041d035203244410f0361042d0b995000341e80300f035002d600b00100480156009501290220b40301402c18560f4406d10314000c03003c50300c68070115400b03030340e101100c0041c0755005030302c039911100f1803d00310700d0f214503021980b0350403001010008840c3c1503986041c18000c0d040c0f011100a42c1e005041c0f180d0943c0303441c81182c42d600100f01404180c4206400001e020824030a000c0441ea0000c0c0724031603480e40304548440300e0340002d010150050003044441c5014804204100040416960000e55824500040d0b500e0300c074140308a0080500510080c8440244400c2d60449003075a03007425080001c1e000c50130b074280145a03210784240f641c08600008040d400000070710301041c0407a40c3d041480b9603010001d0441c0d205028103900b091a020710308070150301032009540c0043d0020102480c00400b08022088040304481300741598001003101b030300c0075030240103684d034900c9140752048485 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 306697176 1250 306695926 306695947
    0xc030c052506020904020c030415050901080736030201030b06030c160318030c050108101503090311060705090a170604110f090907080f010b15091302070c0e060402 72
    0x5034030741602408140c07410090701c07041201550403030344c1c4c46001038802e540b1740c5c030b101d0072440d02c94109200710050301e9800c240c2c01c200070f07210324200c1d0a2200140c50384032051f00d4041c0104c03400f810465400030f032160040901c0240c61440f2100705581404007454200306819440018290fa20380d1004902518051050142c442a00030a813800b501024038400a010300600b403c403174111306d4840034201804858004030600960483d008181c0c0c5080e02c807013034192114408207250303039a40c0c881e0404140701440110041c42c801c0d0460003c240c020300d003801054844048207420084160790f80c0c8046040083c06001d5030912100e490018014404000c04d140540c8680a445c1d0320014001011401d018290046603600d6000301c1c55040d03000341001c44685495400680d54590b42e0144c80401d2180040512000c101400b4105080d20041d00c400307044c0741041003903a1207405c40001d1982c031a40880518800c1000c91004d007500600903042d4408940c9001a0308181400103044540a103004100c1500e10 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 306698426 1250 306697176 306697207
    0xa05060a1d07050f130203150108010803030403020a1e0218091c0206011503020d0c0c0201022a130608150103060c0503040503070215040906120507050102010c08370c030c05 76
    0x115a800c0c4c1d201c03d1155143c1d000a507280b80c0c090060b480c041d2010062141c81085a218548688000e8035144200d903250402d841d07607400308680003001a030144c215440019402e40e1894011400c41c0d4001c81c0c01e05960340019241412544650850506036040045180f8204000f01d030344945203480c044240c9504030700a4903038205001c1c0c0c041d40c04c1c82000c02084c0b07600c01e034102da00d00310680ca81007000c2c650b8100000d00034108a02c00380d00520032403061042c03c003030204141c40c01700d502d00001c0441c40788aa090101410208982004070b950700c00c00040c1e001e501744016803041503030080040040d81145862003c5808205603181007140a008000001c0c80001c100c1e41c0d0650120b070b10381c0da03045008501000911440d00891601802c1c040002000400700b090364440750712400c20b5484440d00c5500490803645011074602c0061032450105000080c0c01c1d440310038219a04d0500c90076400b44141601d480301d29907000d00c01071552501600955039040c421a40c450440349040ba1510003044d201c10711 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 306699676 1250 306698426 306698429
    0x20c0d080406060b1c1a0406170114010f060e030a0b04030807390501060b0a021608032b090b040803010510030b060d020a02160f0312050405130207060e0a05060a1d07 73
    0x3c1181d0b803614110403003451001180130300e0340010018846151110080c227070b0580400c1d943c090302d43c00c02d941e00118600005505042c6c03032000d01e0009113903103800d008441d060318045035590140506400c0802150703500459a11850107921900c6031810800c030000c203111441d040103501340c10000504d0200e440044403200d4000c001404000c44c03445141031090040604c0d903c504921040050341e039691640102c0d44414800d290100680169990840ca688078800c5440903940910b00308005052004446490402014950320005092000e951841507401003500d05507015040440104140d2400300042d144031281460103110184103a80840c2d0300e03004050035600c10b0b540100da180c0c50180300304075100111001c442c0e410aa1640c139900380204130014041621141c0c4030460002915002c0c00481d801c481020305240003c96060380c1e114003c3d04101811a5115254000c1c0ca0400a080020071034940c05103000d00482d0510600510803250040e035925139649560401c070b1400301c40414586c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 306700926 1250 306699676 306699727
    0x6060d1a121b03120d1e0204090f2301030b0903120f01030323030708040212031902010506010c150e03160303090309060828020c0d080406060b 63
    0x34406000d654004500003819003040e04603810180400031800001042c0d1580c440c540d0584100e044500145500d4030001c0c1003040981c4820415101c01c1e12265100c0200c41d0004e001502585c1d2602000030300f80d900581c0500145501e5400a0006100c03e102d80d81d007841a551142905251005a8142c0d40d141448080c0c00b001000b0001824903101748102c400482d04950707110700a1914402e80b240e02082804207900045040d810307410000700088410003d051003461190071a40c030080308581d41d4400030022a085403050303c40d2006140b0420182010786050212004103601c061402421188000d08160402c81c48025010100302c0500c0c1c01c43c0c1c44502094049004e0408040d00351035403013038500381150301403101c0c0707400305141d0b2541c015213281c0e00c03d54943c1620b40e0b80b0320088076820419110781681010703240d010040d0000148540f60007401d006030141c184003810445d079080a01049041c0d02080b8000b0030002000500d120712405003a5904d12203082c00f070082030034450300d480c100600c03 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 306702176 1250 306700926 306700931
    0x903060b0109050d060c020f0d08010f090504080f07061508010203040b0c030c041a040e1303020706020705101206050306130204050112080a1d09160f0201050103110d0f080c010c0f0806060d 83
    0x4610051092044031600455230046951100403484020b0403003009124050384c03c2e00318013011031055400d0080310701681d0800340c29407d062200c00780100d9035118800c12690f2075982e40c81025036520408000000346200b00006031686400d04060201541c010f0400c4018801002049141e94030b440075107040d9448010002c918410b82c6000c00484e2080d504038003d064200c004211150440c0329512110510a60039508030b15a03c071026039071107141c4c3c01000d5101c40345818500d40729120392403060b120500900c0108a050b61180464107101c01650300c20078520117000854154109801180e00418140d440d092003003c95440e5030f94140038000e510020011614007202440f100c1078441c58000b14000e00004041c2005400c0c0d00d02d40200d4002d08000c218400308031008a8010300c2114122030f0003980c0310115080100401c42842e0583c20101d034030360b10307225505001c56086009800d01d080104000038030980410406081c0d92100c42d42502040b80301803c1062585501c5c0a4444100510401 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 306703426 1250 306702176 306702191
    0xf090d020721081914030103020d300302090a0518010e040f1e230c0411040b07050a06050c0a09090513080c0d0801050d0209040b07030e07060903060b0109050d06 71
    0x20405400480501810f03180c800300301c2d69400e290030240c00c0c41c4074141391141e403040b204510b8158180d000910020f507010348490007000101e814103c00c110703000e82180314001d2044103c40d01d502000343c40180f030000a580803540300d0050510b00c0f042009041d085400740c130291801041d200e0341c00e205008140c0c007400b40002060401c2203e001d42001554024909103ca441e50b41ca1214001d10791082940e21b00c500c10b081d410010900314002510400043c00780144074503500510001d0984213001c2d620f00c03c0300b0040081c11007070a801900b0440c3c8903001502c00c0c5400c0d0300f049010f507103005e0300e0a03c1481c4100000c0301d03a95000000708003110740c1c161002c50696500c400d80c203144011000c024005850000d20a44e0985d00801d0881c010501a110b914031a40c132003060211200c1490802504500d07994040380105949000041e0310520714540072404081a40301682002081d900280116032040418030801425000b640941002842d09010082c81c1800052144011180c09040c0036030300c00b00d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 306704676 1250 306703426 306703469
    0x812190507050304290901122a0905031209030613050309060406051c0c02030d180f030f02010b0108160503041106040b0403021206040f031d0907080f090d0207 70
    0x140c030009900801030f03d841c0c558802c03070411401000e468500100c02003900f20040700740c54900b602d20440e070603941d9000301a442d000030b03401050380803a0a07090341d1010104061450049107610060501561204407040c5818141490003245440c0c00c0c4450500744114111514001822540014003200b441d904800904040c0c5c1541b0030b01540641103800060b02059454202000300000341180100c05c0490480c41100703000c66040c1c404a80040e0004c03c80c1125000b055000001202030648400a4040c02680c55900c2c0703030b8203048100c020950071040098602d4081c4103101d100c1301c1c00e00b040c2010380b600c15080142400c110a11074284000840490244810b035000c012001402410303141e0790707640364070703540c102c50700144003c0384280c0685280c00722046d004200786000750381c40a1110903d45981e50103448a240407000ca164140c00404080e81c0b565400c00c40c10300500c4651130348186824510b00c1001404401000003203603030f20040145214075400905607080310341d002003581d034404a514 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 306705926 1250 306704676 306704687
    0x20c130609020f250c09110408010c02010b0307171e010e0a0819020304030b0105091905151f081906030606030b090606011b0b041713030c081219 64
    0x800180025101046044108554000400407195690440604e036072010700800040140b10b540240521419103041000c001c0d140c000303203d620a44070900c0e04180e11008107600310b4605400090041c0c0d1100000031403070400344020006400ac0321580c4910700340e8800a5590b90018011100c070804030a02c444180807401e500c1086001080420f8440b501d0140c01d1040b99500440000d48004039018a810300d0140000301f250100d9a0001703c00c0d000d60b217040100312000e10f00070140742e840360060307240d103500391503602c40c5038815414a80c40000d8045403006003c5000c641c90240c1d200c1a1102c91000d140c0346d08001a207a104484000c00503003d00040c0c20100500080d5200804250401c8008420019444009482440b9601c1119841e540d03080c011101000f030014845071000f0742c00156008100407418a030307802030162000c2c00e0401c07103001e80c586640e440384848518074020b00c0c03028004c214205500c0001405004000c16042c01030301c2121185101d021180107622850704440800381d030081 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 306707176 1250 306705926 306705929
    0x70e04060204050d1b0b0405010804080918040b0906010e010b071101091d01030b060109030f0f03090314010e060a0203060a050409110a060906020609120d05060a03060507021506040c020c1306 84
    0x13401e540d60021141c5040c00040d401c80c11020000070198401248681000d000e0b901107990503903c442c0d00d51219213074285940e00212590303030010040140e80c0540f004a1101d18000da10500d1485054900400c0041c20800181c10865000701c0d260010404011001d0035a07000715041105000c00f4010703140180e40b80a569403106000c1014100415944103640e03402c2d40c1280e008008031441c5989580c01101c00742c103280401010081c40c1180040071603202c410326942d0310702c80e0802c0e48000ea00da480b01520481c034030b07a11440d5a07440d100e40320406801440700230340002c01220705500310300f03114000440111041c041c6900031551b510303901c02803102c034000442210301c0140c600a091912440c0c0240440107502410015224841c0447c40c0b03054000703980380d030150748016900e007001905c00005014010190416510000940c1c012000c40d070a0320446006110031380050a0800f0f80c0711800354032520041210303104525000050048540118540c031800c03070308540d10300c072110041c2840c0340142010f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 306708426 1250 306707176 306707179
    0x503011d1302151b010e1e030409050117010f060e1302011e030501030201140f030f182e110f030603120d05040212030309121806130311030f070e0406020405 69
    0x2400f018401c9400300d00020455032130040d128095007081e0306100c9090b190903482806045d8010280a850442540408524440c150b410740c3d180c207599115000a403402170b003240600504d45520442180307400d1040723a110149040003448501e10f0b1046c11040c401e030040444141c80d41c1e01d805c0b80e0440e0f01c50042ca84080310110420200442a85030040c0104024002240843d5101c112044c0000407079041d94195030501101501e103170b0307c00c0d10f1841401ca02a06203d440f6010041d40d901d07900040c44019a0700d214041d00c4071002d05001450308800c080006c6030860203107400c01c03a01d044c0c0c1d104402c07210198100c0e110140d9945504006c03e140131058400c45440315401701d00d1030384118903600054000e130700031034000241d09110160503860348015a030505031540161781d07800445d00c8030b001801c001043d1003240f007541100705000c101c075a44800c45030b0303508504441081c010081842030499428006500401a00c001424030640c3c40216000e18101c031207121002404001d03081d01210042c040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 306709676 1250 306708426 306708439
    0x509060c1014092107060b09090a1b06090902090303070f120210140622020d2c120d02040b0712170601090611160605030a0c0503011d1302 61
    0xc40c0030081c01000c815041046040b55400842e4001c880041c054901c412115000c40301c00c0f0001184e121640d100043c02c0303d00f40e841341840d01081d902c00100e20302c03625602018228000c0e031481d00820202108104062749000064280326082e80f001e1654196004807000595a0a100000a02d103001b648402443e038044800039108000103440450703164032071074003101c1303d8111054071003050328000040c202417504a007000445c00c0c034103194281403c20b5002e2540104401941401d03003030b40d2014221480782601c840602060b00c4850403a14001c0c032030340c02e40d0400c0040b550081e030f4996013202117565030b40c0c0300802c2c40d42202942e070741220024210000c0d42a901c0312149444903500400340031031008203d081d060044c081c2c032042100f5110b980169a811005800c0c2a003e1320346841003202c000711032007140b103203110040c1c0003035410000d05403d880b01c0c0d440345130100401c425910f00c0ea20100400000780b00411546107550711068084201070a0702049584040081134210441200030b5400704 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 306710926 1250 306709676 306709693
    0xf14070504030b011202061606110f12220b07030b06040311130605090106200709050f0703060b030a05071e0302030105130b0d0303090519050601170d0f0509060c 71
    0x25001801801120f00c02c1d50002451303a80c94514140c5030000e5007019401c03410402c0320143c0300207480551a1154455800059005015584103005400c41d20403c00300520020b42103160f4000320002c158000258417400c94404045541014443c03900c0c64001c0c0307000c150801140705a0f000750800c105141015102540351541c0c0d050640d0074103a504002c80c0906130302020222103e03000d0180350b059600182840d055039203002d00845500034031074203090403440c14295000a01d4000d00070340b001480d20020120352070415010720030040e60007902110074980b610008000384003028007540c0c2d00000301000003403240c0e1a680255524030318003501400342012100140b00b130b260160302940c141c407010741d458640d4800341c03000e41c81101c541e000a5903111a10482c4d0800003803090304030741512440f07402501e81d0005070b4101c1101961881004440f260409401801000c000414204907145c888000b42400340b003845014048088480c610030400000081c898240c1d1a5403044822815203c02101d4101 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 306712176 1250 306710926 306710941
    0x60303160c031212060602061302100c14070303030501050d03091406070812011a0702030709050c070b0711100911090703110406031b0f05040608060409020901080d02071e0303030f14 80
    0x1050036002c0046080c80c005c00411080d20014446208204100d2440e08102664080003d031528005408007000300000da0307000000c3d060359020081c1c0035401d0081807400d05503c2c0181c1503c0050300520b0040d545540c089011075840380d0500125151500c1d040718841e00100850114400c0c070002a1031554009034a6404041100016040351080d334043c2c1e296440f2680a0019446503110195241d800101c0c14403580c03070f080d4001034201064014883ca2b0040b156100c0880d2401103580c1000314040103158060800103012902044640d100104034004055464141d10040e07020058082c04507100040e80b15030096000c601d9225408020395203c1341d484000402070720440f001c042c0c081d1080b9a011507024010382d5a03031518919a1541801c0c1400e2100072101240010841e0703038400d4940c080343e0050380703a201000c0c0c0038001c400050039468031080c20180c6402256400350030b031400c042c100e0030262032006840c202035940c0b6181c080360482c20014100040c0a00001007801080124240b0104 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 306713426 1250 306712176 306712187
    0x3152a080603030c1b040f060305030703090e060d060209030c06030a0603020a0518010506070512030408311205010e01060803070b070f0e0d0602070b010b09040b0603060303160c0312 80
    0x40901552105055954001030589034010300b80400d442d54414641203000d940c00b07400024001d0006040041c0c4070b40f00e0306000c41580c10715442910a80c00003e821001e066204103a9030141c400b401030300c4503608104020441e2044070b2100a01521b5010903241903075035007442182e1103420000d11098880c2400d4454100802c810300c0124411900b07000c000134141042c035170000f1403aa03400c4411000342c0c6018103200c91988210f100f1155030003103c2d5402004055003000e1402140110400d580301c2040c0005c41c0103d900b83d008107110410351246070001c030b60303044200c0b60a4580550380c1c41030142a500e8841c0c050300c3d00025508555080c48000300ea110000406031181501641c07800c2229190f011040d04e5040c401312802000600d00b148580842c11b02c8070001454622421006162102e0350702d6600903e98203800518000b040003401c0baaa40c41d00340540650f40d0b00449a8500d0f504010780020350300d10801039100310b1080450300c910140a002c070000340c001e40d0030808121580740800001840c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 306714676 1250 306713426 306713501
    0xd1d0601090617060103060c0203041a0d1118010f140711010206060a0e0705070201270602011b080a0b03210309150f06010c080405190305010e010908040315 69
    0x10701482c004001801d1460907580c040000102d8020f810140d0941e00c492000d4200881d50b1000e6200c01c1000080340d08480050b42003581402441079110060161482c059402440601110303280602c140d103908a104503007130401802c00d003000001c3c1c483d01070081d0b4000390f0041c0c190019180c0481da2005001c2e1400051351110426401d40d8a0b40c1d882d5010407120203031a000f4401308040340302c00180480c0c010001003040c980141022280308003441c0d00110f8003140c003041c0c0302207282404801c00499409010340690741c0508a007040100f0b01182c4014440180200b114108079160440b0a60507102880020240744070ba450000e08180b4944440f902c2c1d0344280e03211001c0d40b1a02c9291351114411000141c0030381ca041e81c104e00302d41c4440004441010010b04c0a5445420401000817503a17950a00c8038024034261070001329492a5060503801c584e4003918000c03560741440804000680d15900f10307016a64821070030101030b040c03195410024000c6903c07102c40484002090911b0302d8404030080da = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 306715926 1250 306714676 306714689
    0xc130609063603030819060b0406050c0c040504031e0f020d08060d080720030303010f03020409060b09010611061e0112050102120f0411031b010e04090203030a0519050c0a06020d1d0601 81
    0x4003802c2c159031000707085503801d00c50104100f10038027060001c5441140103140c42440c1100704c2d45501c03c110005401c40d00305880840120b0004540d41c14541001c01d60b400b172000c2c5c0c5040003500d010030720002a4480341001407a80c00c04c25a040018419070710b00402400c0e05403c4208252203142516102030383c189900c20982c20a812a245600742d4640041240e0594007a8150001201d24540c01d010144c0030b503000032144d1a8650701500b009407600c2460b64001d007000c2d621040b075445e002c16614100704002d0803408412040411200201401c2c0d041c1504443c0c21015400e0302c41941d0410900a00a001d00c00300800fa041041c030003a04d0b003c05429000303e001d01e12200000d102c034404c00d65501c01c014103207809100c0c034040c6081c280d80917111b05110000050000324844070b035940082c1c1198800c0204c200410000304424aa801005a0190004240d410180d10f8450880c11165036420700b804010502d0b030300020030b011484a02c0c3c01800c0d4100300c803581400e403d48010f0710f06031191401d01542 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 306717176 1250 306715926 306715951
    0x2119030c080907050d02040207080702040c08012303060601050c1e0c0f01021504060b040f06090f0c090303020601090507091806050907090b030c1e030c1306090636030308 75
    0x710122000703d114400c541c00200003030b040c461a0360902002e500800c209980e0281d081c420040035031514011141800d0055407801d68960418019501600510154100c5424008e404240b0350b00c0000d8400d4102d9000d0814544907103a44903207030b181c80030604613064442e0320104440e04182c1c0000c0e01c259100c0048404904c808070803001247d8032005410083d08240d01700005c03a02051540c1d00008161101910220703c4081c4c14961a054504541c000342c1803561342d4800c850117080e10301c20451811618a014030203030340b80d03850080d0350b00340600440d5100d95403003001c20380c46c5004100d140002c000c00f03d161104500704e11014801018139209030381c01391800030000358807035200d458550240ea040f84186425502c50610200c00c1e40c1214030952011003400000346040f030107030f2001d144982a40d607801a9100491514444156242c4c0d00080070302100d000d00784450394005071201b00040c4940d0340c00f5092003a240c00c01c480104800d6901e0355520f8003e17800304c140355101c3c1340944200d000a141 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 306718426 1250 306717176 306717181
    0x921070608091504020a08070f0f0e060a0e071206150207090e1b030312180706020307020f0616120f020f06010501051207021f061809052119030c08 65
    0x9556000d4200c1e902c07201c03034004851040c80280288041500b0a0010345090401c0b40ca840324603142c60010340101c0003100310f10380c0802644105152180c09080a8152000981004d1010524443d6280504010101d100700040c3c0308520900c01c0c0c10580041120a010060f61075142580495440300814014042c079140496050154024203c0d00760350500100348510f0880100c0c04000f40186201e80d040c0000c00c543c036840c1c003040708010301850303043e0003008450000c550b803645814015070052056400a21183c1c02603a1407036003001c007081e010b84a9aa645402d00c94a484507060180d00508040800009040c10380c0d110703401c03041101d026003c41346035400c001102541c40009100c1c60740080c074208122046800b0180c010394028259004885002845c2d00e403850007240d41c03500318012583c0e96442082000c204010b4400d00319038020303042000801c25100c1c03e441747c1189a021485d00000032060340c650525070300315034070214659440745810300305440042c040c03c00000e5600000d0041c201 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 306719676 1250 306718426 306718439
    0x90315010501140a0909050a0501180504080306011416051e07030b0406020c121602040b2d010e060c070806060a080303070e120313050112140406050903092107 70
    0x914180c0d40141c444460381e1022401094031548000c0804080250004c0d00080014090007a1801441c042e030000c1362541c10006054052000c0482d01a0920700b8001400007203090709003280c0c1c02c50300030f1801c820207209400400d00c161045094104856503906c90080c144100030981814494180300c9501d000c5441c00c0900350b03078000c5804050450394403000030600151640c2e00900f50074002006844400c0d109030b50a20171500040340042d980c0501e03258807000c40c94148107003030444408880c3e10480354445803040da10140807400c0301e40003a100140c00400e6a000b03140b409080a00100031598030380000200b581c86000510a466241c8a240c002c030311189007400000b01601ca0900081d82180c0d15070700226446d8054012580d0042407520384604c1816050000b0681c03880202d02e1074192900c0d0800060003849403201c2c19021615050080c0c80c140428101107407c9904940d0108894a83c0c11425095101e040000ca17400308120095280483c071545500d0ba02880540c243c511144d0fa514 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 306720926 1250 306719676 306719713
    0x61f06080112020a080706020706030507080903031825090f020412260c011b1407110a0e01081014040b040b090703060f020c071203091206090b0c0903 66
    0x2641000c80c8000e001440020b0320146400c12050000341042c4007035a0700d45289007000a260000001030308503050a00a02c0e415004068000200b0b180076407051078140005926400701400c80710b1040802d01140403040010080034030a00c1032034100003c240007050240840342010b1080300700607824900440110300007031003600d0884440418140ca07880c0642d550781681005101c0c82c14000c00c040710300c0300741a10000e018000341d403805800010782a04c412010000013038110741c3d83c0104030075020740b007101185001c26601210ba01120340440d15200d0400504507109a800c42c051011401c030000403030200c000b490200003051490700300b020000072070312101d40d110100c401a20b1070710100c3c0880e00003020018031651000d0400181d034001a201c1c2d0b03405040c0e45003590209651600801c1c10100c17110b0a001110060903000c060232103000300c5035005004d480c2d01e84120f981c4600303502d8090045c452160010782d40603911501d4181103191040d515032840d044070300c800740a03204031000c0c500c0519000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 306722176 1250 306720926 306720929
    0x6060503030f16050709090f0605090708030f0c0c1e0a060f0503010302060702220b011b0210050f0f04090f05150a09020a02030d1b0212030403080a0902010302040302060a02061f 78
    0x4014140380c403c081d0207600020141039400c07141c0c0e22580c40c2c001504a80e61013a49551442000c0e0070f007024695082c544155503010b000704e83c158200200c06c002d80e80d80002194524610301d0400307500c0e03500d0f07506102d0501780702c449078680210b00f10070780c0e40b401c044000b10940482401c0310040c1d44a81ca40c101210401c16400b150004a0020001400989443e40c050500a0702c0106010340526402030b145048100d0035602410640d00c0d10311000c01980c200c22181d4550f034104020380459906038000a44c1c0e002968003030400e1180005030720605101c00d00c211464510081c400c02d03a9241d070340700a5070040150f0b10420940914180c04034002c8810305410200d900001054010040e0074100c11b40000d5010884000079403000304a445840b200c41e000e03800c0102054603410419201600019082010700800442e0300b00d410810040041d400552403500820b404a0004041c4014401a0300134440d80d000030b9408000810640c40d080c0d40010b20601c15200d2844a00140041e000000c1c07803492a03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 306723426 1250 306722176 306722197
    0xf0306050a030507170d0f05070f0f03080405120c06040605100e070f02011104060e090702070909140d0c03020303040303050907030804030b062b1e02180a05071803020d0f05030310030606050303 85
    0x141904887c200e00c202c015110040c0070f002d519034000c20783d603541d00c0d190040d00700480c04204000108414005c0a1004a0034036025151040c6810540c8100701c0d00c4000007803004014550341e001043c51440100c0ca8513003d48405d14140c12241011140a81540d103402000780042d820a0414140948440240c1e070848149407a4010346283c10f10402c81205c80c010100c508522032880001001c0c0e40a018003007a80d1302403004290103a0040c0e1003503080c8543c0108500c1881030050300303000000e40c0041201e52094140c90000b0301921841d07940c0381007105c1c80d030010b00b02142c04900401401813074560346000b4282100d0320742040c0e00341c4405102c0c480700d01905000080004606001041c0007a00c610404081014402c0c4116155400101028001c02480343c100c2d402104014600001e4410301c2d0304a405070a03e01980c80342c83c0907054144140307000082c01070303100e0300d0310384104400c120720885147d40c0300050b240c50f890a066500c0310b8484ca84410744845061000001c1c07103040100488140203107 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 306724676 1250 306723426 306723437
    0x30a030e010f0311041404060905040819020c030d0503160c02060a05160c08010903021b03062d01081c08040503030c130e040602030a0f0b0109060f0306050a030507170d 74
    0x380400540320307221504054000c1c15282d41c01c600d03615025400610261650000841e10070800e0410310044030480d400c08103d40303140005000209014105131082a0000c0071f000540d540100c504a05041c44404030b1784e0180301d815074501002d40c100c0b01961040468403404e2115010741101121807024000003e0f400003010441800d40314410030050484c0203000c82100c2c6003a9459540c04c020420603404042e042e5502c0e02103130100740e81400548550540c256000b210414044000798440c00007608800c102c2101506100120800c41040d000c1c50100160800d03040d80d5034407010b0707280c180a030501800b4202c100703020402c090080e540c1e1030266030868021030640d515949421039661041a26034544a00c05070005007040c14130700e08900c500d1180d030015850703080100301282a01d451400713085942d0701300b15940328180d030701001a4013122045d24140303003060188441070b001482075401c001d8100e200070401000740900043c118048a0201680c0e08003034866004180e101c507500000440041e9 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 306725926 1250 306724676 306724697
    0x30102030411040b011704080d1d070603091a0a091712040b0702070b1c05010506090f0d06061505250f08030c0f0a0e10090f050d080706020a0c050606030a03 69
    0x10b00740d10000c004c1c1c0041c1030402c804500c5039400ca07030401c1c048504940654002414084c04600760250105004568100151000100418036158001e50081c030080554440c080028020100c04104205100c200b0048450370700e50030700e0014141400d8190380f0341007146007100c000c590203401c64018290680c084100340d2502d5888500d140c402401c00c4086102d50300020541e986c0407070040102484031f20b0001402001e245152040d07a10580c00280b0406041c4040d03829610b0b104081c0c0800c0710122451180721440e0301d0450002d00041e008201000824140403190503088030052802c20002c1040c14003034410740300042c03184170402c0390003024040342d83c42c1800001d108001035500840f18081c5542450203034024041c4a4002148540000e10f802284071454140360070822a00c600d546000840c00e8103000081c031401409201c0c031400b9040001c0b020b800d215440c400c0d210181d03404241556500303040703440200080326042c01034074540102d0012581c103246c00981d00b42e0300e07a419210500c0b0314 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 306727176 1250 306725926 306725929
    0x3021809060d170706051609060206061011010905030c0313090e0703240912180b04150203070204020f2505150406091a0a11090d12051909030b06030102030411 70
    0xc10f00714204044101e41440b0400c001142c2c0e0107828814640e40700701003043c00d080e00d0000c10100503a0300c07903015900441d080c4000d5449201803400c1c0d4400741c0c1400c0384000304200240d03006000087c0050114000410300d8211014084001c1815200c035101030301102e51203040708002c40d0303904c00001416502c182820800900c02d008208010030200600d0140a40421080020780304928821100080203011115000390008081c80c02d0f18480180c40c0003035030400010381c031584507501901400c0c2841c09940c0c040d1502c02c0045400290f40640f0a540b109150107904405401041c09400c0101e150ba2008a840540814245002c1c0d00074006180f140f02c0d02280d5810204040e006480700303600c032180f0001007504d20846840980072080190010b180c81800101211809807a0f048200001c0116200d43d651300b0100d020080c3d04284c03d054140c01e03c110940f03083c8101003000b070000d15110110403c003900199910101c0340104001c2d080341c1c0d10281010300703e2000b01d400401d540c200103a5107185 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 306728426 1250 306727176 306727193
    0x180106091d01180e0a0f2306150f0a03021203180319030507230604050c01170c0c1c030b0a090606021e01020f070b190b13150504050703021809060d 65
    0x513a4424002c0d100b46200e1601c4014015083c46070079910350419074600c4403009042d42d03012091500b4000a48002d052825a00110034400240c143c4030b81103403150541582e0303440302d20500455004184031030f04030109844c107450750000c0542c1c1511200000c3e01140b14100843d0f00c402d81528080d0103a80c001c00c1c2c2c1d50689160700311035000c1c1c808000782010151140490001240c044098100601c007511b840c0c0b070300c0792408003c003001e0303410088884461a8600c0c07644c1c04a58006028088a603181c00152030704910b0710000c06440700e225820501c24144560301a030040346042e0080c0d0303000640ca41c440e00f01c141075440620503100142c1c80030b0b4010f100f40c548000715408000000c400540b5150380c0e04011005074100c00c005507900128079050101c000310f00740c040c0084285096060051900b00d400090700720380c4250210f1300c0580c5564070000d42681d120404409000000c208106c5810074580c0200250408102001c41c0c201035011600303d0325010003a24403400c4003d0000d03507508038a075640704a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 306729676 1250 306728426 306728441
    0x21e07090b220c0c081b011104050307180209190806090102040b041701140c1818040b09010e0a030c02091503030f070515011205060c070201021b180106091d0118 71
    0x8204c000c1606a0002d16400010901c0d2060f0b10181c0740c80c0024040d84500715505604030058460782008204103584000c100c6000b1079004c42c02a402110f2880c0416019100d0b50881603400300315858284446400f08440b1010b44404800b02c490783c1d0381e910f0044e0700302d214902405001840c14441088442c0c1c80805c50580810b240002081ca0000e034580254540000e8401030303030140000c41d103120030b038411000310041044211105011b80c03181c407110007200c00c0301400141003c1c040800080714024250040c0c40802d070a101216071040160500405502c00c00ba401c0344900400004142100c4d019401c402c1c014800038041c5240617001d0a035145540c0c000002140c03140a07038001c0c502000056540c1d00d0080403010940980b541c11464214200580106880080c541c240036240244c6d0380001c1c407640e5100d410403002140300d60700000074000e12545000503040c11903440080303002ca5001c2c03018011500c6420205205150900c104084004240200c1c00d041c80720008041c01a2400c1d0000f90 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 306730926 1250 306729676 306729701
    0x20f01120f0e0c1c0b071e050405100c0302060105090a09140d020d08090c040f061203030c1206030b0a02071718030601140609040c021e07090b22 64
    0x520241448440c0c400d54940035440c80c1c20a99510007140c0924003408010300760b89085841c500c2c007807560102e07040945065500500000c81e0103000030812406920548006881d07641d264483c4846907200a0041d8000d003d141d004080c41103441c03031a980504440c0040a904d174001d0111a801c010170311009490003001c60042544441584c40400d40e0004031344051180b0901400303c0304841000646003041140060042180340c070100200d50360301060341c100952080700e010a12004801034200070b81026000954125004400d041c105501a03002c00350388086602d80702503086003c0080c0e0308446051201410f1803000c0c5001031410601540104540c6100d0000141000d0030803032000007640280c1a0043c00324a060400b800c0c0707203420842c0c03600401c10b081900c40c5003803050300030440501542d00f4040c00b0716198894102c13203a009110200106000c1d00181c113801d034100030a550f84134224405d07051090302e030154001403801c002101d0300d841b04808080d43e54a404400041000305140c01114 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 306732176 1250 306730926 306730937
    0x402160b0a0b060c3a0c030e040e010b0a08011a090903220305071e330e04051b090112060b0403201905010e1311040f06080c07020f01 59
    0x480b0183d5481004d80a4072002c44001c0c010841e0046408441500070595500710303030140048032013144118040d80107056050310303013500032111038601a0380858500499580c481d00300542c140b0034003015803107044402c0d01200c49144160b82c540d8003608840388140705101d0400f011089040d50f04201c0d040d42e42203000101207902c0c04520304143e614234024020120212110715004005002c820131140015069007418960f26a1500c2241d04018410b80b103120194266000600c1400021544201c944007094103c40c6040b103003182c4c010413004c20884c41c903102d10f20788004034444106000654107580e81c170000c02841c01c000301c0d00546a40c041180e41d103803000d0300d401020988142410143c0021803142c80741c889003600d203070b24074440f080038007101038018840c6446048132600e2015610040760070030308010301080d60b2039002c02c03182030560800500701410039020904c001400030007841114690000d0b42625501c0c0c001c1101d640c1002e88403210300c00c10a1114001514041019401850050419 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 306733426 1250 306732176 306732191
    0x1b1c0206041205150a14190e0706080a0e01020304020913050319080403091706010b0c070e010314010e030301292203120c02060f0c010b060d09110402160b0a 69
    0x881c0c40740d040c0702c404031169000b40349030700300d160303002c1c0b6040c0d400403c1d405051050402464503072074618001400451010240b0354025551086548041c110606407401d5440e015214203000d001503c05840058800346091148414007906100742d900681c0e00500b09022034580400b441802468403400b640d0900041011080d000d9005640b881d030038003140ca40c0001c0b0718003400c01402110700d552190481c10015001d40b09541404a42c8a0560f0700115009860388441c94021b45041000c1d00070311400300744240003009011101880103c5418810028403110000100840d1680001c0c820a000b48610030340200c61070303403106611450001e40302c1b449410182d00c40507200440b500f1122216910b4a08442801808010104807001c5005410f00301c1010100d540070950910400e1464410000082074100e2804420340100b00252001414292990501c1551f60003c001c1c00ca01194640d11040100c0c01ea410b140c029250b0841c41400d01140c5041c2e59221b04044150040c001c140507540c070170f107 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 306734676 1250 306733426 306733439
    0x4050f180f0105010e09040330060305160603021317120301060512070905010225030b071101050609070c0219050613030c08120a0c1406070806031b1c020604 69
    0xa4801d1282184114107549403400140906801000e82406603007800c04010100c3d1700841e0a10011050444080704540310b01c0c82d5403108698420f185041c00c0c20401c001003844400500b40101140d410070027200696950401d4081f40b140c03412003122421808000c010342040070380d03280407000000c03007560090440c01d90307264450b52090f000503010607030106240e18160702518101d9400a118104400103d00340320020b50385854014010181d4041c190520a001d80b99800030b5000316441000c1d240c2505001c8409002004203558140f034030740c84d000000c0c2c11484c115002c41d0040300c00ba151410002e07a19028400f000615008012440c41100b40018040c0c80d032000500e091071800f14a0b16400e8118500001c3c0c124041e4007141403a0300441c0d40707604c0314440c0f02c1156545201400d004007960141d00d01400700d101000d00d00392003801404104210030703400c03420a0b8881d4800b01c040e0b9103001c58001400107a4600c0b022416001b00c405112a0615a441c440410031140000c10032401c0954406 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 306735926 1250 306734676 306734719
    0xc01020c010f02101e0f0e1209030f1b1903020d0b070e0d03030e12040b0d020a0903080703080a05012903073c090e04030819050a060303020610030804050f 68
    0x3c41d40b10b1a088005e00003d000e00da030b100d0880c62030100002403080418140382e0b2035803411002110044034000181c5400c4664040041c0007109124006540042d0100355407140f08190860340c2d40c1c041d214002d03400490640344c0340001c05603030303009040346040b9000e45c40c0c3c2005010001c001e1b500b4059840601403295541c1c0d449880210b01c0380d500402c28180d0882c3d003a007040481e904840ca4074105010a0001800e520151030044052100050329140019030455800d5039503400a070001200140800a041d40b00130030a100d080c0c00142404266650200300c01100120394102104001d0042494901c0200400a5411a00514101c04100100381058085030040c0f0703e00c0b4540050012302e8184004400007001c0148031a042205e0302500d00038000d002400b00410060401080c2800201645038001d40b142d124032000104010a00d0021708c0c1c000100301d18001540940719200003d1002440c4002c0001945d40c819135403130510f4a0401840014040400c00f25072104040c400340204c84600c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 306737176 1250 306735926 306735941
    0x70c021206041205041404230f041205030f06040e0c03030a050403110603010609030f051009060507030b030102091c0c03080a0207181104060503040219081e0c01020c010f0210 77
    0x40203800e00d42450f10706405100150030a082c2403040c244010042c00c402c2440d076900d00c10040c2c40205510152803052076003a9142c0c0c0b05802a004030b1828040b0304112040c1a81c40b032031207045c07000401c000d80e01d0195064003045a00000e02e1030300c4000503502d03041c01d4002c0e1203c0c901b044101e40e200c041900000c0e0440d00020fa440b00080d10215040050201c003542d64224001c0a40344103245505000c00140946901e01000d00a1103400100740c080000c01c20001d401c940f04043c04210f000c0242c40d000001d00703070036030740d25000a0170107180040d00e14041c821650703072900080074015004052038000c0e4070324802d030b4003d4403035980510001000c41c4442c00182141d10159001d010018244410142d58101545040c40450f1074450100a00000d4408413400c2e10702c1e40c10040d80b266901c0c070015424901d904200b1050640360080000c01000000302002c030321109c0b1042005401e12100000e58602d20740c8036090042c1d0008200e20995401f170350401d00f1002032841038584c0303460398100c043c0603111b86 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 306738426 1250 306737176 306737209
    0x10b0406090b1903020901050907170114010f0f1d060d0908040503160b071113060f08011404050a0803220302060402010801120c0519090915060b040b040608070c02 72
    0x90301c40b042120303d08a100a0880400221070480311030035500850710126050003584e0082c00d000300850b158034090420703103100407103454440d5455a155500000401e82880300300b030129549004000081e030003901e4510b5842455504c420000f800c80d902480c01031101b5000e503410020400c905c01d081510ba001c3d219000380614809a542d6181c0024940f5141c01e105c0d0001810040f960305104d110200c0013103d01403034101e10440d100110b0740000884103900b4104100032245040c5000034403040f000715660031542d840c002000100404c05001007507c0040328001d10a4006440400000310319001440d00824a0100c4100343c2420004400c65421084000e0300981d109104020840d03034000c00b101d000d040d003030304100036682d029626005000796a001e1648503500d8100da070030b024040202c281005221862042c05004a941095164012065040b01d580340c10580c0205000464108031400c5500c00d60015107054500305045400310805801e42080003410340c0c0c480e001d6507800c100d14080500 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 306739676 1250 306738426 306738431
    0x303030f0f060603150118051801080d0c1137140d120c03110a08090406141507060609020d140f090c0909070f060504030314070f14010b040609 63
    0x180300c40e81c80156103004004074801c0390108204489007500f0303040503840007001c2c2414400c004070030740c1d41142014140c00c0650898880030301e80300111042c4045904031215142615060080880d04640401c1011405011250111078189076405c0001d0300151090143c0b1840380742e650a812403030780600f40c0140c459002d00c2d8000003844500030501081045003030842d2400d00102840d07139290424800a2120001e0141a44810301030500502c845011203410000740c803032590f010320309500c06070030500e043c40c010391a043d008030301c00c030b03803000341e00b01c80341008005080d960b001e40d030403110903449200c1c1259201d0320b2389000035155505001030004036105000120349845180ca40d00c405410003461103007034904100500606c3d110104419100580c00e0303d290a580e640c40c61468541400c9600182001c00c503800c1c0024001c2d480000b4000381ca00c80c0c3e40d100e91590300404507840d0350181840207000140c240e004400000d40003140c403024016900c00109100a0340380004044503040d41c402034400340c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 306740926 1250 306739676 306739681
    0xc01020c0d0e010f090902071518060b030304031a1f090b0f0a050604050103020a020f030a030903080f04080406030c110111040f050a1a030408070b040c0303140316050f07020303030f 80
    0x541000b10070314590000c4c689251074400742c181c000c10300c00d540d00c90400041e0380000c10009101200c06035218031500d0030014400020b180044410307062814038144d40e9030b8581800c2c1001490080110750840307400449804141040d8040c0103c22180130b090220f00c1e4013541c01c1d580480e40d1410130b840042c1f03ea0103000a0400c01102480311520340225285e01c0b404030500c1c180b006a4840d8260303010740f074081c030300140c5500e00c0c21010f900d0440020042c90280c4004942000301c0341c2e240c0c200c0003241c0d01c280d45241803034aa100019510f80c20a9900401d514010710051110070303ca5400b00359071558928004007191030040750682182c828141340ca540001c0010140306000c0800b003a24000c0c60142c43e244034551400003040a914076480800040040c000003050911900f01b05807495281c2180310480d45042601d41700070200000d200450216502000c4201e0480411040e030317110306e514520902102e18514402c81d16035200e00c141c00845d50081c03100d500561410405584103141c441203640803070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 306742176 1250 306740926 306740953
    0xb0c0d050601020f0703141f0203090f0a030804030e01051c0b0306011406030610170c04080d03050103110114130e1b07021c1a040609021e01050708030c0c01020c 71
    0x10381004000c07505643c011030f03050124a10016803002101d401c18501018254603d090ba818241c81c01d4001d0341c00c515550600d030b40a0820b81c0210300529400088405c0c603000d40c001c003601d443c50540c024002c903040314002800f09000b801c54408001c014035215280003504400c102400e054500290981c0d0380d00d008451807404c040080070b02500744920340c0c00b203c9a5400024055110040415000f155062000b4200d18020b8485601103608121014410302c1c2690303201110b074210788030b95040d40c89401c04190741c03107002c1d1095905880c0c0008540ca155141c4d10015a02254039164500540c2400c101c0c604c0140c3c540702113640508800151641d60381060310068945008058001040e40401c0044400580d20340403140b240c21074494880c103007015142000c010105092030b02d00d040880e5901004100700345a0b01c005111803007100c0d00540c0d1824140200e42c43c80302511114041441004000c01041d099005954818000c280c81450000c07501413540c20782e00721050039042a0300038112070200 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 306743426 1250 306742176 306742181
    0x1090327090b030102040b04120b280c0c020405011401020f01060b0a11100c1205130b060d020607050109080306120303190f0e01060308030108010605030f150907030b0c0d 75
    0x180d40200c00a6125811103141100009842564001c1e0750351100300d011a10301790195002411680401500d5a50390000c00c40b0b00720340c2540495000c891100060411413150b032001070400b5200d10f1030000e40304074034000d1004114a2621500740000001c10000599442c0111806805123501d5408c0039002c000000e4a84808a20f0382da2042e4140030b400c0c00400320140694074900f40b24500090f40684c0c28598030704281d0101480501a4180203036641c095812401e403c03e01c0144440c1000f4540d50704640d004c10641c1003900a00508005010172101e01d00506598403840c0010301040c580101c541c1c2e42400c40d13049030022101c04a020080103800d01e40701640010b00d1030340e00095890351508612802520f0f44030340d0300c0e0500c165030300e08034842103c01e94005504040641c00070000e044c1c990400300216002489100c1c02903080000128160a0104640c0c4c00c0e02000b0b0020708680042038524000d6060080031030181d4030401c5000400302e100c0700900c038011807001312550790f5002141040001e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 306744676 1250 306743426 306743447
    0x7140f09031f0b270a050402150c01060f09020a020c0103150e0f0f0601020714090a0905011401050a090c050d0e0102130e040303050604062105010f09031e0801180b030109080c010903 80
    0x40261820404180130311022004a901c4000c00c2400100c90380e651000604918050034400140e40000c036902000c1d80b0154810000e6440c910445a03100f9a40c00b40c0c54107178401c503100480140c005180311905075000b5001b645504a800311046804d5864a0102004800031a500d1140c1d02094003808003080800c514650001e40c08c1c0301620031181001c0007031500030099040c00c1d00400000c070001c2d403100215804078041e190320100901404101c0028248031100030b0050b24441c80381c0600c009402d5500740305d044c072a10840e07100c050400740440c007070380005c00d00303030140381c00c2035408010818035040043c90080142400032008005800d007400c0080480d00c0003458035008038540103050001328080c00320740c1c0c1060404c2070060b800315068500240540f0300b058502000c20b08080d4500c04240c1c1000142920307509480024107411201745085544560a100d44400288000000c0c0401482c41d0030200320000064000f0440311403540d56082590300100136500c01da552071a20508040c0e00c02100e60 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 306745926 1250 306744676 306744709
    0x1818020304110405010e0103140c0d050a03080a0e07061407060203190615080402040e01060e1008100614010c1407030305030906070e06090d05070b0f03070807140f09031f0b 76
    0x48136605069022201500c10f00025008006a00104207004130802c2114508080544555110100d510308503a0710000e6003411004145048005401b03a41036110321284403590701d0090461170b01d041000d9407981c2141d840d245079041b080001e0004140d07280021802070700c1d20b020b030820300c0c800d4610340000c0703600a401a82c1c0340c0c00150079040e12580c1c01000103410540441f800950142622030690041a40750300c6003100040a00802001d214003400a0048075200307030544480f8060f449045040f1360083c003c20700d044100c2602000305d544944402024035209400000c02e40306c110074010300d0300e6825401140061000410040940000c0c440581c0000c4076043c0a0101c0c500f500c000f4119004900c452030041291040100130b00004001103001001141c0d070b030550b2110000300128540d40104c800e1402700726941c1c04240c2a51142407014240784110702180e04082520756503d845a00507003040c1c0e458491081e0358080b803c102c030019031403c0010040010b2083c10391090102c2e4074003041811 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 306747176 1250 306745926 306745931
    0x10c0822140306011505160507060212120c07020a03151a12060a0e03070b01030821010b0904110f0c0706030b01020c0a090504020103111303020913030c0318180203041104 75
    0x1c00252000150355054500b08198541516000300c011170719801342d03160043c00d2488024210045c0400400c04c901968841da00355404254450b120f00124800c0c40b04808204030b05800007090b51031808081c007840b07440100601e2120381e983e01c40205071036444000c0007502e0b40d140c02e111400804450700490301c01080c1e88010840f002d6558036074840d40300030401d40c42151588000c02c1e01003003c0c422070b165503500c00342c00e5545585a04001c3c0198000c1406080780300c040b95400408582c00035100c6049503c808681c0d45040317071410034000079102d0046198103000081c803204003000c900302c02401c04040d1010082070760f6440c05400809550360f092101d03056400c0308070140710700d4648041540654000800c0401d064a4502c0103d0040c500403e1080e01240041003420003840a10400340480340201c1d0082560303200c80c400102078408196004000c20015844400001e001d81066130b210340f001000804025a01d0004001c000642d00b42403075071550020800007008560003c0e001c800d0802e9408 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 306748426 1250 306747176 306747209
    0x602280305030f04060b030a08091c080d18021005030702010c1d01050c0705090106090306060501020303010e060d05011d011409010509030406110a0816050607081014010c0822 77
    0x90807038800a090034401104143c002014840d442e0450b00c00050040c0803036000e80101d04040382e20740c02c616007542c0b007040b298004002d80b4a8040e03040c0e803881d800004482c40e10225190b074400130610b884a126a9a8444a24001513a14001c510076450f07140e4607070039a00d02c3e1040e0028215840207001c20140042d41c40c5001c1046075824100c00d55440a08001d580c40711464815072400105500c00e07039100000d0b400105550740d0203a40035080303071b02c0b40106000d06900c601c01a40c032800240a0544660900701c0014080c2c603200f1030035100140504000100064219206a5076041c582c080b000c04c0d0f07442d00860900301c04203d06490340f2103a001d000704003600b414405d41c0e85031321680c41040d08020000800c01d460440030700400c01025800181c45070b41d600710405d42c4031358100c0c0c9807007aa42c0340078a000180b007c80c06400c4072489140b020180010070340c00c010f48002500d0742d440845042203c8100a200000c595900900380d070261040c008032401c24041b00903103480e02e40e400520842026246 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 306749676 1250 306748426 306748433
    0xc07110a0b07030e09252106050a0803040303230d1a0f0a03050c0621190b010c020d02090c0c06040c05030c010c05060c0313050a11030105010605090310050a090c060228 74
    0x50b0341204c81d000e011b07201000360006408030348581312820b00500038005001c0c0484585190392142c0c04540c1e042e144400e400e651000069102d00407448044c0104003241403a0306c440c80111040c003144581c0a031014144440c00542c4012141000c0551181d403c20607150b0b82e6601d082c20018101c20340c01c6a08149850a50f95255110540003641ca4011040450100010b2088011010301075615141d0a1480c0c60221b0081c40c402c002d0040c0801c8003441e181800d2001d503c03d80740644099000b8091440c481542e500b4004002e13402410b0110f460018082661107407014415079005a010b07201d544034241c14130003090308080007020717280e040c4011070030018006100032608940c40420400540d8482d070718030245812407009240010a60b003c0c40c00503004000c81a55140302007841039008006907070700e1354004e0780e6502c1803815495240c0c0c0141c032804c6010149070042e95021000344008100c144803030f92121600c0c01c0c0c0750400405030300840b04882100300c01c580c14911b46400c6040c2100700351400c1d00c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 306750926 1250 306749676 306749701
    0xb0406090306050a1b020c190b0306010f05040906180507030203011d0601090b0403030201050f06190902030613090c1502010c4b0201051503060c07110a0b07030e09 72
    0x1c40104410b03183d0f00081c004000c994080c0e810758004c41c61800d07071001070190094031084013aa0842c415a28103008080005030448610252441c00e03050358956103540006451b4441018034200800030308000100c0c84411500500740103003820340d101010390010500070010b03038038000c240c54100b51042c001084680e010701c06020309444001090005070300c1741e000403100310056030010345c060300b03001400004065055118911070b130340c0b400001f0f400b1b4903802c0c07c0100c80200201e18030182104c0d04000d0040c1c265960065400c008001c0242da00300b04801a02002d65003074010948501e00c164004000307070500b20001d5121003e65100804c0305008100c005031150100c03007102440003100c01160443c0c6076815041c00d90003181a52003c00f81160303028040da0300b41e014030361030005508100101b40fa040700200044100301c030050250071540e90707880d03961b405500700c4201610800300c02c54582d4a1a201e2400307450150058041095607507100303060103840c851802040c0303030003852044200484c02d070404 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 306752176 1250 306750926 306750929
    0x170d09061a0d03050c070b0a08071e27090c030b090a020a090b1605061503070e0c0a050c03251716020402090607052505150f0702040f0f060f0b040609 66
    0x103003000c42d21034030580b85c494589150340d0402950b241001802e044890b804c080755500c511080d039240c609400c803050070b2070750360030600b001c26004c504542010010343e940306900b00780281000c1050303c1c20310b80d175400301c00603900c2c500034100c00710395100b0a00c4030074140001b103543d000803070810545c41c100c0c8486004160300068800c0c0c528203200410500b003100c000e444048451070b0020201e4445040c24030544403165003c1e60340074440c2c032500c28005503c90000070b03030501c44c20100d83c40b18203003041803400359901d50290070040e000d8042000104001d40b001c5040400310f65107200410010501450000a0381800006481070368000f8466212600a038420020009505130740160701c4140e501d001c070340340b4011110001c103a401160140214000700c04000c2c4102007201c0304d06c1303600030b50b210140b1844005040820004050401604110140b604000d0070605e01c0940002001c0c520311050000319241c10480014003500e8400c100404a131008060700a0042c0b031007072900c3c051501c03001a03d5078616 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 306753426 1250 306752176 306752183
    0x61103190c0201050702091503010e010b060909040f05250905150103090302071805060306062704171803060606040b040317070b07080f0a0621170d09061a0d 69
    0x4030789560440e4454020b88460550240c813402e110700b010712144040b451a1900035000e98a0300003034102407441402182c02d00c40d07003c2d0009280c50903003014403840007001041903803458140420240018410464250001c44075605000445051068043c08064a030300c4401c11030306100510451040c0501c2e078410250b02401c00040108244c0741c11b03414040b09600841468a44d120100740740480c03600a2441031500310295080b960320324041002c0f044850a07c0e05508140340741c00002d05030705042050708640654203c05201d003407200668241e90180100040b458260040240542800c014103600150119111030405007072a0218100d809548005809000c07a480080780c5454900c084401c02c60f00300c01c810480346402030004e850260207407003000c11050300d00d00060070300c0c2440c4200c405480710703000030041c8000304014601d074154611400369401904c038504503410461400081c0b594040208020881c0d114a0414504451411007a905060f00c00c0d1006400e9540d91030381804a540e2 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 306754676 1250 306753426 306753437
    0xe0103090c0e0907030507120b180708030d0b010e0d1713211b050a06050307170a05060102120316050708040e0f0a05092b03020904110406110319 64
    0x5080c00d000341455030551001c2c040720b0646062004818000c078074102070324000d504407403800d640d908001404890500c00542600320b2200415842c2241e01500514003021800f201d0034552200c8009055501050880c5201c5507074503220445942c024400005040b0200d49501001c040740e00d400701d203c100c49840b03000d111000a0780454007020074603414040c00300b2042d11145000d10002c14070082111400070342da20100c0d00c5405120316181100b0505595019041c000c0306441c1c140c0c15103454101410030410b020300926400d040d154600742d40d40c0324540b42e0a0124150030728a00180c06c00c0100384402903803c0c009c0040040385c2d0503010f440f89444d50a46040ca81d644401d01b094480e501807900007980308050034003030009206090100c0307802a03498030820019a141c20185643e203d80864501c1364000703890704108100c1c103060010386482000c5003030143c40c2c182c200e00040e00b140c02c550610750701104082803c0c00440d0340615002d104001c44c030006c524144900f415030510000c040b884404220 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 306755926 1250 306754676 306754691
    0x20d030f060f09020d14150609040b09040501060509010605090d0b100503060109050f0c180f040b0315090c01020d0927060b2221050705030a05060a050a06060e0103 72
    0x2403107600c40002030100c00d10902076a80c44403140780180d8002c500d9211800c4c10305c00460b101009082c3c03c607024004281c030304004420b00030144269504051040d90740550345031241200c50b2030792440c3e944540e00c41c1d400043c4260a00042180040307040c1c00403410803009100d1403541d0f0712402e03888640d00340c101d5500001642c1c2d01003450b1404815420494042c0511800000d80150340d41106000d00900600f9003295aa10a0020700c00d00603070908050707580c001659640f80e4141168110f015110281000c1481485400440d1038241c07960791840140d0a10010002050001d110502c120202440501030100c814100100400c40a01a55148035032003040f500c0c03541c80e003280314042209184014841c141d07840180001641000040b90303d007035420305000140e070040074408000c2c0e420a641da40e4400250050102698151060459062240c1c00d0003180907038003000300c3d015851040c4000c04113803401e41540000c0d10350180c00210401e0525500784074440d040482e00e00e1842c1c00780382c0000c00300c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 306757176 1250 306755926 306755951
    0x4060e09150319030206090604030c030e01120e031c09020f1315090e060a09050615180103080913090206030604050a240f060e06071b090507030b0a06020d020d03 71
    0x1015460076142d85481901d61040185104803c40e9501c1802a02a80c00329603490312416260a41110004d00003080a07013031000083c000c480c0c01e16034003c1850f01e0091842c0780c2d0503010032580c118607841420750021811185000003049040c2034017100344030034444140198080b4403841c00806119104510798121481420001c0d88602c915103485c240b0311030f08655481c1c020700180803602c0010079901400d00020308004923409185140c59000d00200441c0d0748031000f41060806a03504140d002981c91f00502d90303c2807000d40b041c081d40c082c2e11015a12080242005141c0c40c40c603d00740c4d6040c4c1400c01e1100541d4680c0306032540158140c501050594035015940000c0c0b0000394903011007410320700d41880310344e61008440300b1307203803406c0ca120000c40d01e030002903c0060103000c2d0703d0f910800c10081d03440080e540c1034929045c424075182001d200d68850781d00034103440703040790b0100019030303126900002480d040c080a00200b159001816040c00920b000079100c4084040c0c42c400d2589500d6422002c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 306758426 1250 306757176 306757201
    0x904051f0e0711010e0706030b03120d1a0a0b0a1407050307030206010315020403020321190f020705120a061515020a02210706030905071a090907030204060e09 70
    0x80d24940a03221441525000103007999041a5140d800140083d0715075441e44405100d00c003105c6410400610201d0300c2e1440880c0980b100340941501405858886061045094080d041e909120240411037941c103040c0303001030403090002c80d4400d4150780020070501c580720003242c41468042c6056110305040c00b0610340d45114584000741644400940c0d03509240d40841c40605883c03007081d002c2c00e0100c06548400c1a4050743c00007039416004602100001ca080a14100e1070312844940e0b1400c0c03501e060720200b0400250084000800c0d0340c5410061001c0e41401a2000380c0380c05c40e151f00c21164148000d43d95250050f0b4010645543d95004405071030091502000400c0c403042001c2c9146210540251036848010049010303078450b80c0d171400c41d680d071900041c0240310200014642e07035207083d5049010f0800d010041e505805401008260041c0122120404811614641d40c0e1070541c4401e00c0071035a0f0003401c0d0010144140001d10100e64441601c846000048400c0c034005d440703214040d00c1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 306759676 1250 306758426 306758461
    0x309060912250f1b05010806130f092f04020a0806040209010909020a05120f010501300c0c1b0f0504090c08010507080103020312030f0c07051e0601090b1203090405 72
    0x30f1182110405081040303070f005032240410269009074421741d4950054592000035200300307a000010f007181d42074001c500d1b40500c00050701c0900100701c07207e450b111450401c84507480d0401440148201c00700d8002070344080210a0000d4a0461600c03004031401000b1030405451180704540004400d00644c0c8154224809005c103030f0411555200400d401800650044a400300c170400d480740014640c0481402d694125003040c4c5441f40e01041d068803a4031480fa000449624190051407000c0b034402c000c2c031449155241c1c544500310701184e14140040750f010398101804410b0500c0c0c03801d002220307440081400310340080d50086400c10841c035001a92890f1a04001129880e05040000c1103911844441c1203038000e4003a41e0065620030001c050034402100d850b0700450300740001c0350107944040c008201c080d003d002650030001d030380101c564185010012501580e072002c001800000c1061241d89030303407107048580030700b5007489d10b100d562a40074681146205a55640000340400c039a5030b078022 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 306760926 1250 306759676 306759683
    0x7210605041401051f05061305010302130801050403020114090d17060d05030d020a0908031801050f0f0c01050a0e07120803040c0807090c030b04060608040b090c0d08030906091225 79
    0xc4c0d450320030743c0c42c211115110700718450040701c00310001da1810110101c5104211000d410460030341000c005502a61028229110b179001006000076400700a1107818005c62280d07001041034080f01d0360662841c04045c0880d0500c2e00010322082440d0f4010001910404180000c5a1160348000000d07010400824010308240070000388081100842d90082880c514251582c900c0151608452552401740001c0d00401e105d88519a54032580507102910044800403042d500c7d00152820f0240c0c9604400c0400301c960703440ea0180016009a4001c015090310154024080c0034035000042050034516030001c0c2400d00000042410f10144441ca5000341000304222402580d0f240300d0b10000b4034402d0722140000345030807248607191802d4010181120000d54075541e46480c0c603207445501110140c24041103100344c84100c002d61300d034501c217401c0880c000e0103c80d88910380500c1c1c0906090700101000171070340040c060b8054189600007644c150404181060000c403040c01c5201c10340610a0b60084e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 306762176 1250 306760926 306760931
    0x41104020406081902040602060f090304121112030a0c0212010b030609030316021501051c1203090b10120b10030510020d0c090b0414030115030f0507210605041401 72
    0xc0b5045401c018000c1c090300b0708080506100c4088601841280254060080160007090201301700d002090010354002d04450300741d03071826950b094081e102c580480320441d65065104401c0c0070038a000d40341d079000c18049401451808444010080c8802d00b440c10092003180c04424440c5d030400c00758403020341824050f08945090510b5010690380350811580804524042c0c5030580e0034500c0499201021004003008802507400c000c10880340e01c848414108456004c4000300c0007140401000c0c1341d00e60160b0702c000800f40c15504040c0c52086006102113070850f44040108440110190801c45082d0042c43d8080c4607220001814a030701e01c5580080d00d58411035410300b00c00300103580100000111100104902c4007016420b4407040c80b680702d014a10380045c8010080c00c5103150124078003c070000c000084000201503c108c4031091608251035610740c1102d040104681040120b000d004030320074030071001c03c000b0604a214860840c00601e4562180086010400404003c042501010009 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 306763426 1250 306762176 306762179
    0x50103050a051b0f010509031c030219080f01140307030c03080d0c0e150d0e01090515132109030501020a0c0309060906050415050702060d02040501120b0907080411040204 75
    0x60341ca0559541c240c8090041248180d6800c10190324020b00b01d8004e4250f0207225905070064580ba08502c102d01c0d01405100304d07c02c0e6020b462804240300c4a034607140180c46034101238030303030817042d141500310404e11000400303000303c044480c2c40c0141180c082070303c0c500d4601e0100000c40d0030806143c0c03000300048000c1c1d07008401c0010340d401400c010b540380c50040100e41e601c2c0c030048071443c0ea45e442e07083d0032618402400b0890140b240050a00e1001000d002c00d02c82601d0140a003101c02c105010364054001c4c000e50303000c000c2800d0380baa0300b024001c4914140407809807aa150001c0303118007040e4071401c08000c0e84407100e024503000c2c0001d5811000840d2288280708002d404844005011000104d2031580403070200e0080701c0450580750323560344890a081c2410070344040b21610480714020301c4014002c0d400184d8840005180380100c0702e501503141c40c60200090240c10210050b040d209003058100c01082e00c40c480425071012041c5030070749280d01c03203080c03103010030f11141e04045e005400041c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 306764676 1250 306763426 306763433
    0xb0f04080304290f0a0e190b04150e030d030c140304031824080a0b03060709031401061d07121d122503090806040b01080c0d020f040f0b04050103 64
    0x80d6141c0d440d10803240e141c15030f082d14201c541c192080a862008000d02031125541d000d2045048418002000d4034181c0c2c441d004001014440d01c65601c1030305514400601488641090403d032a070002c09410010240c41c85480041c0c0c40341c207115496403c144c1e4480100fa02c4034030034210000b0213044102d119503a42001d00f0f00810f65680408206000c40ca02800003a501c02c641446005035403680001143c40d580703802c0c00319004100030300a00740b4151155007608441d6010701c003680c05030003981c9580d00e004e071a5140000d10000c01048052503030745001010003104800d144000b0740107003000442e403000d0f5240542552071444d21040b10910fa8174110142c1080c1d0199848844035010f51400ca5040c01c01190118820303104840780100c2801c0d40d14000b05e800c5000c0f4096195451180c00d01507801900d8103195461300d03000f11801c0c0c0345aa04900100400c600510041c4c02020043d1041c0c0034040854021401f02e81040812600580e6100c1c0d268501c802c45a0204010300d500510520055070b407401d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 306765926 1250 306764676 306764699
    0xc0706020a0f171b0706020c120901080f1302011202121f0b0721090902121506070b15030718020304050c0901030b060f04020c0d0903110103150b0f04080304 69
    0x1c1003501d030b0b43c00381c00000c11036100e210b001d0900700c81c0e000c4003400007030250b42d400c43c240071101c00e5001c0c0203861045009000f01c81803070760408400ca40340c10300a00010075070f42c0c024154005a61840f0140441c41803100c0300c60402a4080c20008010041900004007d110f09054540b48410b05000e110008582c3c19031611510781140d10f01c1d40312520b52000486610811900603ca180e90f1120824520342e141c150021180781403c00c181c47c540d550030361a02387d03404081c44a4501202034100510b0342c80c0301c00500c440c040f007030303403101c1c240742c15a9151321295402900c01c00303001010504001e1155402c0100d41d0140024040d1078000484e6041c0c8103001e1f41040e80d0444080c000d14590407a50300740100502d0490b50840280411525001c00b802121040034400c50307002a002c1001d022400b0081004000c0c074000c950344e45400c5071440c00e2402030440c42060a50401d0b00301030510990010366140a01501e401341c207842d40e0354550001d103c01c0c078413855000000380d020100c0c00041800003031 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 306767176 1250 306765926 306765947
    0x7020402070828030c09180e03040f09200901020a0b0a060b220e060a03060f140f06030d05180415030516060201060602011503030806010908100c02010b09040203060f0c0706020a 78
    0x1910144422a00405e042e580c104a40c040c0c030003445041c2014088400054008078010700803070007564942a141e05100c100746400303030043c040c43e94035903402e4092020b035212940e524003115003100741011007000000751500315014029001500c54408210320090b80d601080040900f040402e0b5242000c8900c00d0990300d082d0030740342c40007042100001c2e4001094800601c90315005018140d11811581c07044010042640c1c0c48501c0355481c2981e072040c5840042042c021007000010410b03d2414000705407502107903076107607410420184501c0f0000c0c8142081c00c200003908580100d400501c443d500c54182006038806071080c810040c002d04500740c059a41420741d00c440d4001e02c10b090702c2d07042c141c4c00d9030135680c035441324403000110030800719116000907600142c0515241090399514060f1074600040340540c0302140741c0c4e4005040044d40c09124070805c0c00010344102c401c91410b178002035111000188481c4c01c0d140d8020004000000341011113462950200c01107440b01a1140c2c010706d00d4200 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 306768426 1250 306767176 306767257
    0xa0504230c09010806060108130501150609171518010b1c02120d02100506011206030606091409150705070606080114061926010615030b1203070204020708 68
    0x920001c44d209401040c02c2c0e00c90841030b15012103e860304401d8202c0ea4103c0e81e4242c915540c5c502ca6042170f240c40750440e9006251540d644001c1034100221140b01046220386102180c1c060701c81109480703402410350384d10041820f9000d15044040045a0150035066007459116081c4000000c0700340491041480443c02507a94500c0e6503d2941802c1d59824042c04010141c0e00c00011004030b0a016040356500100c1854441100100040410207650882e0801c461040e200e4906104001c16442128406640b49903901e00504000f84200d44441c003414204280302c4074900000d4200d40904d00b00d0782d0342c9500c0300301001415540c030141402040050740ca2802c65100d94041105803410701901603501710b90000c501ca480d890301041c215108044003240c0b030415041759200c0801442845480000c04002000b00640c2d0300e4040020119460751001500c181103103180324031100300000903555221b42c1a50300507603500f9581400c05482c001d0000019004140c00c103460402d0114902e0902402d08 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 306769676 1250 306768426 306768439
    0x30a050c0c06041b0e040b01151409100201021b060103060f0c080609061309060b0a1203050f22080a120807020a0f170a050a0216030b0a0504230c 64
    0x1980039051031144500700710710000354000e401203004220700401c2c2065076a5081c0306480c000d5900e02440c0c140001c11a415244c40c8081c1c00100841194540f0441c110015483c0c41556034944004603141c1d03024001c3d100740140c0b40380311080da00358003d45c100c1300d41e1605500e00940c014004150f01c1e507201000d020459000342000703500001d241d143d0045400c51051500d0300c0d1a43d41d1108140801510003c11565200000c06a0fa9800d906107124030701405004501c046000103841c0c051106040c1c096001c0c40c0300c140a0001c003004241d002e81a03c00e000e6610b00c80c5a580e071215516244007003010100f1b4102003032085030002d03408000140440c1c420748540d00554140441000c180ca03225012503010700941c00840c0b2440016031440b12100000d40325884072001d210503810100169080b88540358003040c0c0000f07100104a030104059003403030300200c40880907941160f40d98403880101403c42961a03480d1808541007148000d491005400f550400f12500340340400300b0f541d90030b04080030074010b40 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 306770926 1250 306769676 306769681
    0x3150b0301060b030406020304020d0210090305150702070e0c27030d0306080304050f0409081206130c1403060f1503010906140303121306060303120608030a0c02010e010e1302030a05 80
    0xd040c0a55000c031410b8400321401c5980301d45070070003c0d600082c02240d00c50414444140143d80e03d29620324011442c0c2e84070070403a821403404514056a4000c940580c98805041002c9140c0c001010416111014818032607171b120013020a00c240901d03100020a0503913200404d2404070501c2100c5004174044048450400596100784d0444200d0300546107a6081040280040c0c00c08070007440c0131101c041c00008410702a9120051140c2106111a0032030114009200061509504101c26a0842101003154034172140010749191040c13074540d28100c1021001606641e100c0c022304510040142ca00c3d803a524102c90001c00d40c0d4030074080c10a0039490b020b404107003220050b02d01400301001400031403410304103c0612860210007481640c80010002c16003002030345a010300e030f000b10f20071f88a0050200103d255802659000c6c1c124100030341c4103000310801c0d140e2001e0f04400103502070808030701c51700d8540c0048540840e0300380500d800034500e465031415018103600035841030074452410049034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 306772176 1250 306770926 306770929
    0xc2114010e060d080a0504030803012402120703030c091502011b0f02061b0f0f1e0702100e150417010c0203120703020306031005040f1b05280b0403150b 67
    0x2441e068600a800500c0b1900000c00541050000e1400c0d032842c1c20a1410940d030317035030b80b401e03140d2003600705441038044454a2107074021442031504c01c13a44280041c0c402841350100100c00c2c0d004500d40a0b040585a14584120500a60800c0094240f50441d40f050200c2010041e0183c0b81a4811509404c40005002042132260175107103140a110f901405990319a2240605043d5101c84050381c05c0d0000c002a49150311004000d080c21b107445c40503144c503140328050004900c2c050782491040604200040300050355900072802d421019030400b4080c030203801010a0100d00c4410649107081800100420f502048203205080c3e90454402440014500c0504a859000b480c102c1c10071b00c2c2e00d00001c84c0c80c2501a0700615841000074040f40e51128844071400161001a1816901051042c08220901c40d00c01c0070726014451200b088030b031305860800841d0343c00d00300c1c03040c07502c00e900c40344503100450f40c10000c41c00003800784520b17880d141d68403802c2002a0b85428461144c1c094a8a81e035400315 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 306773426 1250 306772176 306772199
    0x40f020c1204050618040b0303270604030c09090303090203100b030f152202030712031211030c070804030c0807150201061809030309050d120e03120402040c211401 72
    0x5840f80900050308109299803003a070388640a03840385c2c0c0e1080d154440c00441d6101000070303064507511801010310b56809130900500c400d856000d840c0c0590810072081c808600ca200780030040f180c07000e40c00120100c07542030840c01001600c9000354980140d40d004929030880c1e820450501c01c0c00c5080e6101d0400360303220b041c2e681c4c640307620222044941c0070005042003a1341012020895414a41d100400000d0340000d0903c1c4e156003007810311640100580080c5540100501801c1a40b0b803400c000c40340034080c11002c00e00000344601540c02e0001125010800d00c4403e9800440d4002d28000300581c5840342c0c0c544504450154941d191920040d011540c2e01c140152812a0504100420a11400c064010140c1900349080d0117058540ca90000062001c1040703070005c81e05070740c1c1c09904d00b6800c000e030300984403080f406490b103620600c84041e107500c00400700b0b600a54102e0300018903000208040e02c0689002c00c2c01c0c0c2201c2c0c0040c140082001030b64001300a51400c4089864590380c85420304641c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 306774676 1250 306773426 306773429
    0x2040515030402090a0905030d06080706030c020307030215060f0d050303011a030f010e101d09070909080f090a03050712210e040c090807090b03010506090c030c030c0702040f020c1204 81
    0x14480381c180c000c101110046e40c044150280942e040c0c91078240c0b8000201d0079661150f12240595004510811146c1c0d811705c01d10303d81400c144081d51a1040580300207588a0303c1081c001c04c0c3e008038002007030940d40c3d201c0d049103800002400034880e404017070406a071284c000b446043d500840141280560400040072030384515680018500241d080060401100e80018903240c00201840004a0858030078030321040d00100381c2c081c005240c0f0b4070a44150400394142c2c00500031604210021000039007030f6007500d000d405008006038942448400150301d122851f4000360880c0a80b01c1d0101b902043c0c10200465540110040080c1386030340e488803e41d040300410180b001a0201038141818540781c0c002300100c0343d052904055950321016071504143d40d581c030005002d070350b600085840741400c0c083d0a6010346c0c200d5450700645048212000117110041c08000c1c2002c00100180d00c2e1400b140c150740d03550390041c10411000c4100e081f458000d6000c200c5001d1144900c0c0d011016030003e9000f11030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 306775926 1250 306774676 306774679
    0x816110307060e0a0b04060504141b12030912160e160807020a020a080d030e121903060807060305010905060a08100c03180503220f05131e02040515030402 68
    0x14504001070322668001c090703e600c0401c40d8054403e110b008a20046241409940500f0000a46040614080c400441110748114035608110300581e10398088c81e89400d07084505955880c42200101841030540c0305880d5281e0b03121031800b04040d00b004001404178881180c1301080d803862900c401408650305000c48400003110300c00070f030090b800c900c1404047d81103040ca00480d80751103030541c00623903140c0d52038010a8403980071618411640b5810302510082691400103860556180310074846a0700c0354800311400d041e030240c02c0078040ca100c6d41c000c01c010a03a80041d032b51803030b49400d03004000d01001c4c410803103440d080202150a43ca03242c0300100843e908480140100f1100081d0503002d07200c803844074024156101610461207101600f110311461090002c2c5554410010280860407000619001c814168404c14414910320045920030303960112580010740008003590320182c805545250000074480458804020303094010300290f60081700e249416502180d216516400100c1e80a07 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 306777176 1250 306775926 306775933
    0x2030a20071110052b14010e0c030601120c0302030411090721060503030f1b0a05031e2203020a05060702060904050912030f0105150c060a0f060510081611 68
    0x3250345141c460b043c0111010039043c140c0c2400c69030101c1d00350100018503078031078003007002d004080c1c40010f07807140706a102e0075550081119414411070080001c1c000701603a08030403002000c1585680220703c041408990384a040c0f148024842005010390802e6808494500314070321803561520380342c00040e2180440f075a441c04208503110300c00210200700100700d00e11541d50200825151802c0c4024480c2c1c5541c0c0c00d6070b640d1105111207600b22019080344034201e07500181d0107140002c81c0801201c0780c0803800c1103100c1e030310b480c0c02480c0142441514801c0843c500f41c1440c1445070407007000c210003120b00031605160030940c4d17201801654031900000a6202004120035100e034502540403e4002d86400f0031030f180c0040e0000e80290035413094030b2400d107049200c0010005444c015141036620840902200d05100e031008040780d030340d403014001d482d405482c0c0b1131b0301c0702007007031944054002d01000745040f07110950f0407000b4081c00c03070603241440090200c0c000c00310194000d9081e52600040c64004 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 306778426 1250 306777176 306777203
    0xd05210403031104030b011a0316050c1c0e090a0608070909150c0c0b090318010c0203011b050705010b040c090b0d091502032508151302030a2007 64
    0x1140000248100c040c0b41e070315490210494003501c0a4005148214490005541080d1109207290041d40c4e06d407118200c100100700201d0521010489110f07032500340070f611354852110060601620341032010724001800003070403141c0c3e884030402c01d46c03c03000d95070f400c10340d221203d002081e51138034040e2031111752280c05c04228584507580001d143c64094000d02601a0310070020301e00ba5151070a410000403010f480480c00d004035454020b401c102d4980086140a001050b00c0001d9030030100340d64141b14482514505548080d000b910120903826920203017110410300203025600000d2040e0751039884c0c0955950141400d2182c0c5c0e000409903240c0d411210326005840b040c1e6807040c9405005da03071f1036600801c0041c0c881c0400e103e090010b0314015071245004a031781000c011941440d454818a81c40d0142105600494205e030800407101c884c40e00039800402264020710002c0422038120300c00010058400c005070300c68000c200d00c00050744415051408042c1035801000d0000e030440307449484 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 306779676 1250 306778426 306778477
    0x10207061d1801060c15090c0e0603031204051c020c0604050603070203040e01030c060311090d0602090402040b03040639050310050d0c08070f08070b03061c03110d05 73
    0x7a00c40c0140402004071001c524240c40c0340000ea031081c1e00000200d0f1051a500c01008040c07109074200b50581c5c07608001c043d00d5900d64006604441c400c080ca28030245000c1040c80d1401d01c104c842025880140c9540750400b440e000780d5071420404500ca0004c3c3c010803c8540e244041865540361030001e00d264141030400003001030744d0340090f08550139440100400214900c2e03280080d0700a41c00b601c140d501a525008001d4213540420400c02c010301402c200032021940c502c1c100c0c0705902d411000068a82e540e01c03010400a204941000032450004010882002110740280b02c1c2d089801c02070603124800d02e5030007401c2c08400514018014010030109034000e110f2400f96a0004c005141d0b00001c90303a40011407012160508261036514403400188808041040140014403448c0c18001c2c000b4940410f280d201c030741c180100006190000301180c040d44c0d50280301424009800300d0412080c11601d0042c0180c0c01300b01c1c0034412805900d0f640d008040c00380054902060020f020440e56001000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 306780926 1250 306779676 306779717
    0xb01120b030a020a0303020708120a080a1109150d0c031407080603120a051b0c030a080d0617030c070b120106030c02120f0c070f031205070f08030f010e0601020706 72
    0x900c0380350180705030620000941d0795541648021806034002d0221213007400b03240341c00d040c5c145850000715101013000503426548404d86a91103201c0c0d10b000a400c2100d0380080b8070b5071040c42c250030303448861100ea4a8410801000906050840180402181380c03150402e07815210500c0009094000880000b00c0050040c0015940b040000301540c00d0400d43c40100c1c070558001c403120b80f0001d000400c3d200c500f160300004486929103124018403080741c0c503000280e500d50080c2d03401491582c000c038040704104c1041e000103019001d00c0d0407200d00400c0c3c4812182c3c1d00d4100b40e80c00d4400307106000000a8141140701112002480c0d040c003014141c2c2085070541c05010503130a06002c41c412056803180310500080a8803041210a18090303450708030245442c03808856070040c8a01c0c114903402040041c1040300418000340700c40c240310f42c5406850400568580c04010094900c880000400c603d02d410f003007160b410303030f403c10b0807015554031160012030b40e6400500402010650b0002070300f0503c201e18 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 306782176 1250 306780926 306780941
    0x1030f051b070606080106062a020a091a0301020408030702012a060b030c0d050303010501032703031d011e0c0302090a05120a0c090b030609030a120c0c120f0801090b0112 75
    0x7000c004c41d07460307690700340d19003122a19030040b400651f068071103140f00100c108101d00940c0702620407401f204929000034804a40d107100300c6496a658101d8400c0f0050072450b51b055031a0000c000f192200d035100d00380c07074880d0b0041404030f0020b0801e452003a42c40080f000b00d00e068206a0360019070907251503844000030841c40c09140c2e030503ca84038036030481c2d588505400c02d820b0320500c0515201d51500d00090700f6154513810b2545d0018045a070441750000044000019640500c1e0100c2d2441507000d8500d43e14030804043c5000e5404c003155511386a860076092821110707400404c214803c2461802c42c00c9010b05100d440e0301c003000c44010803076483c04100c403420388501c3e202999680c420540ea0b4140010307042e4801c442c440c0d142d00121800b8541440b80d25809070b02ca030051442c3c101843c200424030304d0802d6006142903903400c0e200000034440d141c504e6400b0350001c2c03021030004089030041c00103503001500c02c0000300f24400104005082c0c2c012101103042c1a12031604103a001c0c584c617070240404 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 306783426 1250 306782176 306782183
    0x20405070503090d0f050f16020405060d0503030a0b12030a020a170901020c0f0f1e0f01020115030f420608070303030518030703091703030402090411030a0611040501030f051b07 78
    0x248429150303800035400504234100c2d0896a07440c40320461044c0400c0d03c100401440c0701c1ea211928881c0400e1001c8210b99000240c1c560008888886c840084d03002946010454420310004c00c9070450705030005805e192040c000d0104024980c2e41d00700f46040703841020300c018010781100c6510174440c10500d500f440e10f143c00a0040d4280310f030502c0070403080d0740444030484010740c101503000c1560602c4050000000421f05c001c0c403000c024171580268851b1036201c020302d407100b074400d10010301c14080e4040c4200ca03480800e0061110400c1c0880d80c0740d42c2d000101140e504800500850745924500c690000c83c0d81e10400f402d40da03440d540302034000f89002410a60004540c05d0341040f410f8081c4001e014242c0300b40c445250203802d100306408150348064500c0c03102d074401c000b40710159a414117003540c0305900c01000d40c0340d0004c10002c2400d144074800010704060170046049a21626032001d0030542e0401c1c0d0302000441000304a61040da2802d44410b00309083d00107008240400c0c076401460790500 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 306784676 1250 306783426 306783437
    0x6090306151503060302010905090124030b0301050a05010e100f0b0d0207020a090e10020f0301030b090a140619050f130f122001090b06010f030b0d050a020405070503090d0f 76
    0x152551101a041007800782d00000030780d100c4040c011980c100809202411050f41c1c003281c2903050000c030401080d413103c0501ea02710810b4244140c0c681c403e070002403130f2000c054000e01550038940c4c0044060700d002e006900c544444c20000582e2440c0030408042102e13104805260722610341545207801e94841c08001c01c9031902006050050785400d400c100003800c000d00e0000d034800704040c0590030102d00444034000306004000580c2500c0b00c031800e981c1503c0e040b8080a845445840069103007086484008040307d09100002105020100d450352203810148409882c0c0340d42440408102d600c2103520ba00303009660703004140308111000c28a54018440d141c10010500b80d52607143d0820f15005004c0300151402841341590740304028400c141406404c0280300300030555803a8104041d0042613241041104a0b070310070300c64843d803c5030340120009071620030983c031a0b003040d41e118030480318140e001d90b04150200b040039100b00c04aa1240c8501c0b405011030310000c081c110307001c048034540c1108005 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 306785926 1250 306784676 306784679
    0x80702070e1008010b0d03090605090105040914240d061a09090304050118060519120f090611250c0f2304020f0409090501060b041508060301060609030615 68
    0x1c1001500c90286581c02d40c02c1d001246000c41c01400d41d4404040340c0e0199800102d55000070703401030522801e0f18003500f02aa00c52402c2d800403144ca0185504c5581d00c1403c00c0c0309211b2520507244900d016a101800c40717600490250310441c0f100c0050380301d00c0c0e0022221484100410705030351042002600b8007424940301e0f42810700244030020156040d8986800c006800c006540c0c03c6a80004030086203522406440c0c5403810103441d80c000c10100b071440c60700006c48015081d101d85044011608032080400984000030040401001220f000b16142441d165890241c01801740c1a180d440c61001021038403c03402d48040c44403001460402c846088115070080f8010403e10100c00c00380152401514400083c080c41070003800c95482c52a01503841005019a010548011a0140c80d108040802d202000f460002c1c01401207510000c0600c6000c10041100803103450100302c100b03c1c96a0340710858580408042c200c40251240c0ca011512055041000601e1030308204a000c004000042c104c6 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 306787176 1250 306785926 306785939
    0x40804030f030503070906080408220503070b09010e0f1f0309051c0810080d0f1202030f0403080a0b0d020904021906050a0906210902030a050a030806121c08070207 72
    0x1020003207011404100e02008000d1459030041e030780c0d8010095072500c0c0c502070130b0984507080f0b54880c3c0620504401003c0700d03503049803809032802e04001c000103021610150b584400d81a510b8000200042c005100a4100210752030304802c21942d0001c010b08071820310003501006500d000c00c40380c4c40b0b810f258541c00700c00c02140081c8261001e100280403580440e001c100c00003455450024444c1003031101c8040c041c002d44c100040c6001041e88a402e0903486006003000981c3d81c40200f041e00b502041c0000b04100300320080e40c1150307001d144203464a90f229180ca001010549620049054020711910040740252604100321500700d40082c058a2010307004498074603001c4081c8e00910041100000c0100c500303a84040c141009202c6c81c0703082070110458000700c507500002200c6092507a40c1b030f031441c142950fa01f40b1240c0311082e4010200c4e034215049240251402104441d40740c8218840580180c10140105500c0c1c00103880302c4e50f01100c038810000581d0b2105024042c0c0d0118442c070a0b011848 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 306788426 1250 306787176 306787193
    0xc020a11122103040303050718091508120901090501020f0d030c03060b120402030d0e010c0f170315041503030f12060b07151b0504031728020f06071704080403 70
    0x110b03080070400d141d0340d04d400e041c0542640c902400c01c43c05c201d4444089100c554034030758003905480080a001c10020000f02550314007a103250450712080c01040c268071342d0348039448020451a0b40a03200c0307a0313403260b4070801a61160f03a10b100081f01e5400105154025901c280c3c0300204490090800085581c0c6421a0302c0150300680c128001090300f1005110551504105462805220303103810315200c090207000078451040004002c220080c03400d84181084040016065840494800551640744c0b03e072041c11035024102d0164001e5181124000112158031401c0040d250182c40e070418054403500115282059000c9620350710303580700c03004039280e01805e000b0144580247e00c034200028074000d000b401c0310102800074904185140c0011b64450b0440d0a46048030b40145c05034007040400d2803080c0440c41400d1003408905035041c1c20401c20860307a0203c6884941e541d00315540480040d62055880b1411340c1d4250214003105000c5000204440308598400c0c403600540c0e08044da40e0761920305 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 306789676 1250 306788426 306788473
    0xa0f06120f030801050405061e0d020907080f070309110d031416141501060807050904090f1a01060905040218030a0606051008010b0a111e0d030c020a1112 68
    0x40d44001d64441d0014540d10004490140100300c0d4208610b05101d000119588141e509001a0342108160005144e4400d03010001c0c0d81e401812800300743c1780c1144001c16840c011120500390725452004a0203040c8648580c0450a5004098002e80c01c4040304000706403030310020890411004001e42d00d2403540141c0505400003040d241400f001d411480c100810694076411414158009506940c4200040e16051304481176030802c49819100d074007040740c0b24441c3c1301e001500700d0705103a19103041011951100c81c03040d0107101c0750441c0c560b08550350043d0755428802c5c0f000103194850140705d50f1516038020609100700310301503000c0644007004282803c1c503d07081501c120350703690402c004905219124078494115480c00030803230b40c1001250b03241c82c015041120100031406070710381d07002c00c400c000c0409084543c5404503000380481864550710079990300300b0320000e403d040c09059203500000e904c116441d0300c1134414242142080a01400c64a45d0f0005081842034401020614540e0f030781c00c00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 306790926 1250 306789676 306789683
    0x30a08040503010605031c0810090e06010603110315013606090e01291b1c0323040606180c090501212c03070b1506030a0f0612 56
    0x545503440c080802d8210703015644054000e07040740c0310381c001f20801c400b0742e03400000031428401e00036200c008d009410b42680e0b400000d09141749c5070b0b02c4140d0340c50002c0c0c00c3d81202d402daa02400b204881c0003014205000a4940d20408916850340010300d60060403840b0a04001064500080606130045070300084034618007800742515001c240070143d88900d0a40280004811440495250088903001640546030029520700400c41c24542044900100d821001550f1360000401220f4400c194444800c2c01c0d0000b00e00c8110074400142c06c1c0680101c03100702c10500750700181c03040014120144400020001c49085940e04c0010500d00600500c00003a083e0780140015500400d0b54091b110a0168001030305002c0c2c407a002c290081010700c6490b1030040100d0000c1401580c0c0244047c950341c00481203406e009120030402803c0d5000000340042e5800341038868416165000245041041c44201c40d401c40802c00001c5c045048507044402000d80f448000940c0555034036403925103080c0d005084 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 306792176 1250 306790926 306790943
    0xb030a0c11191101020604080f0d090611120a0c050f030a1506050a0206100b040308090301110f090913051e07351605130f14091e1b0f030a 61
    0x810500140e00303c2c0c900700040c20b000402190030b00351102d000034010b15201d045100b00c0000ea41141d00d4031500806040c0340d002a040c805005070314400c05498110050710f80c62024900001030001c40c0501440018044945900d80f038a00404101c9541c1c4c1e0005042201079901ca80516603a80103503050040145401d030359141c0c84100fa294000d050030303806041203610b6540380c1001d0041c222110219012a503002409980d150003040210303024140b061024402075101180c40304400c5002002040c201e10102d4805526070b48105c50307000d6500d400d48001e0410340c400e80348801c500311582c11284002c2c804c0021500c00c299034807159500050b441c48108281da100c1b0710507060080c00300680e101c49a480350080c00c284041c0c003404500c0011248a541e00c030781c11320780c4c101c0c10321007080d4489040c1310b01c20340e03061241002e08841401854000c1c0c5080c0f41601c0f8050b208003501d003d035240f620200c602d050141181004540c602c0c01103003518a4616840807140900d10403580d810044210030038400e0110 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 306793426 1250 306792176 306792223
    0xe060d0f06050d2111120705011d0f010605010c0b0105040b060d0504060c0912031202030703060506030108010c080f010608010b0304060b03030c010905010b1801290a081f0b030a0c11 80
    0x4070f013a54514041088240807001d42c000d03c0700d070804611820b00c81c2141c0b0007681c41744510706005025121011944040340642c10404810b41c00101c1c90910198100009001c1907554000440320780c1d800036009400c0050030001071280d45029040340141e15030017043c41d4100640c1d0041c600460b101500c0c1110429030b1110301880701c507084080e40ec0140440000100d130920310b9100500b802400c80341038411282d0010020781c40c14003a42c004070140101808003074580d0786405000e8000e10005203030f00d0105e6085400a45260b040052007816030b01550307541d060700e07483c1500c85200c5410103803089800300e81f07810080300291802c0000d018032119120001ca50341540303081503408c4a428480d0303039015900321400042e0038a4020307181c5045070030680c1041c050082000c2d1030400c641010040404403000095824002640301040a000701d14035400b00258242d1b0341c501c4401c004440c450b12041c0700c0180b0009840303113941c0d0300c5000003180d581414850305240903149130520311240e0346010401b03008242d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 306794676 1250 306793426 306793463
    0x90f060705130e07020a0219170703060f061802070c05060a120c020f0a08070f052a0f010f0f09051903060617061617071e0e060d0f06050d 61
    0x80d600c0040c00c604420030f405061848000391228841a4080d004007800b00c5861b079080c030082456002842c01c4410030000c507a50002050700c442451200355546c0f81803400c00b017603122a500c243c0c0200c2c1e0004000104007441403030204040c0d0042c040030384454866440005840d20707400300521306100590340740380002d80c01c46090701c111540340402e00c00319071080d4207404607400b001491000d0103401040722521071544c2e1070a22009441c950001380180542c030200100c8441d8000100001a03481c0c0c21041040c900500744038030951480e52560028070b140030035400035070003401500380c0c20103245080d0140584450109550000248051591062a8408200740903043c81918040d0012003a00070800c3d89142c4003075a691000b070301d0424a070340301d580311242d010300590a0380a40c0e0044a4030511603d004c000180c5101c0c959075040313900c02d0b54030b1642c0b00b5052050014502481c402416503050445c1000369500078072901c100d103461603607140341c04941640c80080d4200420710410910342005101e42 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 306795926 1250 306794676 306794707
    0x1080403021c0c0501180314160f0302010e0d020a0807031413060509030106080313090b01050c06070306060806100f12020c010e0106210c0b070206090d030305090f0708060c03090f060705 82
    0x80d01941c403802e4107891800254400d10124043d180a26234a440b081000311000c1c4202e40590001c001014070550f2404060701904001544100351081d00c0c01e0002c100800e0344c0345c281c2c480f4010309083d410000c14001034064082319841901003050140be00c503a20a00000c0ca25450700250040f6101003611740051809014241c054200180078604050298a0000303101c00940188040d00d40c0300d441805944e4410400c2c0e540f0805440219036031820030440140003015903010b01c600040c030b06400145103007090840c0f800751200a540d003050aa0444104550103940201c0c04a0450b4003000703510b0300c1a009002c1e4400000e14080005003691900b540940c512020043e50090114103030030000218842504141c1164101c1c6100399a6240910019040d480340300d52007540541d03000258000c0c9603050303010b41c0c0f05c1d540e04400c541c1c007e10b1202c011540c07810b0034403c6ea0007035072041002a24940381c1da009160084440f404503442103032002c50b03642c2001e004980400000380b021400c150440d1001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 306797176 1250 306795926 306795941
    0x6110c0613021908190f0b0103080c06010504020306130b0f0d0507080d0e0604060806060904021614012c1504030203030a0501050a050a05100c08040f031401180201080403021c0c0501 80
    0x1404022111807401204546a510304c0310141174004198000c1410b000c42642810401760b40300f402c2c240d20f5a141c0c50010031982100d01c00d0301e400e206613070021845003000e1080340c0c020a0018160400305012842c51070150a403406400c0c1c020004465150031138882c030404030f03d00e078894005000b00306c4c14003035544d2419004020308002c201c030038038202041d92684400c80c1c1c156031507840c20304a01d6585d180030a102d40703c0c40141503000303440000c144244604007200461928460001514030080b004c1c2401d0a0316407402c2204201011604102450140100030301c19100120003603403110768a0525004191000300c40a5000d40c000208020035000e252141c1805010100d078060101802c000c0407694000c81809000c0c050b003940100d640302c443c0103c143c070920580c0301518584c1c864540c82d100c1c0d410841440121030340d81402c180300c148500180604941c1484c500026407020303456400440340f42c0342c09001a4154040c4600c2c02d0f4030003098503036041c12007003142c9030000c40d0703481c0b03107040382c211080d8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 306798426 1250 306797176 306797209
    0x9130912020d081e010e04052a01031a0112180f0c1502030a12021b1e1506151b06100303110109050c0f0609040f0501030303050f07050706110c061302 66
    0x80b5130341401c0a8000814a030305541400b041c2d12000d0352285081c620740703100c0c003407110382403110f1903030a85410290018082d0302c0403080e41e06010441d00840c030808040d080d02034083c04503c2c800c1102e00c0d00700707069001004031001848082104101a180d0403030307042081d00c0a96222140180038003a04400c0e04507840581c3c0688001d51421482000081050b030010705048891500022400a21161084a40c030400c1506059030440000348450550601d46040c00ea60b0501030080c00c0101065040c2000b8820140a8202d0251300d8003101400c00b10341c0512500d030b40c010240481440303034540400401d44035000041c0a10001400c600f0080c040001c110b4120295038149080000015030100e6446010401a03981c20718110210740044c031030b4040c00080035003003498201440603408242d0020350480340262010001900c50300c0341c3e41100b450032036000d40441c804002c03900000d40c8580c412440c202d80c80c0c0320030b403c20100c0580c00d81080b006a41c1c501c6c40c031401080b160150701d0400f030030b610f0b103808 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 306799676 1250 306798426 306798451
    0x6021e0f0a12060302120f0d02121902030403140c0f0607030512040809040906051807030f0b06010c0c0905060316060207060c020a08011401030c0501050f09130912020d08 75
    0x1503080849880780300340d0141c03504000e02541c0800210400ba04804051036004207400c3c0e40c20744a0300c40c1c5940303c1c17942c070a104052007036114040c4050f0022900350b007002907101c20703185000c0d008100c241020081e1500700046200c20000040880c400740100d2a450006001030f01843c044c00f0100056403415101c024403c2c40d00304100c2c00005c0d000346c221131412450390240d03105985c0311b04120600703011f034142c07164100e41010513075010807100d0b500151040f14000d4500f6030842015802c41e90707950356408024911000240c824000c80c01d00c2d42d045502050515100c180703a6065640c0d0180014280d01c055580c40e00c3e01d007489518581440142c002c0e444442c12040c116181c0303080250b0b11802d1f8401d90042c0141300c0b03804000e541b03942c00c064000d0160480280300d002a211251007007030000f44000d682d5441000c4020415600c10000c44000341e50b0a1305160030300c0000002c001d48650801d00030141c456036002c486000411444100900f0140c0390050704010f14800710141c992036000300720707890860 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 306800926 1250 306799676 306799687
    0x81005070f05030f04050106150306030c0b070f0b0a0b0a090603021e06250803130308010b13050105210c0a1205010807030303020a111203010302040624030e011806021e 74
    0x9030b2142c1079942c042c0703030301c42c480c500343e110ba080407401401982c114400d4a0400c0c18000b05194264120b5811a4820780d070703080781c250740c41070f100d19140142100180041c240c0c00304080410204e03150541c00ca0b614079030000d015642100094107881407075202400050722040c0030004d52070182502c41032802038202d012000601600094018411642004a980710102e00740d0b41969100001c0c0c501568000b40441d078a0502c071081e240200e0145500310700007a0355400101b42003003104165003001c03103550740b018100c41c200001176600b500800e0221190001600a079903002000884c1e541c001c0504420f429920000707090300030002801c1e1003281d89203a046c280100408607000030b20504032601490010780345c080104048498060348544250132f8469030a00f0700b0010700303040085040324401c40302041065950c0640c00030414070701c5005840e124051042e441030502030741080c8045100c2400006284801341241c11400359011010388404d5808682040c08600328000c0d5150300b950094201e0820 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 306802176 1250 306800926 306800957
    0x20011a01031505100302072406080a0b0114220c090519050f0f0307030b0702010b010e0f10091e03021504050d03050723010c031b0509061308060108100507 68
    0x2c1c092150f40d000e0360114000e02001c902c00d0341981c2c1000c1c0d202440030302c11a0042c0e1f01800c10151084040d401910b46080028050750018204c4140d83d0701446421103a031034280c141d009020301c24502a0040d4903090743ca070030444614444108408070400016051103501c00040010000340c2003103000f11503112a00d014006540c217400c089490848950132800b00600104925441c0203410075014402c6160200400a4076602c1a01ca03031210382c000c10605507a2401111006400c10003507400036264a0104514103002c01e84a0b1100c8103030908074001c599445a50605150a002907824600640700c00d104500e4140d1618000411049005003414100b000142560010803801404c0c080c00140d140f041042816411598025a00340c4c5058015103e015030301078148107204500082c034160042100c2544030036036030540310383c0d03070b4540d4144810202403164030fa00c041d40c00300302601c09210019400d00700708070f00e0340078003000d0028022200150146606480d0003921074018023810800d540e406 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 306803426 1250 306802176 306802211
    0x606050412060203064209060a050304170415020c030a0308070c031106151216050d0c0509090d18080303071b0c03110a0e150402070320011a0103 64
    0x460741c00280060f40c1761190f200094010614240d04101c0c2c01908000310520109110b0655103001301d44a01100f00501320b14080306403283e01d0f01264040010311a486075a032103032018580c400c4c401c00c2a41d0003101c1c5007613200d107641c200790301044030021442842450554180b10302c1c0d140507415001000700300240d80c0c000e05070403001003421040001d414414818107200e40c00ca040b8170140c0009480c0242400480041c003004081402e82c02840b00e482c407403184031000104191510807003078070002100c1c00e01c6d04000c5214080401a00c41c0c10188501003030540c5c6410748c403402003450364010100442240b0300645812259000301c0300f15018010108003103e00841265449406841c00b546d1522411607101d9803108040c4020304001d24042010003000040403220b8081c240c211004001c15a07505242c1c42084400c0300c05000305452641c20096038140740d001741007090b00c641051030342c40144c1190713601d180d03040d003c60708001e80d1902c02c1c4181031000c12100c009407036403c1c607051166890600c0e00c0c1c0341 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 306804676 1250 306803426 306803459
    0x102070f0201030b0d06020a02030a0e0d02031f0e01140115081308070c1806080106080708030d09020312030f060f120a03080c2208070e070c0b1e0c070606060504 71
    0x141612001382010581e01e552a001c0c1580e80441c04549030281c040c1c00940ea500122000c0b808034151004e40c662529081ca50010b036a5402002009020760303400660f04a98140444c41c0d50807030320b4503810240c8010a006d030010210f0306000304000d962402c85264688480001d1030307002c1c0410541030203c07a404140400c4a095002a5019901c22480c9480b8251130080d170300405103d4124800c1c40722052041c0c102c1011514904000d001558407070510649406140c403e40205030f00412840d40b0350740307464114408507400201920092808010411000da0044880b4070180000c074040110342c0c5020b1201e03081c00e01068403141c0f19141c404071702c075544140401001d418406ca41001642d10200c8008407a0301c48514280103c00c0711038646482085616401266142d01480d08086401d98042105030700c43c0341c0c288c2d01c0e882840c40c10b803103500004401601d040302a09030075008080401c080d40440c1c0c0291500211581d4074400380c201403040b10019081401007141c2040700308036074048002c500f01c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 306805926 1250 306804676 306804679
    0x14070507020112052a030721020f0304030909060801020901080c090a170a0201030509062e050d0c03110301060b09010f020f060c0a120203191e09051605030102070f02 73
    0x80c0e444a540c00103032444204801c04502c0b80b81000c0400c10000c54002c9000c9080341c0510030304081e0401c40d071301080a0f000c200c9080c000240c0e440c03205170605040045001c0d210001020051821300c6528003200580c1c0203c1c2c0c15404118030704810400c0031041d21840008180c4030000314206142c01000903d00c0c0f5025028480341c4001280c82080760399003820400c000e143c0b641412091055a270043c41d240c020480c8146d021914041c00240040c42c00306106102d000419500c2004008404c55001a200300104e03804400c02c0c0e60780c0100319034075030000c0016181d024000c0d07000041c0c55446c0c07655042e104035510354007030303410304900b0451344540001f600c0049109080c5104c0700304020b9412032500b4403842a101051040d00c06229080312090020441060103603a052461408942c4440c140e100644114011b2001d5091308504030b010b9500c1102d10940c0641c214141e13801100704d0209603131520400381c9194200c9100f890440420701d102c40010300d0b0540095003080602d45684c82e000b00c1400019 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 306807176 1250 306805926 306805937
    0x102100c0c030c0212011b0216050a050d1a01230415050609030a0807060509060f01030c050d150c2c0a1e120308091612060b0303042d091407 62
    0xc08569409500440c291100c4008001c4401c107c03c1c2c4403075404c0111603010243c00f0700705001c002d209000681078190740b00605210280c0c0c1c541414048101518081511207010101c03403010701000801019008102402068202d888011644110584800555407040d45409000e08000c07101295040c02c44100301d500989a000c0400070a080c502080001044d890f400580b007420458541d0005008500315001c4805507502da45610307a400d04d00380405814000300c460200564600b5007a0017a02510580c4905c4404018175070183c1a034200f0348001000c2407107606d1110340042400900e00181c0c2c95000c19022440c240700218084d8191409411141440075899020b688044c0300c62000429a220207480c0441650900a001c09400d4401d640c050040810720090103064003e14010341d51101f082138140081507071010300070103044e50381540600043c040081c2c2c09148070142050130f100c101e60360305002c11660703120301294000c7d044501c040d031400141c4917a840918240e940d1054160409 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 306808426 1250 306807176 306807197
    0x2090a05010321020f030f03180309010203030a021303140d0f030204050a05130905160e0f1504090f21020c0402040f0b03040501020f07061b02010e03180d05070f050102100c0c03 78
    0x40b400d011600080b61206e1100240052a1884d810020340c46240601120421056111000f944030721499080070700507441031001c103ca00085074001c2c410701d00d032500d100c1d8407a6581e07503c02c06813011007200700381d69410203e0465402c40c0c20503141c0410000524085290505103000180e14170003500403180101c004250503e0300480580c00740250507084400c079400e8403078603500d00c00584000c1c0120588501c2c3c3c5404501800c400c0600d07103015814040e054908490600180001415154410303600c10005106000100e41546940002d0781c1d41c120311010200054800a440c04284ad480030740500c0c41000b00b0007503054056007440c140c6d0b8040c1c50040c0d5a13100e03030801c0c0340a401900c030040c21314100082c203034080104c0b56204400070418211008180b20748140103908868075003a044449070030800c9040d031203024065001e11424401000c5e46651042034640c68540500754000c2c00c40404105014041580c040042c41d0b40ca00140c4003c1c0114021030200604802c8685001001d2140c20f026 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 306809676 1250 306808426 306808493
    0x3031b0b0c1b0f01060f06020606030c06070f14010227030303010b1c0e0d080112031707020a060905030a03110a0903060506120327010507050c060d02070803040f02090a050103 77
    0x84840c0c0c101c0035a4102c41d2403070b0306000380a001740218402c800802c1c101e4080021040d00101d43c8520030f000c010050580c5140c42030600a059100641c102c07012100310845800141c1a0050b0010403200f0318001030f00c0f42d00c000030f0220000614034001c203c02c0355203000e001d04c4c1c1d039000040368151078481018035100c085a544a481c00d28071581860400e608081d000d902c440c2d0001120705071503d8907502d2401d40d99aa944d00c0c02a40c9911801400189820180c000101b44001322286c100402c6d10484491001c2d0b82c940e0f100301d404080003210141c00014114051680c58020329805062081c5050324141c900c001c040d0501c005132000801d62a2074000080040c0e9413240641110a001001e407603607a41901d804480d01c41c0e040790403404a19402039080c442c0c5d441b0303106648042c2e81c80070051550a014902700000c54100688a006081d000c011490015840c000610700a0b4880c0030031407000401c9104124884400900c2c02d070b03481e0315000041012544c29120251416070550202025100b4500d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 306810926 1250 306809676 306809707
    0x4020607021807080402030706030509030a0e011e080412111c03150e090f03130b0306040906090c0f050603150907020a02030106140108060d0203030a210f0603031b0b0c 74
    0x310181d00d00e07041c1040203c07460f0040c440502c594822010b070382101d40c54440507401c440007035a2001007a403040c05650340340741c0585026034561005051089070800160588000c00b808280b04000003032282c0140020007052031541400c1198504007503102c424410405e50740c0b44150100c2c01540c54031100008556802544410b04074845204111001038a640031503844071800c1d160854503109100000c0c10383c001c0030054032150b8180104502c1254601801801513404c0076080c0341d44581d94104c001c0c0050082e220366500c1c948505e074140384440c42c0c041c0c0c41c0e035000c0c02c0e82d22603070044504101300071480c00203034aa188880300854140341039484015049160660300180203425600c0c084021030361120ba203e5020740d255090340c0c0c0c0c0304140d440400340104480da005000750558428000605803a00561029490b000c0462040460024001400d41a0b48076841e4400f002d0340d681405000341540802c80c6456804070740ca800d503003504c0e940d9030305c024404010030468102c00041034082010702050b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 306812176 1250 306810926 306810949
    0x30528020d080304020306060411030a1109030f150f0601080402102102180604121421040f140d0b0a0209031b010e18010618030b040b01210503030402060702 69
    0x341100c001d0100c0d5240015141d030040d20180c0c0301c0d100b8040000c02d01e142501800c0c034129488540c2d83c2c10f41c3ca4042301d460140208410703260014409003d0f081458034208060318049007020010000c0800032000b9414a00d405003c0b00c0d00e0407400010840e4698102c220030f0340040c0c0c10340d000d48150714039a00440c0e50341d0059036a4003001c141e42c3d12052030b000b015000f401b58141c55818850b240040700e4100307d142d104610440720400354641042010401c190b4034103207092104410340e2481c42c0d1180301c4291010080d14040003240d4085020721442c00005898009000c03290320410b00c444c05940061000203862030000c000c81419000600c00c120142c041d03582000c400340072160b09a01e50150b40c110980c9840489001070000030020100c0d190044e0701a40c084020609001542d007414022507402620400072581080e24900c00800a081804694030a034000d03000d2000a50400710071041661541d81c1c0706c10308650007450a40810404400c407500203034100c80b02c035980c0160344082651050304 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 306813426 1250 306812176 306812179
    0x70f02040c120f02040501140306150708040e1506090f0a0f14040c210b0307051002030901020601090605010203040b03040f02030f1c0309031e03090c0f0302130603052802 75
    0x1805500140c450700b115901454001c084414000420010030450490240d80301d900d00107940807913002003000420b0019070308200040e0042103900302a001422217640301c03040072214110001005c00500030558000c3d90840840001c6040ca0005a40000c090380500304c0118071800361030704861a0340d0743d6000e601006060301e00628a0042d511040040044080c00c41a8001d601f810004500e0500c05d21102d41d03844103045800c954100402e02040007007204a000a42510803010041902e07a103060201412580e071750700071503881401c040020704024069006640007410000f050085a80100950b4103a030100c4101c070340c60f41d81d1410a80401a10070724065018061280003a000c0c5c48082414442c079040d6101481c030301c030381c460003c0381200c00c1c0c601c02600003030700740e466888076203007020381c0892440040c030700400c0c885c2d280d4a41400c5100d407a40000e42c4244140300410071400c0070480d007070b59681100c1d4200301c4146580c9070b503520352040041c6503103060801e0b20600e4100e2000030b12103100d03640 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 306814676 1250 306813426 306813431
    0x30702070e09010b15090d08031003060212070201152402100f200c06040201031a09100f08060c041202010504080d080103020a05030303040309140310050c07030809030c12070f0204 79
    0xb4505061802840d85402250007042a512080c8040360344100b20303110000042c0c5802c0c0c1108240d1510101a000076052094015036017800002140300790010705400344038199000f1150502c20b001a0071100c1650341e800490360507900c1003015518040c100071644100049240292441d078034100d0811110045203c0c0b909d2030400b0303144802040d68048040c030403070310311886076024040020300614060340724181c030b65501c10b000040c0154480e4001071681940303c004103141d0401100003420b01c18040301e8080d00c018048004009243c0103145210003000c1c1d820162915040c6807496040038800c03802a881d070f008440c509003045900c5441114002c1c0421026203c0c0f00283e0000200b114000b88016841500845404585454080200d9000b42da26480d178804a6260640c44a500701400c0310240d03050080003403080d041555401510b02c07490000403425540c040b540380c09068030b4400307001e142d156402404400781e00d15001802d40007540b040300c4403d4840b0107a1900f010032441d01e4000030740160 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 306815926 1250 306814676 306814681
    0xe060603280c08033a020a030b18041101031a101403040503090406090209010527060a09080114070c11030109240e0c03070902090d060203040f110306010f0605030702070e 75
    0xe0012000d0180300b00e118110741c00441d480b408440a4015403601c0788190f80b8000d51416002c105c0354010404d48456042c0802c49100c10b000080000c80800760300c8804011070410042000203503040070003030b40c0090808124944600d0341641030700c0d41140c1c02500a4100008009400340140c5000581c8085040019030f44c6c601031a007117849070002c081c014081c604224011580c028a4003e0321a07503207041e50b4481c10100003070724071008006d0400d0040403152000401e20003903242e40d8000c250000d5180c40d48400203281070040703400c403400642101e824180c81c0f030134021001c0d07101c541000d103035800c501d100c4101c0701140c1c0000e00504c12950b006100c03122121081c01644500b2a641500103141d1800304202c00000002980301c0200c100d99590540024800380300c41d0205a02400c20440c0250051441d002183c1e0751004036842a602626240d0203402c2c09401c01c400c400341140d14a000340c0141096500d002110102a40305005280c2071080210021b02894420070222004114040b0303294a80d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 306817176 1250 306815926 306815939
    0x71a091804050a0302011505010f0e190602010b09010b0f030c0c0f031204120309032703060906090b0112050303070c140a2102011803050c120f0d0e060603280c 70
    0xd0f001008104c1c0554240001e044140a000d07410408446044c2c4969100b901000021030303042d5a4928460760188042008100b04000300c6440d00c00303045a82c00002e00105c02d4070411803c2d540503031044135400d904011180c2c0780f5900c2e0b000d50381c11160590b000d81c0c0b140351161243d070030080000d080034aa48008950607080c5a251580c440c00b540c0580c01a080200280204400340c600d440340c0600481c0103c800c40d1008110340d403410703688246009801080799200c2d44c0d81010f54207142019200d580d01d611045080c841f20704001401411984070019071b020207540d41903124040200352030140860415a0300510900002c65642e048508090f20010000c6140c50810100904190b9104100c8210900070542c014810994144426880c1c2e61b5100f00940d4212507581c8407041c1e07054140903441d501c1c88081c4240d0060070805038a4421661144455135102c02283c04031a8130b1f484542c441400e010b00d81d100494044054040001201410340c0e1103640c0340c102c040c058000812209d80e552000410 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 306818426 1250 306817176 306817183
    0x90503221d060a0e06011404080d09060c050a0201030c0c021008010e09010e0a0b100b0409020702010201270f05010209060f03100503010b011b0c1a0a08010602071a09180405 76
    0x9880441000352281200459004440c80301207400c40d4010440000c01c0c1308400007541d0340c0d41d014005162041100810065203841c0b5080390f407125216600c031950360000c841c3c03c81c03c0c29001e0407242c40c2100d0004455211196103407044540641816a5003010100d02c0d4400d0000c0020709401401604094005110040032500e007403140541c000075030f10100d9600702042c042d40c184881e0310302c02000c800459803103007510760502501c2d030f03805904240800120200c00f08040c10040c01039150052b03c1e00468000642034408089800040c500e18501c1744100c0740c45001e01c900801d40165411050782e20520300343e0700901c00c1c905c580390310100220301010400e14403030055114954880d40031804640d07600134942a00c45031820a404074841c00f00110701c11819004560249000e45121401e5558810b090040205c40d040b81e05051040000c0e05210180c021208600400443c801081050300c2c3c45007018000445002201180b14005030511a554400e01000b954000302042c40200342424606a540c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 306819676 1250 306818426 306818429
    0x7020109060221010504062939060709090203090109050708100b0406050f0d0c0e0423150703090501020c010f05100608010501050a0e2101020a0207050405060604030609050322 77
    0x44120410f000130400341843d016107812a0150604ca0401e5901030300100103c801003001450303000028081c40000310b076070422000c058001103440c013104c66840345506002c002ca002c0c00001c1c42c0d01c142e081c005295404803100c000c0302e40700c0100503225243c0d9258107000d02000300d0042d000d44148030b80450540004940c400040b00c45000412544038100c0c240001d5400501c80c00740d02c030a514200c0262810100350000d40c040c0300d8420800c90700e40f210b00407000c1d00001e41c2d003500c00507480f119000c5a415180410010b01c0c0417400207103500168005101a40d48000341201d040503114031002003000002d40560700c0b2503402c64020700040c1040d0070000b004000c1100c454081c82c1c0c0c0c0140c0011501e0081294605845041e03580914150b0700d62020b42d2401c4100780d03081d41056031220400c94160b180364204e085002514000751303a0341c3d000980240b84c407010313400084c4142e103840f0038010b040c0ea030301c41214100c07503202001103800b401600f0414214040c011001200130b840c2c0310344100d1021400b244a0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 306820926 1250 306819676 306819727
    0x16060f020f01060f0501050304030504030b160e0d0203070612140a0b040c050703020c0405180d0206060109081603020904080f04030f0204050a09110d0c08011505090108060405060c03070201090602 86
    0x190310054010005090721060311036500ba06241324400d02c07565201b1001103170b00c03c0c0a828105d16080d52642e4100c2e0301d0801f240e4046039101446104c91010740d00407000c0c002c4960485011581c041582c0001e51100c401e0310402b400d02c120145410f034940c0c0f061300b140a842c0d03820702012000f85410f5500b2405000440120307817003546080c240c2003081d80200207460401d80c1690080440308141000d2000501c0d014040c4070209034400041e440c10341c420000d25020b00001d034080c15540c05c4c900700241800c581030b041469950800780d10080b14004982c0c030741d01142d404840c2040d0300d4803a4100506a8070a4038072100c1410400035021061100111202c83c5040c42994100f105070707101c000e2101103540421300103025615003003d4158a140c5131040744100d074011000c0107030003507840001c1401c44400001003c40344207030301e504026074985045d5482c01406d0300030180c01c2900e46940c510381c81c0e55008045401da41c1000c000320741414400d600103a455940080110f540300c09521280040000c50407200 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 306822176 1250 306820926 306820933
    0x4030e10200f06070c0203122109030a02100506270f1b0d020d0605060a0306090e01090201020a0807060b03030307030f2a030c0c0f0b040201110c010e1216060f02 71
    0x420445070001228800850084058182071303e40001c00c66404004150603641440340644220704c103142403005281525101d582d00102140005034200c01e24401080c03c801c1d504180580760500c0d4001c9203601960f21140c40c0001d0039681e140006500d02a00300c0039542116004004182400404100500411002902c25020317946c00a9035070303000041510b40045108140002240c04c05030b9009000020149400402c08a854601049098000344083e40010342c5443d020440d03401d0510448a418403c207009001075001030300013030354989031254010a5070400050050500c41d80f94003407607840350300405980e604c0c14450300040c0649900c1e00c0711081036141128101c0e412000c0d4042201d01c264031020b10725040301807001a402803030300c4040301c41400140b20341c200c0003d45800301064400d210702c600316840c0c10030703000060088000292450b51a4448110707111244e0b040100424201d900b1150301c00c0e80c0c134450030014100a80e01e2194480c4a540350804a50590012100d40500702d01d58202c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 306823426 1250 306822176 306822227
    0x3010e0a050103031d040914060a11040806010509040c08030307020129010f030c02100213060212030c0304020402090103060506070c0608060a03150b150a0206010801112104030e10 79
    0x4000444a083c480200454401d003806116910346035421003c1410081000078803495545522080600c02400d412494102038200642c0f2403507032050075030240120a41f103003010300b0070f00107a076211810f0003041e119903422030002d0304000380882034034081c001c00010f80c0d4590400240c003034040d0016483c01031102c03030700c0c540c1d8081403013551105078034498050351003850400000078154000c00c1740c0c0c09058114000d98020000356881400105a0184046103070a081e914101000381010f000010443c8010310070001e0090078506007042c3c0c1c3d0801d404460069445041070010f078003d0005511580c4c00480100740c110a11010f0030764042210380c0703501e800145548284c1041006007241c08024a9040500d0b840ca05101c4203500c0082d0091000d800003509402000c1c030f00b980d681040c107051006a10200060045680a00a644100556002242c00c0854400c001078440c0e01c054102c509011003c4005801c1c18032035041584610000362029141140da03c40085c02c01c100c00070320240e1000c40006 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 306824676 1250 306823426 306823441
    0x30a0218070909181403130b040e0a1401090e10060b1222061a120703030f0201201c052d0921040509070905030606010c050c0d0201090e04050303010e 66
    0x4d0700c0b41a14480c100200f46101c90f43d620f14108a8840d8101110b201c00d001d807080412138031030000e01901d0160300d41920b6616100090000d000001c24070706604d82400c000407166408004c5141c1903404010000c40c0c0d0103500741159191054100b04404058200103001591452003801400403c6002c00d040e1210b50b50100d0448841d5402820302c903480d4003000e03040c0c01041d00b5038030032441d0380005100c60201da05034034002104020015038040b403603006400d0400030560080750505050f0250300090001c540c035401488240d0a03046500d44540600241039600710f20012070911503629200c030100580d0506950040da0001e94100495070b006102c00f8060103880010001d074843d84840c1d00600003804c03120b0242480c5a0b800e41072450100e010700000c145c2d540c0301660648034800640e44d441207203180c85c040524056002d805241404060b20362100880c0c03020403e1924851705558103c3d80010610040b506d0100740d030702000801d4a520240700402601000443c1212003091002905441e00b90 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 306825926 1250 306824676 306824681
    0x106030e12040909020604031a07110105090d03020d020c0d030c020c01030b0a0909030c14010c1d090c09060405190302101e031d19020102060907030c0e0402030a0218070909 76
    0x840803074000744400c000f400580d400c0007524030702c060495811710781d80b990741039030010250700355504a005000400410f01c0e802aa00851840032000900907030801c507613139540b07801905407040304043d000900400c2c110300e50f4044890301201d2600301d50751002c0f9003800800238105c0c6e04007000140a0074180662542c4a8081c50444201c000d0500403514a130110b014000d00b0b46103411014003000036400004104a050301900b1a1420000420034001400f0014003184c0441c0c2c0c02c0b106c51611824002d984e2f110101034541c0b018642c07240b2503a44885a000828a024962000303a020540c078102010300303101d400c42582124402d864105041031110400e031217210a0405003e0502010007020304218401c2d00042c070f44d07044841c42045040e08a030317121824a986480360354499130358800c10004550b410000507602107076420140c8060390459a9155003c0c02c503110b81c00514510b140800c00303540d8144580c444a650060850443c038100415487c01004201d40c8840441c0311000c0c0081e0347c40d03190 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 306827176 1250 306825926 306825943
    0x14030d0c0b06040b3d0203190311133308070e060c03071406130605040309170604051b01050a20010204060f02070801020f0f03130203101d01090c030206070f1205030106030e 76
    0x80c2c007e9800c00307010082400300703203441619000070103840b40e034a0420b82520f480100359030055403044401240c1080c03140f540d01c0024524120384201400e0990b03804100aa0442c689030140e40f40c87d1032140c459078000ca98501980c450643c5c025000104541d103144c0000c0100911442a00300c0c9030604d605003022610b03200c00b286d600a51040d130350080c03000200e80e17900240d40144079003020400242c0381c0c40d10305042800075a2850b0168001e00500c024400200314281102402c10f4110303118558003000202103000d03038080c00c0c0c20300044c6403006e01c0d007288114074240500c044500031502c80f0380d19070005120007000d508ad1800341c01030300c50114591806000b250900c4010054462801340f0401e08051507500c0244410b4140418541030001a40e043c4040c40c030040707003500041079a40142e46d0802020244401c1c11120380e142010340400600408050b00440c1c0e0121013641c3c68029604100403503400c43c8000501c2004c550400382051a040009903050340c2181d03070b04004055600f0092a0b803010700 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 306828426 1250 306827176 306827299
    0x209180703030f020f120403031701030201141e0703090e010605030c0711060d0e0705010e010c1104090206130305071403030c150703020408030f030114030d0c0b06040b 74
    0x2040309201090003078101010f040c109204803100320004052075424410fa10680504030180041c1c1041131581c42202505503000b00c0681c41c040b07501d0740c3d0000e480c200c000240c220450b007010450281094185401d02600008901800d03900c10075494024605851401442c1404c2058030010a03000d02c684180da11491680c8846807400040340c81e0b40f404880401e41c25a03001c80c080210000001d424020450402050780c0144800c500b841c2c00500851a9140399604000c044080000815508946190304400640740010350350954000305005119403861801e00258540340007040040018101b03048882050040b0608421201015181e02c03070340b64204000d5100070401c054040030610001e4101c6241c1c10010f00e410741e2039200c40d09582001840003001c00b0080010419858a550504c901b07020440181440c852810385c00b4241c5808102c000e0030940194002440303e880b10340c0120b502d40c500400c40c0c020140b02030848070804508980141113021015403071560f02c1104840034021904 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 306829676 1250 306828426 306828433
    0x30614041e0c082a01050a09031707021512010b0306091501110a060b090105030f031905040314010b040b010509011b020409060204290901050904050a0e07080307020918 74
    0x14403400844070349034481094902401045001a40c86020020115030801c052003401145a41d2501804101840140310781405020005100110f600030010000d40303074041e0404070540700c2501c10480758000c1c17010094210790801e130840242c0395600d0103442101118881e110f6180e880c2c00c070365104c42c00155800340c1c004070841c2c0854400d6030000d485262600040c5010b07100134420740a107a20700202c00308180e42507541c1d41d0b000c510300e003040040540500000d800a01380ca40c0c0c5618030302c3d624410001d011000a41302e2550301045c0d4810011100219002034480842945c0698058021321004c615180b003280380c01d007800c196500071005d0f0340714030a058403034000f02802030b07407030109c68038411100f20380c8030b036030384000f10300103005171000e00b014107103504140c0d44104160683c513001011000507030703400b40010f118400300341e03a00100b11507100c1c070141d60115854582d50301d881d010b400100c80c0030301140111b10307011800c01c800001070050203000f140d030401191200301d00c503010002c1c43c1340d4002080c3c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 306830926 1250 306829676 306829703
    0x515090705061b0109050115080c100207031203060b12190b0a05010c050123070824060d18050105070311031501050a0504120f0c090203191503050703080403061404 72
    0x30780c1c0001243c9004070b281c00800c03406015a2800c0c05c4400d0b208648007103050550051000c03c07410080d11600d8003083c0c404203144000041c0203983c50101d44001041d03e100b040020481910035000300005180d900c0d050b64940b52190220403038600110b9031031001803c08110740751800e00c140520711081c10302522046026041000440345601031000541302e80d0340b074003101d10b0b410841c580d111038410f0580341501003d051140d0300910a00002d0311040e85030b2640000794a110090024039143c14a00710b92440c0d492540903c004080c2451800954880003541081810b000064110034442c00b02d0341d4081001081c0f41541d404035000555031036240c0e001040d110071342075001c5e000408550a2a0a00d83d090580c0c5905044010303d0b038400031660b8040320020a410400700c00c1006c0082d03c41154150b045203010001000700561080c00441c6454484042c4132045604507002000780d0381000c19500c0e25522410302101071790040c402151103518019005004070750801c00180203e80c0329800030380c06c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 306832176 1250 306830926 306830947
    0x31806050c040b03040f0b0906090615010c0602030f010503060604140c0d020417010905060a0612170c0709060503191515050d050c01031505060706020f040801020304051509070506 79
    0x400c00103191941140701000701140320b01c90301000c1c503c030700c0c41850582d07000f081e0341c038040b5061000a400c107026070707100b5400c0c450804008902640d00c01c1c0115151440c518424004035260303800c91001600141c40001130182424154950a058540a504903142e0313032948401e020855420b81191030702005420081021560000010800859905009800d01380ca0312200d4865458074035810701300360754406440080003000d00000b5032000303d050040086a20301104001080e40101004201d13009800b0070108840d421001c0d522011850811180d880340c030741d941d0078010503260042601c6071144044003401c044100c900c0a1480342d01c4201d801000e00c030551041c1c040e0080620078108881103007001308181d1500d01c402c040703603402031008000d00300008001400b00c0d143e01e41c0c0355009101d081024400e076105c02d011110303e80d61084006949010340600043c1030300894000c3c1910394000020b00040c4100000e5003541c4524034815480d0700d0721b0ba001590707980c0e0020f10509400200a11108400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 306833426 1250 306832176 306832181
    0x610030b0a05030f030403030f03061203030f090b010f03050609070f1203031b0302070b0a050c1b0c03070305030c07080c0901120f121101060605180d030c0507061e031806 75
    0x36240c01401100d50340d41c0b1080000e04149002030710445642c008101042810390022040301c0c07071240350900b040030a042010082e03400d41d0101c00a000d150701c80415002c0c0d0045503026880c05608000c000035207503150504240b0810b21840260f03810311500000c05c140340b801080e124121100c0c003080800c40e500d82b103405c488500600700158185596030500c2c680e8044d484501040644036941c00594503030b200e2404c0034034804043c045403841464201008261610b40c001c9801041020107500310b183c1c405901e003464030441c54140c941600460344000108100040038002d00c002c240300303071107500382c85040e8030340e880c3d60960b1029070100000340100300c0154450201201e407406070f0107041c000b02058a84002100e60301504070005840b54518000c200c40078400d800240007a4517105103001050358205a01c0403e24190510400c2c00c219030340704060192100080c91039214042e10006540c070140504110b004074030007060805819003000c01513100c7c0c410401d44007000464080d2403207190304d0341f800 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 306834532 1106 306833426 306833441
    0x90a3810170a02090a09021201030b0c070f020f120f070f06020109020108010302060d090c060e010e0909060a05071407060b04110406051b2b1106061003 67
    0x8030080801074903070800a85400540c80e40440303c000f60001c0d403075a00c030305502440011000388400c88180054100d038003c0805c0b020030703035070410004024807801800900007081c0c21010401483e2800d0380b004001400380205a10410142c0765038500006894102c0701030f404081c0c200800c0c0201b80d0780b400603004520083c04941e00507800a044080c041c04001d00c80d16002c42d140c8801c8600e03512038521160407243c031100b90b0780d841074040d2840302c1c28554540090f00c40142200b9504000c0700803070142803650000c207401c3d0b40c3c2a00303070002090003902100401000b51500310360106900040c109d02801010001158119101044116002e031401c902d010f52082c40104038036a042000d8406440c1315120710b0382400403180915061480c951401c040d2007105810002e4500342400d950341400b101500e440e625014440c00c03c0e07540d10300c01c131441c07644030800d8050050614429080300c0f0713 = true := by decide +kernel

theorem cover : BRFrame.Cov 306654676 306834532 := by
  have h0 := BRFrame.cov_init 306654676
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306654676 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 306654676 ≤ n) (h2 : n < 306834532) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
