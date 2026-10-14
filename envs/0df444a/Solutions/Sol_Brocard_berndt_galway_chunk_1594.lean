-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1594
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:45:47.852453+00:00
-- url     : https://prove2.me/submissions/f9a99df7-7499-493b-8078-efcb35dd23fe

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 286510791 ≤ n < 286690647 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 286512041 1250 286510791 286510811
    0x10608060a150b07030f050d020c1c0206060a2103030605040908040501110c0d0204050402040e011a0312090604030b19060602010605100c050c090c07022e05180d02060403080c01 78
    0x1d811040003c0020544003494504030391401001140300c2c00038075003040000111892a1041750b0144e4504500640554206d070100c0c055500394070b016692640d0150141d031000035810326001b42c02c9000c89080707881911202502e480710202c1c0c483c0a0400b00d041c140d403080080780c070351100d1040141840c41010210394442c1440e002400e100f10a00400940350704c4110100030076140c1d184d6442c1280c1d8181c80c0490191075a10024002d020f540074980103a618041c00859402100034916914410035030070f07501032010041c1d21031864420b80e001541c1103a820001000024240402c90341d001410410200b0401c500c81b032140c09552459001c000145c1d1542c3c0c0034003072450100b000440a111a0600e0344038642030b0359800752648820415113101d00e07560000120500602422208041e0b8001c0c000003484080390380114020075032000d09030701e014010410b400028003410445800d2a00400d262001d10901d07001c0001d52000c07150100e82010741030000000186800c0c0140111010780380c00402e2120071 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 286513291 1250 286512041 286512071
    0x9200402041d061513050d060e03070b060a171203070207120b0106090b04051c030918051b0310030f030e0904080a03050c090f060d020f0403030c05060708011d0405010608060a 77
    0x204e01c45004a024100240350007040e8491052044078021382c1c111461a00c0d80c101a402400d43d411418a18000000c0c032200300a10214420b11810044900c03040311600e40b044448406c1c9050b4500b4082e5120300c000009404008001d113922403200d10454074429200c00d094041540340041c11100e00321070340b0043c000d25820228580c003814040d407100b81058605800648040b45080c5681e910364880c003150014148101910b0380946a580c4a4071200700450ad440d030000c1c8800c42c0d03c0030801c0002020079074900701d1581201d01881051360344500542c19529902d03010002250f04805201d0350710080d1070581c403001e00e030a12440c0038408807a1600c8001e13601030103442d0010840f0042000c2040340d60a1035942030a4080b81c4081501c0054a506040040388000d2250b1040d00103071008c081400801c065005150400303081c400c0003034810a8454070425500c04e04207000e5600e8117210480d07100104207210f00d103260b1090080380081809581c45504a00b00342050b030f1040030351511110707844942c0c90 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 286514541 1250 286513291 286513309
    0x3040f0303081e070912061407020f01051522020721170f0106051303020607080c1b06030604020a05120f06030d090b120910020a020303060f0409200402041d06 70
    0x61900f0b0916610f030650004046a40ca1300031914000116501a418031500d40e0002100e980300612031402d5040c12034001c1d58440407030858049544c24080007541001512130034050f108409000f14502185880311800071003801501c148a042c1c0c2404040f010034862135072000010603881444252090400000f044c03103614110348001c0f04450418001c00c00c2c00d010700503044507200c1c94055200c0080c800d2030001c100c120791011798486008100c0f403090201d00c80040990b143c000040b500c496507000c1010041c01155120701398007800c00d000140301420241c00603d8075200c180781480c9407070780b1040c06c0b00703000d00c0540703200c241102d030f0a00f0406a81000c00141d01c05c5102313402c1c41360600340b0380804920288030790280c10605065020106d2104c0100704070245171100410701c107644514030f01030000e54a82003140d14a1207504e101d0b8a603020b505061281400301600412402c070340840f901801010702a44450040c0c105c0d9003040002046001025515901a100905444541000820031013804 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 286515791 1250 286514541 286514581
    0xe012106051e0a0b3f1b22050a0f090f0605060f030c0d02061c0506010801050f182a120618041506150c0c0e011503020c03040f030308 59
    0x40c42c0c001c82e0320881e55050020740307000c0c414003041c01c0e484c0300d041e0071120310000303044084141003040300721144034000104280c0d0003000406c0c0f1440c0d91000301010403d900c1c020000d001c3c84103c14019103505200e09400250303010340007080100c2c0c0400420300d80785c00c80d00c1034202900d0f00003000504800f002058040c40e900200c04858070301c0250055000a600c411308041043d20402c28460803c9c210340b80d1006813004036201c02c54072014440e1001840026210884000b1300041c07280c00041810b180c40300e44881c44140290075402c1ea050060890800100d01400c000d0a840c2d035840b02e40b00500501c010441c01286605400703868854080c104044e078600541b1030b622032001115400c100000024902e640300350081d10030700c100900101550020011600905403140044480304441a0050010546030744903120840c1c03010366810482c000d101d000c1c000d8209109408a15620540c0b00e41c0280103251040c1090300e2070140c2c0d0f21816000741609a00844c00b14030407004020000303441044080e03001e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 286517041 1250 286515791 286515811
    0x40605030102130b090a080319030c05040e0f09070b0408030d0b060f07030c03050c0102120f06010807020303130201141207080a0b0d06050a0b12030c01150e012106051e 74
    0x300d840b8125081c002c1c48140213030740800c0340c04521030b85640c0e28150708074010300d0704c0300581c1d60f16114400081c00c480305241204012a06110308010003030300c00d04c02c4a0465184008850b802d8654490640c10944003600c3c4020345d2280c8030000c41c4010944c2c00800050601d500119034882d5000e0320841a118140d802c68491b403418800c0c207401019140c2100e03000c3e0f0389071500c40f00001e02e40c581070350309000740d0703070049401d601c00318401d0412071001d0f0760306000f000142d84102c026502d220044400301021902c00006030418004982400c01c000501102d0074414103160702100181d03a074800654001e803010207010f068000a021025030810303580c64110f0001d90f020702c903142da003c1c040b4292480f4580001d111540d02c0300015082201c55100481d0801c004000c00343e00b17280382c8400c80d6645c0103012902d43c3c42d4a0912a6904012424503040490b1044420070060ba0f1812846010f141800e050100082c0d00d04038031003000840510505100d010110080400401c41d14602c0241d900300400602c49 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 286518291 1250 286517041 286517047
    0x3010906090e1b0607061802011103070201121a121c02030c03040501080601030212180c03010b0102070b0904091b03060b0607020d0b0c04080307050f060f01271b0e040605030102 78
    0x200003030110b00281c010003070510b038084804401c004580c4ca4415481c0c0940401d10742003c40c0d10084100c0ca11450240c000d0f40c905c0000c00000c460340362203101b1007138000d0101c1d4140e03070403100d598490f40000038400d160240180303034128a0408070340003400c0c0d0408a0380d160003c1c0f80b401c41114030101d80d43e6048000703100541c10124401c071500e540380306e00c0c01401e0500213580002075130b0307a1007a0110b03103940018011001003410140059681401c808071a01400d000c0d540302445182014418034a04103016401840b40504e08018544141d1210f000503401603102c0410030040303a68070144102c4804141172000b0424514180f2408950f102d62146100b244200b1070080982d07a0940d04584058000d07041160a445804007060184110303841254075000100392a0240540452440c0c0301c0040c0c01e0540b051079444c1040160b030400c00740035002510100f200d209414854114501d14118540075002400aa0b94031640c80c103000381000f40c01c0000d44030706080c10241458000c1b580200700a40096003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 286519541 1250 286518291 286518311
    0xf0a0e0901080723030309040207051b191205010b03071509080d1e0207050312040306050f06030316110301140103122a05100207030305010e0f01150507050a0c0b0301090609 76
    0x901e848440c4e944400c030000c00c007420b407825074051049481c032642c020011503030b51040340341203a2075803000351683c92814210729640000f0306100c210021210070080310340e0203031400d080c014120002189002d40b0ba40d9a9202c7d856410345040103202e001c1d01d4078012600010802c1400209141c415030040700203a0007103c40e41ca8800e4006490803841035100e0385036650040301030341c102c0c50070300c5a60100c0e5052145109405e001142d40703004200b034074000c40d4188101d9403080c4086918510699403603405500030071410020310b08030034110f40e00c42e108000042410781d05c18002425203d04a0840102d414920010010041540201c1001c0350a174100090703044041e418004c007400446d2040700200d40f10b00342000c03c000003070005a40030250000e04646551007810300400501c400d000d0604051a00700106210040b040e01c1c05040799040c024680854010743c000f103400360800386041b2050312821007a80c0002c4c1001600d10702602c048100f168032036140114400c161503607607004150301c07850542001 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 286520791 1250 286519541 286519559
    0x708130b1213020d0209010e070e1804080913020d1a01030c1e12140a060e01032a031416120308180f0f01020c0601050103020301060804060e030f0a0e09010807 70
    0x1d9070100741c0c1e040c0800d4101090000c10000348020310000d603c0080034001084400b0b40781541d9008000c542d550300707500002c0d0001c0c80062072041001c06200b031902000100051020f40c000c0c02c4400c005440da241c9400c45180c18802d0340c0010f04412407250304c0e65400b9a4101c1c41c110f00400d854803d00e420300c62541450f01c0523050401003c001203800c80311a00b54201c840c002e00d10081c003180301a408100340d050a44203003584900507204480e00504204002542d08030050780d480c1038030303046017021700045440518a10342d619100c0042800c04450705000020581c0d00495000c160600f0020b41420204005080e040d20a1170308550300075040100b00c50007081d031000203260300c0403100c402e00d002040f580100a1904440710b092100e035124038411602c6070001034000e0309aa82070441140c0b004e0343c1341ea005600741d00090040c50009000c200000f00070480c0c80e040210170003054030075207241040b103440e085155031240e403240003c1402d0324040d035400d0800381c5110303004200c41c40207400581e0400081d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 286522041 1250 286520791 286520827
    0x8060a0510030e0f0304030c0e070c0b010e060319030c060b090106020c090a1815050c090f0f0a0b040f030218070203030606070302070f030605010e06040506130908040504020708130b 80
    0x541c0400d41c0e28503070a42d4034a000c0003c0e4442c1440c02c03013226100c5aa03403420200d00e0400c1e004a200c4020040701142c44240203c508490f150340c07004002c070041c1e081003d03a0600b4031004050581c03600c01c112500e180c41c0000c040c0382d1600782c007036a0f54001980b02c07810f000054810ba1505c3d14003508102c80100304440c0e000c00d24040c81041260b80040584a0503c24000303400a502d40d03040141d0410002c0041080c2d41045001c406003409061000d903070382c822641c0c19802541d01c1c403a003000c0b070640c0c006d41502d04032100509000b0001d04072000307035803290103900a0f40c1240d003090035802c082007000e00075450100c40c1c1c1d1901800c0224401a1450002c1000b501c80c08060314140c000d0b080455498101402132054102800f0842d82c0440c03025924100900681003c6c4107200111039040003140b42c83c2054051076200700c40c05030114042c03032088a84c240061880d48401c0e6081c010912002c0340c1c59540c0c0c0018185035014012854850344007902404082c006940a01340c00c1b1410010001c080840aa034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 286523291 1250 286522041 286522069
    0x30306040f020702040e011d03030f040201110f0609070512030408030a0c020604240f08063109060c27030803040c210516060c0618050703030305060108060a05 70
    0x1000c40c4100c540400c10303010f8007a1040080d44642006084400d035601540700b180904035140c8090484c0707502c00c00543c0c0303d2105955400007219900000360255001d503044504240d460300882c0d812070462040ca40c1000400e44c0c1050b11904250400c100510344075811005010442c0060b5182c1481c0000180d81c1380f05080e4144240b05040e1011810755035090b09440c01441c110081100e0000000442c5002e214180b0300c02000c5000c24840101040c4250102ca215000141070070b89000141c00d00084c0d402041e0031700e0303280003c82940b00c039480c1c001c5018405a82e486540d0110300b509054002804a602c4441520869500e00c098540d8038503a0001460490f9003203a0100e68945441c2041c0c0304402c081e40060034000360700b82c01e074403d0210b101c0c1c1041302d0b140503074150703200240c2d0741c0203002240c10f0350311944000491501060740890070903401286080810a00c080361900c059a4032800c0015560098001ca5920030401805507041300c3c11551080d0100d0f802d003400c600781300c0000c40482c4486c40c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 286524541 1250 286523291 286523299
    0xa0b06101209110603190f0515330904050a05090a060b0607080f070c06050a020c1e1f030612120f030b0901081e01050f071b0803100e18030306 63
    0x2540040c40110700406a0060000d03240f945d50780741c055486c2d401400d0481c00f00010030316000d070044000042c2d104d1203009000c01c2ca019100140f03080c0400204000ca02c04a02e560300402c0020400f0a20000c1c3c085440c40340e0a000545410315841000f007116001003841240746d0500c4100249410045a81c0004a0340728100288444900c001300d0154040d590000b040108002038140050f0b841501621655215210320100b10b51900e4088a450050744a004c02581c0469500d02091414040070240c50003500201424140d0510008a50541d000200c550142d00140d40d01c1c0450740c9405000041c20b41c49074500100181c50707450704800c003002510501000a1a004034107028460b411900f2901d20041964440d035850f0310203952500029101402e86202501c042a0307081c0d010b00039644181001c034030510160380d0740030381a07c1f40c0d001c10241800d240981c0c0200c130f00090440c0c0c0514041c1d0007a410308403000b8208072840a2080c4050502c03241911340755100d4040b080000112580002d05403 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 286525791 1250 286524541 286524551
    0xe030c220f06090902040f0605010e01120b0628080f0703021b1605010f0201140c030402031207050705101b031202070804031103061003050a082104050a0b061012 71
    0x4034140148248480c000c901e9041c90700002d01c0110035000402c8083c000c490170000c00c00454140021a445c502c40d850200c3c1442d6180d034259030142c81d184450802c0304402188640741000050201d62080d52801a140b214400c1c101042902600c2c4010460107410528540e0810402e01422100003c2c8020101900005c03d0342d6080300c1c036541494400710304000c17a0216070040121802c0d62603580145c2d03000840b545605441d2034070500559024210500c0d200c1c07080e40f1031100180d190381c40180281d03014410100742d407128580c0b4100a0440b54003aa015114a50502040240b000b0b07020800038100f00c905009000428401c0740710607691981420b0000e00c0020000505003c1e005024002d030200b500490004240a00d400888070701e520102c1c10307500075558692071030b0049a91804058056417200440000007004400148000e4035910411014040400d02603060130100322001c45203a04215040303801c000b201481190032441c00c0714000400f05024600034444403e04c000413144c0d68440d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 286527041 1250 286525791 286525849
    0x2160f14031609181b0305060a060b031303050c03120406060509040525051201150602072106020f0c0f06070806061e04050406030b0f2404020a120c020109030e030c 72
    0x311a501c101385078800c402c100705039004524a24828103070302c010b0700c040c003c400000300c17010420310411054540300c80440f070a5464000f4400f0340f4a020f00c1c821400c0c031408100c00b54140504101520380d00001d510b644030145000d151034020340d011030340f00500403403510092100041e0007203800c0a40840c18580c041c001307540310f044d004540211f6405140c11218260300c4c4030100106420003c03c24084201c1080c4c3c02d40c0d660002c0343c1d19020b61149203090084000d05110a44a501c45611254082d03c0051b04018860380d400c0c80983c8001c00740041a8810001c200008605000441d03100d0090705003010f180c905a40071030402c0c4103c000c0c060345650f00c0c071794500503413112406a41c00b50501610400c241a168501103d40c0c60050321a01264004000000c00420040200c5000e46aa0714181d440c00b44078001070001940001080d80b050144030401030014845a106d07c1c000ca0b0300715030020034860a00e003800b0f80b45400f1301006030f000b9000200c10002c00e03160300780c501c4905002110000401c0e402 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 286528291 1250 286527041 286527071
    0x40905040c180b0406240c05150a0615090b030c0c010e010507030203090f1207110d0f050105010627050108041b150905030d0e01030c02160f14031609 66
    0x8a4002940b541d038000d4441d03800440030352000d514400d09403001c0154079250708003242440c1b01501e001c00c1c104091401103858601c507203160300c2124410000c88041310303100c4a20403200380d030448404039a259201010080c4404c3c1c00020803003081c003410820340460a110045e00d2610005006030704003803000900c81c00000c4258010201e030b00000000308540c0c104940000c019600540e64140b0703507c1410810401e482001c10041074014036450b0042c40c100740743d601c403603030800340c1052551302800f040749041c041402c10310407101c564400c00c000034042d814048043c00c201c00c1c0030f1001510140d119400004500b031001d0300000d40c3c1c024205241959180d01d815613a0a8407401c00c2090600e00b8207000481000d41012480d603400991200720003540c4480a041d80e0f0032990946400040350482c50405a5029034800c119402c80d40c0b050300d0303028000c031907408060141c541c400304032030309680707c2000381101c420540041140c08034040c010b20001c0f41040c0f040b1085500400e58001c2c2d030303031240b450380c40c80c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 286529541 1250 286528291 286528313
    0xb0712052401021222061704020420070f031409010909090204021308060106020d17130c0f0308030105091e040611040e0106020a0b06040605031209060c060c071e0804090504 76
    0x25010043c0355500b170000350401c60249151a8000701c0600e0709004180907005890700c0c0c0c000c8000807400c0201c1e40d03e903000c01001c1c000c030616403c1c41c00c6503030a40b4581036101a000f01041c0c1e01800c901400c854083c0340090520007042c0d10160909011b01003000c8507a4401d903107108517200390901080e195858000180288100421441d00d1905440700182e100d07030204202d0304a070400d40070b0714042070907140c2c1518481400907a1140220340c2c00b00041c24038412041103e0584c1c00740e1009407489803508a00e07445113400344c0042d218920080300400941c41c15403111940b00d0002580c4034480604050603403c107a0000e00010036480e1210613000203c5500025207008015400d1180865651050040e440301030802059070032051043c00a00c540c02c040c041c0720101c2d90094000e0901c02c6010343c07071004075002004260750004003000209001e000410402c0e004056040741c99648084c0e910784100078000489000301841140000790300032502c003000ba0782c11a9603014010a00717a60310710745050259 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 286530791 1250 286529541 286529563
    0x5030a29010807030b0106020a02091306090602030705041403030a0206070f020309061b010c0e0a090f0e06011502150910020c0109150606090e1b090607050106030b071205240102 78
    0x2091000040711080010583c04407030050000c100c07581d8035550103d0321800c280001a42140182020034042d0030440e440d807000c240148000a4030406030354514083ea0310a4889000141c40800c3c140916070324070b448200005030450041d89000c942850182d00c512008044e8018001920743c2226114000c0c02107680ea11030007440700f40d031000d600c91501038041d0080b0201d4920340c60440f41c900014000c603a241602071009000c12552807401451801912040b50b10348070403500c42041344660307102041114082c2c825080c5940d00d180e0103050007450100045403503030a003a82103007031203040d400200d44034100c09190000581c1d100320790480180501640c01c0300a000061401aa2a0ba91150f82c8898156140c6030388114005d5a42ca4120001c1001650381814140c0503070b055000c0b84580c0030090a065501030072030383c202030ba03e4a909003150515441920281290b0b010040031983c0406082c0000503000020041401d03c481990500e92182c46e04d10082e200c1e00112610130780c0200510742c150 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 286532041 1250 286530791 286530863
    0xd09020d0b090f03183001020415030c020c100302040e090a110108100302190503030d0c080109060302180a0b120a15021206131b090315050405120d090215070302060f0105030a 77
    0x1b900150300c0840c002c0d401845000c843c2d29440601d4119a4840d00444a0707441c11540205000341c0401c04110495004034208030905500300400109041352040d01489242d0800103810900d9043c10510396110030351440a040040d844108a09150ba041904058a070155504800c0400f12030481003500c80a4101c298075220102e40c5110b51403483e048203180340380685da4040641d03603410002044e211640002940000e00e4040d003480514851015030703000d000c542c030104411607228041a400f20703000da14003c484c3c005050400c1400b036901c00c0b00480141c2d4070411480d14620842c1c0120411000d046188146040401900788880603000041007102003601e401782c0340ea6182c0081c0103814184004c4820382c02e001080c7e10030200c3c902c80c2d2840f40e41c20501900d8224152003012049600030800c00584c02e541c0c5250700056261341c0700f11904e031b48607d00c402d03a543c403103800e020b890702c1e100405121204070b00b40300600580e1804507900000d141e200000c00c4410b058504c00e0900000008070031440 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 286533291 1250 286532041 286532119
    0x180308070c0b120601030c020f03040b09060d1b030b0d0b0c09010e040507030c09050411030142030f05070906050903071d070f030b0303030c0d09020d0b090f0318 71
    0x1800040f003101c0b405800242c070200b00e0307180c4555080e41c403400c10b00c0484a05400510040210252210003450708000c010030312441c200c0342d001701130f00701c5803800c0902d403041c0614201c800420360140318100704500704031000740e482c0b8041d941701e20b1702c0400100f0b40ba1030403401141900c12a4080c48003c00710b084001e0007441540f6055000800622150b00c580c0c00283d44540c0002e400e00305071050203d03400100c042c0d24550780c01e081003145002c000d40402440d50480903030000d048000398010802040d10a07542145030072824074010250340400e400243d045240c1410310040315001801c50041314241d00700355844d104400006410280d8a40c04600040c1c130404070303c140f00800d580b800740b280c2e0007074036801c3c202c0c1c3d0781d07160803000c82da11a1411a0103910401c00311740d8100301c460103015400c2000704081090820b5501091000d400d004040b01c1c184130b0801400704581081c42082e2500014100950425031881d00c0300001c6070a140040d0302070030070100c140202160142e014040001c00f0300340415 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 286534541 1250 286533291 286533307
    0x30906070609020a181116110d0b01090605091503070302040c0e03011805120406081b04150305072a02060304020a0b03091b120a062a1707180308070c0b 67
    0x20186400074900174010345032020100d88410004240c9420f0240781155110b145c14647e5811010314a11000540c00305440c030341d03400001c012803802170281012000120b100351414043c070009040140c100d840003070105440034001d440c006107080c05c03a03404444c003080d584100319050b40e40701301c881e11040c1c01d0350030040d2007420080c801080c4c03c1c3c1903108804840a0b000d038103a0a1303c150040d8041c050002d031003d07000c941c5001040880c040340d10150019586400e80c3c5103100d01c5500050700240011986407000c0190042d0000490884d500588552016106181520f4021541d444000a11440002c808901951181c0d00f51030080e00f14648125079034100711464950b104486074a0a181400c0700d64086801c0c10050560800d03030111500401607025184c2e5080b0103400400002100000c034091000400d05000007c0c103107403409c603107410850f10020551915181070080501060120a071400f001c800a402e61003030840303402c8013100703881e0841f900c0c1c58070b604007a59100150045c00030460300303 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 286535791 1250 286534541 286534559
    0x1d060d060308071502040e040611120115090510050d020309190c090f02040b0405090703090c2601020406020607050a020703020907030f050a1a06160206040806220203030906070609020a 81
    0x10000fa40540018200d6024102c04c210583c07003540280c09180c0c14600103e8005401508103585203010540c03250b080c0042441c82c0705460070b00342d100d9524082a018210380341504002c880001d00420789900301c07084c91840f000340542c419007010405199000002440490050000d5982c0c0501725114086802c0982040003041e00d0701d0141d20365043c0340c440380c0404481d203882210b0440d07100303841140c01d0524100801c012070000400c0720092544414407840020140c5049501034880b1500d4400300702c9002ca2102c42c1540b81300e6506440d42e00c10042880740c0383e0001115644030006203413040c0c2e501d01e80c4000700e003401102e81c8000e41011049060202c810b0305038000b101d994424100800490341c42626200a0310b40d40e808452075586003030b102001508005000345100300309031075441e401880c2ea030702050869100d580240826001b140a00004401460b8550580c0050400480603070203503800194480c46003120b19403181e00e001440350200304060b00000c83c45074000705180c001a80d141041 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 286537041 1250 286535791 286535797
    0xf18011a0f070507080f0309010215040f020406060801140102030301031a0711100f0e0607080106110f120903010e3c190201081e0411010c0b0a06060f050a1d060d060308 74
    0x704001e0300464031a1601b0010000595040c100140e000b003401950308581c041080780c011700141e400700390841018000d41c5072402004000d00c0c19503600b02d21589041000d0f003200c0c1e4403221607030440d0810001000424058042203065000291869010f80c9801a00781d85142411042464600440c51100c12600040e03100340010a80e40200340000300504007400d0712071008075801c2e40032403010001440003510a1030501c45100c2d03070404445160031580106440e2880c10f50512011a20001d81440b42d0b042c00c1c00764002005a55000b031180050005120b95101c80441124110244c42083d403800e030600610590040920714040d10140711500045860f2105001030aa000c20030f154041607003a040c0060070300040d039508150720740545682d61707440348145035681c0c060704101c90f030b20340360f80454808130007207009900c0e40d24000740c12031501c28060303da8007041c10144140300050004400d16034009461120300070320b454042c0040710100d00040c00b01c0c004e1130b0604010310710b80840407003000500401 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 286538291 1250 286537041 286537049
    0x306180112110402030415050a18050a021c20030a06060e04060507020303101a0405030d0513050906060a0c02030127031202090a030b2e03020f18011a0f070507 70
    0x2007002d0300031280b00b40700581c403050f01d0081c1440440200b8060715142075000a4121014040c080f40141039100e65448504c41031100781c465810101d81078085152560610141040018840780011415141c1c42c0d46810300c00c040c2e012408014184107059a8140101c1c0f801e140e1043c4100005034954880b0143c0041c1218201e41403443d22011030b40260001007540d12458404800c152818102424903c003c0d038031900240f1410024000807800e5642485100010310180d51115202c804418200001499540c45540280c44490a0001300d8032600200c0310892810b040003810341000c0c1c07000c20300400080165000030f010301042982e014907210000190280039540d0304034110300089298080388549500d01b40d010f01054800c00000d010408a568416841228050401d6520f03207400c0181c3c9417201e54459112a03c44244210f142c00c60940740488030546103601c10300c10b84442000c407600d040c02030a80e002102c101f6041079440e09012264a0011103140300d440d0107940c54240d95620013405 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 286539541 1250 286538291 286538303
    0x50d0c0810270813150909110301061b050f010506120c030d0c03050f040602010212070302130b0c0a170904050f090622061406040501050a0311060306180112 69
    0x44010004010300a4400200c0b0400402140c1590701d0004101c803a00300c003088920040500002ca604001480004001d081844144030307034014820008064240581081840f02d14201000c0700c2d50304c0e00d000b502e054402500f004489560741d04158000b81044500040c55881941080450400103400c514080c0c0e030165011100340108400d92038840142c2000c203038043d0f0186019103141c0d8401e04207a03001034000d0800c140703060400300c844411980b1540010016030f400284c0c00c22160b050648017940002c0314541141001c0a04404806501c0140f1414a412502080f4450501e1003030011a5200e94480d0720014030f800d6160a60341c058001d003a43e144680d02c0d00c40041d2604011402840c42000018044c0c603550707903642038038101e11441d20841c50106011400f0354001807050b20480c100d003a01504a51040c1c50301100300302c140d942c160400c5010320a03104040000481030829079000e54000c4034074540f40d940d41404218012800542081440d2801d000001c5400c5401c55240c0d107140204 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 286540791 1250 286539541 286539553
    0xe041109010f08100908070f050609070b0a05031303020f030a110601050105070819091805040506010f062001090804030b010905090319030b030705030706020d0806030a030504050603040c050d0c08 86
    0x15034002c1c4001280c820094030750404001c41e043c050641c3d012164691046911604224003500d420644d440c1481e82101c443e4404018071107901010040d00004102010300302d49810f80301d0200800c2230001a0a807034016260000d40030426000f40f000c0d40fa50000c10040326280c200080d0000c1881c00d0719041c0480034060200081003135403043c4121a503550b04118450310304092074108038916104d0100302402c020301401d000c01c15040220030b8030040c610744000031809e400d09007800d500f4814182d014101c10070a240080228a42101810040040c119031401c4285c104070b198602500b0716007002006030000060100c1081480404103060303414840c02008996900c0da0780d56680c0c45202c1221140e01030031130f0030010151194104d80e403140400b80940b01c3d0f00d5070700d1000c0f17840c2c0391540d0458405a080394107a003045a9022440d103604c640128028080c2e400170703890241c65841030b80985405100004005001d100520448400406010700882d1105003581000d15210391680100c40080c0105 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 286542041 1250 286540791 286540799
    0x40b041703070f030807111b18130f060b04020f0d0b093607060207150203040509040204090302010b0d060615140d11040b34051506031002071b062d05040e04110901 72
    0x501080c1e48550720752200ac1200d1029911056014880c0c0b403004c9500f180c55003640580b503200e50000c1e2003004594401181c40b201e0480e8040705403070206802d00e0160f81400104030056145a001d4004101c80786049041c082007064018100c210b80c280e034a0051090100c00039042e0b6000948808a80000c41640b8840070a040103d88911662182c241c0c00701b0403030045009031410780d1000310102d01c6400002031840602e000300d1000c00640d60180c820541c0c035001000400c2c00d81c4800d41040d007452821034140c0b0103d0320491058026004804000755075102c0c56a0041401c01c1181c02424516031100c0e242c0c07036543c8010011001044a10010811959110704031901096a001806a120300a00b02d080b215104102c2c001000612695041c0308074000c0c41510481c520040c50f03a24065400341e2049843c1c0d41c0089011140340d4801000c0000e40c800d07a02e00092a01e480c1d00d0102480c4d4000f0000c440828412107080c0640e400265490b200401400104268000e0312100900709490100e044e81c1d132 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 286543291 1250 286542041 286542079
    0x1b02070803040b09210a030915020f03030414070509040b010305280b06031608011a010c0305030714040902120604060915141203040b041703070f030807111b 69
    0x103a200f180c0742c0040074000e880c654908084200c0300701c010f420844032248644110103143c0440705a0a602061340305009200b0700c04800300d00c813002038188c0018005070000c144115502d101c000c0014004d07042009682103800d00500c0900010200180140001e043c14107144d080300c6001e110844540c0304298680160400d4420715060003c205400d19100850580700c00d82c00c05001408903505003c2c0c19074070704c10881165400000341980100000d903c0400381011401a40a10300e0706043c00b9103546000c000030340c1f1108907a4041d4191600814103440c400c3c03040058015900003146650011a01c14220b03001c1500152092200311400d0000594420703002040310701ca684504806045001d003484040c000101c0c4120142003c1c0500315a61102a6203d0450304036130840c0001e110000b408102d0003c100c80c080101402c2d00001c2d48c0703045460f60b03890941c0f100034400101800708041c000358016000e64050440301c2403038800e441c40b00030402e902003054403100c40180d20500240c05c030140034510f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 286544541 1250 286543291 286543297
    0xf04080307050c070801060803070b0a0b150d020c03033412020f0f070c0305060c0c07090c020f0f010b19030c091805010e060105090f1e090705041b02070803 69
    0x908041924519281c40004403481c0c1d012151040852251070400591060244641c4005000a2018680f03580080c0b800030740c9100f000d804020442e04048030303481240c0c0d4022240c1d400400101041c0d40c1c1d41003420040d0302038001c0300407443d0a4000801040786502d0b0303110841c0e10521021078104154405650210214102c402105001495040403441e016802c2c3e030003040c1659007840e0180c1001106607500c03d0680c4141d0007242c03c1e601007403041042000400c404e80d00040d030041c0ca107080960f0111116515004ad215254640340c07038200b1580380034020312540c8111203010381078850107144014080d0107010440401c6004e440c0d0411100c0200f49400c00040949a00c02d011900041c50031f8201409007001104000c400030390090200c0c0010000d11903528840d482c0f4020f40207542c9010100004000010007507240c0207600ea0400840080250324112080e510003004001511500081860034805400c280c4c0c105103041b4205490740411100842207070079039030840301004e8890011a4880c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 286545791 1250 286544541 286544543
    0xe070516080a020c030a050a0501060f060509040b0a0512010501050a061d370e010609030b061005040506071109161d040f110703020f032113050d050c060f04 69
    0x128080e03088000100c4103030042c1100103607481100d600741c180c0000a0304084403d40101c8080d0b100d10960020800c00380145401001c405280c0c3e03a40518003074016100340b08451030b16100f113030f072400006002e030355000003407014000250070b00e52941d80600707049009050030f014080c80f40c0039204000030720714450350000007000007060303541d5580c40c210800d11a010b18000c1c560a4004051b0715a038040c0c0a000e42055101c0f003102c10103980031031401100c01c44400e01a0022001c20a06c50801d102164050341a5500032009440d4551640103a003411101401b81e50880755100c080010000c041c850790707101c0401428030482d40b418540c0c85a045148944a800c0724500114100082c020310480400c001b107800060090030114180760848001c6080710f0852110140040700410603800f4154100b001e0016905c00078019031030301076014840c80001c42c0c0c41c00b5201607010410001006040e8100141f03560940c801e080f100203600c00f440c090641c0d040039188202c14403503800000c007650060518103020b1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 286547041 1250 286545791 286545817
    0xb010506030c09060f16030c0b0105010903171605010c02030a0e0414040b0a140708090c180105120f01021201031a040309090c03140f0a140903030604150902130e0705 73
    0x2090111007403145a4101d41001c0505e10710601400b00c41124410700704141c01d10950341c18441d078070075240200080c00706820960410040038400d10001e13900082c3d441640d10a0882c0302d440701480107400343d20501c20f200051041d4207100501c410b01c1e03000030141849001c43d4032582003210341d040510048400344002200e2180c40719000c54040740300503861710781185404e0b2001c2158840ca50410800c40c13070030744142002420980400c0060075060010800d40b5400b152000d5410070300c2c0d040c400b01c2c0780041c010540306510750050540759480030000d1440220201d0000c1d0740310300b0100711a05e881d80d001d21051310f000c2000305600d407070b0404168040340b14603450385844d49068209641e00c0010446414400241035030b6001c2600c03510a108140341c4652250305620301d1504c6c1c1b42c0191000c0d28600500d1440c042118000c3c8600d20f403001c010750794000020390b0002074816040f00300c550a4451688510b060f1880010007040751a0540b1fa50001c1e56021303066052982c440100c100e400e03200f100a0702081c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 286548291 1250 286547041 286547047
    0x51f0618021809070c17040504050106030b130c0507050a050f010e070609060c0f0510050a111201050d080f0a09060e09010503030a031e0614091005090412050d180b010506030c 77
    0x2c1031a026040b103070013541c1d03444d000f0851400c960300c95407460050041c81c00da04c2d5000c54104047e2800340603442c0500864541070003080c00721004550103c03401042c541c0041c1d01d81b900203030f5031403050054424594021003140d09029403801c02580b04e0180c0740c002c5100d542010594448400d00080c801d0443c0c0039599014841f41c039040c0300321075820400787e04403903680c000a00c410203d44200049a03600601450000d10f03410702941c1241100c3c10112403001c50740051000d02c00c1050030b148540d0444100780ea00d0040280e9614040129115202003551480c0001c6803500f40e25034402e82c41b400351034103925030803c082c2c0901c0030889000c0b4244907107075140d4820880c44503150f110b50090b82110211011a05280b5603140041007528040c2e0080b241008000021603842e1504007003c81e008a10320701c3d0040b90300c0c1480003185d036403000104040e20320640364802180840c410011501d0b0940da1203020099483d011200103910132030710009803010350703483c400400e482c85c0400c2102e0003000b0f000b12040c9 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 286549541 1250 286548291 286548337
    0x70b0405060f0a1e050a03061a070b040615061e0305010e1519090b210c100e030a030c140f101a0307090605090108030301060e0409051f061802 63
    0x3072594401c1c021641080912001c1041122888013140880407642d02e4490300c1e80805c0000a04403140c03039100017083e126881801c144070500004443c111604a03014080d1541c0d10308110300074001440e10f05c0844590709800040140e40110481450107070052010540da1850034110142c030001e004501ca024449070104103e50040b070340c0f68030024000b401e540340f0901080030300c0150344403503840656001c0d12030101c40b1442c6410f0340052a2940c840034034080040b20f0210480e0380e121441d08050187d15640480d04115014000044182c44000c040b02c04581a900d8024150b150410007250106180156683e854901040342c0309001503440c010030100c030340c818003040500320400d449115a2800c185420854a0a1180030007922401001154580c608028410810230590104c44140c0040c8014488103500001600a0b04022500450343d25042e0808505020281e2448100ea0100b204c089080d070340c0942049044418494541e00c0b03080c2036032202c0003a40309540035032000c2d800341d615581c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 286550791 1250 286549541 286549567
    0xc050613020f090907141c12050708040801090605070201020307080c09061e03090c0d030e0105030a020910020a0303050a06030503191103031029090d081c0e070b040506 74
    0x180c1960700003811850102807441c080384240d501540d500da019002080148a94010802c1c19001190165800c000002c0c252013100740b041003680e0020710072080c1c1c40d0012030541c4280242e504454101d0400c0396259500c60400d8001d240901048074210b0802000605181c0188241c03886440e03d500d8800f41a511019009420f03408690095071111040c46003804056014098144007040e0000d0995a4148590340074940380034003060030f12070000c1903400c4000a43c418002c6410003c01e09107580c49868440f0031102a005980705543c0005040b01400882540010074404642c00b03528200301c5516001e9540c000d581260101070110f0b0b000b0050a15030301011401c1030340d05221854050014841400c201d03041d87d2054480302150160310505101910b040900e0702030019050304600c140720340308400c0c40041d0080346c042900c641407002024060005120440e00c8081c0340b0000d00c006c00815100c024003c0c03054100b0501d980c0b15916000c08c80c01410007c131819030754014a030a0910b14090481 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 286552041 1250 286550791 286550821
    0x2122a071217040e06121006170c0d0c15021507020309011107140d06060e0702160b040501140705160f080f03071e05011104060302030103150b150c160801020310060c0506 75
    0x11b00054072525403203800803070f0f043c8103803c003410381178540c4429524a940e01d545803c0e5038a81c1035100d400c4103803459000900325142c06044454056081224480320075042e4285041c580380071000418280c1040a840d07404401003800040c00d80b14a0025405070720b005076540760340c0c006c810380b4050030b2451000381d11b0078102200c903041c0305800216500e270301c0342d4080480240989986d800b5074426158102d181d9003450b05400070700403105030182020b02d0000020309071541020320a82024001031540140082400760321040c0000d5601e14082c81d65441e8010b0800060b4403030200d1a00544c502010468400b0084804850300281d04900d50304100200d0f00030350354011004c40e081c1d969240b480700c1c1040c0010103070004201030b440c0183c40e03614605251180284032503042840915050403614582c3e60511003e840381d410000841d2034030040b21074549411102d5100f4103c14843c81400a01d0030070540040d44104601c002c42d01c00c141e640c40c0d00382c5044028400043c420380000b000615a01004c00b59 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 286553291 1250 286552041 286552069
    0xb0105060d06030c1202031b032d0d0207050103060b0403020a03020603090a0f0b070806010e010c0b0c0903030304081b030703050d0207111e04060602122a071217040e06 74
    0xb4075a40c1d968400c007403411107610024156100701a0001986018025590114500c1444040409445001036103826810801c420443e02001502d01c1c0308801c3c081c0d071003c6147c218200d400c1c490b922280a947c0f11140d00ca1035000034146034010641840e901c0580303003120b5014040d00c1240d0b0955080201075000140442403502c90324151801184408200100301809186004424242600024603d1000414041c184240885000444d0743c0c0f0080c109030040d0001c841c500c150311081c040f0000e43c412a4007a550503c0084180410f00540c9070040041d0014145c0d603c03002481410495185d00034200060041603003840721140305000341e001000b541d40f0900c0501002183e0500150400141c010026003480e102c91140903203040500c2904094040c03800241050528000321345183c0c491401081c2e0030424040c0495403000c18400441b0034100158243c60502d500c07100b494a00c100d40d000c00780d4200351030000030198400240200d030180c2c0c1c1c1031010b5100554407807080c00030700105940 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 286554541 1250 286553291 286553317
    0x30f100b011b0303060906120308040f020609040606021e0105100918240b090c250f0b0906070816030e0703140f01060b090604150c060212220b010506 66
    0x42c008042c202c0101c840d801c903a01c03070340300041c94600f0216040c040300c98680002880070252104c1c4404281c00002c01c079845035000c005285000c90903c04141d1500401e4559070b00181132035000308084d500844d0440e5030a520200c0c0d02c60b0b400740c00401d40d0903a00c00b9a0004201070400200f80000c41c01900203211084000b01c16200d500c6440e583c2500340c0c44100b090b0911307410f110400c20003101c170602800000027411505842e050410006c1e2400f180304203109010384448148a8080d00300e00700300c00d440c000d0741214080564092034102a00c84e030200715441c209a000b4440080c807514011400103021b007011039803901254040c000d041c2c0050504440410b168070901e540040040c41400c40400a0b4400d00086c022214848042c2401d450f055045000682e03070030f00c1600503d894490039503080746c0e8055082c20182800c00c00503158860004006003503180000789100c00900342050341d230300401e1006008403001010f0349204110203000310000781a03450140040100e490000c0c09003241203417182c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 286555791 1250 286554541 286554557
    0x7110607030201020c071401031401060504170f0304080114130f0201030e1e01020c1504080d1e0c020d11030310060f030b0a030f0b0c0304050604060903050f12060f030f100b01 77
    0x10242a00d4564147d00140f03560400105625855925014094000034124000e1036554180716010f4818000d034001e1900d000c0c520f020800b030202c0300b04107500c620029501501d5075035460b0344003503000e4068146d02c0102c208040c0c0200d24a0305400c42500d044640020401a00e04095070044020b4a80f041024800380704800c006410348403081d064031b2640c0d003400001030ba29804c1c0c0d0141814000056030000726542c3c004200004030f0075160403610141c1c000d090005020920010f040703180d13800c4040003583c0e40e14000c0107043c4e0a40024101141c0501a241c0003402c4001801f6641d5034842150681c1c0040c0f80c040c02041818062481d510201c1003508010641c11240760102c0c01244140c0d0094400c50021800302e02803280c000c6459420084102c0e8075469440c00307841f081d5590101900080a269441e4004424948100c06841c011000c030f00721300d680c51141c1c11203003500c09025208075105038003c1c0d140c6a0640740c0001d2812030341a04001418542c2425103401006000780034100e810701400b1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 286557041 1250 286555791 286555807
    0x60f06031a0106090603060f050409020d0c0b070c0b0703020a0b04030e190f080a0309060e0f0406030b0402041d0a0204051e0103030909060603230a0e03181201020711060703020102 79
    0x9012200c8160504140d4421a980f61000081c070804940c4d0082050500d03241c2c0901500c005480300d03800341c0f40e00340c03000b04036407100384042080254880d02c0a400e000b580c0700c0214203030b0481c4000b23080060140703403900c01e025210326484e440c9209408004000d03920076600c00000441c003500b01584140030307003445000412510007203080b21700b4182105181603e40003003800301092500100024160101c0108042c0d01d5968000c2c11031926802044280903d440c40e02445035a490f075813003e00c030800350041c80219641d10b030106800340c050386e0880c403480c1012012503a0414580b281c484418402c401081c6081060302444014280a40100c800030404841030440e0384040c980c0f58000d620907503503048007514004e000000c07242181c2100080509160244200c1081e4010b00d4040030050400309000c0d89600303401c2002070181201c005101c1c000426070f4010f070324142c01500740c00301e0152040b40035810b0300b42186080740b00b03115005040f04061410b84150f400c1600180c18400e2080c0001441e240d10 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 286558291 1250 286557041 286557053
    0x24010212120a09060f0207050f0c030d050c0309030d0f03050f0415020c100c0c051501030308040b06030c0a06020c01030605040e06040803090a1b0510030207030e010302251208090307050604060f0603 87
    0xc00c0b122244c5c5400140340020020304221408840d0305136005490079040a00001e920f40016a040d10308201d000301d4490f8800009208941e51003000038100c5160211007003000c3d00d5024400410004245040001281d0200d507111040c401c0d0381c0040d030b201d0b01c8014085a46c00a410a4041d959580724410a00034122518810604801500d46039048001681d25105103400060b2980e03640c40d81d07241d00104002030704a03060b59007082e448502030305141d469001181c43d0030700000b20ba503840000e032038000030078035008100804946c00031f0342c06218143d110300c28007043c0c4030101903d0200c0d0740020005804145410095a000403d540070f40c0c03540c55243d01e4548054400c12031a05485412703440c20441d030702d4101ca401100d144c460409508040080c0c0b0040c0a010b440349500381415000503d804503550400d1500043d1380604a2a20308501d03203042c02c401c2c050041e001207011500710404038001d904008181e4010b10f51150040c441581d0b10360300d80015210008880240d603499080120020b51 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 286559541 1250 286558291 286558301
    0xa0201020c0a11030f03040303080601050928060806042c01020f0408011a0103091218171509010b0d06090c1503023f091524010212120a0906 62
    0x80151240b1501544030303010103003004490541d40160364004c007c1040003c4c0c0000116034007001c00d0811a40325440c40e40842c440310702c0365401ca1150131603814410781d074403041c502c910142ca2490b071b83c1164a0341c9080a0200326010240f144044800110203414100d204140c0229103c10140000d414407010301d0105105d5001500300744403030307515903000d00e40702d0340030300101e00c16140700740303014003440d4020748400d1036105c014109002048042e90754406900110049a0000d02e90702484040ca401070b4800c00c0e8582082e400c8c400b801c040b1000104003184014080d0000c4030500400300365000c440c0303645103070003000c0004c01110b0902c031203036001804042500200340c1506494034056030b034402a20400300c10003d0071181050752868a246000301411030000724015401c0803003200303d60340355505054175003030340350300f81c914a000700c2c60412921688803000c03900001064408120058480360041e611580940b000140c0e1800c140101030f40c15504080071a0090704950b0001a104095111103007600c0c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 286560791 1250 286559541 286559543
    0x10f1104030b1608010e070c050d09141816030e07060801140d080a030f0f06030303060608010806010b270301050f19151e090c0e011706010f050a0201020c0a 69
    0x5011030200107000e100081c1591040d0320707240d007030050919104040c000b06818043c003801078890000040c20940945c51411040e50000105c0d0646450214000e05050b000d02030303034200103040750409100d030500b0500e6001c81e54100c010000160781e03102610504480e40c458160406488039002100418240000340c00381c689640d03140010342c142042c2c00d0747c03280007040c118041c040907034240d4007044503142a44c47e00400c903d0040b030040150305090b80a01482c050245070f01d880c0c12000420160940e21203012101c09482d00b2a00743e82e140c0400707840e11803d115806a160003001b04004039544d07042c02c240b9801030300b484900b0a030111008a030840d070040310990520071000040c801d0b44000c8072070041c01d250043c0400e1041c2c641c00725804e40042d0561280304010314245408002c0512851940301c007034850321074204242c6000c80d03001130002c1c8071441351a0101d40700691814540601a0100c4c0c4180c1041e1100e083c0004030080c02c583c01e5000762a142c046540c01c2c061004030712018843d0075055 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 286562041 1250 286560791 286560821
    0x108010603030e0d03090e0c040f0902070605071110050601050c150702010b0f13020313050a15111612020f0f1006120515091e03030a0c2f010f 63
    0x401d0a40c03038090314666681010701e225082180d003c000083d40b114450041e60a10f802c00c2c4820b8440110f001d1050203150030014035514074a102280000842e4080d100c443d020345001e1000c0d0702c2d201820749555000042d0010250040b04c00d401c054101a08159000035040c0340180c0780c081c65040160920002850000c0c000000c03400348154194240220340320580e00b158690342000c1c440c00003855810a203c1c802551580200000741e0110341e2404409a403034102c0c0568540d9462817604110f5550b00322240700071546031503d030301c41264030201514203511801d4000c04909509454030b10841c2e16140d80c0200f140701d0300b8111005031071f080c0188206090710200404401d0002c540c02c00c00e0701c2260704002c01040020340b104012440029462144414040300c98005454582107036090440407003032100b1017040040340c144a07290000055210f10300c010020400010780150072110b00e41c02592490500d058070044840e40c5140c40d02860380c54066400008000c01101c91940640740114900e41c04 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 286563291 1250 286562041 286562051
    0x4080705070b0306060d11070204020f03070f0c020d020d060e1902090c0f09011d0a0b0d0506030706020606040f020405040e070f0801050108190201030f2a050c03180d0b010801 77
    0x3004000c101030070107007100700c11690540c9440c00c0440c0c0c960090403044289a900c03455840d181e0340340700080340e1003290040c3c0255902c034203681415138903900c203a0740900003415403014402c0e03051040c10100c010310340c003c0c191616070f20150204000665410000c0d50729076a00d00304100c400c1410081b00a02e0b4040600c0c0c09403200c91401001b818a0380146003243e81001001034150340e1155600300e98007403409081441ba040324213021b01207804541c09800740c00640644010a8a00c5140301030310332148d60701000d0082c2d68481c0141074a8409a100c0c010141c0c0c8044040341030b9103056003210781c1440300d1440050402c0d030b0b21800a000d130b581421014081341c00c281c00501c2000c50218086d4041c10702c01c4d0082c401e652520700d4071640c40c400c40c03c1519003440c8841d034042c2103a200303030041c0d561010113440078444100400d4085284085c2100350740041900c5840380c00910b0301503c2900e010380d0038040a50b00b403a0f03499112000080100c160140d102c5050000900041c240c010a44d009e0f01c8043c0001030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 286564541 1250 286563291 286563293
    0x1e3f060b010201110f0301051207090203040606090501090e070b1e030c03010e071803080304020d0639051209010b0a140907081521030408010213050607021e0a030803040807 76
    0x1086a00d1248120800d00e410460160905c4035101141e045417000d40d02000d40d40d03001900c07241003441c1904600086400001400280065038001d50b042c0c2c0d010101c01c02c41d0740d0382d890645003110112000d0b50320f40d4200c81c404002d03070190b080190070a00026401211180300c4594210400d80c01214640d240103404030051100f401d904072181d504c0011401e1103a1071500764140c013181c60446210003450b030080000003404644400300070120b165031103030050090002140182d4011940c1d20307600700b210f03114114a40c0000500d080d00c1880264961070780c030300d0540798564410a512000b018403106649801e40010030307468405000006000e41501846401400c400f00305c0e1095000e055681041254014051400001030110200010441e60341110601062405d80303e940700309081e5046000100b400a45648190010a401032038440311701c090607114010044280540840a904002281e0000b5010b005c450194500618010221802e51b950303580c440d080d61f03004a80440d02ca48001c603101c4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 286565791 1250 286564541 286564543
    0xf090a0528060f0f0b03010b03041112060402150f0a05070f020d0c030b0a15060305040302071502030a03052212030f060303031d070302010e012a03091e3f060b0102 72
    0x1c1c140c4d0350048841d00c3c4c07806030302ea680b500040c05107800d60ba00003c08103040100b0344210559405024201142d0780b15100007040d00c8241c1120180e00412021145240c2014901c0071501c00000b040080e50500030030150454207600b0001c0c0483d03001074400180320161340c2d083c0d50038503000d11401c0080c107841d0851a000301500005006044207909001d00c211040b05c0d507042001c1078410034940001e440d52035040480c1b404c08980e100350f040141021018044030390100050aa84120b0b450030b0210303403500c0300d81031411500c500c103450007003d0a0081d0800207801c0c07441c030541e8607a1032502085103000351440000703ca1003540114007282da180c01d81250200e900035100e00c020000f8010300b1419113142c0018001458440005041002103920804410315050000e4141c1200e1036000c2d13002802442c1c0a40b2840003070090800101c02d9040c050010b03031614450800791540c40c0d10060300c8444540c1807031030348000d0111441084200c00b81c0600018400301c0000301190103800e0108402c81140006 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 286567041 1250 286565791 286565819
    0x7110f030f1e070c090c0302070c090e12030402090105091e0702031810020a0b09070314010203060a080d0f051804050702070f0519030b0603071203020106140f090a052806 75
    0xb0307020310040c000034000c101d40026000480d0302c84000400e01c10f61002c0114002e2080900091601450440215030004c4da0361250280c281c100044a4510f011050240030320300084a00a5001103e03100500c001e0230001c2d1541d800081c0d110001c0c5032a06055800d442e2014100c41c0c2c4801030384081a0221901c0410300213504046050724043c00b50715803140002d448420f015009004c1d0a4984041051580b04005039002190080140c4130141383c8010054040d5005481252098100507004a607202780890389810600c6903440d195441c030301554058409800000780141120510f008003440783c0c655004e260b11950b0558040c00c001410308840c002c4403403c0ba00484e0045c001c03205e1030040603810310542c109072070304071140c642d2642e00d42001038940400c580011840d031920a410108154054000d413040d2641d141e109950703c0e83c100184070300f4084a445966020301d02030041803a80742158801904550a0301d01c03100031550217081c070305030344c02c1d5907110018560340c80e0b00411510170a5130755 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 286568291 1250 286567041 286567087
    0x12a02030c09150103110d091109090c10080405190b09070f060504061821110102150c0904110a020a0506010f030305070b0a0612060b040507020604020907110f030f 72
    0x1901c150b50808075511503540924a10342e505060342d41046d40b911a802c002600c40742035036000e051010b09201c0c03400c0c0c00050f64043c4a103001d032043c0b03004035062490200c0c3c03d131080400500060080c07940381000b2115400054000c1d240303405080c815404240c24003c1d2540c044c0d01030305001240e4140802c840b440c069450740b1000a00c420100f090020540c41030484040b01c00074680342680c10792608124114031110f07441b00500244603401c400e0414003000094211601641c141c6401d070446000586e1038a2815080505480c103190010701200c1c00030000d04040b06001d040003440303801c0300403241c0066000d14110005684015005c6080020422134207000d40004200725001518695000e40b25008162004059021490000345140c8150380034a00030400441818440101c07070600f40d00600a444081d80180d0134007002982c083d00009410740269070242001180b0b64500c94101d45402200c04d580d00c060150304810580200c081001c0c01d14134039030740300d810f5a403840010801c030342110b1500 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 286569541 1250 286568291 286568299
    0x140103050d0216060f140a0c02030d140a11030c07081e1908030702120406170a0c120c1b060c030c0801030302100c050d0207050105040302010f02070f020f012a02030c 73
    0x414681e0a0f180110440c0450381d85080900070201001300540720741d28207110001c0441404075041d039406034407141c01a0214000d50035030740200c41c080d80403280d022001241b18403142e010043c424070f492250076484040400c0b0015a400d0690008107942090010f5000c0407a40e8402c0f110401406c403044040e01311181140014141c41d0404400303044075185091001c1c006000120015082c01d0090040308040e003240100715a4654490002826060f081000109071500481c0002c00e4400c00c0e04c6081004038441d100c0c0308026502010741009007042c07014a004100c44000211440c0305000003000b1200d00c9203002150488070b0210060803a100c8681c5001001034150040000c690003180035800628801008100340031081c0055442c1e10407000001c2000384001503100034044194071060150b44284c1c005d02a80b03402c040340105034050524003610842940004900602c0d00001c031a5940d001030400c900147e0a882c8481c1419000e4900801d00c5440c050b040c10451070180240c85004008072 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 286570791 1250 286569541 286569553
    0x62a030705070b071a01060807031a010203030411010302040f170c0306010b0307111203090a050f01020309151b04030f03080601030504080901030e0a050601060504090605060a020c22140103050d02 86
    0x6200e01c1c2e6030b55494890b02d903011a00060902c00e10001010190404c892a00340c42d00b80c2d69660740040800408440d4400001e190426000c181c0e40d1058000d62111016401107041d40c07500c0d284d80266841d00c040c1103040c10b9080000040000002110340d004218010584442c00600d0103190b00b848480d84155100340c004400602c280202c000aa94000c10341c4d01d0101402007840a815160545005101501400100420855080009260f06000e00c03d030107172140148640d103624241d0000343c0304888160010f00e48114070a60b10013a041e44180c660410903102c0c03110304000c010079400fa800540e0700d803c610324004289034200400c15040f401c2881d040255140c6902c400306240507118281d0304040c0ca8096030740b003060007048000c440c50307002800d403000c0b9603440ca0702070850b0380140b0601031203d007001c3c000503172440d000083d1050b0481503000f419201c1031180800c0b0204507010316001c1c400d55090714006103454140705130101404050803007010b650642c20315038600845445194110341c030034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 286572041 1250 286570791 286570793
    0x1060e06060a120204030203010f0203040201020c0414070f0905211908070809180f150307180e0703050d0e090a29010e030a0605060a060f1704030509062a0307 70
    0xc41c00c5511141c218038107200283d0900d005500680300320f60000e540b640c2002c8010341c41d846107900440c02280300740c003200c04248114081c442995160900125050b12440004000c01e01800c00c0c403100010602c0c01c0b0b500345446000040d042c80c0b00071004207806444034240140308000300200301c50604944d040c00c542c02c00030368900045100b81c0c1c9004140000104145119444140c244200b031490303c5000012803803d10b4401c04d00d400c0031911280000303964020001941408604001520881440b140d11000c0c10090080688106a0400f01c14416503034008082041070129020392510307507032903103100c0174440d00300100c103a0060a13018460f446c2161a00e01010202c00040e20303000e00c0b0b0007075428292128016950000b41440040e01030091500d40020460140d011601c54103045407005045a162181210840c90800c0000041625070241009400d040f9807041d910070700c00e2620500c0e10200b80c021848075040800724124066551400d00c034113034808503d0f50101c00e5400015801e042c61 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 286573291 1250 286572041 286572049
    0x1603061d070e0a030b0f06040b041a04090201020703020a080313050a05010c060506060f0d0f05010603020903030a0804020607060903080a0f02090f240a0507050114310b0c0c01060e06 80
    0x406481c0c00705000b5110b1078804180c6440840d0402150011502c2c9000d203881c0801424a10088510520983c5030030b04040c030f140b906100b030900c0c80110030341a210300c2c640a0188001840305003020b90551041d21400801640c480290344050408403010350b40f03503009a4941e1240085540026200740b160300010700040c2d910007031110040f41c010902041c280c40f09008561030f889204000c1140000c0012081210203280e0003041c00d1202181080101d85c1c0d999004408900a943d0042d905400030403003c004240303d8034a081e0414002040d003860308503566509030807034091341c4049001c114103c007002100300040c4210030140e40c400c0b070198500004d04000505d25079001a4082c810001e03c079078408070505104c516103004103024140d95481110500151640d00000411211513081050303c148058512503100e0083c854502c90100900090440c1c5401300f0000000b555401c22920310b840104800b0380b00c0c180100c55035801340d540c40c0c0c41052120f0a44000380c11420034118040140000ca0311 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 286574541 1250 286573291 286573349
    0x1030614010c03030b06040b090109080102071a0417030717070804032304031a041707020a06030504051006060906020d080c0a1b080705061509150f0a030605160306 72
    0x10092070300d4200b0701c030145011350081c070722030b0622504a030b13000c580400c1d0b03107404000404101009813540c8042c140c4c0c40f42124240d100f000e0000f01240030f03a41040e510800b4804507550080d10a04490901d01c5101403140c0c5144c00840d840f4000410b41d0411a801a200041d842d4101d1824a41500685850f0310080e0580c0c11010000004504a07062807190301c01d5442900c004c2c50340281d80010001d800300c500200c1074429102903800140c40c1161b506130f2030204080303800050f40903020400d018078000d010f0f00149001401a22540219114a109140d1521840d805850181c403088000c60800400925000b0607612000a00000708144640f0210b0002540e04010240c9810040200d1440c01048001420701d0011b01c20342001c1000070401c100030030701d60710500102c0c11100d808107122041110700ca50540b00040c240c5030010040e5030318100302c0343c1c030f1300844005024010b030036070b030303036075800100c400865100c50381c2e580c2e0f200080620340e41405048001d1903186020300941c0505d54160721081 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 286575791 1250 286574541 286574579
    0x317100e010506071133130503060103031d0d0816030f0c03080612070503070b09040b04020403030f1215120b0c04050108180703080a0201051501410f1305010306 71
    0x10400020821440d4080c4c600d903201c1b004060809000d2140326000804d41e0420007000c1030120040744d010a013414001041812240c050392084c0c0f000310138980c20300d82c100c3c0605040e504580c0107500a00803c810100a0031030b80d0000004900c10011400c000341003446542040302000004101200441d034090b141c0c94009804850451031580e904686515202541d40201d070107002c0c0102c0081d484203500003034050100103035402c1c0f000c150407500300412840b650000030007003080c80700072091562185001140b02c490110380080c480149c5410070000e41030681c0103c1d101004040014108083c00300750580010f94039407064101400c1a0029100d644001d0000582004000091085c07910811884d0011754000071059982c00480390024068001110104c00c0700c1e0001034000819481a650388030240c024600041c4402040301012120022140ca115484200315601c061246a2100240619001c0d00b201d2035445c0081e00b4880442d1f03100d41c0c0b080b03041c10300d008000c004c52413155183d04801c0d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 286577041 1250 286575791 286575799
    0x40f1a060d02040503120a02070e061f0903060f0606020c0f03060115020a082a060108060a0b06040807060224100e040807051203060a0e1306090317100e0105060711 72
    0x1041c0355940c0400074003441c0d02040d40742c800c1120102900c0c0c1300f03200500003240107902343c80e0855200d1400c06d000f04000e403801c58010b0080162030321841d10320005041c400743c451400401043d6a6145d400035070b00312a44940035241d85d8442080f030190100222454030350305440d008910707414200040c0e1100d030144203400503602920500c1c03101510a004064a00d9405002c0329110803040560b00300502e041d44010290880b00180340e01b0640c800680306049a810000802c02d540d280000d440251102080003038101c1e8080c400498403003070500441d0081c02d441c1d4010074401011180038204071961808030f124000e078000c00d00c5140c814890300142518510070310b090898460b407030045e080c1d2144d010090042e00030003001c03d44108419000b54015082281d00561385070300d9511400034188140d80c0c850030350110a2082c030004196030880c44a06005c0d06002070b001040c81900f1030401821100252084100d200501c01c0c0210307070241c130b03025003801d480c00390603e441071350340d501c130f42c00b201d00c0b4a881 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 286578291 1250 286577041 286577047
    0x2070509101a040e0a0b040513021e010909020d1b110a02010e1807020109030806030706081303210203010812030c120405100e0a0c0e0702030d020c0102120411040f1a06 74
    0x20310b5440004030b074001c0007a802044014a007580c9101c0c010907602c80740c548100e040101080503100f40b40550752084e6002400595401c0b00c101c00342409803815000b4506102505c480050300700ca0610142a036401d0340b000c0882d40500c02c81c0d4484405030449002401d00405240384035000c40b0000b90011041d81c2820040c0e000b0b08641d00066140760142d05041d103520312007040042199041d002111514406d4480307032403e407200030401d81c1301c80503030141000040d09000000c0005510100d012800340c007908208680381d00c8032541c913598151008484410f150008010480901c2c104609900303d15070b82815030035810800d09210992007032038410001d190070390700402c050140510403d91005040f8100b00884055030000759140c5510203010b6400d90f010355400079242c01c581000350b1040c0300e241e0181d4a000e0074031a84000035049454681d015650030701c0a80009400c102d450381c0560f001c0c052083c500c0080e00e08000c182c43c3c0c5040c44026150804440c101014500350459051910844030b10792 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 286579541 1250 286578291 286578329
    0x62c06132325030e10020406030e06060604181109061605060109050c0409050702100204060e0f09100312020a201908030a0e040b19031e0b310507060207050910 70
    0x1c07410214a04000405d03200080015155406034030510707088002d07209840060b0b4403075040040c180103600c0f0310b0803c00d560508454a09606d98004000b4010403081a801c14100c4408901c0b030390015402003e0f0764605080c0c400030b2040c1004400c1c01072a44000a004c41d10b410104507205006c1c0c1c1c881c1c0350030a520b403030214003001d0080c49480800d04180c40c04644035952580010064051001c4460142d5030b00c1d85000490300303100a0840c440c540201c00c00d8039a038655525511504541c1d10319504602a15500c400000d8140b080750f1042c00c2e0066a0000081030501000707802c0c1d006a40d013001501144c1420401a0720100996407240018107020101440420100b400f5003018076101ea07003ca05082d202100e80440c05a00003501d004244404603140a644050100c2c550851302400c40d610312000900c2144034924804c483c4044103e000449240c404810140700e10f102c40c0403101a08200b2042c003901d641000524000c003800c0f00c60001c20705003900310640c100e54a01590004062800d0300b00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 286580791 1250 286579541 286579543
    0xc0907020a051005060f030c0d030f11060106020303181c111005160e03120418020702040905010e0105101a0c0c1c06062c06132325030e 60
    0x8030002e0708041a21090000781120038002e00044030510310503680c84907101a14100056035045000d80a4440349520100340c805035403001c800d210002c04c2166500c40c0026459007444114024003581e001151203082c403d500340740b84074550303804c0d900030703800442035901100c4200d008034140281030410000c013107003c00420307013000c2d088002c6a49440c14103060001c03a0701c80c40c81001c6071040d03a40c0c9401408003004201a21141003511aa082c11006d2106002e000011a00641600c082c0140140392014035400708041d1140a903040c0d5059544550701c0754800800e0041c1e07980810a803280001c2d9a0414511500812000343e8007010302c1c8021030b0681c021941040402c0316450700414203800a4a400d20b040c501070501c80c1f0031038140d41030040c0026201c0d0740465001000b14085d00021001103c100c203180000801042070343d00902948403060b042a040c0f0450447c1c80043c80148440c0708032402002010070041c000b03450f03990f2019020443c4907100080b402004545207404901c10302c802d080d00f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 286582041 1250 286580791 286580803
    0x427030f03110c07050916021002030a0b090106180f050604090b03030403021207090c0509010c110d0206160501050609010528080303180c010c0201050f160f1211010b030c090702 78
    0x24030302d01c00c0c002407041c0740c43e1002406078225841101d5048417940e44d58010316428031003500000150780f054509508040503900910391196403801c001480d2000c280020b01140c6c42a404036020400252604a90211a01d00c00002d00400055692001d00e0715020170365510840c482c1c0300f0725075580d82c101d80e080d660500455005580091005241000f841011a1501c100344581719806c5e00d006402a10300c0d02550a40c1c2c0a03440584076a280d0004c2900c8104e481c0b180703030700340f1070780b05820b000740600580d640e00103822158641660144400e8181c9462400c480c40a4400c52290a000d80100a165600c1c1c44084a0050794003603904c0340d1008103504046a440e80d0420040c5000100c01c00c0a4140040e0303d19240103030315400c80340792802c0a801900c40c0c000300030020f800501d0820881015558040061580304080d4400c01e64010041c0c0301d55888030701000c3c6c00c0b203800d48150701003841c003540004200c40b050b044400801034684d4000c006a903030030b04000c586001c3c0500b9400680b66600070701503 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 286583291 1250 286582041 286582061
    0x1110a03150f0b09030f0c0f090c0d0606081005010c0203060604020c030c07091401230405100819020301061a160804032004050912120c071403090427030f03 69
    0x1d600d0035203d0107011840e80003056002e00074400e200c030400130a140080c030340d000c0c203002520b101100500c19050020040000340a0180e8071010001d00c0038480542c41802c1c000d041ba0b6a8808460400c0441044a00d04c660301182c10082d541f0002d60160750b001c0382050b00810121401a41d034480c0c800d80314158047c6840c032150714060780f1000181c0103903d81009004920381d031284800c581e01c0d1005c030348101c9601070444650480c0d000c6500d44a003003d034041034000a40150000d90300e80d4038030103140740c0004806280030720182620402c046007000d00a00c005080d01800d4018800e240150304040c60255000d00a00c0da10746c80c21550a1210361011200555081030040400c4482042c1d040500b20f4a0800c1c0d0380554603007400100d1070140801d0000c45c0c152144245460020302024404c440d0402500c560000c6c101000740000240046000a030141c45940c0610385401e039180400c4100c580b072015512a1150855210111b82c0307441d841e103049507506042c125101816401c04030010014101 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 286584541 1250 286583291 286583309
    0xf010e1216020d05071d0403080a1d1f0c08071b0c05040c110708060717090106171b0109032307050418060f0b101b08130e060301110a0315 61
    0xe0b10b0018041c000c11001700380c40504614001d545905102c003240ba010071138000d800140c0c1000428901129a04440e4020002201c40c21100030b030584100e00744505524614004040d0300d18120310030045000307107031801700d83c0e0510107401d280810340079241c0c0f01ea03808516601070304841e600c3c00700a07181d100c400103030901030b04c00c000c485400d520141c0205280384907501130f80f0030140001030101000409038030905440d40e4902480c014800e12014441c03001d0860b603200d5403280d40c04100b4180499032140b5a00181c00103198030304800f040e04000011170703800340381003002c248018408036011942c041c0c0c6080c1c1c1c41110729500350310081c0241c2042c0e0b07242c00195109040005c4144892100211002c5881c014002004000b40c081c00042c101c07103800025542100381c0e40a81250302e0700651800d103280382240b00d80b428024569503904c003264003541d000390004600800034000c0ca00d12200450348084103134000c1004582402c1c104596001d4148803c1c00c1649032a040f40100d0300c031400e480c000b00701e003030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 286585791 1250 286584541 286584559
    0x11116090e0f07030c0603021309050f06120601061403090f0a080c0c1e04090507240906020303130b060d080403060b030d0513091d16080f010e121602 66
    0x202020060301c0c9541c04124984564000099440404522002200d900120307604d5a54036151090700650000c4051454400402c00300042c0d8041c0341c010b0f84d1042600f01003601243c80d1000412079084c1c0341c0c41c01140d5651200c0010f005040c1c021803144000503198400c603072a65100c1c4000d030315041c1c06d400070302c94a010300c1250b4001c2202c0c1c0000f800210000000341c60030082000280040c0001d005040f4a4a0308030340d4000c3d00c1c40c20682e004446035230103807041e00d07600c68891003034004400020580c040914038846903100302a602488900241881e1300c091407941c1440d2942d05c83c2c07800002c201800f40d60309100441c2040d624503010404160f44064102d807030f1380d903e08041d8001c1c524501d43e03e00078040d120b503401d1000c0c410401c44800700084803510b011103082c4082680280031501a1000d4101c0040d00205000c1c0c040142c4d00d072100c8801c4030700c110300341000c8401e130a090f059840c1c400144c1c10404203022080e80840c4103890301a40d0f07104941c42e075003018041d6502d0b080c02e031800703500420301c2 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 286587041 1250 286585791 286585799
    0x3020117070c2d050a0b09121e210a0609060308181906020109050606010219150b0a09021321031d0a08060901050705190302090f120a1109010302010905011116 70
    0x4140b185c3c3c058001e10311003185a9620701d0990721754013400c44030b0281c04400c11a44c2e007005810704056005800041c3c48500f0041c0214044418103290307003800030783c65403160801551030315038000d4001404100c8800d000c4680b46680345542c0c0d02804041101f1058503c140008a4840c0200b8840507844032500d2100c0f294ad40310040d0003410440f41c144c489010702000104107500009030840038040c075104040904185442d05580d1440011420041d15211508041c013641c070960514041c0080e10030061b9144603004101600c40790550110500c20106e10751450764411201a41d400aa094100148070406030200400c2207034127400c945030700130003905001c2482600001c015108100c51002007000303440350311054800c3c0c001ca4205402041e806011000b0040c4a41c014280300240030380504000300501000a501c1d14040d8400c00075544151b9000f001d02880c81080809620251800c00d465411500020b00b5600d240c020581031010300750417140c03d4034040001d89800140c3c3e4800075400381e02e03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 286588291 1250 286587041 286587043
    0x6080a0f0c0c0602181513090b0906060d0e03070309090c0320091c0b06011404230d020a08031804090b0714070b0a090c060201050f0601110304051903020117070c2d05 73
    0x82400007c2803a0182c54011130920030610a0720f0040c00014140d4040e43d44810403c12558021206a40310340c2c0c0b80c0c1e84070303c502042000a8146a4840c1c0c0795080180d06244c852003c1743c8540001c4002c0500b03210b4090703007022103c90801c4806c036200704a15500d501c2c0c1c0c07010440f154003400703805000c0d0300030507030303031010b001e40c000d040741c0500400d0b41c07131800700f07040700840d00c08038000d41c000c030f2414681e210325100d5500302914a520103006c0c05000345074640300c1d580028039501c445500100803a00001424115541d21403046184000c01f00d800f0446840151181901035000400d1502840300d203844458901e210001502c0c601540244061098074080000b81c0181000040c101d407001100380020034424010301945202d0100c10b03583e004940d0364000110b0f021460182154014001088007003601d071a95800601d81d4014002c04000980c51440010710042d543e0004025000d1960103101c00aa4040b00c54040c0941142d42c0e0303090410342038420800f000715400c06040301c01c601c03d01d1b0020048 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 286589541 1250 286588291 286588297
    0x20c09041424070c230f100c0507110a030f050d080a09081602060405040f05090c040c090b030717070305060117060a060503091606080a0f0c0c06021815 67
    0x20040151521000c1459a40318140010444030101088010002d0002c40c484d83d000c507a001e000302601000c1c641d010b076051104900c410314910150f040181c44a0409804010719540760044800410010000d024028141d01510000401c6001641e201686944c1c98044101c050740e0081e04400e0400d20034a8101c0d51030300310080c20b0010800042c00690340c0100b0b4410741c002150807a40c0149000a208281c000702280014200d911810901c80450551103920807480d0390b0301c82510000e16800e113800c90918040b411960306100b0707410000542c0c182039205492404031030450b100341c6d031282c50308002680d85010540000d000905d85000700310241c1d51542000e8085c4500303803a180e0752825400b4150040010481d0b115411407030740181000042d2151000b594010030240a4885560b005e0a0203801103c81d40d00c4580021498428000c1c82c45481c428110707000311954007002410745905026103a0701a40c0c00c050300305940464040c1c0101c081c0200804910801440c0d1407180d082201c0c2201150 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 286590791 1250 286589541 286589573
    0x60705040305010e0105061c0212031c06051c03180b0a0305060405070923040b030102160c0b03160f05120906070e030703021c020d12090603050718060f020c0904 71
    0x5130900743c0d0400d001d041131043c6401000043e140181540b808181985a210307603d10498010905c5d90184100a8040c00900180d0900c054903050211810030745400b07842d09a0441807051141c0c0096403051189903031040300c2d06070b0609060305035541400001402c1840b60b4026003003100000b42003010182d05a00c49881032030102c2d4100405d48406104443d0f484c200e00070888001103402c900d05981e4a6402070f5421414020404038001165201003801e82c0c000420302c00c952618400c00c41d041008081126018020410f0180c0c114906828940550002c00c010075040c8684000429036242c840c41c00c40303040c00d1007100c001485051201800742e4540044421400154800a940400e4940480c0603404c580d0014555035007141c038018044128440c0b40d50899103c151441410001941000c1c0d10310783e45032030b4070341002c8180b030003001809451000f403005d410000e50041c44003101040100400507602140f03030039804050441c4007603203051090707070034107078801014003c0108201c802100c0031408 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 286592041 1250 286590791 286590793
    0xd0b040c0e0f070f020604170310051504050f011103190e040c0206090c0d02060d1508070e0411100c030e040e030d06081507050a0806180901090c050316060c05010e060705040305 78
    0x340b1044c001280c0743c140540b07004042c004070051003048044500d000d0340d0041c100d007032150146c41d41c075030014282c0d0000c0070b4078418049011404114a18024619100301c10007070a06942400300c4180c161340384e11500c0512002032100b201c4150901d172141c2c0c40b1b210744034000707030007000001b15444001c2d560340310403600e007450391047c034400c85450b0928030500510b0640c050201424400140c1e4600d001d4503910404810140000c0000100440d00b08551401888101001c003818106405c1c05010320f40e800f54614020308041c0c03039001038280c1c4414007480080e003629060003124840340005002c1c1c0100401d0361020700c0046095043e43d1103660086084030502001c50781429042c2090041c2c011080f580c88020801c1130000c21041030003011b5a903400761000340a800c00c104044030944031410256940050f0740e6450044004015a002440025000072001401d01008456151b0f0040300240681c20400c21003001c1841003060035008003000300807000a40d8464684400d004045801610040d946 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 286593291 1250 286592041 286592057
    0xd1b0b0705160f0b0d0216050109030c1101080103020618031f0c1e080f07020313060c23030d09020607020a060e0306010e010b04060f230408010f05060d0b040c0e0f07 73
    0x10f08041c408a401142c0707100f4001030510061030103880080d04003a00003401c20442c0304070140051001e01c502501c403071003925908455a6103041030414112400d180030306101c886001400035075141000da8000c0c000c0310b141c0316080c600d088042402c3c000c243d003d00341214040d980720740e08a8001c0d04100020391035692501240d90b004410b82e00224003c0c40c1201c007090345d1b9030114004910031150140c2c070199030300407a80b808005480400d001710550b0302c80000186506400410000007001e00085c030201d060203541c0d0400c500007010344a1141c00c1400381d01580c3d804030001103403110015909155001081c104815540d400c0107001e5014185905200340035400002c901940000c50080c1a1151034802c0d600f011b0402505480e61045480407100f40b0008610003170161801c10a01aa0f070310000408079160f034500085982512650441703244e06500740001c100840d2140d56900707d07200d40124440b07803a41c40320b00f00b90007034a2031034228591800c400c004002174400741403103a502880c2140ea440316 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 286594541 1250 286593291 286593299
    0x10509090f0a0e19060b0307030f0c0e06120714010e0603151503130213090501021308010b010e1302030a150b13050d050d031a03030c01090203070902090d1b0b070516 73
    0x3031100c1c1c42e400c440c0c80000307000e20f9241c0403c9031507200c803006c0344010b4221103201c3d07225140c180946080500840f007201012230306000c00598000150340100d4150341d05503035030014242164803640390b4021400780c0032006000c1c0d101e43c1e202e90079040c0d1a0a010300055600d0030040011541a68410a1203000300100803141881110030421a0311a00f0315051460b0b40c41010f500b00a41104404507810f0800c2c3c854090364041103081c40149000c100c0450841030340342c80c2c88102802e42d51000200c0e4180011681c0b10102c94590000a01c000700c50740d200141c2e0f9030756428a54004010b00340c603022214a11b21004200020075800034100284114030300304c1d09507981c00411840320380c1500010300c1c5070081410314034421b0083d080100501514080c0918000800000c6890346e0000800ca41042e911140e0110a604003400400b0140820b004254580900c510102b080c0d895449002082c5804104c81c402d00c85884280c500040e00004040301e991300a40d04000b42c1d6941307040d1302c1191821518100007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 286595791 1250 286594541 286594543
    0x40e01051908061636152307060c0507030908120d020309100515041109010c2301090803160815101e030603120509060414010509090f0a0e 61
    0x80356a040000c0261380d4074840312920f02c8401010305001e001410411401207031840c00c0e850300f80008106000984465851030216050031340e407294800e81b00180c60042510b0340701e0740c540002c050b159843c034000c06042d10010110700c503c0320302420240c50103442d002a02e0b803020051090724042e560310041c0c0c2d5100d5121a8071010660404691034508002c0c598074084187c001c0e56004503403400380c0f00000300d01040c070350079128200ca0010038507406046141452802c0c1c882d290740e0f003141c0c100d9281050b06403400079142c0786000c000604600303a00d01000c040650125040e603484c401550007031041032540d14000c4529081070b039004440405c109004540144142c15551040200c154407492581a90060020b920044035174070040040c58600504032402c4419490130044055a00251245c40d50900c10104090907a00c1c104101c0308020055941d642c80381640c007556a4178418140007100350005a4403440b5444200350007512250030000d0706c8202c0e01071280305085010043c0102d40c04c062030030b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 286597041 1250 286595791 286595839
    0x1120515150a0504090504030e0d08030106170405070302010503040f06060b09040b060306240f12090606031902040c030608010e0703050c03010b0105030408070602071a0402100804050303070f0212040e0105 90
    0x881c000440504c01000b9058090708000c1c0c22038020300345241007c0d0034070301144c1340c0c84a00c030050b200c1880000c0104207290740180c1c42120491440001c11440c1800e50b0b505450340543d00c006410060080041801c0c03001171001d4881242d4041810040e40340c1d01c807100e0305c071504020320071403003a4603143c900505414076008407440350300010450264960381482c400e04c5141070348807040554000340100a0008a4440201308403121400f20304554602071820501d4410004c10aa009400c809030014406103003c02c6614066412180452460402c01c411001450560700143c40c542c00c10400081e0381d500403800c901038038015000c1d1440203036201e0501d4280d40b0400074080c00120b08200140100e08003002400c3e01030711030040585020b11540340c6500400c0d03e900d82c1c00c40c208101080c40304514254900c040910b1160608040c10300d0b007a1500d80d100d000050101d414080307822100c04400d4401d1101d403c11b0b10342a08010b40312901e8218040301d6500900842c0d000e000d040b01760940081d420586 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 286598291 1250 286597041 286597057
    0x5131502100c02060f0a0b030a0312060503010603230a06091103011103070c14070503030406120e0a0b0402060304020d022116150c1502030a020307020d0e0108150112051515 76
    0x1c0c8400e40390708414585405c0b0051201d0409035496002c3c9900d07a40a104292916000b607642c1410000b140e040d0308200e03462688924401d1b807400b030042000a07011008113007004806020150031086c15a003d60a08100c500010f00c1c2da49081c42d170300100001c0802f4141580c1c0150000c0017500306070b003164100c2c1d20081c0c1b41c20f00401d41103402c07540003400302940e009c1c2131402942a0f46101c0e540c2d1021918640198000c1000303d158002494038200e002d00c80c8001c0d0100000040c03480c0c02030781d101e18001981c09407011303000c0c07900000000d0a5488404e9071011195000c0c1c0900e40300c40343c22250260701e264600310042e941c0104d100c1c501c00c800c00452050300703840d40408402415030020b041540c0b06410900b0031180c0d40c0070751841e8801400c8a2000e10b100d5052842c025030399140c07004000381041454896038051041c4141c0c00e080380d0341d00c074146c6d9602141110b141400000d804005940c3c469107842003040090420080000310b100c02e00e20a002d40e50103807000040e20581d14005c1ca070074011104 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 286599541 1250 286598291 286598293
    0x10c170610110d0509011704030c021c0f1202010b03010b06040528030807060e010515040e0a0506100303030528151d190603200105131502100c02 64
    0x458024545103260100d450002d041c0711600e1403003a4010b50504034122407641c045800424403011070b50700040c0d1024900da280440c4075440c9171a9502a0490140540107401481b0001c28081d000020302c54910f14660423034190095042245004a06105c4403140d4100550030200d0f0150582014007480c07641100c01410241024201000d1118020701c40c480740b0051001c82c1414190500a40420320180d40035000e0103544000a0401c10140d40c06000100745a070314050800019120803450f01c004c151049a01140341c0e801c42c0929031401c4040d030409086401103506000b03141414600c450700300c82c865181405207a40f4040310010030844000349804084601c00515a0f014540d1701c0000e012400100d20b0b001c2036103d20605600990762803160119010717582c28072900000141c80b0012400305103270180181801e69031403103c0c0403201c0d010094040c074110003065582e8041c43c15248441062050207500c40d640321035a9610201200d04c440c094040d00b050983d094180c0e000310a80046150 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 286600791 1250 286599541 286599587
    0x23041d0a020d03050915040504200d09170409020405030609010e10020a0912050a14061308070c05060304050618030f030106230c07050a080c0108060d060f0908030405010c 75
    0x50240400100b68080803010001c0070014030003503680358040d40000104c03140310350303440b1400e20041c0401c4612244a61a03010442030354154000c5645003200c4d20380a2002e00402d0440e07052500710080c0301003000440164030081004915003946034040e01c11180210101d86e559100c0004041c205c800380c100303c81c0142c02070115028089465001040358100c18a82400000c1e07861604003040b0842d041e040380c8542180103800280107051310300d0900b0011003000341c03900341003541440d90341440156000702100c1000c10107000f403064200001d401020b001d8560355030b925041c0f500a858100c11107481c000507604c0d00801a03000c0000064684007204503142902e5039007800000c2d00c283c034004030042c0c00c0c0c5403d089510aa2000b01d00508420201c2d80c0080c1311590902c001c020706443d4036008081c407548101810261a0381c001e038600e03007102c02034400314840103840c00c10b18094600d2880c400085414221104100142c06000707521a40c0110000c1003007038100301c3d0480d044043c49402c4004030042d1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 286602041 1250 286600791 286600793
    0x1404060f03111c210f110c04112809080c06030a0203060f130b03011113031101020f0d020c0f040510030201030b13050f01080601050909100207030923041d0a 69
    0x6100192903168001c10b2405603580c165907043c2192402604040f080280c40000ba8203068105d90a000d5203d41810a1551286040d030701950342d25110081c207100e10717224290000c9490154044445d5210648541101c05140e070310071251001c0d10040308400038070701041c00144000040361840c074070380c0000c0840307183da240d0100740d90280d0801b401050b0302442018480d030450ba41c01c0081100850511008220310920604242c2140d10780060b944000104004084125411030645000e60754000c011400307001600c80101c1c036001203a9114000c521914411100f040e03000507419501d40c0c3c0c115260a5402d030700038240400c1c0c880c199049100003181800510040d8007a40001604450103440c0c81d251040c10180041511420b480140100c040080148a541030038024940500801d55001d1203a040c1040c520b560fa4040d601103400c01c03903000c036251041511032100e6400400c482c00c503810800442d090f10007015035000313400728811880c120301e20740d507000d4407032915a00c5004c91000d072451105c2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 286603291 1250 286602041 286602049
    0x51003030206100b0a1409060a0e0f0103110909130506040c2102030d0c030e0a14030106050405040c12020d080d1b03110f13030803070207171504030c020a0b041404060f0311 76
    0x100c0711040030700d0001031105030503d2300c500c0c0107026800880e07542c03112076502c1c290038040a1466000014100f505000d140a400c20074202100c0c5603130420b61310a5450303562000a80c400a80451005005014400521040c8a040e42118042d9500c0c801034032005e2500e0b00740c211107a040d0200c025017540014503150320312405203c100e01050302900b0710034401001170000424594158100019180100849180c03c0c2000d01ca5000a80400e6904100e00d003019200c41c22005c5041c400d040804403000d5202085440b070403888940c00340d000380301f40d0700c441d006004e4101070440004002e841c02c05054a481d00d0130b202c1d0040201c1803294001c1580780281505100e04998814446244d120407601d00000025084400551043c4c980794040d01005040412a2417040100540b801280c1c2c0301c044140c1d40e004900820710b80140e0b0500707040c84c5064061002c1003203198554400c07441d9002c0414001802066614041041e16084408000c610340b104511400440e481c0070140440411142c01103043c14 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 286604541 1250 286603291 286603307
    0x40f03050a09050a0b0409150e010b0d24060206090d121107020a08010608060a090b010608090f0105090601050f12060703020702030304090c030207060b0d110603100801051003030206100b0a 83
    0x11030740c81d1041189403101c2c0407030490000c0c1d038045001590b0000f010003c0f52418481c580a04030101e40410780589008082100490306008604102000241c0c01c0d03c0c0d0405a80801d170344c46031101c00704400c80c0c0610b4004161301e00394403980c2d015000382c90025500040100c0c200c0c002940c503807520018000c1024902c0024050182e000e440b41d1002c000b60b10250f61540c0056004007040000410703603908006000e410400094219483c81e410103e009000420f86e00000741900e1240c503004400c1d5a034180d0141c5821503c140000684d4a000240036500c071000c5034547c182d410668501400d01d01c408244101d0328900e41056035150800004182028403070780061a2040c001800c1324200390f242c50344042242c1d00c01c0c0c048004070764001840c80c10004180900c2400c0c032004c032103950400300309031251030052070301c00c41c003c0c071950380000040c10020441ca010380250040317800820140c50042c280349200c1005003c25005407040d4800074203140005010170041c2c0b85545a81d07030a0030820582651000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 286605791 1250 286604541 286604557
    0x60e06040b07051305120304030c05010504140d1106190207150e04090c080d05030a0501050103020903030a0806010909062303010c1407050304181a0f030a0f06150b071a040f0305 78
    0x240300e5501c00201940c82c103c1b00c55600b0740d1740307002c0e41c0c0d59031445c600510381011a03401141400300500040004113006c1003028010304090340e01d40c1d80c0c54a01c4c9402c0c0403401156604a61240c80403854450140c00765a42402840d0700d43c0860303100c0354556800a400503d180c10010010301c2d44403130b030466410150040c0e4502c510901c2408032594495802ca410003100c10b11a800007031f00032003040f05803106405468010a03007070034110316000499021035100d202c0c090006007130140c2c003008a4440e074455070140b4000c1c80346000801400b52911a00d040700582215a281c10f00d01450301180540f80c1071107844114100c5440380d00310282da1200c2800d05400c00d000035a420300041c080020342200c030600400c02ca1070f010b4400038203124054015000c14002105440c0506e1607050040880e450000e032040d001d07900400103440d4681140f6041c1c01070086212154460903c00d42d00050080c0c408000d03120b100d105000c0c403803540c040c450f08040f840c4401ca4015101040400207440072a0298000305221 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 286607041 1250 286605791 286605817
    0xf0a0512030f07200114030a1a03030c0f010b040510030b0406022818030b24120d080906040503041802090d0305190509060a200613060e06040b0705 65
    0x2c020300d9622240b54001c0101a01c100044e04040d41604200d241101500300003420704180401e034080c0ba0003114000204440c9400341e468103009407114480304800031038840241141c3e070b600039020940f40c0340d4808000180c01503080c9444444186000c0c0521886054550300b00100c55256484420003110090026210290308000000156800e1100940d41a8004d00c0039040c10030342c0f80f001054151100d400000c03d690b190740030f10006900a802c00d41002001c80003c40c80143c9031a003803820980d450302c0d15440078841510000e030020100d92111404078a450b0303001c855444000300c507100c0c4001c0310020110f400402041c071080b214110b400a07401c4140c1001400c044000002c940f007583d40c003505501180010441e64601c038000da03005650020b0915115050040043c081240340c028154881c0500c000d501c0081084010384141c40e118001c000101c940b0ba05000f90002c1c100c8500880c01c0d50000d00700340ea2404449000039809005035881105000d241d514490102c515400c451492004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 286608291 1250 286607041 286607047
    0x180f0201050f0f0313140102031006080709092a020a0c0510050702180f15090609040201050c1905010b010512130206090a031a06030d0507080c03090402030403030c0e0f0a051203 78
    0x152400c0f0000395100f00b042c1151041c226009041800d0701c1d403081910070006a00400070801d08520301b007e003508480003418400e1150312038032020b840783c1d17005822208480323144c9080c0c080700311001c0600f00f10100c0c1e46082780054202143c012619040c0c030500161a000380c0304002c100d9401d188600344102032041c07070014180545903000134004045c02601c421a20340742c106000c0444a1854105d420260701d00141034038608140c0400e00030580180102d118900d10381c005029a4000e500f181d000c14901c3c4c0a8600174114190a16450490401700761681e44c039000b0300e000103501680c102c8160010000305070995544000e601c140b0a5204a004c0382c0282043c4460710080d129046124081c500c504040b1071040140c4644c0e94145100404052013903100009405040750010101c40c101ca0304a402969980746048c036003891803040c4001a9080342c0300108105c00d00d03038113501c00782ca40c030070554556036800013400400100400044015a020441410801c600d10745103402c034911840b284d0a50703007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 286609541 1250 286608291 286608307
    0x52109010204051c030201060b0c0a0609060e0109052404030801090903110105090a0b09060705090d030507120905131b1805040c180e0f04060b030f0a050106060201180f0201050f 78
    0x4900510b042490958500302c0302013a041540a01412014103070100b5158200f11038295103e980765410003001d85421307550700b544c1c024080c1301d0b00500e11302c14100380217010131852445c1c501d640b10209645600700c16950000c6c2c03104c110080f60710b5401103401d5560460180d003024a80c000811200e0000c606206010b041403205a80a0282e030f44034007113080192030220311605000010403c000d081d0300c0d42da0404001c2044e441e03008001d41b0081a02501c00c03084581092030240d038036118822024202d0088020710458072607021881c1130030341c0d4081c1c03455200011a801000251454441d00c0d045406441c07803c004464030400382c07482100921602e01c031a09a580004c5000c4a90300482280080c1208080b603928283c401525402824441280d040c0da20300300d03100c201c84440107080284059210b00c00a0016941040151005010a41a41c0060b034151604600034102c9106901c09942044640d4100584485d01e0044980e009810380102c06e039154011521a4890100c0c44141c0345e090046071 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 286610791 1250 286609541 286609549
    0x1020a060e16090203010807141302030c070c0803030412030b09060f01031d0c100f020c06093001060f030206120703061212170112020405040821040c0605210901020405 74
    0x400400f1100c50060382c3c0e50414284a085c580240c000020801d5141809000f5840b07211582180e504074110043e200d840b200800c60f0300e440b550b40e02a180e426642404141c0180200045010b688105000414140c070414142c054411320148281c0c4151202c2c001800e5050140182d45103607414500094000701c0d0940e120001020080c600005030701920382101e060030b00c2803005000004c64106140a0f003428003001b559100c034130114a00507440444d940941f42c0f100b0101c0c0c101d455890f5800701c80300c0511a019012032120450070340456081180c0012801d40c500108019207401404c52843c02503031201c40514410040c00c02020140d0b11400000e00f03610242d01d00300540d103da420280141c51030340f401001c0080000500c8030340f001d020f00400c0360650040c800c00c5016415038012a1640c0d841c14856070720701032030112a94101c98040c16041c280b1186451501c9030b8400c250205003503440703800c122500c0c06003c04025035000300070181e13a840e0310800c0c4115070008180c8000740c0340a455070045 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 286612041 1250 286610791 286610833
    0xc0e180421020a021512070c050c0a12020a05040605130b060405100210050c0a0813170a050417010501050603040803090a1506032102030901030b0d020411040302120c01020a060e 78
    0x144005030800c03043c400441c6840c0c210050051081400a400c0c000c54030141c500540300541070703074140b0225070f40413400c001081c010124141d100400c0310100a40c0c80c003600c070001c2c20100d0700700c0c490510100045a82d00c0c0620540c07040c3d80c009000303600340311246182c940040c070510903000d0b844841404006255558907506d00d080007440c0e4003a25542c181c00300402c00359100030700346203010701c03050281400d565400040e04c0d0b0b101c074200000c0c903868421800c1a6903006000890011544000606c150200750440300510498820217403195013008401581c9080b07a81c2030281d658403030700402c0070402041c4904095604503c007272040d40c440e6030103503480c1a003003909880d8162856884120800c10b00015090940d40c210256010740e108900d2000002e4aa1041d801c8a506269484003140429110007940c80c41ca9540900100301d070221903240b1420b980c00600c0124484c54859240c5045100017003403045c480c802c1038005040440541c0d4616010300b69122503d4a52710030180240818a04115a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 286613291 1250 286612041 286612103
    0x11030d06060f0507171b071401090807050609040504150e0c1309150e031225140313020d1509061802090a0b060c100c02010c0e1804 58
    0x1001409500d4804040d100b03031094440402441014081d03000810380900040004821150000356a9821540207100502c01d000c0048010701c2a00008070390f00360039100c0320702e40410980315404002d94403080103036a071205015482d0014401d20545209090603048150400e00c40ca003041c05d4a2030b0405100c08803a036031b2003c030219074080c01510040b4140101c02f00e00c0c0c9141e42c1c00038468006141c590800c000c0c2c0d40c080e150906a40e0760036500c0e40b91010f009549043c89c280e581c0070000c0c181082915040354620310100446400403110341c1d00d00f801072288c0d1a2034140483c4080c10b540d200140c1d0420040d0541090b604540c01d032030703c50300240c521046d5441c40141c0500024240140b030804008841500c100004014034400030040540e4402950560089043c4030110302c03043da000c08240d5034010040f500031b2512410b04184042d8801e90460403040d02254002c01200a2003102152603410114031107130040da26100b01c45409c1c401056242d0701c140500794141112004000c004440308107810 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 286614541 1250 286613291 286613317
    0x509090c10260f061302090406030506011701020408060103110402160f050f0619270b0a0b0d0807020d020102070b191b02060301210b0c0a0e030d08010b07031103 71
    0x6407100c030701200d02c0816440803602008040c4510b0039503440c682220024120600c50005142125590078241d011540728650140041c0400c1d592884d104e56208802e0103200b030450301500300205050014070a40301142d6080c4020150350b46940c940c100210b01000310283c00c581c0801415403003100d000e5840701464805d2200b44200c81c06410001c0c20030200c1050300136690020014881000d0040d401304c2c500074030398940040c0528284900501c82195034807011000c52020a40e80d041c010540f20b0300f4410010f1200c140702008040040100314045901c00074660300d0148040000b50030b003940c021035114410f00440380c819888020300c40d901c0d0030811000341a011607000c0800b809600c90004201d1488000a070b100e131448a60006129020500401904404004400703601c2c1d090301e0682d28110307801002c507141300d080c000810f060980c80b03485035030081403101a085200d4100050383c0b030205c0c0700a9450381c080782d0800e10940020751000304c040c0c0410017103212031301101d042400200b000f914058 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 286615791 1250 286614541 286614557
    0x5120c1203010b0c010e010e030d0e010905061e070c1208070219080c12130e0618041a010b2818090605180c040605031b07050606030708070308040509090c10 69
    0x211209007511b0919098032916410002121298074000058904e0000000781c04140d17a429014006e004007040000035220303201d01000d202200100c24010f203881090200c0c2c161055440c3e0400b0355145200040003000901a40c07800c0d60f03000e12032000c043d0000854030582d0b20003d4016201c459241140e00c003552820f4bc00112000c25080400005041d0003020441900301240035040c40703010203c501c1245000d805e1180000c02656440c400401c044150324100314040c01c150a00c4001442004810b4000098100010607a681c01d24140c40356071200e0391000300c4030010064200c100d01000e000110922034010700350b080c001480c080d0080a000d250701d000480718070f02420088041400005032072414a10011300c04030710a40d20894090340c507941400d540d80d0300d90041410189115807100601120041182d1080020200c0d00600400044084030840780c0c403100a81d4030344d0483d20000303003080402c2000f044242050105541c3c4008464141c460041d02c520124062003800030a001c00a1919 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 286617041 1250 286615791 286615807
    0x10e0f070c320d0f0c020d0618140c060306100c03030e030f03090d05190e0609090103050105150301020c0703030c080f040b04061d0a140a0302130b03011805120c1203010b 75
    0x800141096080f280307000200300c060058085c202c40040000a0f0159028210001c24000c590300004080c02c1c1c822840d0f49610424104501d00540250001303409000c0c40c4c4642a4901d446c8060b01c1c017400d0000e00d50707030b82c1c1c00c0c12030019074402d816000214203058a5509038640b04030240040c3c18005a0181c15070380c0c0346019a1581d00300412881d400c0103020043c001c070f080d030140c050312100c914a124240000c1031020b002c001a403d000e4210b007140c1c0b0040d0500048100001900400e01925001071104044c109520403d07090340a100c1e0010300700d500220301000880d1003501c40070496030003001e40c1450445220f50b0310b80300b070344190484615603a000508200d02030340320141c040e1100c2030525519102c9403140005402e5070451060305005000c035500c800155903100865001107034000c0046140d0045140000e005d40a64504c0740d100f5403170143c84440e800000d142c0c081c0d4155001001d00f0146128019801080c0c0004082e00d0030752107540c1e06604503007840c0b401140a4000e60b48840c3d20313103d40f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 286618291 1250 286617041 286617043
    0x15070209010806070503070f0e0301050403110606010f27150f020607020d020727060609060207050a0302092208270103230a09050114060405010e0f070c32 68
    0xc1a0b200e0280c0d03501200c208001198483c003601e422010070b1a040f9101032601c20100c071000118010b01d07502d5481c00d8184410903401c100c18100c40f81d10081640c1c11681c8900054840500c450042800b0030020b8200c14043d843c00548003817100c02c04d03515501c0890b1107859500503002c00c0496140482c01d4414500c01840d0104041036011001d0301c002c180c4140120002074035282c5920541003000c2902e0707600b610740d08010b115050b0000810000700a10f41d41c03108020700013081d5120b000c0142c020000040744a007850001031742902d8002c0e24200080d12040307020f23a04803101d01d00c0c0418204482d951080003e0b0b1600c000c00c402101c0580b483c800d0341d42c0000300452807113440d400c2c42c141490310a4160100303c0102100b00c0c14040c0b20624819599821500383c058a1491070080c640c0d4607061003214655802207426006010944c4c040241783e0701c5010441841d00c042c3c941c0402c2c00f1400002801c0340344502034010f22035201e0002051710421003450000042c00701040c48241d0040c2c007a080c07001d980c2c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 286619541 1250 286618291 286618309
    0x1219020c01240b0412030804020d0506040c0e090327150d0c030c0503130b151017070203161b0f03030c1b051503060402070515041b0302010807031505150702 69
    0xe0f44211a2505290038031a13516404214001000d10203448006030070356855600b9030f080705030000103a80492606150003000b1208030b00a00050605402c04140c128800105503060010000b04910f85d182e201400ca03894580b1103524070341d202a00400c03103c60040e0440160105c04c1c8640b00114401c0a80d01018041d582c820b40c220041100500400a08150b04068685030070b4124119481c01c0e101c201c001505040040181038010352040340c56448140e000c520305225078400c0b658030b4510b8454035022602d031301c2925404420381440300000d4010405107a014031420f20101a4209407a03510503854054010076402600030450401100b03042c085000c0c202100c400e071000c1c03262600c44c1860300181c084045420804c041000201c006001912554100c41d8000d4101e0201c0352920400805100d08500c00c80782111a4a4520003440103180e0708001c5100b500d5050719901020380d2a45000c42c010080d52100c64403480782020005101d44910501035005099492510350780c090703d0060017180c1c130b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 286620791 1250 286619541 286619549
    0x1903020d09060c0c030206070f021020060108061f03060c030506040f11041703090a080601050a0b12060d08090904060203070311040803031302030a0c0e1008031219020c0124 76
    0x5010700c2a070700013800c8203d0503801d5a90450321203850303521500784650602e05282009402810f1840e030b0740e01c4a034000707448040e01c01d0811110700003010049a2152503031820f215803400c59106901061900b00f402a40f9034100d074000301c112400170350f83e4039200b040d11000038a0b070000c02d503140c0620003641414024007181c00b19022051125600ca480c81da1000e2065214007203c048458640007112881441102c0c000c0034005c01d4000c60715100c01c0115100c120030b1148a01c101e101d060000703440b2180d2025544030113411150000165590b000b07020308901000c0741140c0210081003055810f03900c402080e0b0007a40503650058603031070446005000c680b2225507040040409000410400ca00001100c0d8041c0300340700c80344180f0781548080b0385010720307000b03004041504c94100821645200d102d010b00c00c001c00c21400224030740d074265107501c92081059100d1400d040f0000103c1d1040c00007958400803020802c01450301100b02c0a050031105a050140c8441c03680c2d90310003018201d81c0149001030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 286622041 1250 286620791 286620797
    0x1d010806060d02010509150c06060f090c0403030c020105210916030804140d02060a02030c010b0a080d0e0111010f020310050103060503030304170d05040b0402130c02030706020c1903020d0906 84
    0x1414140c1c0051910098040001c0c104803001802d0380310b40d102c0e01c41040c110040c608116850348040034911380c80f080204c0314107015840c86180904680b820307440e01c80c0100342030a0703043d25050564504031042e0400c0d21040c0d06210b03040140401010760b040d425429010410030b104414244260b11a0601c07402881d012035541000a003480495061000c89040380c80070703900b0030030010201011a601c40100c5801950044010440124107a000300c000c00c0252540d030002c01507003021100300131078140d0500800c503040d031050004001041c0102c0c1c0b1005103580506040710046261078940b8292649140d60304071040d0040203001d840c10369400800054003090070f01780450b0b818013010a0b40c1c0d000050020b4003484091000c40310b000742c1c8030304640011845c07100501c002d24090804d21166441680c0882c000e240d00b07002d04540114030321804905c20503aa016503d4110907840d240c01035007005001203541d00926140e800109810418811514402d402170302414040c91006402e11035982e00c9032040c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 286623291 1250 286622041 286622053
    0x9150c11070501021e010905030a090602010c140405010f021203011d160f050d02070b2d06030304150210060608090f010c02030a030905010b13021e18060903161d0108 73
    0x142e1300412010300c1c25800f070031550708800240040901400d40c00d40050b00c2e50100050740c038191944040d03d42c0641e40150000c0c040e055010004031020b115900090315013071001c1c0800e0240d50711800c40c1c15050782c5180704960340030600600400690b402a031200c07181d100c00c0001c40802154200550b40d008400140681c0c3c5440700c0e50001d0074480c0d14420007030421600050319407442150b907040e1264241c00400d0440d06180000c5994502d03034121044c002005441c16406a402c40d81c0e18100740301d0040600a0750800d441d00d2000701e0030199281511003540200f0201650410300c61181000a1603e5030710040e00d818540901400d0848411144000c0c3e4100f6451045241e000800c80722500032500c0c00140581c664240303540104641d050903907110010500004568401e50040d00804c800381034003010001182c00d01c0b0405124401d01d0005035099483c9940030381c603001018080c400800f6044d01c2000c00d400e401e00700741c1070701600580c03280b28088041520b00e01c940e880c5180500f22143c000c0c9a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 286624541 1250 286623291 286623299
    0x605040f0b0901090b120303010807090e0a020307060e0a05040905010f0c0f0e270f06120c090105090c070c0e0a050105041406040c02011d011b0513170109150c1107 72
    0xb404190500616111035141c045528581c5c458a49444101020001366034980d43c48945107602c1301164411002d244d07040080070443c601002c2001e0310200c1e40180104405ca01c0c0035000e4071020084100e440d0b00444280b000a0a40c44e14094070031110b11031000000c090f1800011001181c001060810800c00c000303a1900e011608040c0c5152840002c8944000d00c0d075003440c0c00800c1d8081c1c0700b1110800749a02042c0005404000220303800ba900450b00c80c0741c84112340740c00c6580c400e07160002d240c4c042e004100400c0f880c20844a415000b81e00c0410852034403090b6165203070100710030f911825009041200300f00d11501c05120303241c0035050031602849806c1441c00f40400340e48003d0002407040da0765a01c0415030724001d40c004960301d00c4211218410a800c054098000d0a1050400d51001c0910710070303400702c900c90380031601100c40e0103180b03080f401e0801a808d4880e100040d690b0050350359414503400442c0340701c1840c540c1c10010a40110f0741e858640c0b1300078031500d02549a00c0d855809154140 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 286625791 1250 286624541 286624549
    0xd0b0c300723030417040806090708030310090b060c0a0b010614040e0609060a080d0f232b020301030f05010b040b060d0c090b0d0203240109030b0402040b090a0605040f0b 75
    0x102c590b026026040d00d94640303041c400303040e8080400c041c441c0040010009005100810050700c41e25a00e41611406940c3e08051038030ba00c011901f6551514201e10240003040242d44a041114000380c0030f641070030500318242d4074043e43e0403000d54601212900400c441a44900c854076440951041e4501f040d141807401003103020f020b882c00784291141800540d84d500c5d603400e0b44005003030640484146039980f42000d0802007040001c0c000191039003a141c42840950050141014902500c0a00e06482c207070010501e10780051850344450094208111150b805002030340c042c50103401e021801403402c4c03600c182110408420a4040c1303007403a0f1040080c1d40c1d03a000380c03074100b51b94140101c2c02200d681000c42c2c02c80d02070740100105000c04100c2c40300044113a0f0207180300340130300303000d0031180201080886018640c50300c20038005450700f2001d000040310150107a400c0b903c0071300301055047c401d000081490300d04855214105966131070800071303840c1a008100c01618542c40811242c03001ca000300e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 286627041 1250 286625791 286625837
    0x909010603030c030c03051306050a030b0303040807030b0403171006030f090b010915030b09011b08131220010f05011d06090c0c0a0b040c060e0d0b0c3007 68
    0x1800b440101e170f1300e600515004608640d03c4d0740e4001f25441c81d041c0c41e404007a003580c04c00c03000b8a000914090460a00b400d00000711025120002c00416000d860740c1d50b203407610300009204808006112030080000702004e507041d030003107850280f8182040c0c1025002000c54402030522424103080c40c001c440071494446072141036503c1d98101044645e41d480c4000e43c3e82100340e0000b0085280101000030070407066001e400050000196660f02c00701030281216401e009481c4c00c0e4095508084c050009462011088000c0307045040418501050206038110444003501c12105030351a5100407100c0e44040c40354a000d400810011042c540e1105800d02c160078005010306c0c0101f06042c0400c44060015055032a03011480040700c260812900d4101019001610200c0700100f8054011a0b924001c2044401c044400340c410004050355440c0d0750481c050281420b00341003c10800107010306455140001c0c15459140c001104d500c50109284001800401c413008101c00034804c0c2003066092200 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 286628291 1250 286627041 286627043
    0xb030a0b0114040b2508040608040201030605100e210703031b230601060c080d0f090507120c14060915092d010c0b1f0e01140909010603030c 62
    0x211414448016118100548110b010303003140482c0010b803181d481e0005100c0d80344a850b84656400101c100000300c0c01da4000c0040c9141011300c024000c10784500e00a540c803900514011501956400100d010030309200254000511252143c000741c0c1007040040344040c8048141d025081c400710001a102d800c60b020080420124000800310034110b4007070b000d040d6401c1829160701c1c40c10318503001180318402c0082c000c917004040000400764011410440f1150300400700754034040403101800000d1070305c82d1020b10055a40d40030b40000c10310030040e0380043c03c1c004000039041481820140081070081c3c0c8690f42c4a0f4401400c2c15841e10740005a034201718040c3da07840c03403d6002c5014000580148683c40e0f4000c20300b10782d541000c5281d60f45074040202c2074250f10440030841001110000b250300c002034181c003241000708800b42d048049060388202d20300c400d80d145039114020a81a801d0170f90149140070b101c0484841d03c2e01d0040805074019032000020000a85141d80c00b402064441c00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 286629541 1250 286628291 286628311
    0x7030c0506181c1710080d02030c0606060304050147102f03090a05061315110a0c0e090609070320040c030f0f0b0306160c050307050c09100b03 63
    0x3200c03080c09805101d01c0c0d13542168030078005a140c038107000740b442c134104a481003410900c00c1c0f0600e5079a440c008000c5940b40020200030b0329042e600c460034003001e5407014108842c85c0d0b681c0d100c014108400742d14074130b05c1c0e0002500340203034030034000314440714070540c1d40e88024070a15151009100c99841010320000c6030044e003080c03480c03443d840200381d903002107042e1012855580400101039403080807008207801d42d4200d4042c1c00309910ba40a000c5070740030f80341d001e4040d601807079014401c0b46e00e050307444c1c49002c91620b4030354502d1441441c4182801048141200d0a1103220420302c490800c4440183d40194200b00a02251900c0002d5503960016844050071003481c01070340340101720301280301125007280074005001d1041a0303440100100100744161248a29100d440c002c480c02c580248446084010020b05581e158411303201541c51180c1441010300030104001c030002001440601742981c000c0c0043c000c034001140600413074000080c00c5e01e502c513030300b100c05000101043c0300340c03034120301001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 286630791 1250 286629541 286629583
    0x50102100e0114010b04030c14030c0d05030d0c0302070501050a11030a18080304080c01061707050105090303070c030c0e012c18030417100902010c0807030e0607030c050618 76
    0xd01650042000f88980708806a03100b00218280704050000c20440e84502c02806850382e40303591542c1a81980d600c2c0c51307850f421018a040c01481c5c488002c407003142c06501a203113810102c8040380c080f070700e000c211200801e402041310401d11600f84503c2c0e5214414440900a50f05407c0c0c0d030199074400180b04a841a0b60f40c0c0200440404000011070040d520048056403410301e0704100301103402c00b41c05028207600f45840881c03100301694010781c01c0d0069500030001582090011343d1142c01402c111a014030081c80350401042c102040c3c0c0c00254010049240030500306440b0441d112016000342042d5411140310400041a40c00000600103650344c40b803c06403203106080c50500b90030210b40c2141d01c07000c00e0204028804469001420118a0880e4000485983e2040071384960810181c08200c81891903004515035000501040e4400c1c41d188010400c044001050394204c940154000b620111000d410480d0811019030014100001c6403241c0303040b07007120340d5151604060840e4003032880b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 286632041 1250 286630791 286630811
    0x17010f0e01021e1b062e030506070f0315030c03020a150e060702010210050408090a0812040b0318030d0c0906030506090408180409060c022e0914010c02060a06090605010210 76
    0x201c8008941c821048180c805c0703410000342210381c01420b400c6030b034850010340900807a107210f100c50038000c0325408809446280d075200c0040d036418050a00306010300d0344868030000090f104182d0040074600c12081d2008071400c50061191181803a00301e6080007004508a17040075400c203100c0c001d5100200d40c5182c1e07450704d07032004070b05003400146038040c0542000c0510042201803405006032000985070103010550300c0c606030b80c0d05d152102c203011040c4400c01040c80281000801035600180040b041c0c40d905102d4a55280307107034405942c40400c00d698140c10151164020003490080c0400c0c82d042c0b03c6d90410f0400502903070006400185100400107640b03040d8040d0f10f01414003104004c0003044182602e0501d60090805099044010b0048141001c01804004c40b0080e6203404040b900381c40014050580004001d0514280ca01030f1544804100c548024000c0b01040740c0542d000c0c00e13640c03c00090620598a00745c01022500781004000c4c80140d030f00051603a81050207480110303c940c00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 286633291 1250 286632041 286632067
    0xe0d020304090b13050708150f280b0f0c07060c02030c0f01260603010609140703050403051c0b0102060105060a0c080319060611060f10120c17010f0e01021e 69
    0x10030903003240401d0801080002051f007102101d031180d60041040c0066409170420450800383c80e40080b58010120240c0094a29501034165807003d000005181416250842d209003500400000e01c0d81c0200020f03501c01200c001c0c49558010121810213070390409a0754006522400e001101a0142030500c01012950f031007001c9003c12403402e285030041c8080007190070003060340200c9255001350300b0514000381e014034603ca418074a40042145c0c0c0d11640300c00d001107003e014060019810084241f00d4a480304143c00a4030a00c4c940d0b012002601003910800a820008142e100d68070504c001e205e401030305034000c48000d2000c2d5219100e03030741d80e5880c0c50b86e00c00e450b400307555000e400c1c910781540440c07083d4200c48803500403440c4000f1114150b641203418203c45400304c031076005581c41ea0f1400c10001418000050245200c0d0320f05030711181d120504805c104500700e0b6040100e0303441e01c41060071910544140100144041700a52030310b20700140c1c10080301c07401048403210b0341d00098407280e8001c0c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 286634541 1250 286633291 286633309
    0x40911040e01060b0f090319080708032a09010f020f03030114040f140103050709050c0d0b0d0203010e0c100203040e160212132303070306020a02160305070305010e0d020304090b 78
    0x203500c0207480c1c5903c0c00b0b07170090300c0581000e0f400d03e00078400d10115020030303c14040400a156488440c491500e0010398031149690030142c039071050000e0102001034403a100d640e8011240410403092034448070440c000401040c4034101001c00d5411400c024040c00c0310100071a8196001c8010000201074284081402001e0717030000704012501e01700c2c100441908c0507001e141240d0003403003120305040d2154130b480200c42007642c284003061820400031030101c05a80081c4800000181103280210464012900b52003111010740d0564008070860b0413a40742c00c1230054031291180c8001c44c2014100308140307118180140501010204100300b6020790b504c02c100c40c01c04400e0a0101c551281c5031075540901582d010b00400381e1003e1a01070b088441700040890060000b4020000e0200070704d5510703000029802080341d5411809000841100ea00d03100b0501001144500024580c0e94030790304080d405c442048051400c0c40c1c0294840903401e503400400e45094070000d10002030460203c40025502007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 286635791 1250 286634541 286634549
    0x14040308060f060f0a032004181d0616020a0b060d0507030804030302011b170403030504020f03070303020309030f150f07020109061a0a06020d051e0906040e070e040911040e0106 78
    0x50001449482949260010b41103800050b01d0511160b042101c0303902c1fa100c410700070740000b004180700402c50030079996110f0608102c003807000941034402c5601696100c08800018040f0f85c000814081c0c60b41d44800581091903c0344041c00d9140c0c15517a40f21500c8070058140ca114003d800000e605000d03080c0030010045501c0218580e07110354030b260180c007800420039103191503202c13000256901c0340a074a25400100103013000461550311030754154010003015200342d8100c9105c9925003c15201084042c0186000b90011503e4110640800d4540a00420b100303900c0e07082201e070301d107182c065444243d40107640d501500140f50f40c0d80c001207004004082e0b000d0300c102d06043d1142203000640c004802c04501c269080494a501c45609a90383c0d030200c060040024010410900f100c6031103c641b116036540300c4045482c0c9000240092102c1d001600001d06400818041c02440c82c4c0100c0006000b503816036051060144c561103080042c00b0400a2a004030b0b12010000ca0180b020340c0190054 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 286637041 1250 286635791 286635799
    0x312030907030507050f13020a020a0c1d180a0f110a03060911010206010303120207150c0201140f070f0f030e010903050307120509100209310c0314040308060f 70
    0x292a2151036240d4401c0d00d0301c01618203008044c404a0700e41000404401000805480300e842405121a108029131011564004600601c80f07440005900303c0c2d082c034001d00c1d448841c10b140c0c101c94140290848000b0307000310404010034519078201030300450403174242c581041001c0011503450500890907440007030642d911038002070022081151540c882207806004030100040c04410f08010380e030b658400c0c080540820048000c4404520103034006002e20781c45030002c041c1480040d14148280d4003041041c002507515500c40b041c05140240c0c44a80c45003402d42004100c0c00d1890016141d0041f5005801c2040400340000714414000d03007040c01e0300c1c1c103684001c00400750385040081c107542054a400000810341204c1c0c0e114900a4042c6600540e0340c14040d00340190014440c000a5021a1105421003600b4443c580401c040c2d200d903400c0f181c804100c40c41c01200214002045503000700003201814501a0355624500e45803a40e954040d51600700031507680c5401001600e02c003070024a035640 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 286638291 1250 286637041 286637047
    0x80c09040f06090c09060b072102070506040305030d0506010f050913060315050f0a090c150c0b0c030405150f0a050612011d0c01080112030503100b030403020f0c0406050607110312 79
    0x200000750680d1340c00c4410000e010052651105407014080c45402805803103001072000e00b1550110848500075004641d0040314036150f40c0e080070418642141e0310555243c1c10100b0b40c40c1240056014040d031011007480c1604101c0d0310a40042d02d540580c1025034001c284d0b03400400e0302218a54030803006540c020900d4201c280c1c034400c03044080c10b411254401a210301c000850800d916a00640700495804a2505d895a0809405c0e40b400340401050a00304490500b019010400f644003c40c01820361030b40c00c81d81c0f4a81410124070b4009114450f030000ca11080c10000e846004160081d0400d20040c030200d00ba032100c0001844400103031200101d194644a4400c49413000700d0301080c42a15070906960310780d4180c00040d81d03904024401c030f490300d0f9809108500000c2c803d100442e80000380c030300c43c01c0d00e240c0c8600001c52150400c55088015070300c00c0c1d0f40018a90020003480c1c6046108a40c14000b003414607011401c4c0d400344080c014071100c1919801c0e002642c2c05c1c07028810040c4071524050b1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 286639541 1250 286638291 286638293
    0x60504170307140f0c0a0b07020f0d0b010608010e0112170904110c031201171509240a1410120311101e02030121050a0c0b0a0e0a080c09040f0609 64
    0x14490038404013003101449820a91005070824008001c01c0314100031303100303040c0205a024807044031100581e080d40415600e560324002020345020781c2c00b908003a61424601e40c1002d480b8640c0d0401038121103c502c1c0300400744000038015840c0352a00245490010741c40b8101140414042d00a03040060034603e0045640b0307410400000182000c4c0188541904960342e880e207103d0710b2000000d60014103500055201181c141c0074803200c640142ca40b2046441303898440c2c10000b8070340b4031101d2000c0b603e00c900c0203000810029000314140c100e151482c1c01c4081c181101c0c0403500030440c1c0302d024800740391545444140f6004d01c4c00c001084400b0300c03e0b20072210360300a165000341030108422a1020310800500f9042840e8400d0b68141d074018400c0702040301400155541404d8800c03004c580034894940701c500000d40c44841140280b5088031426114072401d640a4500130403c1e002c5402925035a00c01c010060700025101000c01060b28201510b0300c0b2410100080e44140c1000b401071410445244 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 286640791 1250 286639541 286639543
    0x519032c01030c0314010e13120c030809060601021b0112050a0906110307020a02061810020a0b131703040305190c1a0c07060506040e100e0f030406050417030714 71
    0x1110300340e42603808211003e1504810340440302124506503040000784010b2001500740c034000780d040f007240d1006602c00180743e07417403148410140701b400c000580408040f0041603007000c5aa50040d64040142c101850407100003036440801083c030b030800c03503000350b0790583c01d134082e68001a81481444061016140030034041000e010084822101985000f4506400e810030006885c007400c135039800340c0354814080e02002100d4010301000c4101c1c0200320544091a039401d00400750103035484e0040d211106403800c20380006030000703200140340c5965a01c0007002a402c4504610f480fa58411501c0c2c0781d80751401c00311428080c2450a0003080311100a149000d40c0101101554920982c15417595a03501240031058130700c2079074001159181032045400046250300860703400700000d000041d660008441141c545144075803002c00749659020007240b001c0c801d01540391921880002140740a1405200401610592040c1d003269034540200604070882441210140b9411005c58800d010900c1046 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 286642041 1250 286640791 286640867
    0x10e15010c032006060f090417090a05040509011a0301020309151003020901030b010f081c0507030c05010609021309020405010c030f03060503060c0a080601030c1b03020102040e1005100507051903 86
    0x114481c000310906d000507031401140141c822039002440f16407100b6843c041c6012a004642a5903200b408030b28041080e8403217100707980c0b0883d00c840c0040f8080540c8100090b01c0b0040c000c645000313134010810030020b85400103442d501c0d00c4d00d055110006da6074100c0d035100140301a030802544030680b440000309004d00034071268140e400102d20480032030354561840d5651009c1d080030240c2d0010b80d07078110714082d001c0e0303015182c058001d040a02104506e0313a07030203003111800c0e00100349865021540c01c1c6038100b0100d0a0b0301a00401000314030b040e0078517001812a407081a0f0003002c1001c2446038103580c5119803c107500600c07001d01103506904250a4500b02d580100040000082c4a580000d039190b2090041c00c5041d0000d40310100310740c000500c08044022002c400743c05643d003c00001a0070b013032603407071030788202440041140000d0810007017101007004646080c08010081c4558404914081140f15070755018030080f00200006190950b0390702c0c08003200200b1640b460b200111886400001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 286643291 1250 286642041 286642051
    0xc171e06150d060b0a021603030c030e0d06151707080309040e1906020702011b0c030201051b06040c05091b090d0311030a02060402041d0a060b0f060706060608010e15010c032006 78
    0x240d4090402445083e41a447d19100107030004882d00e0708503002c6406405111070250028100d2481145681c41e030718295401b803491942180f0b4405000c1005030303814580c0300c0c0c08856210142200500e00740743d0310350303078001d43c2c124501c51030340d61403426801e090400044a03a0300076902825524038140c03c2c00070003900480026404105152001e00c20403446864262031994800c04540c070031f40c00c54004440c0c85d08a800c006240400300d085588100300308001642c031079485003c00e144e0079800d000911060f0000a841c051800d00c01d02801c010304d442c0c607001c1d00c4c6403401c250340f20381d010390301c5080031120b0300c81c07055401c0800e02000440d1122581d0110340703070f84510700a40f000d00c001e410350003816808040d80030020708241c21003c0303148002030003034020241c050300040c000c082485081000032416404060111001c590384c060401060781c00039016401000c240035041d20f0791412041440484500303d4540d810444411038076010140a00e0308255000502d11082400407180d50540d943e0744d1042d50 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 286644541 1250 286643291 286643293
    0x8150a03021f080a06050607030c03020708071202030106080d020304060f0215041a091212180610080609060c07020f03070b040f0317180d0f05010c171e06150d060b0a02 74
    0x3034801086016400440c1c6c0080c01e0146000115101103a0301d01c5001c40031011030280803000910b041d0b0811441001d007080e00c040090344410341c8101402c4807115400340303821350000c80d0750340e03450fa4005c001e0724121019401d00000c0840c040c5401c904095142c0d190000718480e0744184006d002c118140300300340103174080b405469500c4d00303440c881d950505c0c641340710702026040006c0c4441400148809410050080c0c0ca00c8001c2c0061000d98180f00301121319016240304c518040005150401843c2d0b001110100078000740c0c1424003518120707101d502c901038080c1458080300041070b101005250010f00c001c071801602d40d611002040d020080500c0251240c001c041d4070640204800d100701c9054a0111410143d031150107018404413b1a14200383d03005121442e030381d07010490a0044140c0049684d0311941c9414110034800152a03000e0a0031005007114141020100140946503401130030840e002e80d201103003080c03c1071551003900d41464025050410001d00525610040d204548141d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 286645791 1250 286644541 286644557
    0x50c070f090c0c0c0618170d080115090b030411032a06040e18100e160e1303030513050a0804090c11031e0c2509090308150a03021f 58
    0x40c2c088440041d29440504003010341d10042161900801c0c0d1080300d80001c0c0301d11010300741d54400700c01c045201c44194082a4000c0340e031082002d540041c00c079000d0801c8070a032501540c1c3c070306401440c4c42041c0c066441440c1c000070219060101070078500300e00f5100181140c0200c020000e80d0745010a07080c10f109407040c800c0407030b82024501001a2010764503201844140d642d1019039404d840100000401e84500030714034080c5500c0298000c0140c58a440001040e40d01210302c109404c0e558290321440c18600c10708103004c40c1c640c40060038011250186008155038031a00c0720191000d400e91402001485000038407420030484c43c014000f00c0e10340700e40030000a45550f2080c2e03194107100d640055550001c000e40d1a84802c01c85401090003105144981051b00403441c45213031a0380060351000d0a0710000010380390440b81e01e194005801e007200144500315071907a001d02a240041c04500e8076000c058200405500e42e60ba42d40010340d0014583c441c80c001444412500314124005000010a04 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 286647041 1250 286645791 286645811
    0x5060f042906070c271503060609020f1e1603051c0204030803070c050f1906110910180f0e0603010e0c130b060f0f1b0a0b0105011d040509070503010b040b031507050c070f09 76
    0xbd100383c1d07480300340090080d841c1c8032104c07481d029101468100e0154440d014041c4040441c061611060614409d40b500d07076940c550300c10f202c014004144d508003c1c003401000b061001400b8101902e80106140c10b010a100c51946041801d101f826100002207100300c404452096955100100c0404d005200401440a04e6403100d04a40b06d003200c030704e8219043c564481005442807110a50f00c141d83d40074030140b20303294542c5c00c2250307000ba4054212204c28030140821843d0070f1181c512112108401001d01c59440380c003041c070843c41513000c260f281c0d50710091200d060301c0304c904642c0d24042180e41d46030307501503142c80c200041d005102002c1c034001e10007009540035900014006611034229081c1000741e0301e848011a0011884440300261082110004030540c40b80d0043d03d01600c02d05004c1c0400a00f03100a0508403094040301c103209504103094002551004141600d04c40c21041840c1115034134a10280e605206003a910103c2e8407451000103a9452400c1660b0107440540740240507400309 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 286648291 1250 286647041 286647059
    0x9020a120e161a090301110702010305280c03020408060405010603050f0607021002091903051f020f090d050307050709050f060303031905060f042906070c2715030606 73
    0x80782800140c0401d0100148241540f031420303554120542c004091034450070b940072a0940d4520ba40000c40d03c403001c03a00c08210340e094000c866214125000b410000f030200e1041914030080092820035845da608070035500548203030100ca01601228040324030500f040d140c010f000300780f14817041e10180115000311400b80e4011951a000704016070051510a02030501d1301300030351101e50010b606c140400080c580407607625801e04002c502a030054200c03548046254450a5840000010800d00c100a541e021070000400c1d00e6098005031100c1c0b0806416191480ca1881040d0001e0868403035550f0000b2049425041584200354065030011070341c0b59102490380c0c81c04140c546041170703e80c8800350b081004081d402240d2003640100b1104142d080300340880d007151880400d2150085c45030311054066039207a001702c100e030042510300d5840c01e00f054448e40c84036041401480300c2c2c01200a1000102c900f8000070004c544d84d13103c000c00131500f180c0c89006604089100488000c0d08183e800180303240 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 286649541 1250 286648291 286648303
    0x240f0806010e010602032a0d03361101020109080c0a030e100e0f010516050c1203040305060c070609140615041a010809030c0102030f0403030f0506060703030209030709020a120e 78
    0x405170029814a801c11401000d0003848040c10312160200c0800ca64640d6002c004403242841961800103110281c0a10300480f101c100704000c9580a52411200c030b5403080000c1340d03140c139030800e010320724401a10380100c0c094040110050b000d25408034280328203403000b044040e0014860785624010424680a00802c00c0c54001100c0c0400c0030711a5003201400d00d0101c0500d50790051400610b011001400c25141c81d89204091355142e1190704c43c00c4030360070f01c00796018043d920b207402541064919034440356610300081a4840f5400040b500104012098100100b9942c0c411843c0807001e84c8600517580d62402102d024400d01c01c0c042c60030469050500c00c3c5d5440098102c405c0504901400040d142e03404081d0849403148030411088030031360800e1016500615891131041d1507410b01d81401003e0325405860003036036a2034030041c40026500d500407103851583c107040241e01c1d00d41000001b810b0580caa408040314500003e41c0a1700030364482480700010412020820801203c401420742c0d0380 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 286650791 1250 286649541 286649549
    0x1060f0e01140108131a070e01030e03070c15020307020307060503071808030306060f090409030804120201270809090f01180b030714060705011b110d080109240f0806010e01 76
    0x1d00101c00700d002d10000c000203070545c80c0100711001c43c01300c000c9050b44106000302c400400144040e01c0d40d5115603070500907100a88940c000443c00d040d402c4c0c0300c1d0601c03c4c0441c81110190302040400d8021580240140e0724601d07002010303610102c0d03513940040c00e2a4012213a0300300065600450510307200c40b02c41c02c0d00a40b24040003c0d03040d580c2d40e03001d204080d849154140c202910500141c0031958440c0a20617000d07210303a0f00c40b8142e091614200c40c2d544002d20f98501076905250340181c02c02c10721103041f84000e0503140f00d10f266056034100602c6500c83c0e91125608003008008025194001c0351146041780c205860002c0300c01b50b0350f00204110b56a82105503459089a00c0400040d04019101c03e9450710080c00c4526000540ea159802c64105429800030f6026480420a00c207070070055440c036402c0320030003038007405d1020035008005003814028005240d5946003041d001c182c0310300c01c01d0400181c02803100156a00ea5084030300341250317031082041a10803480040354070020030103114122 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 286652041 1250 286650791 286650797
    0x103030801080d0f0509040b04020c0f0d020303090c04090f060f140106020f15071b0f03021209010f0f05041805240d140102070210030c031506020312041401060f0e011401 75
    0x101108134400c0300e036540624071a60b030050b1600240d61840d07485100600281e8510402002004044130f0080e04104a501401c015034005004200140d01c0100780075a5209080b1000030f03001c4445e1928420840300890b010307013041c0c605850365980014a600030940c240038403000a01582ea142d104030b0740c0d80c2c4001c0c24205550070101031440c650742288001a0400781c1420f2011540c0428060010b003071007900826181000e102200005054060021000e4511144915480c0038403441c006402d5140c40600307801044030641c0020000e5218000b42ca000d0080ca00004a0660b032504403940900410340c2e04000050069070005d07011403128900250740c9802509251021101e84c07180001d12642d50345060955401300b041000680d5241903131101d08220b0380300040d114a40480003800c84610507107072459003a050303106202040e0008150380b854149084c101000782c1c1c540c5403c3d4801a4004a0824a0741c00d080012411400d104110b42c15a02100342d86820342e1381c2d03002e4602030b50034201c0c0f41d1408 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 286653291 1250 286652041 286652057
    0x60911220e0c040e1501090203011202060309010e010606020d11060f010e0901060803070b07080a060612090311061003120f050a03090302030705060f010512030705100c14120103030801080d 83
    0x304150315001004121900d0059851800035880400c0a6502c03190303e42d03229400603001d0001c000c1c20022400c1c05803064000031400c3d9030410307180d1000014007800c044e10501300800020a6101e09400120191140800a0210a59454000e5030340c409191041c1c0100c2c84c03120085244010000d1654031419140c5804401a460811071110681025081c680f00f5500c03006d0100310507000700024800244214949030861520302801480c1400141950b48814288041088aa54001020002e000c1c650400044505561070f041c1c030a10170b110300c65191400f408040003914200210184102d034090102441c04400300101280c0c000496a10325000c500240000b00780306109501c40348400784070340100c3e458039825884980c6441c0c000c440c040144500c140060206041284195021042c410029420320206545960300e0340c00740e00b420004555142e9000c0e06051003428504002c400003201d17140d03100c070400c01058400c402400700b540460100700c0000f0f141c0d4000aa03090721525143c0e12562 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 286654541 1250 286653291 286653349
    0x20d050711010f021e061815040201050306190b0703180e01120204021c060311060c1b03190303050405150601270506040605120c040e040605061804060911 68
    0x343e1a400c00541c40114440e14034150b10305011120350746000310385140282032a1801c051070b901c11803000710902006800c07592850780c0185084464a0300a907090070445e480e981d400c0b02040c3c900c2580190404c50032480c0a00103101c6100300d00818030a4040e5503a003140402006105d80c0e54800d030301c509a40c40300400010080d0300f40c1c4035030200c0350a1000b800075240a409c901803000b1034070311443c00451540c1d6030204100f0000056040f100d905002d840950800340200e0400341c42c1d41081e2104880d0105112521040d40d90911548000c1c2c41403030007060b01c0807030f503007001402880200c404a5503849811501c800300c0c101c0d5410035114000595500500f1680544035601da140d4000e440380404984020100d01581c030240a007014005d5627843e1b540b141c0d070b05484001604c00203800420160004c00082c81703445c03d03141c442c0b640650060320100e09a110007021514031030a501104241c0d441d83e5050000300116508040c003c28015504544074401c11000c005e00707208481500c00c001820820186 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 286655791 1250 286654541 286654547
    0x90501030b04080f0d0e2b02100b030f060c0715020f07030309051c022401080705010518060a0c02040b100f110a02270106050901020d0804240606020d05071101 70
    0x100d0a04e100910f040e0411240401c040241d42c0c04141807046904410513120160402144040301c0e41e685a952000f05080d07244042d465000c411001501c0c1c94607200b114505480030001c00c660f002e203d008590b0145020b9401d8101034010440440d07111140030720404d0040c00f9402502d0b040d1158032112450a4910f90b800d03001403d030400111064040d00d0f0b801c04081d000105c241c0382e5400d00780c024281c52a950850898142c4551508400350254034005100184000426409484007800c00740d03943e03202d00c20709040a03203c40805a60000b00081c540c0074199008100c11030f402e1007680c0c20b1000c50010403c00c50003259440c1d0a20006041150180485119001c488400c3d2130180686200745850b801040510702d8840140c2490f503881d0203507007620102541c11500426039450003e0402e03181100003521404801c40c01c0342005901c0000c40e00307200303110344191800852800d50f02480162001400080c160510441d4094014104240120f0303004504a41c100c91307000140036444003140c0015 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 286657041 1250 286655791 286655797
    0xa060e06030a0b0d0c080c030c0a12021507080a02030d060e040210050d060503060a02030906181504030908030a030f0b0a050f040f0b100905152812091407090501030b0408 75
    0x203e98008411070421011400c107030fa61402500d0300d42c01900050300d40d04180b52800414036491400342e5000807040000205200014102e80d0307041f1642c51701c90364a02a520314500485c40082c04004000981440c440d40020041c0b4080c50711000900516075503804600302c00900329406500101200442c0348141d00c1040207003141010b94400140503501c0700d02083c0b52103001c071030040e4405d034000244103000c030080000b103a020303d110030103074400c4120102240d01c90318640c2c402d58416810001143c1054060410040034000b07100440742c4505021100402070070101060350411454082c6003000c42c141a1881c40c140c440141c04601c90002c014103010042a805282e0005680d6071a00b2015659400203018a645003956801d8105810401003007058082d400202c070710b10b601004010540052204030510780120703034918440b05d196940f13040e101341c0720300c260640700c15180c04808810802c1038210f080d0074889890465450039250380700001241c10078000540550465030000e00059029802 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 286658291 1250 286657041 286657061
    0xd0f1b020a15080a1404081902030d0504230610180e070608220f02130e030c03120f0106050f0a05070605010e01050f03010506060d090203070e0a020301050a060e06030a 74
    0x940c80c0003590301c00700b10442c01c01c00c0d030100740040e107140107121100210340a114451141c03845ca401240c2001d9656a105100785100d0b0401140e0002c080341800307000b070040c1c4a5a40c0c0c1c0c540e0034855441c4c14608040b100080740e0280d100c428100c181c1441841000803414400d1032000001895107090140202000502844042d5480d440310381d00c2050003c00d2000c1c0f00100416107400d03600c0e007021621000606a800c1e200c4d121803003203a00c1040803896a076030641a080d01540d00300101503401c01d200d009410034048c1c10890744000a00c607a40c1100000042080d00803080403424151115803507202180001c2c420320300020001e1248001125901009040055050038014a40a0076981b60000c1e603600341d2084403030702c809400401ca10f06062010542220086000704001d142200c00035040d4020080890300003a50703a6508011518100581c130050020f8100701c000038980f24a02c2800f951003401581e005c0e0003603903c0059100d000c0c50301c000b80c80000420b51802e59460070700b07007030061030701501e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 286659541 1250 286658291 286658299
    0x1203180308180f070b0c100b090402010507020d20010f212408011a0f090a0e030c030c010204090e0304030c06030c092403051807030809040e030d0b030d0f1b02 70
    0x74104407803c0400509004150150307a094441d0042c41d0340c03900b40742041108814190616507440b41550782c0484403603001d0707424206980c480b803907400894144041010b00800c183c010881da42030080e010104120a44000d0303803080c48031a01c80c0011100000e10304001d80c540300c4425051103221200d600b05440c0c00700a5110042007401c02c100598010003542d20003130459544404a000f9042c1c9449000e4400c48250340402c0c0b8401d5090100d01c1c400c400034504400150b440d200140c407031200307000300d071088120030313003101d482e8894a000c0314000e501a21503003003904d2400d03c007120a50004000c1d94201c1340c02c1000c20022901c3d10303c045d4080c0c61049020420806030040218a06003440d4440740c90168070708441400298105016088600c0500529924001050398408414001400c482601e600c99103658031013810701c1c081400384c410f5415429075800041405164030350300e80d00c00c4030f04190480860b15202c001900c19940c8200400303150b0000782c0682c0f4901ea6524203220300301181c5101070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 286660791 1250 286659541 286659553
    0x1090203152701091b111603060510060906120209030a14030c010b090108070302011214190c141228021209010b09041506050a03120318030818 63
    0x400203040d0101850320700061541e182d09082c00b40d2140107225014140c800020400841d80c416a01c1e8400303032a441d0348040000c491206840030000307100c0001b0030000c02804400194a0f454100043e2100302d41100c0703002e4071102c0001b000ba00c200241c1d1304440a0b40c0b0f8040c01c02003541d054401960002a890741c152007155080390003d00d060f070114029a078080060b41e10b403110f0f450514292050b21401503c00c050f2000141b0850302c02084203000c90740e0900f0700d000c0e41d40020007404082d211959090805a8107081000b440300454400b00340c100000c0101000030100410081d1002d40140c039080c01006c00c1402a501d00d481c0c51140160003444540020b250a40c030380c541804c1d0701c46140105100701c0e0700130620403603080c0091212500044444000d100d0000e006c8049109c065004001804000e030054400300d9900b519030110001c0c20024080d041110b45a0900c03448402e024411000013a00d0f0031105420b54009960f03003103c079545566040d030a52246064240baa48082020307441d540110 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 286662041 1250 286660791 286660831
    0x30c031f2105010e12040504020c0f060a0e100507090e040203010209030105040302010c03111e0319060803090a2705090f3004080304060c140610050405060d030801090203 75
    0x180075010200c20210700700c030401450345001d41c00d40320f105214010b550300441d444039200300c0b544141e41c15200705940c01610b8640700901c0d245099804000d20050780200c1c0188603482025411000740142c080e42140c020011144424040780c00c100c905200003420550140312800300d40c012950041d00040000d03081503801c40020b421110180c90403070160390349504256105825005001000d003505180505143d42e00c001214580c2c000300914044400010006016100c00d0031440100c84107444108101500c4203034156a82e401140c8280c07081d80b03110b5001441000348071464903042a51704084005444a1002602414001c2d140c2031041c00340146030506400c04220084d001080c900c0c000d07004900c00848000b00045002e4014900382c41040103019048000044800301c0c0d03824940212500a103081c0b02e005e8100c40d5501d49024002d40e01409600c52201718104240c59088400700465203c1e42c0412811200000d80100814004070040282d16010b81c050340d441030b8220980b054100a07 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 286663291 1250 286662041 286662059
    0xa090303091e050705100210020d15030302160509010b120a02090d05100e06092a2d030c10121116120e1507260c1002030c031f 56
    0x200402d68001c100d440b420300b50034490108050401000c007035986681003500c146000b5241e810407080b110b0700f55000918800302124692006c4000c1c95100806c01c08140c40e845c0c004e4451a000e40c40548260007074a000c58545441000c8504941101070080e1a1005441c01484000c10040a00c0d2906600340800d4100d6280c04002032520b130f10a0019001c003c08100700d540c103c0e1400c044c240c46503882003040105100f0000b50b201060006080d8810901d18501100c03203100030030000b9144c1008815134044c02d00d00c02582c51007030505421030000c0b41c02221741c0905649130301c0c840c1869800741803c62400c01c45070103000003201c02620041c01107026103000050b0f000300d0707106035030401c0551401069030041c0a041410307a45000703042d2802100210003140000c1e40c40f500a0079a0b000c0c0714000405504000d4481245440340012400e4100b104c1202d82450000e40c00400c24072003240100d0303420860b030401398400c882c403920204403500d080d616444084a5031030280740082546950125000c140700103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 286664541 1250 286663291 286663313
    0x2061e2e0509100e010b13031a01050301051e070e010203130b0918040b070e0d0b0f010503070609080601090510030c0801050a061202010f05250b0f011d0a09030309 72
    0x224194105000c5031509080c000b480c04020b00d500f104100b0b95000348600d64944515a0450799200005c54032004050450030300e00301280d10040c10307104500c0d940d10007000b4070b00090b4100d600c101c000304010394034140000f042e11124504502c440500304002101c885c006d42c0076100048040c4122410b101c40021140102c1c100303500030004046021412840381c0c40e03d820005149400c0c401152640e04050f1b6441007255009007200b0103003d20862840c040da2503a900310387c66582c10140c41910740c2400e000c1031019407020302034503010340940040071034880d00170701c1e40b1310481d41031b000148166846e004c1000001c0a0180c01004603a032810301c0000821511030566000d888204c0000896041901204003140c49135440061180c4070a0b40182c0980c1c1c1040c110003405155080043d51446803481c40b540e500c4c5d80c41510320307590001c250000180200030500d148a611383c0b044444051340c8818071160707000200f1000a07410a619000108032120f280c022452241c840c0c00e0124404103e41c0d98150822 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 286665791 1250 286664541 286664611
    0xc0a02270a1a1207120305070206120106080106051804050603070f0f091d0a060b04110c01020702040b01090f03080a140a0203091801051305040f0609080a03060602061e 74
    0x40d03222580401c0551640140b20006181180d00d401e04040b02c0c04940c2d19a4500d11410b80200c405c04d800c1000d00d80200c003181c1c034641c0d0050581d0b0f034665918600d60710fa01001c2c01070000081c1b0810021400c40e02600480380c1c4501c80d000d400400210703150803c4060640100003d4160140c80000501c5444000442c1d01030015401c0030314183e4101510b0404441c0700440c1000c24080f50705075488112004661540e103150058008030300322240ba0b0201c2d0150007420100b899600c00003c9400b2002010b5000d02840c503c211800e1154540c00001150b11304014000c500308905c443d1700400c0020323890303401400400e00905215510310204040501c50340c208001290141e000060b103600709190890040080f61500f140140c2a5410a408500908018561055101d40d10808601401180a02c42c00106e030f0040c006e104224051500e280d154000e061071002180c10100c02040c0c0340d001044180c0b04041881d48524044502d01584180c0304000e003541c0d106080c540c51010158940084101c164 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 286667041 1250 286665791 286665811
    0xf0a091107030305090c0a290406090303140c07150c12090e0702012007030212040f06090f0803030c0904090209091608010501080303042301020a080415020c0a0227 72
    0x5200141000383c141c0d00c004164200e950482049081300e503480209072025500000041c00d0740f1300582c1e0407070007500103030300d6000c0c3d0f207440106000860319400300d6079900b60b91080e56488551700000b080c0d24000e00a6444080d030700d030014101800b21900c2070030010701070003851800760120441c03500e07000b180101e0f92001500055103044140081c20305803c031076800c98600c0c4001c10441c06030a040c16501350900504d01001c3c903002404000f0702d40300308211061a01d02144c601c1d80d540d0b803440a0300605906114080c0802c0da400e900003a00380588500300c2c100c60801e0040c5d4a141d1b81e6800c845001c1d07215012859000e40d803070141d080540c44038000741c1d124605140050945072034840504060b5181c50744002d24907810b01006008450011054903040743c0d11010604a0b41c0f01802c4100780110501a20702880d03101182009c1500d50288510b405640180d210300e081002200595044e4400c1d280c00c04601e5001140c5440107080500751807011219400705080c42d4651138624006000040d0f03844800 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 286668291 1250 286667041 286667047
    0x714030a0311030f0117030c060a0f0b06181309060203040507081b030a08210c0403031d010f0804020307090c03050a0b040c1403150a06021c0e0f0f0a0911 68
    0x3440e0940320300c080440610341494110300d031200f01d001c0251814022199002e902514100310344400700141c401000382038090310420b2a152803404c008000681420f4405070624100351003c6c14070804807000c1800e0310a9107a88061101c05000b2180c9956401b010507503640c8264901254041c4040d500542c400d9000d440c03420300d0294101c0c54040c030618030310701d924400000b200c080d40d00001c035822029485a551601d0b034801da21101c1400485003d01d90007401c000c0f0420800199050091090303e11135120030700d0003003684e031264101c1c84852424074003040b21450000038082c020f03a4004d0707100d0310007800c0b92a541d88070381c001016140c09140460100b07031140f05126080102e8000c40a0358101034404011004501c3c0c0e000f0048280216814243c10001010030561040101c01089030b0350f01414003c1802d90311140203603500f95050780211583d00c4189001c07a514800c0082011120700200f43e205100b0b244001c200341e100e03145101540c03003580148001580d5509000d200b01c0782c4088800251 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 286669541 1250 286668291 286668307
    0x905040903021005070e0d02091806040f03090b04150c020a03080d06030b0a0b0603010e0a09061103010305060a05010b0f13050310050108120901080a0c030b030604150f11070b060303071403 83
    0x1080e40e60144c054806c2c001c2c10301601c080303034842c0750130322490a4049552403166155640405062581442c6105d4170f40129007c10061040240ca071b03241700d612965903240420380d9245182c40c54040c50060214510a20f0217070700d600c0c0d105948401c131050004103840324056a0b03a03180143c07a844407806462031901c0700350070010b20400ca00c402d640600075403402d004180c40a000a5010b100500460300448a010301280c0ba0340910f138024140540d00034803c21900184424041e42030f0000d1004544900c241000903000700e20b140140b038100c40c03880042604061300c80c3c16102d44c0c1c0e044041d615800303040b50702c1d00141e15a01044110400d500c40e0b140000d4075410010118200703042081c084d0101d0f0010420b80c002641e0004000d5030185808100040c04000004102d010f860300041c0241c1c5172003130505000602c440340070710800184d051041008401c0188003140c007a20b03400300c0200030400d000d0020501140070702003142d0307210741c0040569191001c0c07a03862500000102c1c101401315400030801706 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 286670791 1250 286669541 286669573
    0x90a320111070e0a0c020705031213080706030f0b010c11210601090606020d020f0312130b041a06010c080304020603091603050307060c0305190f0209040c08041110020d0807090504090302 82
    0x885c9442a2002c1d041c440e0600022036600c100d10304070440b0b0240c2c0040d0444690703510400c4900980380400544000503903614009011340600c042e035040d40c9260280c071703051960151903001d1400e40e21183d6101c183e094081001082616000c0c0000b4420f1006078485c8400000d0240e01e0107408000c100007040340c00c0c180300a04e1b0a101142d55001d541c06204040c07030010b0000203581480b080c0d0200140302d81c0c1c904003900609a0601c2d070041617268901d0902041055002680140100701d00d0a00140e96030780c001121402c200003806005070000b0000304026041840065901003002c808a0704000c0609234000b9411040ba03009549a030004a1820700b0400c40e80200c4400600d540340034002810020306107a401d43d51520f45010503640c45025006030480e580596518a00090007081b24000d41c9401402c0fa450456003180c1c10303c81070260100e40c1c0340400380e1a100f00b149a00600c4e078000b501100ba103407684080c11440c00d101c00401d00042c00d82d101d006000f1040d01c00e5028140c15070b04e2540c01 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 286672041 1250 286670791 286670801
    0xf190c14070b0f010902030f13030c02060c060403031506090608060a0e0c03090f010218040f06050418020310020414060d060e0c120a09050d0c08160602090a320111070e0a 75
    0x1150178940104148214a0401c020084c1c00c143d011940c14601d018928041e12201007070300000350000070109590814510125000b40f04500a850038040c800e110740c440d0b4040080d84c01074202047c14000180107a610510445070311600150415000c15113802c80c806c564402152804018030f000006c01c8440f1409020828039890b40100940c18000d9a58070200344030030800007140100c1e070301c650b1080e1284490300054020309028008100c0024090840010460188400da029200d00b60402007030703200d50710031a02110100500f541c074502403481001050340c4054011031600d5120311000c903002982200c4a401303118010080d50b42e030310603a60307072003c40c2708018000a0024035260070440800c0303000c980542c94108920f4908100612841c1208103030085608407100400c3c2d0f00202010041658000e02d0402d4040f00d1185241d992034914152020108610226284845d80c0746a00e0b032a02c10418102604e0505100e44000005210280f40114907404940f14078914014894150030603c94 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 286673291 1250 286672041 286672049
    0x152310060f02010c0c02130f0c0210140603071703040306020301120308061002120c030c0708010f111e0703030902061c0c0e0d2d05010e060f190c14070b0f01 69
    0x2d20604c0c070044009030181d40c995101900481c600000d008104c2c03025402a000340401100c10004441c403500002d607a1102d443d0f0300c552491510015504101414552520907100280241405401c02d1400c0603080c0198801030780b03511060001000203031290019501811740c09006024181142c103008004802c05000b035801000c60705030135400c0b00d03408103003111031403c00c3c281c2a5966036008080c038a035101c3c1307501c1c400c0c0c54020104042003010040d008610903103007450051200700b8032a03211011030b03c1509c1007011054071595031039403000d24040203020194080c0c20001403a11640d0085405030348510550075852680812101140a803407046110300c00c0585004e0a100c2c03c40c5010031b1440004041c00f03080c0260100100c1141e441c10060300e8030740d075031541541031141600d1078464042c02442e5201e905502902d40043c0000d041c10341c241d8881c928408880f4046c881d6185140d000300800c403031340810407e1802d148010900c1480060841d180300c1e00400000d40342c2a80e0880003c041a00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 286674541 1250 286673291 286673293
    0x305060415050306040b040c052806030e190302070509010e0a05070203041a030a0e0f0604140c0f1c08130303110309030c0108070c050105040b01060318152310060f02 73
    0xc0148295100002d11581c011b9005240c4449901c65042c03401c1800700070341c46581c2c4000046896140510f2090700d0b180c0f0460310002a0700b04545640e010340995280b1803043c0c4959100c05810400c0c5020300704243c032054000d0041d101c80944400c01f0820f032103400d82014807200700020500c41d41003902c2c815140d110791284059410a42040d0818000091b44015964810f4010020030038003020381c0e2112415410240c11034810002c1d0560f01c030344658080743c0079600380b030f840d43e01021400c1010900d8002508000c0c28005242d00d0f100030003000152054001281000c00d4410400080e032810080076078038555001041d916103503140c02003030002e00c500e240d4001d80040c4a13021640d24002103403000e115007405c2613001665503041c11607001c40c1900c00509158200700500c028000c01d100c0346810703104155814804507103c2001140c86450010700180007014120358185000c00b558400343c03e180c010382e13044440c403150f1203031001080400d0b02c00c007500c2580c002080080c1d5401c030214140d4260940 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 286675791 1250 286674541 286674581
    0x16030201140705030904021801020609010b10030c110d030b03010b011b020402070213050a0614010503040c14030313080102130f030506072303040c1e0305120703030b0a030303050604 80
    0x98002000d0341c1e8010941c1880c840301040090030004180161000e480000e00b045440e0329918501c036504014148840c0e0142c06600003061036a407060051400c0e19402600e00b41c000c03080c0d18000c41c02806c103440308000700030400400c1d014001082c1b0801020841607500480c41d007014030708146c00c461001802c035040c09550640c00103e0b01030841c009010540480d0010b0701c9615500100d1800d04042074500d10f014602410003440c8801ca0b8000415185191401e60404190a00554481c80f05036406010003020500810030350040c40c0ca0361080da20060107681c20840007090144600d000380c1c00150b52030350041000441d10040c0c0303401030001c10800380d0f103200c6070340b46403649600d50201900c05400c0005000301c410358034004416500ca41400400d4442d568a000c0c20515403030840e40c042c24a0301c0145150f11f06010740f82c0002d0405481d04440642940d003030041c0424460790218004600f0706484200301100c965400d0007134401180285c80c00719162501e1404c010494030207441c249100c003409 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 286677041 1250 286675791 286675793
    0x1080705130308070f0506070503090c0607020102031b19051e071a07050c15070309052209140a03120b031b0d0c0503060a0c2a030c0311031306021603 66
    0x1501c08038201da8008401aa980100381042c41c4207402d110000b404501c1507070180701c441c03540000114415000101035038511403d150402c02240310750f22001c2c4c01070703009002448031144039400401c1465101001c42d0920740d0f00c800040b2511411078000e462541141c24154862031084400c0b1246080d614044e042d014100b00118500051250441c150f10724041412410004200102c075041800208080b000303240789440b000c51640040c604400007000000001050f0500807241414044641c426002d04194180d01c20000e00c0030090030340340343c0700a410100300401c043c0000c0720b4043c0280c0c0d94003031ba103041d14002c1c0f0617101d52405d114065800301159052003c407011200c0d1110f030040342d005022016606120340280496000182d1500981d801d1100355403c03a07000801521380d9854585c4041ca1011010303003600c031144558102851034070055000680304110201c0000d101e8140800c59130114848145150011844400c265210038000d10805030100500180760000382c1492600c9411 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 286678291 1250 286677041 286677067
    0xe0109120f080f040210050a03020f0315131a060901030b060a05190e0604170a0203070e150402030f011a071a01030309080a0c150e0306090303010923040206090a050301091101080705 80
    0x41c262014040220105e400c0008c503120b80c0442c0d2800c204040c50781e0300c82c142500c204502c0c2580c107030058803515042d03100078620b514500502d4020400f07080c269903c601d000707040c405035a02c000e1701e4504040e0343e440041c03415690b2002518011070079179111515000a1905c1841403610104004144019180f2004035541d940c01100e040d00c4904a8001c040c07440c503000c081c6441d0b0582e000a515000b0503c0c04214020151009803240c0c808002640002e600042448124802500c100e2400c1d00300a005105d9582c000e0428402c0c04407928415103450b86075200c0c015818018403015401100d184010011705a122082d0303030242000001038141c418103927607011140b441500c00c0080038210312020060f0f0900a61141c2c0f0b42ca0400380c160750140c90600e0010703071294424041c2407081c9103012055107444815070340244940403103100059242d2500d4080104e29000040c1655201b2001600400c0c01d0f00c00703005207049140701e400d003610223014410002d003500000503c80020040188841040300d44 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 286679541 1250 286678291 286678309
    0x301090603020a170c0609040b030d121104051c11130b0a14010509010806030c040e0c120f030a2f060a0507080721150806100603060b0703030e0109120f080f0402 71
    0x1404450aa40c7c0e5060140464050b1106010842e8180140c00201001075013105a01d44140a00c5604020381160980d03442e045000314000c00350843d07040710b52000765900c0311201e448140d000f11129440b8620580004451484907003410140700e448200310211800c0c43e0940070041c002034a14480140c2127600028414040c0340f0301181008080c40203e0b0782911305201d02205808050402c2c022000f494410503039500c09840b0b030350301826400506055000d400701d6a88540c2540350055803a21542050444103800b00d981ca082d000940b24405508003074061444001e02984500a03142c41d1400551040c01c8600081000050100c10000c03c105c1c0c55020b004582403550a116000032240301050803002001d402102e584070b4510b143c00814090400901944500c107840299900c50741c48040843c141c40ca64403d0041200d014003500d0000380c0a40c02401c04481c80e40e000055400f0542c44000104985081da540800c58007841c1e040483d0744030032010f6101c2e0043d03036401a45e00b02640400d140301 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 286680791 1250 286679541 286679563
    0x60e04140c031209060319020d1a0a03030c080f040b04060309060c03090b13150c18080111090f040f060f0609140a060e060c060f0f07110d030f02040302060301090603020a17 76
    0x80c0c0000003070031090458904240201009008544900a0300c1c0584e00611401c01c4d4201c400f20ac0185940c0b00d868012000c8040e00e0385a80c2e0607203034082542d50041641c01c94400d0705c400711028400800c80304031120141008101c00c3e41c01103803d04007400c01c0400c03076100c0d0340002d08250800d0030a101013402c0c9400715402c07005c03440d4016042d0b1080c1c200a11002d45012040a4407410561500e0740158046560f0200d80c00c0c170560b01808035a9444d0140c220f41c03041c041041075080921050120740f500005040f0212000b5001050751440b403031680b0308443d0b09400084060a10702c9050142d583d11100060281103003c0188110300740c4000059030744451845003104002080e51705e010252908419525607a030079404640c0c00c5e01f010030500038603171400c82d16081c1900d9410001840c440c42a600304508036403400c084c003141440440210064455038140b500c4940d001c100010050716524000c0d8001d004806e40082c0d600e00b10b10400c400a0050303444850541e608c080d48140300000814801444 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 286682041 1250 286680791 286680799
    0xa0c08071e0509220501030b2203140702040203040507080613020112020a030e100f111602090405010e0f0105150411030114040b0d050609070626040501060e04140c031209 75
    0x43c000728000a03000210782c20007030340d039210015200e450620b22a041241a45e10a1801403802d41d5440a00005250a000744400720b050301d54031000424094183c40c50f9100134460b106140582da80c02007026684140c5007110305910030030301007004040500c141030b0802c5024a808460b0302c06c0e500000d120f4070100c600030503100e500046c0c104005002c0d80c0800d982c41040415140201e40d5112108010003420301c0300c6c095a421300301a4040c0d05240c50031507007005036403000c42d00500c206409120121a00030411241590303100d031004a64a0104a140c1c10441400c0000c0390610b1700c501d05e005c4442c1d45082c142e02070f82c1420607200c0c0b5688564260381c15618025204a11500001c00050203070454280158202c02021081380c00d01001159080c465405541143c001c91341e40c0c5400c0350b09060401c443d00380344010200e40035910402d1202290014000d03000031451544458100400103004c0d0340c100c030307030b0124245510190342040c4a20803004c482180074044400c3c030f0242c1c540c1c2da84213444400d842 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 286683291 1250 286682041 286682047
    0x402210a0528110403060606081609180504170d0c021507080f0c0f070b011d0c09011b120e01110f0601050607020118090204091a10050c150a0c08071e05 67
    0x1005015401c1c1c50045400560a200d840d55442001d0640081562480715029080f5400710000d40141d202008841c1c02030017000e110cc3c0000c00349e0008100240003120400340f949006800715444002410b400005400002102e51b10034030301901c1d0910103403210300c0300c206085c100500c854008801642c0314000789540091580ea004042d54540b00d20075501c2d4840c0004100304050000c8610024103071229a600906c01e2080140003d241007402c45002105003410480c0d2107507944280c1c0e41b640307211086c4d0b104103c401800c2d980c60480c40003011195001544003129414550303030141c491070b036800030345014126000e41c001601c0d40f030700c0c0d0502440c0e00825001801100b1a44500709030705900c1d89610f4a64486e64403506000081d50291068024050070108600c042100460511003420002030a002c1240050b480c1600e42c1d4000001d541924040e040c0c18488605600039044d1090310440c40008003083c03060000f80c0861006081c4400700183c004220002c0740800140000070321203030a010352 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 286684541 1250 286683291 286683311
    0x506070c050709050c0319020705061b0d06030f03081e0c091813050d0216030618050d02030309070608011508150618030616090b090402210a0528 64
    0x803902c4401d910001d01d1034600010890449031000280d8080c074401d404d926102c08040c89107005a01489401800c640c03c0040801d054021180c001c0781100070364810a800e0220b103040c003c084910300d81c400d0351500604145031080540c03105001c0c2c0d00c84401c003080310b00b4100c100b00500c03580b01c004018641007100001d88100f036070303500b982029070020408002d05c9580750404c419070400100c10b82c1103403a44103102001310814004905100703110340300400284040d00d5a21000d02a00400b80480e050708800e4203003102080e000d020402413861550000c540d203050015145103480b10550101040000385001030051082c150340300c0411014500d840c1b10280c84205018501c0744030303240c543c0d42c841c0c000603030710400c1c241ea8225511442d40c12425100aa550050095510603410041100207403001c8001d104003040300b800b400c07031942c0280005081000c0c0c42159041144403a00104005d41a0004c000080003a03010300c2c1c0d40002015054810035580b040c50039001020010080c07a403680f00d40c0904 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 286685791 1250 286684541 286684543
    0xf0a11010212070c050c03010615030213031e0b060a03020105030601081e1008070e0f18070e0a0204150c0203060c091504060f081f030618061104080705010c0506070c05 74
    0x14002c8035140c4652001070800d00d801a100c1003e1190444043c000d11a40c81c140f1310341840303114111441e032a00e5420317040803403400701d00070350001f0429501241c18602c04004030300700c048181c292825148504891003a02d08042143c840010030891181402102c00c0c00140d0744201520382101e400e00303180d10640c44003100b00d585100c81c0c813004034290204004001204041106400443e0a03800549200301c1e120f00c2d11050383c2e50210f40c00711422100c1404108c2c48102c0c25260703603404401c05c0507039200c01c0d00e4540c1070544960a40b8005243d60b00820284507090030103151612050880c01e011a140b20700ba03010985650f001040350042841c04a0001d500340c9840082041403603c3d6000e055a0b41d48a00d070107010f4180d0340c800400041c0030303140041c1d003204000c40810a0071003040c80c3c0c01307a914a0740d03448a02801e001c041d0b40c0302c1e81408030000000100513002e003070342c030a04601c1150748132800c0058107460a16183d00050400121b0003161000c603c0103e50690440380790714020454015909280b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 286687041 1250 286685791 286685797
    0x20f070f0f050a1113050907030b06010c050304060c0606050105090f0909070e0c120108070305120307121a1f2003042403110a1d01021f0506040f020f0a110102 70
    0x50400d00564402000300304c0540204050712100319003c00c40407441074900c0003101ea007100c22101c0d5610400003030021130300044000c0e0b070042c414540241445130300e550303140c255002a800310001c1241104035000300140d03405030310301408007842c03c0350905003803030006002c0002000300b20303000c3c90028010401d81c034010300810000c1c02901400c40d030181849100304d21164409480103016207244000861512000318400048a80007002402590f041195101d110340c8050a0502842041d00046414580502a00c0e06c62661580990b010700e02d079400380068110a04840501c941c4282003440c0c4554000100d0928000d0310040102c0d60f11010400900d54440d039040f124031a8410303120031441d080600d400c506a07a10b00e41e0f0901c6181d1b4031621000b250f02800000d1004030700d10305241d80180000748005a00d8400510445074001c0041081103070100700039241c000d1180c0c960701008103908140c0a850714480e00b80ca01103150691640b44001e050188d15125400c002246a682c0460034003501a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 286688291 1250 286687041 286687043
    0x3071d01090519090311010e10060504050106050f180909030306010210020c1002070809030106030c09060909080315030106211707110108070309021e03010b0f0a05012307110310020f070f0f 83
    0x3000300002d4920680d49d104880351500d02c20034100038010035242441e0042038100d40e401d0311020305280d0303181030114040d0062418440854182c1d9000301940d40e41c0b5581500810304400030710740e203080c22030009003031045450098031594010040651403280010b440052064005d0006881d405146000f500d5072188402d071990541c24464040144021034089404031b659104c41000321076500d042207030540c4c04000c406400c0340d205000095810340c200c03000840d20a0014000500d480d12099450460581d500c600380005541001180401107491600135110b282d00e40b0301c6092460950fa07241078010541c060314100706286001c40d003001e010740c000807840e50380145041000e0400700070800561440c1c828083c800c1d82050146e020900388009281100365003d450a050541460015550f040c12070010f0808480b244900c4240b50300c070f120140224500c00d5203542804610700c001c0514000382d02c09a040028030411002c0f43d060840c404a031603d9501080d0000c0310680c40c10180746411003150 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 286689541 1250 286688291 286688293
    0x10f170a0c20030f0c01021306020c0f010207050603070f1205151e010e1002030c0f03040305121c110f0c010b1903230c03071d01090519090311 63
    0x611801040340d400007402116956540361182100940030302031050140461400b40e00100708000e54074480703070001c003410070200c00090314001d80d0001c1e58401c1c2290ba440480140c101c4d0411030091314121203403580170b640910040000383c0c01c0c00c000030894440680a0b03402d1191010350302a02c40d001e103103030342d840300401c000400131403400d285c101c1000018940007034030031030002c21f00d1140b0030340c00403071401001c406a6490200c501c5040501c041504204115000d600c41800382040795081000b070002007010a102441e115072542c50207910b41002640304100048007806a10004500010900340400c40310300085181008214115210f1141489020030b0000004848a0070341d01500300b105025000e84488004804218805414942a000050208500c4a81b4009018401c0181d20f100c0109100f902c003221401000249882010342c8040320909190700c00300d8036034804181050042c1a4214240100d00d4015122a11000301c504601d22042e9a00002c4e8141441540c0360016820840c5c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 286690647 1106 286689541 286689587
    0xb040e04060f06051018050306040209040b0a2316210f02090a12030207150903020d050c090903090310060b040303050f160b04290105010f 61
    0x30a86400050f00c6640210b5a030756050300c03650315031400380c44000415813158040010000f0a61007944280c01100410015864521105030302660203860031096545210102c401440c41308418030303e01c541040d51900c82000d004802d0700500d440348200c1e80b000c400e02000c0340c0d41032200c49210522480d07000301041d0411075800400d54054130145c05400d2080315400b00d41c107081543c0c0082d010070350a0840505243e01031024502030f00d40034010f0fa00746000002d001d4641c43c1e261000034000d0f038044621009200040c866030240d0301e802400d10300310f820842c80d2280c7c0c039002000706500c680112040c220f042d0406110311030031100b41100950400d85142c400b0764603904240781c441d1008000b00121840050743c1081020b4251007a15030085130300306803c014851000000788520f0b010007450700c07400c4100340c880f00181101e609103050070681000d41d808581248a10700c407903014000f05 = true := by decide +kernel

theorem cover : BRFrame.Cov 286510791 286690647 := by
  have h0 := BRFrame.cov_init 286510791
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286510791 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 286510791 ≤ n) (h2 : n < 286690647) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
