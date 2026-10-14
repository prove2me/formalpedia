-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3410
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:34:50.938752+00:00
-- url     : https://prove2.me/submissions/76afab27-73a9-4eb7-896e-cbe8fa0567f5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 613129496 ≤ n < 613309352 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 613130746 1250 613129496 613129511
    0x12020306061909050f0402031302090601050408070806060a061b06090305130603020706050c09011d1503070504090f0605010507141516111603120504091e0c140406140d 74
    0x7030039014184c02a0b0303115030100114440246058004c582c480c2d1030002541010f00c2c03c075424021840d002900c50360522500703100200b100c0c142045100b0040112400600740c5003040c0c001d0140350b010503040901009410715008a2130240c400300080c07815400740b00094020510b081c02c80d110301803c000d4100e60420003e002a80d2581038002c0c008841c094542041a41c0303032880c20f05800c2c0300d03d40e040f90108081588141822001034006e4035124000350424210001c4e1503010809030348200c42e43c034045840444c00f8030002010f8418506200f403042d204124080c20f00002a00034002c1c039000a054100f055450301c80d903802800990030080c400c8030755103041e01341020000004038100c0400400036207040d160365a21100001e580c7c8003062105141c03000350b403c41c0ca54100c032811010300030b0203020040000040070182481000c8403102945e0071403010107103e002010070740384026503100402c640706524404916117402182c0841e4031600b8000c0882e1482c0007112464002c01402010a500e080c05 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 613131996 1250 613130746 613130797
    0xc02150d0609240f060c060b04020d020c0d030902030304030b0910090c080c030102030c0f07021809150f090706031a060f03090114010b0a0509040e0f011a010f1202030606 75
    0xc081e5520b09403144a50000f50a1000010301c2522482407003001c2403022030410a103400703804079001250051001203054030040000c00c0c26070780028030400c07516900088548803c281070056403044000d5141c2800b0218094001942c0c0340070f10701028100c090440003045001c00100802900001d00c927205104420b400d08009900245600c035404043c000ca034030095542c0340620071240704181c40f000403424610740611100c1c49800c50b25040360840300c1c0c0c82c000076170b030307018410b42a00c100e1880000b424214070b41d14807050b01d200e01411003000b81c1082010f002c01c0410206003041070310301c1490001045204141804480758500303400310740040000800f460900c0f9504001c5201d1340801000344040001e084400d2000582480f40c5c00b040b8134280300c1224601d104400428103c0c074000c201090080c5000754481c02c080d1030781d9980d07515a540d0703d8080301020b4503207800001d496090070106d122035070100b405000e000318420a02d50641e400000100655104020381d01c12109920b10b41c8150b07001d416 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 613133246 1250 613131996 613132001
    0x201110f1b0d2004110a1e0905030303010f050a060504080c09060a271401060c0b06060928050906010f031515050a0206011428030b090124060c02150d0609 68
    0xc003040e01450901c449046940c02004c1121004001d41c1d483d44006c1c1c2c9110011400c5a22104515003044008c440019071980d04201840c0a0068036100708404c038074140030440c6400329030388248140702e420300080102980205240001000540d02c490440c2c0d101030008080a000790001a100820121500501004100310f0b501e02c10540c070b030811101d510900c03010b80c0420244603e50000d80100c00c0c0000054100640c5c41e000980504182d00f0001d0080000303052942010503132030a801310031a0240c08548100d04600108070a4038401002e00300710740000c01c0700500d01011000d0540343c0072001c144252136481003005051106ca50f40c4410307401c52000b0303e00c0d441540b0040040c4514400030400200c0c80203580300b00203008008081c80310b04403014805440014130000da5513020400000b0115401d44040707440b88082e080005800452101500e03075280043c0d4001200b15900303a41031010a4001041c2d00110360111080f1014115004180600744036418000700424184040010400c8954 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 613134496 1250 613133246 613133303
    0xf091b0d0e0601290d0b04050a09150605060d0e1207080c212a120405010f0c08070803061f0305010303121406040b12010501030804030201110f1b0d 65
    0x2541590540d907600c031306800100d081521051100f1200790742d40c40c1120264001040940c03003014003c01c080d0340d1040018129541210991000f0703444469500810100d10308100300e021410700200306d10303400c16010500c0344c0211300d4207500309139650901c442150400c0008110740100405002d954003001d2800c050346030411100c3c8049071140140d00d6040005001d06100c600703141d0484d00d0b0802c6001c0050301d180708090940d074000c48000840031165a84180014030300e00c080f44503041c0da83d130b1074503000404080715000044100665a0342900000e817445080b036150741e810110607512a26400e00240020032580e0070b2110401451801040d4030f609034000d42e040324000d0b1940c4c64560f168505100c1902c1940344c00c0120301d4103490006003203260507802400040c101500030200c4680d288480b500719582a0020781d524000482d04004541e0f005207102d810380031710b40280540d01a01c00c0259901c182000b04842c803e00300100740091a101e110038450020740260302081d8030001030204101d9400076 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 613135746 1250 613134496 613134521
    0x405030703062403031e1403240a05060405121516080601051c09050f07080c0301061d010909170304030320030702070506130b030106050a020705010e0f091b0d 70
    0x1c80391560100c1d1030f480610000c481c3c05440d80c2c411055407078840390010343d90940c21801d220060031100c0d111840c0c0800f83d441480e0030b0103101401d50311440c07101e581d02c041c608031510a0798403010612076511203200b95400c40c0d00070340300c01300c0c0c208144480e40e0810031200c3c0b0b01102014403004104038546209075080345c008203030302c0d106915155640115003a114200302051803c1032054008031107115507005000b080d0144080c0c03045032003d60101c905040345940720b88200d5111811005a070b14080c407524004102001006c650700421448024003100140319559103e0741d40d403c0641400100d010b0b114070804036080190380c901d4180390150052080428140700002c90400d01c04100c00a04c04132405901d80d40c0080101a280c0001c10042e98041c00440040d11001c02000507140d0701800514042c4c40c1c1ea495590321690414002450b14000750300c80c44c1045001000354003140c40e82d004508004030140c0d610303c115610514281c40902082d249800d4100b03001540c06000e400c1541b100d0750a0a0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 613136996 1250 613135746 613135781
    0x90f030f0414090606090616060509030d11130621090303050118090c12031b051e01110316030920010e0411030a2a08270a0206090402040503070306 65
    0x442c1014828071100445195402020801c10724220780740c40b1028001680310308004103940d00c1982d42e4407058650954128203103900109500c1e01d00c081ca40200040701d10348030401420150030350051507498420340b0071b02040c00340526450300e03141801e407070400d01c4410801702401107010618000380189824480c140621203841138038803258406000706200540c0042c9540d851a0500154090100000308106d081c071655501003504400d2198040105070300503400340640780e028520100400102542e200b03096403400c04a00301e13050442007540e070000c18404441440180f250300076402003198000140100400c04140c00c0ca0a0a50311001c10702c5400f84ea40042c1982d062080c0400c0d80d03c030039550305a402050000070040e10076076101e001982084800600f40a410340440400d020080c160400094000d00420000301d4150101148130f928403202107080400c040051501c0c0c0240080080c4200400076881203aa40c690301502c01801d00107080c2e80798181d0b00c2c60514000d00c6150f0002d101e112 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 613138246 1250 613136996 613137029
    0x30f0a0e161e05101d060d06030f021507050d0f0e04091523060d110a0801020405090f0106170702100f02180a0503070614120106080a05060301060b0403020405090f030f04 75
    0x41c409005119024580c84441720b070f004a44030300101c501c0c0c0981140d0012401e214107050b0544600038103005500405c4511894025801070001003404070b26650611305003002400d00060000445002100c1c032031500c4001c1d1030108000300d410ba104031840692040c2070010390070501455807200380c0440300c404030800500b4200703070710a0046a202c5807125050700103c2d001481d0307811301071441d58136a445182c1126940340410f000520601850304030b2241caa41c003107801c1c001428a4031940750040c00220f030349005585003610007000c1c001c009c070a040003213500401184841d80200103c0c0d07d0761003500c0040c000580000e0400c070080d04441c248012680500d5144d00a80c24501c030030106840000c0c02512200c0d041c2141641c2100345100001c00506040040040190801107420302074080c940e58500d41741003c074407142c156207000e4240303446645032480410200d418801114112581507601107926521007480034240722201e4501c4440b40800209c01c000072070508010300907a40c40c003c82070f0aa0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 613139496 1250 613138246 613138249
    0xd0c12020a080609092a0303040801020c03031b0310120204151211120712051002130603050a060b0307180e040807030f0806090c0706020c1506100302030f0a0e161e05 73
    0x40454002e2040da0300001028101101029581b07000c42206c00b6040b640350136540c02645003281d220340303132108180c2c04c04024400b4008020301c583c40100c04a140190440c10400340b1304000050a10480341c1c5013038001005c03021034555801c0400c03070b90203014140d601c1c5952605544032001100b20708489401c0801c4101c00c40f843c0101e500c00e140500c120050800300e050007002e0802d004403100607511072240420140c0003480034002060515054a24081d8051070f140028055400c0909040c0045041840901038080c411064030380c402c4161801c0302403029910300840d2844629040b0300c8075400c5210401061090140080c01c545101c1d94504800c40303c3c1d504121a010016030320070703070f01200c0c0001190b00c000140018201280c01f03580018074240e12182140c0c6080d10248901e08100108401c016131407034468012400c41207903007025495440c2c08140f44c00780e160000d002c10f011503660740d50414406400c004a14143e01140d0500c4c64003a140c0700c0742148203001e40e80f01d104050302c0c0300000c2600d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 613140746 1250 613139496 613139503
    0x72102130f0b030f0f071401020f0607021b03010b2409033007120804080d0507090f060201060e041b031a060913050309090411030a0602070203070509010302060d0c12020a08060909 79
    0x110001c0000e00380071b40c14003039000a45a044103d007070440c0700741000004e4440061010314080c0c007030ba400a00d5114003a02100000092910040d8400c0c0d140c84e10800c56034492406031082070407559000c42c8440900341c1000254056292400d4243c4207940d62120011481b071801c00c202c4131407183e444d00d0031003c100342e540c1c28400d5040040408164a1558411600074103406801ca4424070f401410880c008031088106d5400303c2c2e0110000b04502001c00c05c0c0150741488030080d00881c07000384401e50810f101d49003040f001400040c00416550f06482403103584d48500d20285500280440308284d0200710740880090036104d9903c102210701c04900c1d0903141c0301c0401060303540000910f0412005200b004181603008001380c0c3c600c025014102940d0341e0900080034000d11805005171030720500d0042c146030201c15080349005d001d04400500240c1d9074001540d03190541407801241c411402e0070100c030800224424221030301d00104011100d5900044020b100349810303501c4103420703542d2001c140d40c2e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 613141996 1250 613140746 613140763
    0xf02030c0a030209010215040b0403091e120c05150703092903040f170a121521061404050105061f0513080d0c0311072102130f0b030f 59
    0x8000d410024800841e00030f0700940f00400b41401542e031400800c40548070b0b20141104c0454100340c00e10200400c140e0403c44050240841418174403e0b00700e10000e03442208118025910051150340c80c80b01000103600602d405000054050980c040d45d086080b0070790740100c00c00b1404181701d40b0001c140d50303900b40c1c42000c4251808000070b00b02000f121040480c0d82c405001031b00c01d510100040c40214400d4400010078601c030300f00f01691450010b800800301d8521200c480c50b00b40c101034240301d01c03c0d8007100364020740b040111032100103100c1000f048101c0c0c40040c8002d00343c2e0f0812480707811102c03481407260f02c254050130090182c2d60343c48040041169445510042c81e4085941c103000e81803107540a018030480000071171840c10344504034580341a102c0d2880c2800140001961010590720000110210f10b08400810003141020100550140320f1030901c400c180154601c2c8056503034000c02181c20124020003040030b111801408009000303243d51050203840744072440c03413460000042003035 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 613143246 1250 613141996 613142011
    0x21908161514030c2206020f0102340605091b0103020c070303050c01060e09060709081204090f0209130c02010e03090a0909020102070302031209040b01080c07172a010f0203 76
    0x21014406510402e0a0300007500601000a003402001108130050704490002200750329811078240c541100285400d410b88541c00c0d01c2c0c0d005008410444a010b40c886101c2d46507040c45081048825200c0b407140b002114002d080107090070300788003004402040c070040c10610080d205290703108010066040e8454030b00818615030103030000b080802d2040024080940002d4000304165590704500d0300e010b8000d0712001c10a40020007030211007904900c04400601458000c0e0501004d008800d1401e0b015511461490302e40310080d041c80c41c0e849038101c0303c040c41d00070b1008981c0000424807034001c0907212030360005586001100081b0706400001d964001c1402010440c3c0f00d1b04280f809800f03400c408004130305500c00d000300840181d8003400703140105011650829111402c13541004150303920807400c00e051080c0782043c0001405a14112001182c001141035000c0007040725800303480c801ca004911750380c1d58900d40c1111403103000488000e03a030300d0400203211548003d00c0b024201c8c4810754200 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 613144496 1250 613143246 613143257
    0x50601090c2010050a24050a1202060403150f060e0405070608010b0d0b060f0a11060c0403080f03040c050a06090915060e13111209010507080702030904090219081615 73
    0x401c030640c495002554402c82c1c00002040d542c1d41d8a0391b5450382c1c85004420300000035045800d014900300801c181d030040c6492207004882e40d03015004070341c00d413246000151200030007441d0a800c0c0c10302c80d040031442e06a0300f18200f2020380e44020307010b00e014044d101102c82e030040e01c80c00900140b0581c00380741625170840b407003440d01d6151140b000040c10544480b0b40c0260081c400f2030a041c00e0b950182080d0795840e10b032160140c0d1034500260a0560003020768803035200a06c0140046031802c415140e001c1200c0c43c0341503580d141c60508101958555000650080518002150261b400180318046903040401444408800c82400004001500030f0400087c02000d642c03900d0f15080340421001d0108610000366451603c0000c0351592000070380c01c0140540000b448a0f8036005d01c5010f0b800032061914044a00341410025120302c1500c040c91b110342c4d1280785880566442e132030b490b251080d503070b400228002d0703035104a1511210000d99044441c2800800080d184080c500100e0741c90f00319036101c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 613145746 1250 613144496 613144513
    0x309140c011d190f051c0c030f020d050604080d0f090510092105121f1401030e0f010c0212070305070b2806030209061c020f0d050601090c20 62
    0x404002400904050b84007443d401c1c0f00f407291550781c40d00f01c05031201c484060b1510341410180076405080c00d54200541d0004002003000c01c1d01d4100c2078080e0b9900209621075081d05000051216500c0d60317001c0c010b8028a8148001c1080b1b03c03006024801c034000040c00300c18510390480003150300c4a2030140041d000460fa0005204880d444112210701c55003d00c1da0441d9107811106840885041030000300340c00141029404070b010034030607401800403903000d040103034548103514800b4162081581407a6a21407281c9907030f0203038002800c1c03070081d9011100a01c60031504c02740070f403032b90003116405406042c0c0038040d480c1404007220071488e0591034903032400c0401e43d80c0080219005040c0c5550642d071441c00d01454107541c8510308000c4607400042601030850042004442000d418588221002120075451156111000c0c41072501143c0c00e0514441842c045082c5520b40e001c0141107002d05000420700c90b80d982d0114281210350750794103c4090201294049540141131a4580e0b030380003010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 613146996 1250 613145746 613145777
    0x1090906050f04181208040203011b02030d2007030507060e010606050304080c120c100b0307060e040207060603060203010e01090608061e0405070e070e0909070b0403020613050603070309140c01 85
    0x4010960380111295070b040b80c91344e4441510b48080c0d0203954001035040c0043c0003d601d4240152407aa408008101d280c0c402d00000213542d80c03103154440d011850721019587e40014206d850100e0300b914612005540c3c00d01c83c42c00801c2c0380c0c84080108d43e906d10f05075958420000511132003007a03a586485062458445407544082c40e0000c0c42206124400e091190b44c5a04481c2d000d082c84007000d00003050704059250b160401d85d40c80528441c040d07404a00c0420400e980200d8850403440b0903100145d480400c0d080c10340c0940b113a50009400706000100004d40c2e2180216468100d540c052801c00c80c81da101c0c0540d5850b52030940d1403a100140122209005050020f0385642291040741101d522607034440c41840301401c204c078460003240c14120b03910b9250509031022980510f003107000c0d014003402d04500d00628003841c0801317402440040384122401211748590000f810b0010b281c19181d1800200050180500300b8085a0009900c0c528805001d40040c0d40030b00c00c501615205c54000801c3c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 613148246 1250 613146996 613147001
    0x604030513030203100e4c02070c08120406090b2506150f03050706030c050412151805511e0f04060b0402031501090906050f04 56
    0xc21031501012030744000005075420041e002c0d40486100c4003060380d145050045040c040707550190303062020707000004150410f1481c8180a040054452540c01e400800894400b0081550110002d80d10000d803410911440c518105c080750494001c503080568110380c40c40050045c0d01c0b9010120f80c50036802e104104001c1c01404a4a80030346180541010510710a0f40301c5005403804d80340aa0782d01c0714220781940034440000901958180b40400340d00d50f0b5901560344510384100c00415030384911400644c1d203e5011500101003070a03800d04003840c0e07400c0c0f0b03207098904c01413500c00c0f8900e441c141a0301c8412081c0100c80c002d400c0300250020b10030030440c91f0b000d003403034000c045c540c0c030407204d105824840110711030315900020410700302c001c181c5001c244120b079902503e82d42000180041140900ca06100c0c1140c0c80901c10314400380588a41c980040903010004642d40e00500100c1002420600300500e0400e000090707882c0e5000d16a00c00c2c0101c100c0314680140ba4121070b120720b0901c01400c01e40c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 613149496 1250 613148246 613148257
    0x6050f182b110a060b04060602010621050c12060702070e0412030509160f1502010207020319020f0904080901030c09081513050a0b01090f02030f010312140a02030901090e0906040305 80
    0x900341042c6010001d40042d042c181402c400300c9409980d65144141802c103446440060442da0008114107800d01c03000d1840e04696803c00040c1c40d800300000420040c040c000d030703803a014000c4c1c5200b03c444d00c011200e0340c50301d07000c4900100501c04c0e0940058005001140c190044d600f0144010b0040c0c0a1123040b009400001d00f100c20307510480102442500100c01000020319062000e4020306041c0b4496428901400d03540004580c0140980005650017113035124041440380e820551303082c00380c4089031780b0130079080c96140e00c02907100030802842945c4008025000d0240d8042010a141d4581592201464014044035034030804c0441c400081d14005290400380c0c540d00001600c0a50356260329008002c40c04494030440348004101e907071b005000740448020b00000643c114688100d0000405405100103440003039815440c01000380104e225407a054045405071f640c6840808020f542c1783e1102e40307610300055860b0800a480e14000142500404000d00034184546031514115450f4024 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 613150746 1250 613149496 613149583
    0xe01020a2111090111070f14010206060303030130062c070f0b0d0902280605070b0a0c170a1a030f0d0c080c030408010609050c09010f1b06050f18 64
    0x403508003047c02d9100070b0043d07005122146d07100b5820f014900009040c070101601c518041c0e4024001070007240300d00900d00350010094007079008102d818a04107803860030340c40005042a4500211001a0b210380c008a0315840c01b0049040d074010540c0c2d1915a131000030341300c0e0040c100e010740d4081c0803080079a002481500004080480c406503a500020307032441c1c51034501a890496200c1e00c04062804900003001004141001c40c03d040c11500c2e500d00b056401460203020350b99480224003140c1c084c5c244440c565000140300700780303032421a0144000344200241d07a514604a01c03903803280d42c60000340b28100e506030400a00304a4400302029181d4245d0307200e0481d603040e4180040c03030f0305076805c00140004014600000c1510340c03030045000101c80000c0c3c00181507110410512813580d80102103101c1610180ca032010b40c031170f00b40c5c0000e001046140d000a28480c00e250900c2180440c44081c213018003240d91085100000300000c4503034030304000e10b0103407c5490040c03600b505070041c0c072441050020b1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 613151996 1250 613150746 613150753
    0xc0509061e190906060906050301060e0d0305040315060305060a020c0a021203090909060a290108060a0b07030203190810030305090102030409020d0207060b0906010c060f0e01020a2111090111 84
    0x899000c9070b02d4400c66082000216591081004683d500000340302c0208154141f46156504001c07004180c10240c81e42540565000c91450040500c03170411034006581000d160045c8120310081d050140c800c0384000e44e49486008049010281c0c18403c84946241c0c200003018030b61016401d1100704210081a03149501051003200b01a443e4031030b00c40c0c0710720000009031a0f07a240441003401126007812404148420502d144010f500310030b4a2000c1da62400d00f44040c0c150340300c8002982504440e0803a961041b8003140b1070701090b400001901085099a81060310709a030000308030741404c022104c0794a9151705400030000709004000500e9294010320580345043c1d1240c8042c020790340520601180703994001743d40c00c00e0140700c0c865942c039a036003183c1111250916000007404c41001450180c074207540c507031024003002400d901a03c94007c41c2d078000d540303c0115110242218420100303070141c550034800c0d481d004100034454034420440e403079000e605040d14103004682c2508428803c001070312 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 613153246 1250 613151996 613152019
    0x1e0506040204080d080702010606020a0b0103030e030a05010c09060e04050f0c0309010e0d0908212a16051f120f0e061603062103050c0a17070c0509061e 67
    0x52090284d02480316031512115010b00b0240002421105103034443d20440d003004885500203003400e6903181c112a0103284c464242c0301f510000a0510b04042001041903190041c8550102c1c2c1208582d13048910035110800b00030b1014040c003099032070469419500d0609400081e411000c0000503541005202000150601141c00018034080c11441c0400104600003000c005a02c4d01b080790342105644100c08140246184112120074090340581001984012400400680750b01e40e4900d07003944407404070b403034805a802080c08214914010103004184200f0002c40004440740d545542070200c1d070390a015820280d02e514010092002c986102a8843c0e42502000740c08001e4140642038030b5040303d00000a0b11409404c845c059880f811891040d51500d12401c0b2201d6054444107802d4100140d480c0e2026004504162019200070b0021440e299120800910180030b0100984038000340c1e140c0300c0e1904104052244126030040c4e10582001c0300300c0d40800000c40780428070101810280c07460 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 613154496 1250 613153246 613153259
    0x8251205120705060a060902090f09070e060f031609030f0f0f02300c0a12050312090309011d28050d06050f010e040503030c181c0303060602011e0506040204 69
    0x394030082c0c00341e0b615401042400400398452242c40000d0550324011440d25a01c1c1000c100074030096505184200c0d80300300040c5165005a011070f0042310300030b015640d0713050340c03442c640c10942059940d00d01c034410071086403103841e028091400503682c011650160240007236852003034401e0814401c98070640f85c110218016140d8905501800342c013401380c0894003054010b001c1090401080009a9074005951401181c9840c00404180d510000e02020716204904050303156100c1e6007030740d2040e0000ea00800c00005e80c04000f5141000342660381d40201c060000300070005003002441300d9402101c1180302424040402110400c5050b01a00a018030b9590000030715644100740041d2031241d107030400c000321084000d6000f80540614101d02249040c59190180c5d20300004200100d005000030b401495031945038118003003800010044200f02c0028a0044002c0c0b2103c00101c000c01d0030400c0c003059103070040c05454041210350054000b0304d00500c00c0070000d400050b000b00d030080d07400c00020956 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 613155746 1250 613154496 613154533
    0x906040b0130050c0f06160816020a08070e100e0604090f02030609010614060a02070b0705100518010e12191e09030203100c02060a0209011803050708251205 69
    0x381d0183c4003a100203401d50007031250258106800500c590303810080c00314014440d0305178005c1a604982c056840741e880b4900d04101d401200c4019500c4549d41d0700000300200f00141000a0703c0752074641500790307201c541c00d203a42c0d00702078000c0191141c1c1c0e0f10001380d80707410b00d940035280c9603004540a060341c0d541c5d900442d040c050103413100042c0b6511184140429034403c40c11010000050f545079103480301c0c60500949609460141c403000d1071000400e00d05104040008030b17211072402a00304143c1c2401c40c00c420b80c007041059100095400c040b4518200040800e42003d000101d40d03e00b441c1c6105240e94070640192100001c00744400c000d86400c1c0c01d0b98107030010786116441d03103c91003454158010140380241c205c0c14452010f003002e00041405a01040250304040b54460141c0c5610900c001a42c103480d8680c01d203013485186200c00818003000107125412106e580c2c054501a07071382a035000c40300f280010344004d9041101c1404024000358203103940c00047c001d0090b91610541020107800 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 613156996 1250 613155746 613155839
    0xa050f01050d0c0203042c0609040c081c030e0f0d11030705060a150b0a05040603021e0c0109030801140f090c12010b041805060f12010b100305040b0906040b01 70
    0x1a44081400d001c000c41900a081001d0030545a0301c8203280c0d40e815007e002c403002044e05001b29010f802050400980d81c40324000392003580c06132060503814004c41d10200c074040d420340c80000d007031010501080d8408241d05034501c120202074242404809025103802c0c826258200b0540b2007044a0f8011400c00d0210070b000724510762020690030f6514001187e080d07169000030070901e0040240042d542d0f000301c215011140c0d18200540c55414030100b102c80990084415484a10b00240781c080502c4194030464409200c4c1d01c0d0407503182d80300d40b490394a814424007103c2c0c20298203004d00b00c3c541b815034403035988440d02499851801042803c00d02d00f0003020b83c050208030300c004c0350910040c020b04640355038902c01028100001e00d040f800207401c041d200d00600340140c003910a0310248000c08c1d0010300d000c090280c8000480d03410801d0003002404112000c3c0c94045118007c90007002001c43d0b82402113401000d82401c0340d003050300f1444038890410b1080a03d50300083c15100031946140c3d080d2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 613158246 1250 613156996 613157021
    0x1d070e0619050d14032709010b1207030b0f090a0b1f091214010e0a0303050705030c0313060b060406263105070f0303020c10050f090d02120a120507020a050f01050d 72
    0x114250004062004418068100107000d13407052108400940c1c101e071030b454bc88a91481d01299451449004c02d60306a60031000759005030500c4104196140160000e00200e0020f0ba802c110440c4c6084d401a261107030b9205120010b00c400c241001614800c00c3e841640a000c1d200720164142d005803011300b1611000103800b6580c00c02c07043c4000340b40e0148240ca41c08515418a06c0c80c41c50404500c4200344001002501542e41c074000348420300106070b00566240002400055807151140030140101e0a01e02ca032203d0341c0c41c03848003e00114510818a4000c129058206000450740c4c1180c0c240f10f07000201d000c03038490700e175071755180410710800000000342910b840507201182582002400c100403229554022040c0740a02030386164014101c40101e1110400d09072603482140c00a034003d014480302030361040c1d820034110320300035010508024a030b00c6000c0760800d80154980645c1c80303028072070001c1d40c0400e00000400440c189040320302020501490b01a140107516481a8112058111420b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 613159496 1250 613158246 613158307
    0x3060a09030807020d090e07120c080108010608031207081f090f0e1506060c07181a0a060c06050c0706020c07140f131d070e0619050d1403 61
    0xc8081c980c00400607600041c0e0b0b0710203040c10302d500c074201500503451803040001407070b07007400010801d42c0714a240301002c43c216542844510b4803000010086a020301441102e94a480b80006803c840002104d104000d88002d0f03449580d9044800c0c2c07071074500249800b1480140f070302070100c05a00c850144020702240c40e030006d50030300104400801c0741c004210402440c0d008002401c84000e80703124030b41d4001c2080324411b03030342c5200890709406c01e032030340e0701808004140e102c0500552900d0340003c20250294518001014000420801840d40c40d201c0c1002089440d58607102103465a0052644201020034030340c90b09008d81d840c50100d0b44141c1c8a60003607008110144005a029138807035040c2c041c00c071084460680880005081c1361000a0426116642c89802219840c019080341409040c41c409440c41c40e503803844d058102c010104e5805114604070301d106000a002e44000d2025078002605490a0241940d2000909917044441800621042c802020a10201d109110804041000c2c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 613160746 1250 613159496 613159511
    0xd020a08031c0e0a061a0a0b04170607050301090c0e21010c02010b0f040f0b0913060c0f0f260a0b03061e240d03050301050f030a020604140a0503060a 66
    0x4440140c2c1c010481988a0300b44480c2814125000070507541541d04804000b8038140e0f05107902c0d40076451801d505811091010300068440050006402140c00208100560301c0ca03056501c1e4072007030201c42400c040740c000d00060221010651040b018044107042295284daa1200050407031840100c0032b82001d007401813a900343c41802c0c0143c40f250320701030000380600703451f03000045c41d01e84103040084c0c001d659416000741c50f501650800c60000001620703414060405810340785060f0341e0100d01781d400034201800f400842e845440012000c01480d501c60070344060580c400c99018078161100388080c04180b0340076240702b140e004024060850082c3c00202c1d10715030018103003404401490000000401448481006011030046600018040c3c60380250840341a03c0c0c803d0070702c4418003d8101c0000a5034504064120740218180c0c0d600f150300303449005242c8105070340c0c0d04000e6402508a001800300b00040507404034807100c10240207010702509502c800100749000b0040b0351411906032101310 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 613161996 1250 613160746 613160767
    0x13060f02030105120105190209030114150307061e050a0e090124050f0403020607050a080c15011715070c0204240b04031a0720060415090302060f04020d020a0803 71
    0x202021007161380c4000d000e10301c0c201118210381403480601d0300c6402e4001032811a280d4080d80000880b800b290101041d5007044801801d90502c10300f2164002d00c101c280200c0e995001c6d0000c548400c124450000010450360700880da0340d00b20708904001e00040c0c1c60200803942e19018818040d006489143c200c0d0070000ba46400e440300c00545180038000300304000c030403140503081154140c94055440c15aa0002840d14916004405034003500c1c40c840171034a048ac1c00d401154551140110b004e400b05a039880d134182c801014810040f80b08150301074140314005d4030310f01044903803004042c2000b040d81d0070a60049402d80741c506002845105814049000400c1180310301d030041c140c000308241c103180c295903d0440080c40303400da071a09042414000b03400c8504c980000d0384401c003540b0000c100b501a048a40e030f80c8802c199003c85034203220301c000020345507aa1080b603640c00c1c0c05500602041c5c440b254100f541040c041d2040c0d03000300418107000c0158480304581d8006140c400020366583c0035001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 613163246 1250 613161996 613162009
    0x90405190501060e01200c030304060c120807020c010e01110f160e040f150609090803040b070f09030f110a030b0708091c0e131505330313060f02030105 67
    0x20480d02c18008924141c0c0d03c140d80c8280c4c05401a20f858115511b000a0824a9480d000b00e14202c070703a25100c001404103041c9d0b80854003010726481010144184c20b901003003950513003002c503038180069010f01c041000ba50701c6210100c0b100d0006062158100f0903103008503091400b80e401040b907503404821000154410391b852074009048503506802c90707062943c0c441d004040d10400140203070024018288012480d41c0c0300b00c008000000080010000e58500400a901704990a0380c80350002d40c00a0030301c50290760751000b481002d0340c0790400c0740c0c2155120307800780c1e003402d90a0365030f02c0000c0040c088a45801000d00091401542121a5450207e02c01006400014021035154000703240d90021003600495050359004141480740040288a022403800c0600b100f0740d0f16540e05000c5202540044c0c2e02c0c070b841c140c400945a016030007081060400a02c020060030360aa0502407544480e0030502002941d04460400f00c0f1191100703054480d441600d0100845552507907000004012901c0c010 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 613164496 1250 613163246 613163249
    0xf020a0f080907060c0f060e06011401030c0801030b0105130b040507050403230d0e06091504051005030c19021623090910020307020106080f0601031e080a0f05090405190501 76
    0x5030010f254980c10001e000f4150359212000030449a01807440c841080a81c0e0400c00c41c148150003201c50075030b5a51458103810300c0c4402d15901103850007410004a0b4030038000c443c181e940000c25940240d18040a200c0100315884594840541c1d60380394403415a0f607400750900031032003646d503240c82c0e508500341f4042841c12010481902d100340c032591081480007140000c2d01c003075a820200e100401c0c1c00040b80080c070901058540c0120484a0303c0d203064509009801034845c01d90b200f00e40c0f10700944027600c03140710545800780a940181f142d2079282d601e0780c90750310211900d88181c0b040c5005480c803031702c0c140140d5007100c0401d05080f20300e0030790107000d504e0080e082c0c2001c0303400d001541400c400c030b543c403804510101504580c00000041d0020f000750421402006884111810503810360502e9031228000c0c00304640d008240340044902828101d112080d941d0040c000303e02c0c004103201d00b42d071700310060211a42884001d01c00300245135120703c607162081c1582080091969001c440303110482e00d05 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 613165746 1250 613164496 613164511
    0x50103060b011b0602090d05030307030c0206070e0604030602070503070804030602040911460503180102070218041e03030c02060708100b2809062d0309060f020a0f08 73
    0x40d88807105a0340100c0c500f4101e03650058001603072400020302182c900d5501503c003800901c0300100703028840354540e112211201c1c850342030300e5a5845000e400c888044e100b206c0b16500000a1005102145403540100415442502100c2c030b40f0859036031707520154000d5442030306d03000e034040b03030800c01032000c0d02512040001041505140200014501c24044ca1103046440405903a07101401b500d040c808614183c00304c95941c3d101000d403900402030450f8802c517583c0c1c1015900400007a0160310500039a45800d034000c10001c0c5c1075000c20448200710000820941e1014040ea00401807241c503c985491060300980e000300380c3d6080900301a1604101800001c1000028000c110342403240110100548066006080e030b13800100d262406050b00f80c0480c010281c07040410080403540041c042012600241ca1700031407003009100300c0301810100b0241040003410220102d01d1148030750300c91800c991089100160b01800500c2c400100cee04240b5803a03011070000c40c0d4141d82c0d50b4014801603404100b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 613166996 1250 613165746 613165757
    0xa020c0703120e060a0504090f27020102011503032118110301180b06130e01020d0c09082107140106060305071403010f0608071e0207050918060103031110020d050103060b01 76
    0x215420091147c4114440c48031620b43d101002c00f100d54a07500324100c0907040089940c1c280a11444910910f41081c50482c0950303e0058034803003d091007900e04044a0301a19481d0a07048680324074034004024080300d9103210341d0340e01d070342004c00700701032417500c1d06405440c88140c0040f64800717040c00c444c19545480540c000d0f005000c80091604c0c042c56510403003d90780701e84032042c00c0c0b00d4100500704450340301c0780079400482c0400c0301d410141d01142d01c00e10941e640303000e80d90742ca00217551125954503440c0380c407000d184c0050001c441b122008003161440b0f900d00300c600041d03954460b401c40e209a008140040e84620138400328a40c0091800038000401484d0343c5554500903112b101c0300e06610416042c0f01d55940091007040c0114200c00c801c20868440c00c031248203110000b5141d8950b406118030403103d000224000059003018000400800300080503681d01b10340341a1022a0a502e046000c2d104c2c24040f01c00100c541e0014000c5640d6001c1c010a00754103601d40b40e03045d00d031130b034040b14100039 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 613168246 1250 613166996 613167007
    0x1b030403241509020a05040f0b0711011d0405066a03020c0f0703060c030207031d03070915030203010b0f131a0a08030d1d10050a020c0703120e06 64
    0x801c01c0c2c4044456005005a484032401010b030f4a071301940d40542c1030881c0c01c6800050003900c400060140c64410f1002c0b036031885a00e030064800190340100131050200d070204590369820158041904460001c101c0e402008412156040e078140c0d41c0e03200c3d0104001404600c50005001c40101c00c20480781740694015800e4403080040031403107480f8041c0b0541d0103088200d40c6801b0ba03040315031055507903003543c40503e00000d0b0340faa41d21061204917885841c1c8201d102e80e1610030320a9554060b070640e140c7d06511380e00311101480060900d10180e050003a01800142d41c3c2d090701c540105003040d0818000c445241d0f0040500b10317076110300454044c504024060a80e40d4400746030300480d269803072000800c241080680b164418a47c41a2074100ca0410401704003000000b01810410700400000d1008ac141c0911584121240070644401c07684209140404c486558114541c8850a540014142140d03000e58624003002c0750303c00da400f280c0c4481c2c0b90995a510040142c0503c1c0152101403410 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 613169496 1250 613168246 613168271
    0x315010612021608120907051806040509010f0612140105040305160512070609021c151109030604111207050a03020d02270a0e0105010e0c1b03040324 66
    0x261150729080700b0342c000f40e420503401e4000c0030b101080780c01030b030305513103a04600000603244281960000e55602c2829000601c510b40f0b14126244200090803501140e11000207210141c8406072001d0041d540700d4262246030740c0c40388620b000401c02c12001880409050501e403c03034007a07440d006042a41840c08100c040303904582102c01c0b480d00c1d075200d091100300c603081050800b85402c009441142001991506000160700300290b964001c130740424040c0c040315103081c084003041000074501c41c9a525107452400c607660008020f44203500c911841c00e0b55005c00281010800c5400b203c016606007182841c50a0042a914048055100a0814500f80f0000070803c41151100901c2030b000e42ca984011901c83c44c3c044144000c0c00013240b0411144040e103002e54400403118541403500c0c0c240d80710b0b0396440c14040c1e035040303502d9050a20f48540380c0280c69a00c9600c80081101019404100b030b00f00d41a00b040200000c0d402450038980c0300316403c0d908071400c0d140c0c940c010681030500e100070906 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 613170746 1250 613169496 613169507
    0x30213030308060109080f0d09050d02240717040e0601020d020a080f2203140c09132301020c190b070f0e1002160902120109090206070b04050c03150106 67
    0x1600c1d01402d20351210395940e0b0040351940301540100e000d500820720401600c640000d401110f00181d80c40300020580c480c0207000e119a030710307640a580010070000704802c646041e0425100000002c903405e14000e015110a50100100c80140803464800501000941c49201e51140c0015007440600341d04020894001e6587e00c00d01c4016140c8040001c000701958007007811030765180040711007880c250003200c03022805001c651005440f1a52160f0182c0303405d039400f04615135820b4004101210760f0b19090401c4a50090300031040382c4081e040d001d01216422034030900c0c03409040782030002d80e944040c0c0d10b650b41030082c81c2c2d0141660644010340302002032105c140c0d1540c02100c0e4a060103181c25040e10855000d0080f10710607401610700076150995550208500030000c0103820f140300c0a5130fa0b200181c2c00c0b0302c60a40798111100e100f60040c000c03a200c41d08080350f0240000c0c42d407820000e0710f03114111000000d80d0115020780c03020008050301e00742400780c030354103490002e040041e540c50840084e19 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 613171996 1250 613170746 613170749
    0x7180b28031e0f1404050a14070812031b0720030106050d0206222c0105031e07090221100605091314090a1403040f090203220809010f030213 62
    0x5440b000b0303c500d000101d03800a40c0350800040c01146030b0034142402600c1d840c07903442c25220185510000c6006a20010b4001d0071036a038000103100140c4065076a881580000d0000301e69600c5070814800800d000401601e441c2c0e000b64420084010b0444100050855802c2c40a01990402100b0411680c1e4070099100c02a0150760407962019500c41a01c0401700c42240c0200c0302c0328602c0007060400600c549091020144001103041142c01010070070203040911405506610040788210034903c541d180e40005082c0f40e0072224084c1d1120103080c1aa0424031044022a498003c12000042c004180b941c0080700124540030403820440e0084c021303c5184140c03401500a10000c960405240d0320044042d0f9490b182942503003008030400c0d0300d03851558000d940d17211060110310104200841184d044a440c0403011048601e0b1100c1c1c82c029400041006405603190020201d440148038080110f1038807488000c0d90f6581c01500151040032450805020548140315114642000341040310 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 613173246 1250 613171996 613172051
    0x91b0d020307050705070306050702010e010501030f0201140706020313030914010f030e070b03010803120610090e0403110613022701120c031406101a0307180b2803 72
    0x10380e42d80d24002c0640b814481c03000020502d2040c1800013080c403109500240c0201003647c02440b600e200b0b00142400d94a0038000500100301c04000cc0f0015800345201c0780d01c0c0c81d0289c10450408803182c07070300002c0f070308215003050014076010222001c141d800b04000c40548603c07942000041d901c000000d042000302460300050583d5031208400d04103007045070400514901e10340701d03503d60310742100ca80c990b0418000202096803a90105119181182e4910701c2051941e5070b48109a00e45044000c48080240050b42800030802014181d600e0901c0000d20805a8401301310b010501441403048000400c054070003151040868174401c81c0c800b4544c503044a414400110b40741e8054104030340d002485610080c15190b400c0b41c0b4042464000c140c2c54840d86000f84011044c81da148081c1c4600389001d03211000030b540800005440d03038041e0741c4100601039401c00907840207849441e1001c03640c0c012140d841c0c0010242d8802c40e54901032448480c0302c5842840e091141d4001c0107108100c14030380c0c2d04200c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 613174496 1250 613173246 613173251
    0x91e0903020106050a0f0e090303061309020406030f0b0f01060e0d030e0f03011d0118031e0207081009110d0f0b0a090b15041a01050d0908070f080405091b0d 69
    0x2003454400d402c43c0015020061107100d855940300b106040c0c22643e8420340e001915151b00003004500040f00707892040901030402082c011291802c0802002050412a0b019a84d810003002242e4068800c3c01017610540440f00c29051085a002c8081816400242007100c03043c7ca00002c1c2d00d032000d0f50b80d034041d0f15041880b0101643c000192440f81220361554056103030907065403010009038400c0031010cd10320002c20651007608100c103003200c5039030400780106420801c2054101a403242c0305011910901c103031400e5a403140001400c08295804800c2080c1d2281c1541c2d0031300a16003c6c0542982041303d5964481090395200c014a4a044402800300c4600500081e01c40d08540c11445207d13500812401719860400000d0616202c2403092500840c13510b0300c1c00483c1e46080d01e4203c000141610f46c1ca0030003403000c80510250840c80412034400000307024900004401000504400f44034814440d1118101000c1c0704800c07100400c07552400b00c0c844c00c2090840501c000320390711100d0086d4003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 613175746 1250 613174496 613174511
    0xe090d0e0f12030a0816030204080307020906062107030f200309100501030515010e0f2205030d050601030b0102060115030b01031b09060e06070c0510030e0f060709091e 74
    0x5280c40300030300b03903054440c000010400b0706268003404442c4181c03d828442d00b003000b040f0808030102d0181d4080c19040354403c005007030151820102443c5c1c00107008200e28503050300c505d4035594459000090030b074449841030034080364641501960b42c1c009980f810811001c4802c280781e41401160b180e95401c003550000c0859462401805503410000811030140801e581d81d00d802c560700d4002c640c60b1546034003030000200744002c2400070079000d0280030362100244e031a01191000e03d03000d50410285010381d80761030b0000044003032001c2c02911803c04400034803403400400250aa40c0720b040040d045400020040c0701103001001c1041c001c020350320340000c60121150050f8000c20802c2024088071038448031543c2d820741d004080c5820740d000365445000542c0b41105025240c0900d160003408207500c40400e01540c10301014200c0380c10f4143c50702107240c1c0c141c00d2131181411807071201507005030049c004005035550801e05c84401440b80020070001c4918a20303034180c1c0d00080e400b041384250344600f41c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 613176996 1250 613175746 613175749
    0x81207060203060105070f0f02010f1e0e060415031a040903051804390302040605040506130b040f0303020d0e09060405090717010b0306061c030c0f0b100e090d0e0f 72
    0x140d9000c207a1120328280984007034180040e41c8d041014081b80007d2082e500c1102091245050b05034602102041d03001401003500d0944c0e14403003081c0c0c0503800c000c003408001440c0b40029180c0b0b0a171a40ba490001d5584507407050020314000840e8094040d50070290b03800c0019500a0440d6141c6c0c2203100c00d0b03007070700d1208400078001d0081244408042e040c160340d412054019111404c3c07180307124502190000c1c11004041e8164020751040700c0200320280001c01841c10400c0041c840c00a26400b80c00f038441c0c07284c95414840e00660402d078210903c0003010710405030100201c04041d40c2c00e0514088200500300084c29904005042d076000d035840710045503003a501080307003c0150003424800041201c0040d02d140c001e00d100701e01e0b64171038811000401e8150400b24452154140320790011200c1d452180c50984030541725241c125040c40d1060b810301d0126080a11a82c02140c00383d04490074645402c0c07071030103000b01c0601480380f00d420600e03d503144150420ba5040340411700381c1d07101c42d02c0e050300c80 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 613178246 1250 613176996 613177007
    0x204030b13050c04050a0b0f090108030a050c0c100f02060c03060904080a020c0d060b040624030c050f07030305042f04050c0f12040b01381605060403090812070602030601 75
    0xc81c503421a01700420701070000031325004482d8010b801d64a071040b0003071b11810003140310000c2c0300c1e4072499042000000d04d000e100d41c0003818028442001c86003e5140e006c04244190071140014002420201c80d00364582d6041c00f483da040452a5411030840c00c12200040e15080041c000801c1d0780d40004040711a103000344098128108014504405103c09081ca0005044854015440b82d4648540440e0180d000217070000308420380c10801c102800728410550051030098400743c140f100a00464035603100b0080180b280912a960200d024145403a000700031001d00c40640d0400c0c812040143c2000d8244c903142c0300c080c038040303502041da40c40e8640b9008031885608501c504003040050440c0c219101700440703a00a902c40e01c00c203400390303907604000c901e000c01c1620001d088008961001c81140c0c407400c000d2060080c00064645003131100304c07203d400e20f1103044c1c04960315007041013080140741d000400740006080c068040c1010440780424946940308116005104603400f00c00310b0000d92052 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 613179496 1250 613178246 613178263
    0x306150a0f0509040b04050703200f031f05030a080c060c09060d090c051804050c04110d0c120207110a0f060c020103151a0403150c0e1234090204030b1305 68
    0x1400c00c000508116000401510030b51084c0800590100c3c2c200d49480410700c0bc4901c11241c02c41514110340b030744d14400303442480b0f103103540300192000362000c2020794043c00002a11440f41040980e1403058001550070050700500d81c00390548244a0030f84152544022a40b0840e540b200c001140d40407482d0a0b007030540282c0000390004104009900590b00701034800c0d0080f4003604c210f03800300f1003a03001c010a44241e01c0c0c04000000081c0b10701010b40321140c208240403100c1c2d06151503407030103c0c881c43c0d040383c014401c02d44405040703107000c070b2190405c01c103d4402b5105091040d040282464400380c600c040c0000024101035480344c0452103c0b91601005c4003a040050a00324800041e20300000d0700d82090106850a904021202c18080c4951064501001c03041d02c0d44502181100c041045000519a104481e80105440190010040313071164032560384051114640c01c44038644909000555080300c540f03c0d1042000b400071076800303c005580036280c400343c19042c02107031501e94100045e0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 613180746 1250 613179496 613179499
    0xa02091810150305070b090a0509090c060708040512153607081005010317030402130609051006141e120103060207021206070e011101090c0b0306150a0f0509040b 71
    0x102910300c40b01031855102c0c4000c9900501c01c13504016140c0c05041064450564a04e6001e60f9501c001c00041c1040c520041d8000c08103010317103401e000590003203616070340128411260600d000a0a03c081e2410b444910101c92030310009014a0034191030354410640d001d03201151500c076070020354003402090300d2050794501d03050030f40c0c40030618401620f5503030f0319550084aa290181c5040b03400c002c1294480e50303048035084014184804c0c01e1202007902c5901c0034100343d0300802c6540d103c14501945002c1d5070020b050020f800217203403408007406400405250410340402001a88003100c1400f66000e0302c40744000803110350a03d50510303d03900e1381403081541d4080503c1a0100000a0040650141100744d00a882c51108000a2401c40d03403180811180d1501041c03c0030000005940b20b010310b41d58607000700c0d0001804080c0c80c0c50b411007032180d650110203c40000004c02c8000e050403140034400303a03452890305003040c1c01700702d018181c4e2102468502c10070001281e0718580740d841e5000080d000700c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 613181996 1250 613180746 613180751
    0x1a0109020913180c09050a0b100c120909090f0309170a110105070507030302010606021209030307060c052a0d0f0807050f1e0d0c08011206050a0b10020a12020a02091810 74
    0x11741310207520290508070381c0800510701d070118030091418140b040100c8100190784054444903d42c0d80c51380b504510002c0d1070200100690089071080d4203205041485004109601c0c507e60f5501d0010492141d9801c040302100002000e02080140010718802e619440f200001d0144003400049030030340071b4404042d100e442400c4001043c5a010350154095440c0355081d41c002016420b0f50f8642403162030340d420b800d0b5008004000201c0d1135580080c0440c2928034003140742c0b500c024440e80c091071154481c0c020001800f45001e190980412040714070b01c0841c2000840740900d8480a0682c1c5c000910f002c050120002d5800c031070084038400c6591102e10200e03ca002030000d028090f54a0f00000c841c01801c500e481c1040022030302803074886049400703000e500541c0700016070b07d01d40540001381100d400c007522a00403002c07650310301000b034030001007540c0103215440050800107000b41025601c542503410091300900941c031010b200c560300814040d2003007520f40d0356074101d0f4038061841301d00307042207031 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 613183246 1250 613181996 613181999
    0x1d030c0f0906030f0105070804050d0905060706021b070b2101080a0b040f0209070c020f04091e06020f030c03190b06040b1b07080607020115050907110f07031a0109020913180c 77
    0x40d080703182315000b940510b04441c107120f00f20390240c0303143c0d07424000c03a64086003d000502c00110b894004007811041524100c5d42c00c061003030b44a00e8038025030050b21915501044094100c6064410086100f1f00e50035448203e525011a95480300142034003d40701100201c005014001d00342c414000d0315030b0251210b60b407031420000040c40f010042600301d204903100c20650400340303898050302800681000100003003291000c124100b8004491080f40c0e0560207118140d1080d4190300a1441800c0b411540307581c07032421084050002c480e07000c10a611a151100d2010581c4030300050b80c0c240c45180460765512009581041980c0f100018842210b00c54004081401803000c16501d018240b6030300207101e10441c01223035041300e646501643e0b8202d0030300400210002d204003002c40100001c1c009680480c030591000608112103a04240d801d1584c2c0c207428242203a482500c68010880c4200840c00c050b9848001000103000740c141440711a100e401a05040e18504040f41030300d94000050650107 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 613184496 1250 613183246 613183261
    0x409031808010c0906110c31020c06011a0906030712020d0905060702071a030606040e0f04020f01050a0509010c02060d06030f0203010c020a12030c1205071d030c0f0906030f0105 78
    0xc0c410303000d83c000082c180d9880050a1401120141e104581c200050040c448040e82032110340c0001006125042070a81c41c08101010140380c040445003002c0c00250350781103154909440c000040c0d0004000f819a400c0f804040342c19101030380c903103c01c1110215a641c0f00d03013100f1075000000c06481a80710780f001079504000c1d046070f48102c9456120300b00361691603880d4a0103980310301480c811400310150402060300c072281f03520021540325a000340b400b820142c40b07000c0d8480c802e4003240c507402429481024032080d407902c040c40c80d0b40785000340f81c01480c001e07507800018803c1c09031a0700941481080041942159075030400d6905440303030b207030081202d51390740d0a008502404024003a03001e07520307059401500c1880825040d207001d400023030100310302424079800c030000d09040c4d190f10100002050a6500c80b1051701900c2c0c095400c640c0c0b0003001c0b41d40740d205032400740d440d18041880781c0d008090111440c3c0b541904001c0000d81201d002c03945a54101c046403c2010007040040d003541fa003402c10081 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 613185746 1250 613184496 613184501
    0x51e0f190f0516032003040f061112180a0905090c041a0f01080a0207060632011d010c08030406140903030615160b0c19080114040903180801 62
    0x300c0c0300d039105a101584003506071107a00c19404400c4026070122084400b103401501281c00e96003002c081c0021181c0c0c0c03101d0160071030308203410907080211540c000b0011301d0b40c01310749080b4519030000504401c1c0e5600380606040e104e60740c00e62800340300c5c0218200390b80c0d071401c0328031000b003807100d005102c030f4034101d2105600e0381c0383c0e001400e204500e000821800e41c800da940340868030034042c080d0384120022500545e03188100414201d1401d408000c0d80000807203d02a200003490922038501c20b00700c04a0111201c03600844410002c0801c00c01c407a08d42d030381e02c905d000c100d100c0b241c50106800341e640c000499100b04815400b80442200106000c1000520741c8048261002810702844a031603040c9000e0701ea20041c1c03a00740e440700008551082018090300106812611002942c4480c051551044101082156031a40194000c292010004540d0402c44e84031205403520203604c1d0f04000c44140c1c4000e2800116000341ea8030300010301014024250400d2441c000e80301060340c95500c910711400b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 613186996 1250 613185746 613185787
    0x50c060412020d031506050912010f0504061406030619060806010b0406020d0203030c09091005030a0311010b19092007080a030c14031b1e041e06051e0f 67
    0x52103801e0911540c5441382c03054200d00c08040003c3c01c05980f60a00c1102e240e08440a8694409403180c000480f04909101e06800420b550070045030b0b503c1c00b401c2442c105e515299065000700b4281003001499030380855a40d84c4941002460003212400d80488801450705e604a0b104500c45c180002c200c00c4000c0000c1c00c01c0b100c0c2c0e40d00701e90413507003251401c82e00c902040d201301c041c0e441c0500040c14946455408140e005180c00740b11410749a55800081c030b000e1080c5030541c041200b2290319103001000b0300601e420000e0554190300880031101d4a054005828482c02403030310b644041c0c046082004840555500156010031600c41d2954180304107607901c40300c207a00100340781101301c0c0e224600600b40c64032a19a00100e8500b1a50b1700000360340001c0106580c43c003014010020800741c00c800d50b0294031224001c1c1d565640312424501501071141050003c04646800103000704012a0b0110440e55010500180982514040781c0e000c0c6090240041e0f0004240000c5040801c00702c01840382c00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 613188246 1250 613186996 613187033
    0x3160329100c120c020102120406030203070e0f030a020103050c120405030301181b1b061104170a050a14070527060f013609050f091f0507050c0604 65
    0x107450140c040d01c2a0303803070041940020500c0c800000c0c9203c250340902000c00d803450060040d904002145440c100c880da0083e08032101183c1d010081c4421786510154541b80c503841501c03507000b140620000a542c507064a04020304040d2110000382c045008802a03400e540030150425490b82040d01d01203460360002d000c0c10a1260600440007001c0419010b090080b90000fa204e40381440400c10888035003880500c9008500030f036090300d00c000b602500c9429002100d0194240e1594203028901d40400240100801a03500040749800410307004101007140a50144c84850b10303d00000c1c0e45410f0001d84d51002d03501c1070940310800070414500342c80950500c1d1200614189540b503004010140380d01895007800503590a0000c042c0070720380d82c4418040240e62030301541c0040302c5004504000d103d034010030203e03a1a00d0130711207003003405060103801c414000f0140c00c1a0040c603420702d01e015015180441480d8a07100441c0103d405482224030405804091300d0207442c050034120070303d21440c010030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 613189496 1250 613188246 613188259
    0x50d140103021c02010c0209040303090b0108031305030c030705011809060e0f06010804030c0201081801023c27100c0c06050901172d060109051503160329 68
    0x1030348241c030400440540341c1d034141c4886c13050060680038081c144000500480500d542c1d0034564000c02c0346488454020100540110307550802104110b0100754603038001c9009a010040c216400d5402080034800d9a0003840c0c034641482c5280c000c00c582150b243d0050b0113180c80d1070004552040c0c1c140902e0700c113030910751008826407211030045401c100704490240c0000e009904900056104e000b400e9040002c001180d14141481c49100c0e007283d2101c008108039030440d200d40315421154030003452000c9001c0703107040000c40d50040010814400d00b49410380f480901905c3c0202d030314140401c80350450b40600075580454002c41c1c00b03040b0315803600003a143c1341d4180034001440c0784101300702d07803002106a442c40c0c0002e0990401c0413501c50003400040781c0c004404440c4021040010350009000b40e1080c0c1c200c40b6040c9840090404401c9812071401952103140900c044840541100d40088015640260b8905411030031001000c0340c0c41d6800055600b400310041100c14094851260442110789 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 613190746 1250 613189496 613189519
    0xa0b07030203040c12150c05130608060907080912071b0b09040609020313020603040f050a081b060c040621021c0e03250c0e040b15030a0305030a020a050d14010302 72
    0x2e00c0d45021380ca80000b0640c02900c4d000842c0a041ba4011090201207820110f05000c00103284803004460340d048a000140700004119251800502994003d07215003000c10440c2003520005865480c050354060403440d00140410400403800c80b284412840d1a1039880e042e41c0314280c1d074816512490340b16200d035041210200c0c8502884c400c80340a4206280c1c140c020311156402c0c0009900010015188450021002030220720b041c8501ca40b1a4421148165541c6460181207404001d134403200000d0b500140810658078040406c86040e15024280109040c689041000d0810072900c0c00d00600c4e4008200c0da504114802082080135030035003014002c0c02551403025560b4052800008000c80e100180d070b8225241a00c2c5041042d8041d10308906421b03140c896031b081101050380c0440f1801c80c29002c000c84818400841001d11404034003401c0380f9922a1401403580c00050804050a80e0002c0c49425050080007240c0007010329003030900c4400744c015441c0e00004024402030f40200b455411 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 613191996 1250 613190746 613190759
    0x109061701140622051512060405150a0e0d020304140319080f0d140406050609070804030311160803010627031e02090a0e10061809050a0b07030203040c 67
    0x100c002d00b240d01c55511050b555180c0411404264541d4070340c1000b8001c031100d1074000518040e50344101101c4040740c03411401c1d5018400710420007401d130080d90f04034806100000d100450507003035030382c038405001b0f08540341d580842d4010905050000c56070b1050300c1c62140c080b0f40100240c8200c8400c03040d05a4110180c41c24540c442942c4090300a07aa1090180b0390b0001d03d0510150407140d41c001903007804c000f08a402030007100e81254020011074415010802088100d0280b1a0f00800503907011120713080c5170002800e0014040c20040034551105905100001040f06858201090b0710545540f42c0003410300041d6a072080c0110f01c0010100740001c2a03000c8007a54040b5000192480030003100c0c82d586600350f04040078014040c1c0c2212078074000002d40d488910b0a400369002010004550b80940c98a078540300442d070f000c481c51070900208229480710301e0707081e02c03066540243c003103a50030702481c00303e080480381c120050000088101340440c0a60681c00b0303521640c40f4050340000c4980b0383c0d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 613193246 1250 613191996 613192001
    0x60e0106081c0903020306070503091c08071d03150103120e13110f0f0d0c02010506010c03030504050c12070e13020904080d06080607031a090f041403120109061701 72
    0x85030041d5000c0c00b444010700040c2d0120b258202038900d02020125102da00080c18100c050f01c1c00000540c01205100034042c040c05042c0c582c030270400c0803044000c4246006800d10900804103000c0c8101402402c0018080701c4c80744908000003002d41e1a2841d0840b00350544010a01058801615400700e990744c042c0611b000352014131000b008064001c42c1c101c5a18050000d07194031000b0000c041c0590f01682810300b010703102d4048240102611303500550f03802d01c0bc4920b402c189e54110ba041c8402c0c0409030741c014003102555a01031801203520b50f180e05215292658401360581c110000c40704014180001042c407106484291190400549860140b41d5811403c210041c1d13200d211007000c2000106410300800b03a85211140c085a80f942c1e48000350b040c44030440f0080042900c80c07030007200745a900700c040d91490104403038400041c03c0c40080c4444841c0b0040000307201a18101a806005204205946002c0b071542c01980466864031341d45006040d480c4140d0004080707a0300140c005d6081070 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 613194496 1250 613193246 613193249
    0x90724030b15161115040602010c03090b2703120106081303170601020a020d05030c0111030103050d031e050106031508010e0c090604061208030f09060c090904030509180103060e0106 80
    0xd02c1141c14110b50300d010342c4018541c241c00f1503444002d40ca1304200e036200d0929211555021030859500c0c1ca180070380103400e5400d5859031508051070310007540000780c03c55985076007000d6000c41c5400343c0049014030040740050440310102c0c1e0b21011510b04c0b1040008a892410f030b0700d10740e884032401d45a40200d00c0d02c0070300340c5400034040340515240b0500501100601030b40050148100d1701d4001a60300424100e481d2030304140d403150000503e080b10040c4c00d000302e2a0003a10130304440d03c2d542c5180c503003c2d181c8150214030020035071100642c9a0f290b1010304110640b03102c10346d0401031960346003005001400c0784841c40001203150840040c0c20320040c482c21000018540c0507005103107080301006087d480092a5035442981da66001c03c011190300d0058640034840c0d20308e0365032070411711002a01103d001b00b003804aa0301040400c2000079240307003515030955090310a071201c0c0c2c5443c0f600343d40300d000e016207140c1c01c4144047d1040b56800c1400c10641240d002d80400c21031003080040107400d0324102d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 613195746 1250 613194496 613194529
    0x30b0408040f0515220b12010f050303070c0506030c070b01090615050c0c12120d060801050c0c15060f04140a0e010501060e09060d050d020a030f030c0f08090724030b 73
    0x74455a030384002100d410719104405c1520211540c2c0e100c4000e04031a8100150707000440c07100d0b40050000c88075004040e0040c0104800840c01c0c106581e070b80c1000034000d0f00480c0d02031400400810083d1107800141c3e20f05951000000e0115a103a6108000078031842c451107a000750740341940c0150342d026804844080d03c3d12000b502000a00c801440480340380400380c0c071079610401c03460050a80d5460060007132500e1200300070070130500d001c5400c0d0035120054150554a01d0230410894001000254520090116011840c07140c2d174200004912a401c903d00303a4002d401c01d0005000e02c50401a03040c41081c555808004001040940d82d00b260307024090940030a1030306925100518000041c1030340108014200010020140d0792a41041c01d400102005a408140321008160f00305000b441200818901080325084c2e0420050003c0d40401c0002e00b0f004030388010039000c907400e1000001501d10b0710800507401c0d01c81d500103848003074080c101c0e0b00040d1419210b8041454584001c0c50b04104 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 613196996 1250 613195746 613195789
    0xa090608040b011e0302030d0302090117070801180605030106180f0605032a0d050a1e08030c07060e1c0306050a0f15050408010513020405011d1609030b0408040f05 72
    0x814500d40861342003d10b1004012000e00c00010040c0d404000e62640d140c3d05503809600d1705000000501045281640200011350500400c8000350780008046d0441c2c450340c8480160511150b14840200316a400c040d415500300107011070034032480c001d80c2d205e508020700c00b00401c01581e907140c0d040314820b00030742d0341c1504183c1c0002c260256103030502c26841007820b803000d4440204400240ea40301420300881e81e507044168200140b00d50410b1401700b9400160910a2000e183e9542004910000780500e02690003c15454140500c13a80000000c0014408660010400319101024024808441000a400c041c808200e40c104100c0340022680b10003180740c045c0b4200544140201c11050380d0b10304014041c040098200b009000d6a40505619000000d241c4181d00601081d10b03016080500744242c038544110010504448199110103401c1038244964038004040701d070003126510240200400200f0700040c092140c1c021710407940c008440c644055920010310a00c100240c116500844 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 613198246 1250 613196996 613196999
    0x610050105160638040e030307170c0405040e1f020a080604020d140c09130b0d030e040e100e01060914070e041805030c0708070b0a0c05210a090608040b01 68
    0x15255081040c0000f141c0e000040004200403c4090203528210f84e90000443e0004038081400c05100740b1080b032107420059880d524011001070100305400104805103400140003441070322424069801600c0000e00034004101002d100e0303036442c0800150300d03200c800300a047e40000c41082c400c507180071000b074460b1065541c071041044000d40081c410920200c1e251988442a0021040d980348203000032000301e510382002006002da080c50800c0c0782c0843c1880c00082000035600d0700b00350b4890700e40c035140411800e1750450200c0e003d441241c0c41e0f80c900344142400c0c001c0c560300b280c0248084030a030030003c0060711b41e1041c0d21815a41d02c40721003981248401c2c086020284101241555140080d0000c128113041500da050004a4000151443e80001c1031604210a0501c074039001007640c00002c0400600f4038421020a100b8002080180b1011100c0581009014040d074410b1a05424034403e9442c000300340c40e0200c1e030001d4007a0b400100040e5011580c140501400c501464200049004c84c3c3e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 613199496 1250 613198246 613198253
    0xb030c0d080f0d09030f020d26090f10140c0f0301050d03180b0702040f0b030709020702010e040c0c030f051306030c050c010c090503010e3417061005010516 69
    0x3035101c1d00030b909103058100311040e40c500c058018008054441d664407070104043c500c009003000c40501480d4204800c1c994421404038100800d032804400503500c408554490130303801d0b0710345404003d040b96903000740300f000183e02c0c40980c0640c03034002c41001041d505580b034200c6424039114440e40038805000c01e200500180c00c0081c0c54072412403003410f00c42d0032152040c00c2c4030700c0ba160347d6206680403180000e0120440c1064003e054000d0f00400c020b0000981c4100026180c403058002c001d2034940c003094910075680300c0d80a107140484003500402c014040084000c0284480303480540c0410023405030610741512440c1203501c0c410b00144504045402c000080340909240c22400c0100a0180700440012000f84111b50f0a010203440e41004030b4134040515003074400304600003516800c01c0b02c2d000c1803101900e0700319140b503034a00d8000959910104840c144c00406421082c080701c100a074074214600c0002e540e901551051404030500c0b6030342c0004490a1040840c1007000c12401007942000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 613200746 1250 613199496 613199513
    0x80c1809070905090c100216050906010c02120102090f0d050c01230a120605040911040e0a0b0f060f0f061b100c020709180f1104090b07030e010b030c0d 67
    0x6181541901e954555500e042010b40d6030946152850340c00c181484120f5192240c07844480710010b0000c1c2890580d20310781490f500c1d2051140b10301580501c80041c90a81c4101300740040c4c1507008000aa00b50703080305c1c6107030003900440c1d261360180b0031900a02c110780ca461f4801070007042d4030500810803c0a0744e001120040c054103c000078010000440288420780c100103800001020740d54170051820b001244400e13141303180d000501a44c0b0782808075011034283c0c11791041c0c01000f0b44022484002140086150101611003d840700e40041e00348010008a50b800c0c90082c40b04842108240c2140003c04c0441e031060360344507a0116042103007a100d80c51908507820100ca0b0403041d28111f180d002581c5060301c54081003600182c10841d4107203c0244103124488800703058041c442c004220395503604900868001025000c030700e08070550012035031540c2200b10516808024010181801303500500902088bc003402c031907500f00700380c001c6a410009243c55102034000c11002145d001174803000324 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 613201996 1250 613200746 613200751
    0x30106050a12080c03091206070e060309100e10050408120a0c0c0b060a2c15030303040212030d020d0b10020d1e09050d0807051b0a05011d0a030615080c18 68
    0x10350000f030006c001d650f81d45c407c4240b00005901c01600b00c524011000609480aa981c070358403407401841444450440000d002492420801000078000c0c0a4080c6038a00345c841c1e40c554040604280421042100030f5000d800400c4401d81c4220172900d45650000c140d68106200f603001510405c031f44000318420004894200f40301911407071900c0d03101d90b110041d800c20000311a40c0c4001c01240149040e09031000b40758880f0048a2405412100500185e240d12001e00040c2c0b10300700201c10307800c49410904c111092582001d2045580d2104d003c07a18010300203c9001621503515030000982071400400c3c80c3c08201059a41c2001841000881030500f0b12440c0c00034041020006000c52962a018000e1070001c2c091408070f610b96206250170b0345000180f140810880208000d50ba490b40c4400c280314050390000d0030006840f00c15003501180d41d04a02c85483c3d4001140ca2000080c05169840f40c1d0b503181c0603a14a0312025199480940d441c10b800d008a9000f81c0c6100b401d1607503060000c1100d4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 613203246 1250 613201996 613202017
    0x4050108070e061c0c0f05070507030201050a0215130c0e06010207180e1f0516051c11070c030b071b0204050c190f0201053402010209030106090506030106050a1208 72
    0x4d01308400134031003194410307554a211544640e0b07060701c20481c41c0c01c9400e16500c00010714000e440d00782103a99007600c80603140700003130501101040307031150580240300c0746010002248040e4601e203171041440c400f07003042200540b804011801d022a680702c2041c0007500c28101a0020054585400b488805880c5011a0410119030b0390480c0440118184560b078544009030741c2d1340412090100d54101101c0b00903001259a5480c1c5150045841c0c012040e1088000388440031102d40d41005042009014000d000070903d580020341042009444043c040581307001d00c80d100401c0da1400815900a0048080c641203911046145401450140c100036404003030007121030304000c0e040345058141c001e84040700703000c10040486001010707424440c940d448841c0c000e460f0211b401800008e074005006c1c03001203001e250111484607409000750120b410b83c0394081d008004040d03607400b10a00421094940d00c0c030075403c0c000006a1443e140c14684140c540c150540c0741c15040c25030701d1104580c0b0070590314 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 613204496 1250 613203246 613203259
    0x203030601081f06090906120c06050315090f09100e07140d1a09010c080705090d03140316030e030703020309090a152301181a07050f010606021204050108070e 70
    0x258051003003050300d8000304903503215150406e08002e020010b440c000e411018040078005400004503174a40d515100b1561107081c120b982e501c80701c5c8001d4000f40c0d0301002e19008103038403091082e0f21850b070240d50b200300341000075120717801c2100c0340c0303002510501110b0145591262905000f0400c0e540740034041220014015a012010f5640703200d4401c480c0e42d0540b002040404c20049001c1003030045030019845032030701648518217214060441d0084450150051182e921380c102090f00804801080d140d1141d02c0c0c94491030f1000f401050886c05c0d00c14080020709240e00800c50f03540000545106c543d140c0c0281d402d2214450074400314410007001403002540b5402c05a0120354203035003440140400290354540d0a04144400105005401c40d113810000b20b813401e801c0e1021440d043c0000d0307500400340c2e40807c68050500420318090100050002c1c050301d081250682815400802101d400e6000da5880340c200921a44441c02288204c0e800f10301e8000c00200d18910808201c48039520003081e4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 613205746 1250 613204496 613204531
    0x10e011701080604021309030c0f080912010b0a080a0c0e0403091e0312050702131a090a090201020d0c0b07050901111c090f270b0303160b070807020303060108 70
    0x44a00c00d0400e81c81071095410600511043d4101100b00340404849580280038400e899900240340d100c2604014107040e032040c40704004c00c11403504030741c10110002c02e036a50b01302c3d0000e002070003088914003da2083c1042200013844250214819800c20303046207028412a05e4244c0d8010454001842181004204180400c511080500e4151207540c5002c00c40d01d05400c41c030307020307220148112011081c8481448070800503a00c0c0740d51480005000c035404550b2401e55114a00c83c020300e40d0030582e01201d00001c00003000c08980c091401c03035000342c4c00c40341144540e52042d505046002d002400c5034003c040000c00c010f0250005100030322040c50110143d40a40710a1745c20700405c52104a4450080d0084450142e481081c00700a41a8001e0021810740f505401c201c00c440c41c00310ba5030a8110b15209040c42e0095540001954500541a031f80c1d590400e0341c0001a251044c1d07412208a4034000200741406c0c41200c145114040c560011455616090010354503240001c04803012000c440d01e8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 613206996 1250 613205746 613205777
    0x3090909100c08060d03200307080c010614150c0a08030403050703080604020a0516050102040b1207090e04020a033f0206060d0c03230a03050a0e0f030c010e01 70
    0x4046104040d0480074001610920341e1034000e44000024031820060303840d09100d4245e0b940c44d0340300300700daa050030148a0480c83c404500c07040b02c0e44a21808443c0004a8070f801406007040092205000315402000703265106e040580d0380801d03a4540360380281c45980b003e082c0020010080c400745400000f11589520319a4030b031421036100301e034110001180410324508154111030304542046046906500b4203c0f8580010043e0080c440c070090124a003000e08011b02ca020740c1194041e00b141c2041a6903480504018942c042c01940c100c13000406450000682582100f04c19000740d07401401041607900e152584e40030401074058400300125480c2c412101400210900b02c54041111401442c2c031414100284c18040014102c5000d1014a483c0b400000c0d05008004141ca45c040d241e6280d500c42d1090940d660581c602d50312a003031050000000038142c010340900362100c4e090340d80c21000c130034210a202e040c2c0e0107203894a0305580b0000f850050366000d0b00060101080603d00780d91103901588 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 613208246 1250 613206996 613207009
    0x50c041806080a110319150903030b090a140a0506090f0402032b1701030506340e0411130510020102070203010203010f05090f0411060a090305030c0610080703020a14030309 76
    0x504035a0300c40c0e512004c0700c0701c1c1001d014000442031481d00e1b500e45011a51140309110030540010150180e40b442c281080501a5000000e4900041c10b0004c95242c84a040303c028082c840600450360080c0001602c00304160191912031200640080b840b074485124000d03104401820403a4540500307001102c50b22503154452501060070b170030540c0d9005922030081d143c01014031071320300c655485400502c007145001440d00d80100f050340300c0340000d507009070030640c0180039481a401c4c0c02c01c151004030141540310311307900c4203040700b1102004031900402031644584502001c0c041e41182c103c1041000c1c0c90004003074000441c4a00000d4500702d880c2d80040e0882c0d109811403c1101c5001d10117020b01c0c00d1181c80980c0c4107911480d045041e08103504d030b41350540d90350400107100c2c510002d0030035401881842540300071a4040f085a40392502c8010180e01d90750101c801c1401889040310004481c0c0002480360100da4018081c3d0580b1820040d6200c07111034440b07031441e05403204012804d80c644494 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 613209496 1250 613208246 613208263
    0x290a030612060b09131e02010309020303030c040f090204141516050303090c0907090905040201091521060609140a030f0309140301061d09011103010801060513050c04180608 76
    0x72040040e40003e514204001000090710100540d41c040e20134000145070641c001c00e500414000d640c452015520048001e481d44000080d0140400f1080c0000600300324042c1041d00d140d40035084200351034551400c205c2c0243c0c81140d401d4030580302c44481900b400da00c50840744861200741f900e84203010340c0a440520605c0000c940700c1c0e00000800076145420312070701d000c1d07140844003170a190500d240010312000b900d01803112080e54450214086a005440d40f4000740340e00a551510015142030140c40c1c96104584401c0301462200802500b020520072007003a144292240108103091001e08203014140f00c001c2600084490008404102c2200030b18001612a544100d159410309241048084811000754046ea0502d441072207041d030008a0030400b20443d40103490313107690700b9014034007602009038244140b02000001098100043d00600d003540c60a41da0180310b41c05000300e43d4100c9004940c10144000203010900607030010a01e82600d151b0301c100302140540d110a41c0d1410202c1030f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 613210746 1250 613209496 613209503
    0x171611012909060a1202400b0a0506030a0e03041d09150405060a1e1b090e010b030c0c120316080105100206010312021014010807290a030612 62
    0x65000c9124a450b040c0a64800d000341c810250061402d45150010001c14030000c1c031075020442d00d00300d076100344000c1390075038244007042d24107602550050702501c2c0d550140210000e4101001140e041c2401e0194008480d40070f4410f80c0383da5508040c0800500301d421850070980800c100004180801c4005200345120390042c13004a4200707403406030301d09503214002e03169541c5203000f040003240002c190340754008202c000103d04c0d41001c415543e2940414011394022500e046088880c5940031542e1400140858032640001d60303c400c4500801002442840407400003000002c903905100700103044400d0840045920340d41003106100069002141c0000304072910424410741c00b40d0261240e801400213451800d80c210180c20002d440300f60500001c0d088440c0b060250003998400c1040551941d1504010003000700d42c4000100d4441d000e01c03948070300d8810000041441007411180c1c030480111407904080000c40d10000c3c84150300048800d1081c5030b070b03860000603821140303501860541e20 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 613211996 1250 613210746 613210811
    0x90a030503040906060e0306070f121e0b041808030615040806010902030a050115020d0e0111010e0109021f08150d0b090604230304050d080c0a03050a17161101 70
    0x280b43c0001c040c51005052a1f109a000320103000c00a40c110b190740d540ea455600e8203d642078021200000030b07008039401e800d6148028080d090b08030105030721a2103203000880341441182103921202d030f01c085072810094a0303090204081117003490111501c810040026041c6414103a9900d5018241202617100024481c2c0010820040540501c2411b02420345424414060381e0301000c001d41c0c0d45482e41c044000d000b001d840b240c515070301901c091480d401c1c15070000d208204841c40c802d80a8100200e00300d01400303200b800115044080310078480006a190703205030456030b0317200d8402983c1030182e5440350000300031507054011a041ca1611403180c0c081200a00e06420b081c900b5035010024440314400d001c105481e07405099001004580031607008854190301c2c150f4070f003002d42c814401c1c00c007015282c0c404c070301850707007090303006005480300401c03d844410541d14070110040c117401080395003401f11b0200c500080d1140e401100344009540404000284900b4610b02144401e99900c0c1e18103410707030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 613213246 1250 613211996 613211999
    0x302122a0a1704080106060c03170901150801091a06100c06020c0d081905010e06060f0f041d01150206040f0305090301050106050306041d0c121204030f170c0c0402090a030503040906 80
    0x404c00d0041c140240003902c1c01012281054800800f498400014038840d045443d01080110f0001d410040c002580c04130840751241d50b0350700c1d89009048001007207a0f0a07070700030ba03002c0d03c41d250400d00c14828007001e00f4250f0200b441c94421200d6141140046901c5642072140e805e0703c4404204110b10743c80251031300e2401c1d06142c80c0328440340241034901d2400ca070038600140704800e0860141900312906035a255100d111080000100380100d0741e9034000050b0108000540c1c3c66004e40c0d00d100300000c0200e40040c2c0e40c845041d00d0020009030040320150340206d02080000382c100c0d100043c000d01a2070407a0030000c0507000607003510405c0c2c0c000c1c0e001400200502580d4942445070b020814010100a07005090843d1202d844440c6080c2d0540304428501118500440c248036188410800f4040c1e556501c0e124a410304241107151802d5800c050031080300e0b030f822060348040320024102807009040c000030110401010790300480900c0c2d04120038010000000e5010002340001e080380c0d58003c034403107 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 613214496 1250 613213246 613213259
    0x20f0f1305010e060702010c02090c09120d090501050c060408090112180312020a090e1810050a0b06030609042a0b18030d170408090901030501090302122a0a1704 71
    0x1d10300a64901c54141004014011f0ba0001c545001c80307641075648610355070b1280704000003401000300d2960841c02ca216045a2110003150703000c4141d0003511005125a216401103a1034006c18500e0001c5900c030002041c045401407000e4a2808814940020761508800307080342911541150340410503800d802c234030105900101d90404145900500b14240001c82a008090b61140c0c405c01803030201d40804079540b0b2112160480601c41000103c904042c3c041d0761100c001c00080328065180b42c40e0100c403200a1400340110390140303000804007106030303c0395102e04045071000c001d490004210705803c460840340c070301000002048045409a200c1130040c0440c000c060501c50440c4c4a500690305e001203664014070144107691001082caa41c035503075490b00000e40d204001001e54000c0c5c01030000400c1120540000c00321300d01c65825203600ea44100c4d0100c296026280810141144280424400001c80c0440240c84241d0800303c440e01000f035180c12416100840d10062003820004090222 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 613215746 1250 613214496 613214507
    0x1090303050604110913020c0a0b10080703080f03101536150c061d0f1606050901030906090308040c0e01060203030430090f1a0d020f0f130501 63
    0x202c094600f84025204940c48a40070f20520b0699407164081c84140f4417400d2095042e6a001018181144c407500c00500f0a0300100200719102c07560b260780e0300d4002c80c0f0207202140007000c507a4458012420103145010103032594000034016190107400b45000200c8980100724155504001e1720f82c411020064041d05025000c880100d203a9180356102e001c1302ca040584d07004040b101002d0211003c45490001192404840180500b041c0e050080005d240300c2c48010700701c004140c04040350440c140045410362525484168041c0c00c602004080040740e00803001407003601c005240018114826985040403680c01441c103400080308241000100300320b035120702c4090000c2c060880031561400500a68030311000b48002c009082850a215402c00300110710212000d006544034850f0300c100344024400d0560f845800030403003000e907000410b43c146000980602003030000c0c19240003810048500603520001c0d003141081c00c01c2040c40039080640025001c0d207428446030318005890075000411 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 613216996 1250 613215746 613215751
    0x17070305181b040209130f06180507090303111f02040602150f04030c0f140604111c0b092a0405010f0b030f04110301110909071704081305040e0109030305 68
    0x800d640070070801000040071071500c0c91901e10442d80545e5442210010400079801c00203454842d074200030f9110302120380c5411010584003800e52840c1d402c00102c01c440107540040da108004100798080500200c0c1c0324148900c2101c0301c840856142803050611780c0451441784640f0080f2603400300b000e21850341d0501107645a102c40095941d614207240ca06071110040140005003400f0b1794412000401901c1d100701e547c101e0b009810620030808620035151180022141111b0b0380c0c01100f4a41c2c00c518088542503e4002c4151148000e000030fa0b13038150032002c004d040340849205105d40c0103074030940c0101c05c21602070110341c1c2e900d51104100501044d1030040e0490320b2492504c0078240250401c42d01070780d0b07118800c0480070810341c465080c07042e1400300c1e0500c9280c1550900045602c0075000318010055160300b80d07081d0b80701d46e660b414101c1d18030300e0100b1b002500d107110030046000300318200c000e49104081c440e01b030350000b07542c0c40000703048919060340300310241d44034050f04007803681601c6000d9 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 613218246 1250 613216996 613217041
    0x151109060a180609030c06050705070b030f07090f08030d0b0a081204030314040501140703030b211b0105030610031103040303050118060b160c090e15090c0108070f17070305 76
    0x4c403a03003540e4030540103c005004035010030002103405400d00c101002494010310002011566a0500311540b6850950460710b40f0045100b50381c001234814100d4003484115400c01c00514240900c2d01801c01c0503055124242e40d206480c05d00100c0c6441060040030340300301c2901800c40d03031140f440c5000740020040700c2e0b116948e40e00900c410445643c002c490303001250785601d1000e5a900c05480c4c00d03401046050b00c0c00390840c4001b4002482c498254011003240c080c60401c6078070108000702020324049207101c0290004074140003060705810310040c2c0094942d810308004c00d010b01481c500309a00d4004440c00d40029840c0c000401841c030000040700f1030481400010b1028500305a40c02c801c0d841030440c2c11416203001c82d9500140802d80ca1030034003806108030305001b901d05e040441561034204185031507036440031401180100c0000980020654810307110203059075600541502d005940303034145003d1110154512101928103140d0a01c9000e041d100003419080070310001c084854140c84a4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 613219496 1250 613218246 613218257
    0x90609010203271c11011505061b03070b0a021201050913240e010204030c052407020a0e09010e070b070f23030a050304050111030103151109060a1806 66
    0xc000c02c480444604100303c80c00c200340300809400002403420b0484401d40d130158030280c042c420001d074000c20f0520ba2807444002030021400ca04010640c3c28a64031407a54481406c00400071980b01d8a880d40c044683c80340140c904103055078881002c8034074102c2d4503900107940015511200010084000e0152400303944e000b1140c41d0442c4000080b1010035006803070403107649420b01e586520b000d02005010b003010800d100300d561052915010390002c0c081241e1180d034418020620f800d18100400172000020840b120722102c0118000c030941c84400143e170000744c0c440303000c02e41c1048000003d0141c001000002040c4c5401c5030754505240d41504000b085c10700806c0080702042c440c0401000301d541014442d2000c80340f141840001c2d01d00d09007400d000340804104002040e40020245110340c2c0144000e10600804c500301c8540c0b80b000b4003000f00040c000c2114000c0880d000d83c00791048607910406d6031301d004a540002a4103402c4240110001072890fa038404c02c10180308404c000800c60703402c00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 613220746 1250 613219496 613219501
    0x1308071a1518040813060e091602060a090203030906030c121005150d061208041a031909020316090207020102070914161404060815010f02190c09060905090609010203 73
    0x41c2c0741c51000301c0140040c800000114080c4071040c021150011640343c50f05401540e0340744040c0940400010603403243ca480d40002d500340d032980724592070700c158541c064a20386d643c042140c4010308240c0000da8143c802400802c4c1aa1903001c0158041c0400820003030700e074400c44190201c40070004041040c03404540c0382c10000c507121140c0c050b182c1117048514588640000d0660300007440326a202c1d0340152140c080b42010b01c00a07100410940b8100344020305400110b482e044221b21094550740303000d4400a082740c60b0050658802900184020240c41503a00584609142e2010703a400c644511a40011524119a010840d1800404080b0410711012500140c105000710004107950101d003540e810800015100c2c0314840040d041104120380c80c5c58460038010101c26044582840c1c0e4003020440d200190700032405604c120304254000c001c5230f61010700382c06011941e0103003168142280d0b040881c03104007600629000d011500400295450301400c1c143c5480005040c450b0340e64030402c203 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 613221996 1250 613220746 613220749
    0x15020c0d0c0305182b0201120615031a03011a01110c18060105070609080301090c1107090f06170f01060b180405041a0406050f010603021305091308071a15 68
    0xd0f00e4110241640c0e144c1ca05944d0340108910881403108041c0003c40d080d4400151a44030a07400603c0d8000c0c3d0710101456a800810f00441d103e902410389d00d40c0c029100c64040510a130011f00021f1804001da0304980c501c040444d09440500d015043d8104441d140c0f20210b580c44900302c000c1c0c41c4200000c110003645407001c40d4a6081c80c00c07844c4076071480302d00000c034241d00075412140e540ba8489030800583d12107042c10046500280641080c050a040031070404500c2018005900c80140c4060200039141c80300540003004c0034601d0a28030350700e4210010303c01c540100307454000000840030748a45101c0180b101e085580a8110469881c001d00004d9046070060b44051103000c03050303a00046075207590038910314001c005001c0358148030500742004100000c68100c18002d941200b0081c03840c1c4d80300c4805805038010111001d1084169080030440751038028025500042d186104805e220f00546032a1070682c08030900b074850001313080d411100794103182d042c1a441200c1c3c1d40c201480305840e10 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 613223246 1250 613221996 613222007
    0x70b030c0705070f12060c1706120c0a030f05161a03090106030803040501022718061201060815010911070f060b03031b060c0306030d0f020a15020c0d0c03 68
    0x100480c05514011401c0c0040080401c050400350211032081000b8950364a2504609640420121180b50411400c424224023074500c0203010003404a080c1300c5c07951441c060003128402038030490302c03920400310040019101c1400d144090350084d00c105840c4400d50800d00e10b1709aa100c1c21000c070803002c480400c0b01c0381a60000003401c6c4060510981d40b520707140300e500d001d01120780002c1d1403420000148410400c0c158000d02c50311500614040000e0000d00c403042c80321b0381c90b01c1e807560010307980c028000410340c80740711855000f60002d000245d00c1806500d0f2508480d200d40203110150720102c2d204003184941003a003801801070040c14003500320951180152401245001840080c2c460483d00801c0360700d401c034201101c00501101d85407135400d03d00b0700d100102c04600e4519400341c0c0000ca844e0103101812a40f00e550050014500240c2401007180c58002a502400440c080c0081c0d100001e101c18444415281c205240540c580d02d55046c6a800e01c0341c050080b0381844030000c40c8000103900603 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 613224496 1250 613223246 613223251
    0xe0606030613150c09060e0f090a090c031203061a090310020a0c02040c0807200d050304080d05100f06081006080601140d0203011a03070c0210090302120a0302010c02070b03 76
    0x40b40c80d4a00b00000d203410b80c5002980d000e075242e11810143c0c01c84d800c90713000314000e04903a21651840c40811800c401d000c40000d080e2540c940103001c90300000c4400341240c2103a000240f0914004003480d0307403a1120b5070342a001402c6c0400103500e80384d0400040441c22141c90543c3c604a603806d2528400e400001c0e82e032980c0c40d8400384010340205190340e040b0b014441c8010125000360041c085007040714801030000c00222810000f0500c00050045c1c4401d03968004070320344034400b00510a0ba10320100603250341d000140200c804090030001c0b004407142d503000307050003155040e1041c0c12260828401940e001615001a001c001601c010806c803441c04c0b81d00c02048034254100380005071928001240c40c0701149182414804000484808190780b95000f1340c12a001520442d004c6803c1241d060350740d100a41e2900d000580040920001d40b400700c00754500c400079810466034080e92580440d5a2074180ba100345002d410030b45c1034a0500d6028040c01c5800384940c03028180c3e19050100307541990102 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 613225746 1250 613224496 613224511
    0xb03060d03030b09041202060c0f0403020f0a1208031e0609070804291005010c0201050a121e14070203040f060e040f051f050103020a0804110f040c0e01030e06060306 73
    0x1529556000d141c0254026201040c3c0584111024a05410702035030005101407108010306c03410b00083d9080000805692909046030f2003a842c140c615000c200c083d80032255a9540302c0325044c4002014075007100e0000070b1900c03d580098503460503045008001100c1c5a00d07030036401e801000c00070f141e501c20407540c0c0e002896040c04441901c0300c0c1001d42c0c243c44051480719510030722038188241140c41c010464450000301000c0e502c21901d520044541c40e481c5070000740403a03001e11451050310702441c000282c2180b80d1600141c04140704111031141031140c00303c0d1040540e030303074052140b0110a02c0d00741e43c041d01c0c80c00290b19240c07078480c0c8000340340405d05c01d44082250501c0c01d0441581c642d040f036210078298078818409414004040505014441000c280d15011040001540d5000c2d00a95a00d4580c2e5120108140d42c0d0740c940c90851843e45030440e5008030b4003414420166070700d00c5601c2c48034205544411140b01c3c40000901100c2d00400d258030f05511800030031100340d0380040c800768000e02 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 613226996 1250 613225746 613225759
    0x11011a01090302060a020c1201060f05060c1c0e03100c02160308030601030f09080316080109060608011401050c0a030206070e1c12090806040f0614070801170a051002030a05100b0306 80
    0x580003400c80c1000307907c0380c00030761001d080c1c1044410143c1c15000b1171b059400e88003c2a51f002e0799001044214850020301841c15001000324030000c3d6515203000992050a04010b400d071300a25001130b003041507261141081030b941d08003584040b0750421200700c03040c200c003855621880c115280d4500760f000040c621030405032642ca0040b80001a030300608441603000301c1c1c040c0c890500c000080200e0041004c00b10004170390100000d041c4a160050300102e44107600c696126900b017603440243d100d1191071043c1070000030007525a803007400300514100103000360301800450800b250002e0000c4501c0240c031744200d00c041b03420025504043e40c0c0c4800254011041180c402560105840881490740a1011801100300b040140700e9000c08011405200c0c100800002c000d21042c01003402040e582c5d40e0000302a100140003450389403291021111000b01110342034038084c0d803011702e80506400c14150329a0040140f02040700e4a0050302d40000b43c0594000416060000c200183c0c0001010103200b00c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 613228246 1250 613226996 613227007
    0x40218070203120c0904050f0c04050904030c0b1501080105040e03030a1a10020c041103041a060a08030a090f05030307170f040b0a0f18080d030207050c0a0611011a0109030206 77
    0x380204210390110000f00c100440c00c0c9052420180150480b1103010700480c01c000000754261040b1001c1c6108e41000c410700d600781820401408030101c0010300c00c400b44040e409500000c1040515054801e8240560b0302d116a44900700043c0308002c180d01a500031030801c0703211410200b01006492780301e4101c50b030028a01c0c0902c5015801031010380c9040c1d8111028035070700d0b50001d501080200c0301c60401e46081c040b541300d04510b410f00d131004446c0509484a14003226150900d2420090f42001004041344a0507803903115244c2513911000706803000c10400314040102101c4d00c4c074040002c081c00c5001d10300b0303d00c05440d0361442c155001c4210f400e00000140703400d0810501c0c020303207010700001190951250f4075100082c5c104004800c010010550440540743d841001910b004140e031040e50140031009020803096010b0b4001040460340d500078001603000940350343d042c1d4802000b042e56420300403100700e224142100c603068221000010400180b00789643c0221150003100d038140c60107aa5107 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 613229496 1250 613228246 613228261
    0x28050910141908060a0c081501080619080a050f0703080f0319090809011b0804090207062003010314030f070206071a011404060e01030b04060b190f090b09040218 71
    0x2140b041903151038214108000304010600090451041095140c10098803120304800e0f030b0200c4045407070503002c0c50449001d84c1a94800c8140c00d0700b2540143c4803ca070001907003480c01016440350808219940045514010b12504000710201071080c140586113031415529a030348a84070b458036a111414000011540d140007005514880019403c000c003d2f042841c58001255485610381c940054640c224080d80421031550b02c9003d641d000d9121403901c3c2c501107208010b508036100030707182d040e510210061104185507a44111207140c0d00c02d26905c1d0305501d8076003c0c80540a80044075503000303105500c280c0200700b0854180030303011220305455000394039108040498500070f28120040707001c000946071117402e000c0342c0705080c00c503001d20805031034450380c4100c1c107000d00c0007508d05002c100208000c14803c4e40010000e12020b0008200700c13070103880c01c0078001010fa100d043e0200703071144101700c11251445002c0c40718200f1a522551414140c0005002c0c4542d00c607c2c00b9582c03000800314040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 613230746 1250 613229496 613229509
    0x5031911061612050405010c03270b2a1e03040b010e131a01140102241b0301030b060f0d0302031e0412030e180105011b02010e2805091014 61
    0x42d590203c402e010618240ca0020301034207030b0034003100100341000112001060941485030252545402d01e00c030741d404580710350170050000380103407000f03001012001c02e0b004101000804400b0720107004981d40c00c1d02a10031402d000b034494181c0200c00044c4140701c00651000d00d91811103201c0550b140454691000c44000003140c00c00c01071201e520049862540405506054100c4010112280e1403080a5006a032a01c0c031410410704180c8031000e001c01e010380c00c054801c1d000114100c1c2c01084074948103017814264004e8005682c4603c500040103228500080082ca00e0340c0c081d5402900c1800a03a4065901c0c0030f500d00c83c821207034668821040000c50340003658001d202c09d003002c0044040b0703400c02814610000d80000d0080c070b91000201d151082c1640094120760040e90385102d08403844100c520035800e071090032130400c41100c44240250b034030380c2902465040700210481014041200d50501482e0b0755100c00d026248100c2001014003800d00d00c002204c0d071809807000303c0da00d80d4000541 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 613231996 1250 613230746 613230767
    0x60b03100c03090c05010f051b0106052d04060f12050f070f0302040e07060c120203040305030301030308150102060c22030c0308070309080f0c040902011b050319110616 74
    0x10201e10301039441007001ea05400000249008006585a294a500044801c0c0c4e10b880b1039100420300401c204089403220055030986542c0041c000a402501c9800040840c9601c45040000054a043c2c8509645a01051061260f82143c00700180392404641c00c1c840d80d0b147c4610408078521103a020207004080c40160120589003003903800841c0c8500342c0c0e013034459003400301b40c1c0280d203008419414039200240c00405d45170140c0340d50720ba6841559070b007851110400310071002c6010a00001000810800c0035501031842515140414603160b40c1c0c5000c40070760440c84904552000303090140982201c0c04440d6400b810001044070000c10700c20360f04021810382d00040c505c142c0d51310000701f413100007000341002c148695151640c0c160f40b004c92075651003400610030942e8100244082c0d50380341550141c2031091041c10400c1c600b6140440c55090074102c1213055466402c005401200d441d02001903210100c440e040c440881c0c4d1041e081540c3c0e540000306805a460000600448110b028402e82030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 613233246 1250 613231996 613232023
    0x30e0114011509030b010e040507030b0f0a0c170613111206030712030206132111120403030e1023070317090a03030c050906040b180607020d060b03 65
    0x41048424100c010200c002403080d5081001d401e0344882c08988603040c3c15080f6504172070101ca4030307400c1c5044410050000b4104540780d1091040000020f43c02d800c1082c4504504100049985070020044041d00c0800c861a0100a00200e03400300c02d203907540341290400b00688400200180c40c00e000e2005100d1144441520000800c1c101c54900944042030301c00d880c250140c0b80e841e9070310420040d15a00f04c180090240c5c0100c40000c45d401103c540f0280042e008042121040b40c9204103480001c02d494a0100002c2042c20015103940041000203400030361200b2107440c040c074548006107000c003000d6190703200d000d20403c0d00403074070310a04460120308001c4640c0c8118510040403035270180d02c403070811000315011100c038401c0700010303807200c0d481006640064032031101e95980807001882c8040d00c00b801d0000a10002c030050300c40f84007a1001d00341d0814100c1d681d40010002520980215100d944034041c2000110016210520303031074810b80e0302c02c002040d60310490000a0070300036a10000c1c0b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 613234496 1250 613233246 613233251
    0x1209020301020c1203060a05030705030709051909030203090301060e190e010e0d0c060501090504030f080612060709060822082b1a010c0c060f1403040606150905090103080703030e01 80
    0x44c0b54124401d00460040c6c0c1c04071071071004655100245074680026201d1140e0640020307100308a9801c0e103030015603100c0070385000d90721300203005140c100440b41ea9030ba00b900107030310111f00d60580303050034803c0001038160301d1a64021450144400b051000158920007030341c1e62110503c0c01420400d401140c90610f800c2c1c150b0305045240c050082c014161214262200e41c1810300001c5c00071407600c909400780e5050340d2100182c401d03881040e107460201603c0300e500120401084039080f0740a0140c280100040d50310705140510705100100b00480140008030725000d410900000c000d4600c251907455035100811a89884680441c0114500300345607848a0744000401d0000303000342507010946440c4003000b0440c81d8802d14004407801a420480244039101a14007030100900610480c0116401ca28104500703842108200e40c0d00d030002d5034115900c41d11541c0c2880b007408424103055510a451410041d100e281031b001411711401880050440c5c80b00141c030368141482500b100d08101c1402009 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 613235746 1250 613234496 613234513
    0x1801141003140c0703170f010303050705100e01021911070314070909030c1e0209040b090f01090602070605090624040621030320190e13090210030c1209020301020c 72
    0x9114954060709041700010a000d010980b034a541088079400386808901c0e54171641e0035640d0944140e80140c809849a1190f90207601003004180a140e503503e515000142e10345032a02d0746094240320f11a034003024010350001c2202e40720740000d9418112a0450074010000000601035418844aa0000d05695080c40d807010240358115000041c4c03103218001d500349000c01203040181c2e144c191400250701c5240701001c1b8001c2036400c6845a000f04145085d039840d5000d92190b1800c40320350314811140d150b00417072164188804c52262591045801c8050451841c201c0c040c0300048000c05880ea64001404502c40308903103940d84220b024050150f00c1d100c401c99518590701c4082c1060400f200000d042010b848520312a0082003009407a4445402e810800420b80c456807000c030100181d4108020700301c49a0007550f40319a00c0803440c8103520001508242c600500c03d6000750312408805050420310025100e552041a130701040c5440000081c0c584a81e00c00030f03002e80304901000c031051191140 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 613236996 1250 613235746 613235761
    0x1806091008061315140403030c0e2d0f01020d0309050703080319060b09010203183d1701150e0a060207090b03010e0622050304060c02180114100314 65
    0x5960015401166405008031881c03000c070701030f030709103c51948603d45c40e4804500064001c0c4c00c40d0342400c00f5030070301070b06072001031010400b40c49003458140d00c41000142e011910201c400f9002a040e0701c07d03556140a82d0348200040e685a103003580401c105503a4805000520206125840103968040d100756501e040c00381c1e07000d585044940c00948000d00d000400143e03a060f500407500d40a0068001c2e5042c054010b0040c01c10070340000790950048040020043e040710b640d0301610041c8003030084c0801c2d0580f04d074000c02280c0002000d071414000ba959001c4803410791030f40340c0c90440e100960b004029008407801204d142403c080c409821901062010955a801003042404d840702c0381820007082c28010209405d850841610304600e811250100c0d02e000032403184c85078043c00e80707400303464016525900c0c14070310345c440d602c41e0001038180d8549808610b0040d200300012186541c54600d030394101000c2810110f269440648100442d1a6010055000b034001140300340e50004000c1c45881c1154 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 613238246 1250 613236996 613237021
    0x309070504020a03140609040510021b01110a02060106050901090b07020f030d1121041403030f0a020c01080a1b0e0d0c121209030308070305130204020c010c080105180609100806 78
    0x86814149010040080c0c0c040c00c102180d50300c03481e00480240003205c031030880e00ac025031000396a8a007900c40c1c0000b680b10400d09020707038004481400b203040c0d41c45680b040024100001070f0060300c1000707020088204240c1c0d0000d00c41080d00c40780b8014580d01d00e405e03c009151180b21106071901405a0310170392083e80d030428850603550315031105556145414124020038082c421542c200c40180a11050240842001d1522580a001b81c00ca9103001c850400809481e000350000364010703440322100c81a1940d10000050300410404001e100316640a180c624140c0a501000006c01000a4805c18a580c2c1d8900502d00d40360440c102d001798580326101d90404989102094a44040640014803064400c0c00a00304480d01980c501c240354940080440c06060003a20100c030f01000e41c0d262102694030380c40107120b8490000d00004050301700c0300000c0c00100d0141d210034458030600480b06040c10505150381e900a600300c0380441d032a540d00c0c8180404005a0b00260542d12170003040100c2602800d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 613239496 1250 613238246 613238261
    0x60e250207261b040609230603010e0f010c0e040603050c0f030c040f0f05060d021f0e100315050301020c0a11040906020715240b0a0c050607090303170c0306060309070504020a03 78
    0x1139034140300310303511400a1026240100c031300411503256000c1e50b400b002d068404268000000500106204030005100d03454401041d404d079000d80d55506402d0f0041c1e401c50340000c60708105036000c3c40b206256890352512104907184150042c00c100c24941841e5809200560410310010410454440c101018078010b00740d1004030240382d840d060101d20b0920b4007100c08000941c3c000c01c0110ac40030025030094500c042c03c64910244001c00844090b250b5a030780050400c103d0b40d6500050340d900c042c60301903104209500550090748100512020540046560b402c202d40004c0b0035000c29090071f0101d0300400c0204000f600042c80807a02404100f81c400c00d116a440350b0320801c0c080d04051700018403128418103071924130030a518004204290010018150000c01400c16040302001516024100102100c030390000403008102441003580114103e03400c6400001380c0c0200345040c10781070b0580e10000e4041c1e0711524001c00001e203288001c0105038042d02001d001551540d002a0001d0080c1060 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 613240746 1250 613239496 613239499
    0xf1401080109050f1506061c0203070e1f050a031a100221030112030305150a030b06100201020708040e062214060301050415021804060e250207261b 65
    0x3c80c150b5003074900002403003145c00343e0110069546904c1e28001c021035548146400000d038405801841035051551014511440c42600c130154170f240140f0410200c4640c10f0040924440c0c041174441c0101d52007000d90710712103e5410005103d00c2d00b04003100308030305099980c50b4401c0d20f0340641e03600c007540400c29001001c0610354010400002c40c0d0701c0039440c04240600303c045200fa02200000c05c1c400e0b0802c6c0d800041e440c0d8540042c15806000c9012103060390825034503680c03440300744109820040c59104001c0c100d03100860030301e111569603005138420f52082c21180665080410040e036103c5040345080f081d04a070000028a84440c6000901620080180c01e41c00241c0000c0b1141010300545100325800500311018078100c00451009401250b1440100c560790f02038800c06440714400e80014088450b20003e8070303d000c006107611510100103940c0095100c08480300070130340005044007034035031640501084800c0303c04038106070748032544015500e1261900c00007034030b448a007080743d01110 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 613241996 1250 613240746 613240753
    0xc08010c0503160e010507060f0605030c22110f0c0708010501060c020f0103052a030105043602030a080f0901030b01050a050a05070f0b1e0f16030f140108010905 71
    0x11204400e076114002100c0c9046403030f15118100c643c2600c01c980d4040e450405040050802d1000e0711400100d0300c800f040d4540556440c0e5003800b5524007089080e034413400c2110440c2401080d0402d2486424840b07011640301902c40100078503010031001a42c00307800c40680c42d140c4810090f428146c6d640c03014411944c1039481c150001c00d01c0d610401c08030311a00d4029001c00300d0b02140c10700440080000a00220010724031003003c07420403d4201300c0d42d441d00c90407040c064036941003404001c1180d840c00e0b040240c02e82900710344c2c6110a04404076a1803040c003c022400c96034811b001090501001c0c510040c04904006003d20100000b5409070249060aa0f01048001c140c500155054031601410102298060040442140c030074002051124031030007028011031200e60300c0003040034007907852503031010000318220200c1c6100d00d40c542c1e10248070604150b450130800b086d042000c40e601840c00070151a06000c20750352100b504000c06246880c00c050407a503079100b00e10b0303000740300d044000c60301d600 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 613243246 1250 613241996 613242011
    0x60504051c02070b1b0703120908072306210a061e140d11150403031707211407050a03060b0408030322060f0614010201020c060403050c01110301030c0801 68
    0x51002910f4001e4860701d030a664500f80011000140220000700c1031a02e9106010020000802071a01c4032039031111500d035000c0b928104000f1034181245030b040046014a5400100c010b803480b40c540c581e1244090760030b9075464602e9042c1485003030007940440d400c0701225007030000c03030b1650740e00600403100c0d407441a407401002081041000d1019205412481c0618510f444803860000d1106801a00c5080200307580c5000b1004101c00c40c281c48c076110083c8a012604209051300a98100340b05000003e03804018686081c0140400e5032001a09a41c114203c000c0401c1c849264044100c85560b08403100691900c494014140e078000518400005d044c2440082c101c0007410644040d00c010602850465841d01a400e01c82c214541181030070081503485140400c0c00e600c164803160081c5680031a02504104a40c0c0c00c201051810714110ba10400100600300741c04546241c00985c145091940c454078440d10078050000070f0885401844000300000401400700324400446a901e0001c5c070a05 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 613244496 1250 613243246 613243303
    0x15050c0909070e090a0b030c0d110a0f0f1a12040609021201150302060a021c120b010c020d020d05010b0a1805011a0714070b030c070204050105100c0204150306050405 73
    0x25440b40c3c10340380d00001c01d08007242c2140701d01d07001002e80d800d0141c100c801c0304130401c0000f41a54502030054440d00340d43d40140c18213080a0040c8000b43c00d03c22074003034806c0d1602c1d01c44200b2160718032400680740310f02c02d000d81415a00c601143c0503882440c2d13540301c0e24142070074204000e110366182240304030349244240c4000034040c02400310042d8800c42c481080b92071a0280541a8000380c85c00046018094980e50445156001d44485034695620b400c50113614030400c90840344504038950500021809107801640e03000c41224006605031115082031f607440c5041e13405010940d051030703802103c5800203e80e0714114142c01c140c500c3c085c0e0f01484070366a42c000344045250903000d000480c6c14100310070700c081403128900c4101641404201d804442d40e030201426190415102c0c50800c4400155002c19464140541c5001d0a000c8030010300040c0b038488080c1c084500803000074019600c85038000f140010310f1a00d0001190814030070300c0540750030319140c3d481e02c90505100720100c072a0b821a1211 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 613245746 1250 613244496 613244507
    0xc0201050a0b150706020903060f1e0c090d0f060c030c08010b09030304031209120c030209070215010504090f0c060e0307080601150c11100f090611030a05030415050c090907 76
    0x500c0300500020961003c070a508102640102c0302a0b400640802c0f40c40301c681c8040081d5032048007600044042400d21411150044107120141d070b00c4d01400c00144040703840e43c24200c4003201e03c111001080c000d03451a01590004040402174011891f107005550142e415400207141c807241540c985041d40e8075071500480c540a00d444081c0c1641c000d0005200250110b480c5150080d03490400c04a0780c2e550f0b03c1ca041745403d905000b01d4950380c424004004509142c0400d94105400780050017400c0005001e42128000500c0356600ca2912400244107200d040780c07288a10ba41c01c22600c1c074140f40c9500c4060302401005e50054028416820700140d804404140141614114840107a404074015000c61750040d1007030b07054400b4010194121655590780c100c03080100d615480e10405a40c9241026204100310303400b01301404440b4441d200e50b140d0102c1207807210409400c0168590311507040143d08441907211050215141600740404e194201d80988140c441c119500e1406a56041c002ca50 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 613246996 1250 613245746 613245761
    0x9060f22150b03011214030705010f0c08090c060a090b2706030108060a021b030c0c1207050d02130b03071d1302010e040c05091809160f03060203060a0302060a030c0201050a 76
    0x1240c10500042c08a0425141710040043c081c98030b0f07045004645040d80d003183d0041c501142c03587c0d9541b4a115400c0480d004180d00301e196414035101a01c1c083da002c0d511119003031030084c03092900003a0f072803c4a00400410001c4d289000f20a034559403850b02441c1000083e508902c0d541d82c0074940702030300c3e160107000c50303041c0c8403028003030300c0c01e5155001c00350041d40010084021440040007020045e03102000034159000000006022241a120034041d03500c810044142440e08502e80600c210b451754070595180030341c1030700c0301c80ea140035246c82000181691a1440e51501074400001076041921201c0c9803002c591041c0d00c0d92070348501d540052821030000c40240494280d420761001c0d468203500c001080c1a481c06d011f4605100c101c001640031608030b940b22500301d022402e0140010f0204040c00030540c02011151925041a51100c201c0c204e900c00204819000000540ca5032076140144c001158068481070300d81012041c040c018040c81c0360400e00542c608400112111210300540c0c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 613248246 1250 613246996 613247009
    0x2011e020304080a0305070504031509150b0f011d0a0b030103140c0d1202011121090105090307020909010b0d0303050f10050120120705070e070203030702060609060f2215 75
    0x138601092034074142e0107010000c003000c090006c01c0c407000000ca03410080100c88188034540c00036600d649444c1c01c2c0030a1409214601000c0e24002c002001610703820554100c225007401e0000c1d07007034034141d40e00b81c0e0f1240380d09503643c11440030000064000c4041000c1e40c16a8403401646010302d8482c610701d65503520012146511501490002c404100428645001d6500c00e00c0041030508107001e03500115407000e400d45c0034284c011030405190b400048001a000b42082c002071000f03080890b070b07140c0d9a0040140c0030307100c0c42c511804290f100b00c00358000340c00b03881b0141442540c3e48003824003400800048480b2541451210300003514400c456154005441c0143c60b00c1240025800041c5130650041c041491188121240000d1020310703e00a40b045510030801170010a00b0801c0213944184082d1017002954030a0044c0b100d8241c0100380355a0101c0180c0e8041166900d800000702e102411000064000d4580f101c07045102c146142c04142c3e85000f42000d0110102e60555101c051580f4071560 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 613249496 1250 613248246 613248263
    0x60513090f030c08281106060303030705030c0c0a050a03082514120a02192a03141b0601120b01031403130807030506011a070b071e02011e020304 64
    0xc0300003405070014102d02d6010b64003a506060003070120300203404c9840217900480c1003221201c510964054030035000c80c041caa0140c07645060820103c1c0c1c1d240405070060301440808800910003000e207a0076a094812108200c400d045da15040140d10389100d1a0140c00240304180001c034000391305081500d80c03c00450545040451550040f2004181040c003a40344240070007210005650111011b80a440068001640c0d041d02000c40300e142d04916140000f8000b5403008652484212400c07608103c494032410a60b080c0203180403113808100302c540401c0100003146804050650b031040c8524999400c2c22a101a6290382e840c0e8200442c0e03001c02003078200090300500025504075505989900700380116801c2c05903e90241000401603000320020342e1210500308140a8108842401001e150f844151403014618824000c0d205070b100180c045201c450114032401e1046030802082d02e1000815011a001c5e200000e0180200c03c802c1028804c00c0400c40a4441f441d00c201d07805036a001c481e0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 613250746 1250 613249496 613249523
    0x204060e09040c08010c050c070905010b0f1c050c0c070801050919050a141b04020405010c0201030b13060b1806090d170d0615110f0606041a060a0306051309 69
    0x10007005480092003210504540c8800040c04c402c240a01c003903900d40c50b1982c41d1500c10142c074076490a403140e80061440c0b41018010880c0807410000c69019070b010111555890540f855080720071070218920301262071501e010015862542c1d0301a010403000305040d01d40065490001b14240d46007940d80d01c40341e03045271244110504400b0790000140e84903a003942c004900300c0d120398400406400e000002c541101c2c604051040031300c0800901750710300b254210300301418080000c01802e20464020b040c16602c01c4100b0a030b41e5204010202c1d41410442448081d498003c2da000c130b41c1004180e420318040400c12402035162001c10744d6440c0344040d2803007142c0070107900c50341b0705404030010b078251034030040040300c3d0b0021041c09508003810009405101c540d001480007044440740742104a031a401001c1040da0380c04000c030301d440e0403500481d0041807881054101c0c5c01e02800320020113502c40390018940494a406420110446008a480509041201111106644480c07400801410780e64a0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 613251996 1250 613250746 613250749
    0x1b21050c03010b0717220f150503090c0d0c1514120c07060906051008030c0a1b090204030b0f0612030d0c050c0d0207030b0612030f03061207090f0f0204060e 69
    0xc4c142c61401441025040c2040c582c0c048815030017041204580c0400c0001c0704800008080104024180b00d40c2d040e10322454540c0700e4030447d41e01c00e4034604001001004c5881040204402c055040005108569412940c680310f1040e18161141088040b224400110941c1c06800c01001340e03045800b4040c50114683c034484070300e41d0002c150041b0480180401310220711984110712442e8440d0100040904000d44101540b08030356103c00340a500800202c83c100e2000304002c41d8141d88200f90340f52408242d2100301c44039801d50410400144040350010a001da4072a155015901d542031005140c2c40d40400c1c840c0405000403500f01c0355208000068034100d86610a607041501e41c43e105060452305140749043c414404000700040e80203000910601a0942c00142c01407012034041c11a50084d01d4600c2d168010000035451a002c04400100300d40c0720400e14218205079041603518040d161100107005101010307440704000c1c075001514101c2d4401303108540540d8055110400d0040a400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 613253246 1250 613251996 613252019
    0xf070b040512010e030d020306040513051b0f030a06020d0c0504150804050102130909150203130f02030a05030a0f03111809060112110904050c04030201080c0a031b21050c0301 77
    0x1c810385503544d071300e80d1600b008250501c06010305a041040250341c0b42000410881a01c50181210380030b44140c00d0464001240044c648030300304511800390b024080c00c000059403c044d00d200b0107070180145c030301803010001a0350041c2403c00203010104016154031000f21102d0049000b06041c1da0101001c5440c500d0240c0000303a4031030b109038005441d0111198100c808a10130b9885184250b03160740d000310030046a503071100300c18005160110f0030752034030b01c04003000c0b40342c1144060000a000c3c940304003552402c0c007c6034195504241200d0ba0b80b05440d8000380385000c0249910006407400c10600c00e0314500d0021108a0409101d0311491411810100a0b1030000540080c0c10f100528040b004011802d01810301091054040036444050080034802a076000600343c1034103800070802400180e8220400c00c0c0c00c0f20344080003070f0321404404400e400804000391401c3c02a000503402c002d030b89903c0440c0d15500e805905000f481d02911681420544402360388034002c40b00c0610043c0040240103 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 613254496 1250 613253246 613253269
    0x111c1a030c15040b0f041503090b1609050301022d03070c0b0703021603050301080c010801052407080403050d17090c04110d0204150e1906030207020d05010e060106020f070b0405 78
    0x6207459203010784d1000c1070b2007030703621a0310500c4403030b0b40114040120070a040500b5210340ba0394201030124500c00e43e40e80c02e40c40001400400740401c0c0451003044036109140d8003000c1c0001400071560f40e210151914007001d99070200d05002840c0074000e24034407070f003482034034050b03640e54032280504080780d940c4000c1103030002d002604043e4203200c20072004401c0700c210140107001740c41d80c55803541440101d50a10100ca007010303040c003841030010045e6450307848800c01b60b540d0b85803d40c624101050301d4040b0a1095000290100e80b010602002744840482d500c10000203079202da80001c5c2048000001441e421503540302550030020386807000d4100740d001f54842d44034141d002860500c038841e1280c100c4c0c1003600400400d1242d00d80045030b040e0060200055808121070401445030520080042a08140100c00c20076801240c01c0d0215150039040b880c400da032180c0240200000420090354a6909110310380040c03154208201000401244010030343d0011b080051803d070274802405480d0508 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 613255746 1250 613254496 613254529
    0x100e060d0b04020f0427030305100617150d060204050301060e04030e010e0307080703030306150c05250f061e2f120f070c0e010e041104111c1a030c 65
    0x41d80e000b10500511404010f424828181ba01c80c0060300710304006040300c00040c180110f040051505108464202102008054000c03028000b41c4d5103803401c050018400c034902e01c1e0032105802c14001000110307009001901c40c290020070070303c0d45d0b40c903c051214000303907409008a11958054003e5500c602c0842c108003402030219683c01d527071100d80e2460900c15074019000203607207150a010104215201100580362442c0c140d0709889561035507a1112001402d8a14002031401d2000d030704c00f50341d40d100b80188074003c840d08100303036100e40240c5003c0e840552524000221702c445d0710541d00901c1c45020441c4040e0700c214213021a894038000c81d45000d580340a4070710a8842100c0000030b03400040075042851b554080c0c9440c070350701d00400f03483e859800c0300645e00041c100520003a0712010b0910762090300203031544510032400300440d0003060191502c0f4169100022410034000c4131080d003551400c0112030401070004a02c142410000101faa015450380041c252140d940c54941100c4400341e00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 613256996 1250 613255746 613255751
    0x140301090c23130b340515040302060a0e03030601030b0d020a031a1006082d01030c0f090213050402070515040b01260703080a020114100e060d0b04020f04 68
    0x103041c2e4034003420440020340034164100018850402c41d402402e54402041c040100e50700348641c0da040091117031005c030141c0c0340000c0460221104600f5071007681c03a5042d0410151101c805092048016001048a080d00507200d01408170390040254801c8040281d501c9003d1400e5840304801103014002c080042540244503850420250740c2d01c02801d0021886002c107002c485210207858030b040f075002094401003914140c1d042285981150900782c2c014400162141c410008518010407402c540d0500030401400c08000b10801510398400415280316008160900d42e551101c034003a80300e1104d05a08a85003254104183d04298002d0318074144900c041e11242102503026100582040314161820035040c0e004000459a010720a15003900c81103820702c0d5514002600c1d99583c00c82e02c030080c43c0c0030300003030700900e018400e600c41040010708070341d070306242d08149580c41c6890321036000300d0f0b1141803040b010403618a4038038000007007940c3c0001030304941d540301c0d020004104200e282994100c1d4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 613258246 1250 613256996 613257017
    0x40c0504020f04050402040e1e040317060a030f03030501180b0109230303030703091509030c1b0b04060306182d060506030906040501050a05060d0605100806040c0303080601140301090c 81
    0x5d4440c0041d00c098101e00d800c007005854803456105c80e50100105054071050044140400f003907000918031869031b580c015007040c9480341408225203420f29400900b0901c0c9607540c80040541c5900154126815044007039503016a0950300b400722170002d03c0c0b207400b20340404010822110b1800c142003064107002046c06000040c0e502003402d41c1d00480b00b84001a80d41c0f0415010044080e40f1000d41d03c0010608102554803660050910442680040c3c001c41030504583d1040000b010300328040d01120f0051074441e80d8030140038019141c2c0740507c8817415540c0c848000460034500c20000d41e224201d00540c001848803031081c0d00302c000c01446070701154031080c0c0811035880c0d000045006800080040c2160724103820b00d01e084030005480f621640d4103000900c90569101840711980940010000405071224905248500540e5000450300c2c058a01000f080c48180307501c1808485c0a6181c0038690380d0391600441d0404012601d00321003241c14030040c08032050742e074001020b285903410f0100401 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 613259496 1250 613258246 613258249
    0x406120e0703030503011a041401030e0a0804090b090c070803012607030b0f28021c0606022a03030301060c1a0406020c1b06120702070e0903120f040c0504020f0405 72
    0x2501a402c241c02044002004110001c0704152243d01c503008072450605240c180072050300780c00c107001c2d94903042645a10500080b91410300c900c1268950003c5415030304c1d6030703d00c011400340c81c150740442d105040b204002004600d81d00112140c5036409071b03c40789140c4c01c09440d8010900c0081420701038000c020064a000c000400c1501c0145d400744947c8002807034480580d584211f002410341d444c20030f1402c030484039003981048a00265000d8840540ca98030514032040850f245080700c280c1172824000d00055894001c80c0100c1070801e07600c4404002c3d0f035144409060141440035a82d0140c1c400c00040007064414043e5100c40b038418000c02c030390003070005e54006140344103440c140daa00743c0c00106501c0002c000c0181c105d200d52400c032504e613244540e078006a44c0740910f000c211484c040750000165824405d110b004068003469404100601340324001a0b6660080c04a8881110780741001c5000c002c10929010b108507070100c820010390b0b0404080c00701035001400d9022003007200340004100c0c2d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 613260746 1250 613259496 613259503
    0x714120304050106260706140c031c15030506040b13062a030e03040302090a0605030703050313060e0d0f03050c0f010b13050c030a0509030d020d020304050111030c0406120e 76
    0x1903008100100d4400d04240102c079080516401203581280c8a1003914075035070b00455050110384807401d182e048c4494800b00141070b803045010000460000040b006800c078085292104c0c81412103000b00508200200c403203500f05254000500b4030b41c0140c001600090005540a601486400d202d0352010200c0c5c1c0d83d00243c600d08036640001200c4800c00104a510091340803c00d10114039081c80780a10612601e80c1302d00c03031800040d0048804400061016255400050040501908841c006640c81c100942c40350819003d00000004031140041c216114035070140840d0801088600343c001140d0700d04c0d8900866580403018000300f44a2003500c0e05061003c13182c0320740f0000021952018a4003044000030000c00c00321046880c2c4001c0c02912458001581d5004201d07000000725911914601843c50050401802e00d003400010401f80b81442c580165000b20300c550024042d405246207400d0b107a010844080110941c14003003040f04a2117500040c003d16804400050130642e0f1888239400d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 613261996 1250 613260746 613260751
    0x42303100c080405060a0c0f050c03071403070c05041a01031e06080d090801020c0712030c081c050702210918090304031205041a18042d1107141203 65
    0x10510349400c00050000030f2081c20350113011030ba01044110000100034009200310340d00c18003000000309030f00c03039000c008100302c0d1081508200c2c26140d40c0307201cdc0d014565903809024200ea5400e001080000c280c185070260b451032844010740030024a80540c0110000c00c3e040b01070411040a070f00c1e01c4c0301800081d2140601a000100c09031121f42440303540501071801c5580020007d0384100001d0684003404501e001c1929115074030411042e0503402d08517403611424401030145180080c48000044c9080803480c000040f001040c130032503440764000d80e210b000904000da0705140364560341d401200a5402010300c004010308423641d00d80700c0c440701242c1080803205040345500003e42402401008075981025014502d0414545401c0c44001c6400b039804810030b8500303c001085003110690f01c0e0b1110f034204d06003d40204401c4001c0e80244a060314628601410070351800f0086c12011070034001c21180070101112035103005c407035a562002e1108010107501481c00340b214101c643c609000019030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 613263246 1250 613261996 613262021
    0x919080901050f16232407120204082a01080109020904091406040515011203200a1a06060a081f120b010302010f050429090d030302031501030204230310 67
    0x110f1443d0604104440d100741069120340e01002c00c02d18003009108900c0786d01c0401441030411a21400800c0e0303901c07141c5e6040d071480c0078008100030034000000106202c900311640d84501d0741d08404080c4d4480c0410b0b41c075a144c0000c491000500048500341c0017411500005400043d102030507880710a401681c0d8000000507400031018081802820000030184e00e604010380c1e6025494601c0185220f401804010140407403905840e25051500300c130f82c0d800000180c140d403280815490081c08803c00018011355101091000c03d00070b040c800107843c180b1f0904d80340c1c0031030394440c0c84642120450383d000304011882c41c2e81d00401e56824030051003001a114414403001e0b54118030000d00601a245224401c1110501041242001490103c0701005040300303211411130358800322080c1d03807082491507604039207840d91560403d6455801944204808155840c4588500b40110705920480c41900d9100709840100e2500140c0c07469a441040001401c440c10810180b4040c4140c1b09181c1c07000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 613264496 1250 613263246 613263263
    0x904080903011802210a030c030521040311070b0f0c030f0406050c060604090f0605040303060510021b04050402210c1306030b0a11032d0a050919080901050f16 70
    0x2400c508121501040d076414006800d5040919290b91741c1d40c03007003451400b0b41003052039800503003494060421525900390403040004c0e0003115401c4410442025030b0300301c00190380b03200040c01010000c116001502c12282c0982d181203e14840c00e100c80d0001c1590345480c0c001000900c10107210500204024003c94a0b501d895014030b55806040c00801000a400345040c5201040003411012041c016598085400180d948850400f20700611036900010340011a00c00000000c98000801c540140400441540503000c8802400251a41560020b400c03807441c18601d640100211104210401c0480848050700988c500050208207403c038040100b0341e40d43e10078024041100d11843c0e000e04c0d941d40038032002c960100c1c4480c2da80b20050410811400340c0400582d12032400030400c455075240e407031041450400e00380100c005c3c1800c1e2540461449100500f1100070401000111035607040700c003e6080c00812001940c0c00c2d800300079001015842041500c00002194041d02c214a024841e41c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 613265746 1250 613264496 613264541
    0xe0a060302032407030f0e100203090d18050d1a0103030c0605010b07150c05120f01050405010f030506011401031b031a0d0b0c0708070f030f0e0a060e090408090301 72
    0x500d81084010441c001483c0c0d4003011490707800000d220565009007003031500107141310140d1405001881c0e04248420344e4014117105481005058024500a0304c40101f560b0071640c2e1030900707a900b030320a5408520403921035882080b2034a405040c001d070641c0640049444d5100d492142c2020700c00c04d8008a000c120440c140d14140201d610a040c050011000001e00c1e00d81d00307807506a40c054046207070508440d00c8141d03125895108809440031a60b01ba50040414204180c803012404803d0040d2401240341c00000188211600300f1001140e8124001d401c00d84d00341021032401e8401120707000e050540310310022034210451f4941d4a05030b0450303a03002440c0c0b085140c0c400100070800c554a44210304458002c0c01051902d1076094004e81c43c107500c40c0e500c25003480c05648601610201130a0381c8040c9030000c0c189500f0226070f400d1400b076641c4030041050054208911340c0158007486000038030007204c501641c18561080d80d00607018050190808150070002425038000003429903010340c680c4403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 613266996 1250 613265746 613265749
    0x140f01051501210e010f0f0f0b06120901060e04050a03031a031e0a0803091b0409030504050405062805131a010c14070b040503190308130c0e0a060302 66
    0x40c16088040031448100409030307200002e095106980016071440312010044000c0c0e04160711202690480c000240324005600e0811001007113580341da5071200e81071050044010703005200d0040100703801000b0508003a5954540c03560300c01c005241a000e90341e5850003043d0003516062040c4518420002007607001810f2400030162411071511810800c1c100d1429012541e000c07504042d48030340308083d11030044180400c2c07450002e080a0103080f0301c000006000c04e08001090074114260714441801d00f40460001b8170003141e0400344041c000620520041c03125140540103683c2002000304408407168060b60140c41c200c0f041c3d000d04150f8011164200140e00b04070790a42184000082c0410400d0a0b111000d0030520441c3c0b22a410083e007061010308002e03404e15003039441034034041250540b5842c1e10304080503078468000c00d44680319803c1c0e00d20000381400c0070190300d55490707071f60341c0e405455040440c0d00d4800451021104413103c01e80205201c2009054540b140c060001e01059182c40c600 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 613268246 1250 613266996 613267001
    0x3010b07060b010e03070605130e0709150c0b13060b03120a03060e0105310606080f0109020c071401030e0102030928050715030204170c1504180f09140f01 68
    0x41d040e6050004c1d03484620215540403842c4001c40d4000d0070031654401903081d1095007901e0a4000c4204425102c0a201d4040e50266540041c1c6180c102602c01180501704140c9101d56129801421101121b002465007940d200d100003140744540740210307002560b4800a400d041050800f0f100228003c9011410076500d801180014a0121030f1582c165040ca800b02c1e5035005400754044410803004000300048a203040005042c103402d2004000c29070722100c00822000c02511910980c0100c42d00200c2c81a00354804c40d8000c01105008003544d03850911480303100481c0060f81b5050560703e030006078402600b8001175106107101000780c40c04d0441c2d0b01c124204882121403c03107d5000a401080008030005440801c0d600c02e8068608030f81031000e8201c0203842150002c402ca88400a03c00300c038020006100707440c5900455801720707240c114007405155802113200d25615004140d02507144448642d024071314a00002c03001140e140040e890f1148007400040c0e911a1070b912600040710511030030b1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 613269496 1250 613268246 613268261
    0x120a091e0515130804080d0f0e03030a0e012003030f01080c06041208090d03030213091808070c050307030803071404030c0b0d090c0b070303140903040e0a090803010b0706 75
    0x40d8095028024581c450a0791107400c4203940070044040004260440d0742107401e403480a80c401000e41d42c4980b03861b4031a4582404e00710071300c04035801384414500305000b030303092042504014004500f8094038940842e600c3c50703000c0c6128103101d80c60030b00c10384500c841c1440c10320a4024030021640ea08081c140c0c1880a281688070402503005072201d24a00e03961030f02102c04482c084000f50100c0303000c80c2056141c071301c00c034200c06034462081c0c2d420b9020160160041c2464041d030b4882005450380e5041010b003030b1802d00d0700e00640c13152006041000914560054490380d40036400c8842e42c0f54071a00070030b00e04074003600309540c414004005c0240e000d900003903242240c07807806829403d00d46160f582c0043c080c5240a040b4a0100c046600051540160300030070700c0680003040c42203041d960341d540810aa0101609900190611010442e240001e00c2c42d00c2c026000c0d94001e42c070b0246095000480d80c0809410b1f02d0359680c48100480c049540303207026501078041420b1441c2d580303030300e80f0b8080b003240c406 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 613270746 1250 613269496 613269533
    0x140a1d01020a050403121116081c020d050f0c07030804030b010f03210e040603121107080d0c0203191209090504020123041e030b0f09190305120a09 65
    0x41200b01c1079583d00905940841c0e521803a180e8107480c0c0300d1410342d848000c4868260113842019050f145000142902c04100c9508000b505c601503100c021040450242c0e607020b80150717000c203840310b032404d228600515101d1149040d49041c0801100018200400c50388241e4a050300413070240140401d0303c024600521003c00714030a00c80c55555039000f0008407185410184801520103030b04240216410b81e196640144108015512481c00302c040c02e071a4200760001440c00ca4214a2440000804401f81c90f8071000800c0311403c1c3c2e04040b5919074050004036014040c034041c1551058403107000c540094400d01401785540e1449800400800c2c807039204845d210b0a050130711000d41d0700000310f01c101031440f902c000c00407056259080301074481c1d5404801d000c81c0c4200840c0350f5080c491020402e03070703108200d0b4164580310700c0542404d14000750744820803500403480d80000c00c0c01805410051074030038206907040465003003d43c52401c0b41115140030107074590511008028074003004c21544081e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 613271996 1250 613270746 613270751
    0x213020c0d05041a0f040b0c010f0c020c03030d0c090f03030809100c0f0c0303150b1b0f07060e01090b030703051501091206090203030702040e0d1b0b0613140a1d01 72
    0x54058130743c00c10001c074984200034020008602c072403122840200c402500c014002107913513180c80100c007402000001c406290325881c00c9420710390a4070109035009c200300020011410803000390212401080c8403201c035414415400790014200200241c0f032030045010344c540c07160304d241083c0070320f05203400400d001603e00d103028a02c0c0071894200c12403008a2b45646480340060007549402c1d030007810898548408003522090015078201d003a002071000403910100441e10754080e8064940d5450f00b940101e101e40c03c04501070003018458804040030717803c1450303d00c0020703035036100d545030592040c0d071504002911402000641210b0710521509020b00b0720349a68041d00c0d0100e4901d000030003040041000c0c0d03c07011007c056542c00c0007510b01140c0c00400400911002142c41070f510300c05882a140414106001c4144a07200b440040603000c0d00107442c1c03190340c0d90362810844040c8600300f096204a5071010305c503800b49100080b8510508105100054040e00000b0304510316502c80100080e913030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 613273246 1250 613271996 613271999
    0x50a0306120330181b08031213230607021c0302220b04030201110606031906180c090f0209100f0c06090602031902160318030213020c0d0504 62
    0x250701c694100280280d0080341c0d500201c000100d460822241c601c990329003400e0140d00180c845100c1340d8094050700c11003601000070000311595084c030140384560180c42d08217024058208500756081c4c0c0d4071204015803150400a180d44000003542680305150300c030b64181150070f5405a08000c8540c1007000c5000a11001e8041041300c60111103400c44842010b802040590000070541c1a600d2162040030b882c0a87d20303290300d0b016045400030b10090380000c000d06c1c03604000c9040484d019000c0d48001d405020f0078049080b003851040c1c070444040362600e98500500200b84490f80400022521810701d02d000039151a41400944a4826112905a104009401007540d41c01c56048a0b0f044900b0320426040d81c440c1d05941c00b01104002031710650601c0a0001048540c0d130095124210f20b144642c1c00c64400c0c4808400c078001c1da140c40700e00540310b6240c4800302e4001c00940826031104610314884075101d80c041038a40d003d42850901054021903003405034001407207103080701000340c078003141042d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 613274496 1250 613273246 613273253
    0x9150a02130b0c0c011412180607090f0e250206010e071b020f0a0b0f07150b01120b06040f030302031b0d14220b070b0a0218060d020702040c050a030612 67
    0x1001d2044e0070301d06100310240800350820030001a9409061000459201031070aa4461921040500140441401054009081ca50180e8211001c0e1440300304182003c1341811044058184003070640c60b0014202200c0752500710902c43c00e00c0c0d8595aa5015003403951608a071241c0906010344088140004600030301d1030740142c10542000550100d4220240480800101c0c40c10540c5030400c2c112000e0010340c03031090310060760082820a00c240300190032200078100c90400c45010104540c00039128140160308003505410050f11868014070035454955100c000036010f1000303510440160700085400c141004010301c058a0070760030300e0007801c10b1507800c0d41c008001c8084120071540c110001300d122901d03c0701e01c64907445600103481c88261030a4540c1440005504200c0d8100c82d0700564000103040080c2d903000b52540222841c440340840c0e00a48100310a0b074004452401c0ca00d40e0900ca0030025039a28000d0302d070030f6880e940b216541e4808030b41000b07061310096005100310144850f02c0e007001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 613275746 1250 613274496 613274503
    0x6030b0303092205131205070803011509050405190b030a030918020d06180c020114060609040e10050412050a0203091e1305010906062609150a02130b0c 67
    0x100c0444007011851043d8180f00c3c0002088803081465901d848100900000482d8440341d481d805140c14201424402e88200c80034491040d004120b2481440100002010306c15248110542c1d81410b111580d00e071b101240c2100c9003110030300000300a00c604080c1c01c01c0780e8803502503016010b8010301200703c034070344020307014484601c1088240e9414001040b0211010342c15070b680c14100031000c3c4409540e0740c28208460540820b2101110314090984c00782ca0300500c1040c0b5404501c1c0d0034489250317141810821960050007400e40c006803a11046007455005020982481540c1c41300005c850030142001d00481080480b25018020304100c0403280e15000019074003480021a116a804040c181240301003070220b500e01703034128400700c041070030b204080c0d013000e810b03503a5401c4100941a1341c0c08040f2245440d000000f20141920500c5084c9010240000317940507907074000b2158058404500441c003040c1c11121103941c240d002c100031828015a0700824020008520490f0400d43c211900390789 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 613276996 1250 613275746 613275757
    0x60306080a1e14070603020706050702010504030e22110414010c0804180f02030a0c0e030109080318011416080105010e1c050c030d0203040317040f0303030f0603020604080c090106030b0303 83
    0x41c6508030140300710420140010305802071401000b03544e0407aa40b100094042d41003100116921801c7c00000303640e4900c1445094812505644c0b8034020010600074002e1141c5c0d03040c074520f402e22802000d90702005030384c012441030306d6140b10590740d600d14000e0751a0307400503a02c0e40c2e1070400204c001c0400c040748001c81520706030340003203c401003002c6c1c03505801e8000f001020129a0101c0c0040204020130f140c640c0038440a1503e80c8039203400a0051040601701c1d000d6040082c201c030418004502455000c06107440d1641070000001440f821224511810781030440304405108111080e5400307690740822000d004090a0038050b025150380c00006032a210301c081030110600c44d0044020500500704521031000601405890120300c5801e0025202c3c0d1007404141c0300b2000d20801841200c00110445040341c29a00c4500031072030941c0d0b412405429122590b1104981302d16020000d40d69100040c03008140b0f900007089102102c00034880b003044141d0000e0f00b414501749040f0002d440c0402260b2 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 613278246 1250 613276996 613277033
    0xa140321070302090d05100509010e150603010e16030c0b041505070c05280e06060304081810030207050d020609031903060e09010221100303080601020a051501060306080a 75
    0x207541d500078220020b004400c08158000034820f0700605000300485c00c002c040940c0101400b031130313560141c1c0c0707403d980c05800403035060b520140781c0800300078034000c082c0d03040302008002055044003812403a140080c1c00c1c41810000b00306400070020011481840002005070f08287c5d81070610f803103a134500000300580036200788140010071508101d18070400c84080c0000500c0e4504d402c0d001c9a500c41035401000e040c03140050440c0c03000c600031102020b40362060100920b01407640d550b968603030180b50012100400049401e81d480030940c5e907420300785944040141e400585480303050505514041c034044554003550404802d008910748080103d40680711b15184000070004070440450082045600c1020010044002d018002d07006400410342d1808081c4c0910075100c501e0490048100c065460b014528502001007000902484180764001d20500542d00300c0075494403054204412401444915181000144a90f54041c0310b140f01410781c0d58024269a4810782d6a0b2a0700c989005032174 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 613279496 1250 613278246 613278307
    0x203102d15030912020c0301060906030f08092b1a0603060a020315151e0f22120b060307080c1e0301061d0103020a06030203040f03030902031006080a1403 68
    0x5100796009070800c98059034807180500a01e0b0100350021b4582045541c40340c441d501b049000107013107686008072800d07a904034910301610622540c8041042c1e000c40c0030690054244201d04400407400100302403000e4410140800110003407400100c5d809001c0c001040545241003031042507100010515484002400010395986401031003401c0d0f0118007070740c0e0341c0c00201c1641c040001034804000c0c1c0707d201b01c0203034040416000c80b200d4400600230b030b0b022a0388019050040407111203420340e08158168171081d01480b001c0e00e8107030808035010000c2003070b103603542018244030080c107040000c0030003001e031a40903100b451110070000702d0100b804501c0f1400314103895001e400340d036001e40c0b00070010b10300840c02d40d015914404400c500507000344020381c481c030003410002079540e0003402124459a4419008092004c090b5800d81c000c04248000742c2e090311801e101c4680c15042c82c0f0424019042601c02890380102918140100a848070415030f80c0c0e81082c081c144041c1c1200152908000d10b04801 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 613280746 1250 613279496 613279529
    0x80703180303120e100e0304051201020a0f121107030e090703050c09120f0a05060103140105010308040b032802070618050303010620030301270c121802040203102d 72
    0x203003444c00103840174a8003a14076150f442044186c0000041003216070a03560001100c8220300707003508030301400c1c50110100b110035041b0f81d41da907c02c2e540c4944c1d030300e0360100014400400745101303103140d0007094044010481080c00d000251038150700c0558414014601400140b44c0005010711602620162600540213581a168402c0050041a40c0e01c080e6400701d030f6060146040c50740e0398030030a10059807100364806403850341c1d51040c01002d044e00e8002802d185410700d01154041151b00c02080c08250805000c00d041003425000c0f65886201490000942c840c0410f081c400100d500350704000984200781c4560b81d000a601006880c1100c0560070202e95480d0700c04e0f103000d5440308817038036070915000010007c1032084131261027041c0b2010454030001024141d8140808940d520090303d404641001403c0540903a2074000142880c02c0002d070120448441e408182a0381081e030303001d4442c501d69203040c481c002ca000080202507050300f0f9210603403400740102e400d0705a140d002700820f40211000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 613281996 1250 613280746 613280771
    0x90306020f090130090c15030c1211120903092107090207151515351504110417060c12060907031103040c05010813050709050405070503070308070318030312 69
    0x141c0d20010080c14100080741009400014020041c405164002c03034441c0c0ac1400c3c001b0f07180d1080d2000f11000481700f900c1c0c050100601c4603005c000510030621031108001601035a25150200303c840500d00c9214454155003d964505058460300f02540c018810b0040c00086541221034400c8080c1e44040090b80102c0c0c21091507447c1d00c0c5412a50140c408088540c2810394070209294517102c03008031824480c1880f400f01d50000b80603202c0407120f04820701c040780e0802120130241006807801000040c2140450102144a41042e030000c900490040560001580184121607011442440440c6052046100d4440340f100143c02c16000b05019030010381d030f460084c0d00c038001420b506815180c8078a800d15049464a00500420b070014403c035000c5000f40c00ba00c3ca2141034149c0c0000a4500141031807106001080f0003403007a43c20703228082c00051551014403502002d90b000d4988107a0382c1c0030609014211450115881c001c111213000c007000829070024000706002003098020400c8484180c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 613283246 1250 613281996 613282013
    0x30251401090518091005270f0a0305190507051902190e0411060307120504260c070b04051c321b010c080a090306020f09013009 56
    0x400950f0080d00005441c8980b1003050001441402c0e10780c02c692600549134030502c15924103440910752200d480e0f8a030b00841c1d40d80a044101101c041c012200d00840f6000e5207840c0a25009058010a0001035018000c000452205911403440c1c241035191800e640c1c1e4065480d01c1c0c04040e01c1e50b1041c580281d008640d0baa0344010408501d20380072840f03d80d00c59424400d41e8005460840c1c02c00b00182c032a0304d0905250303054a114042c0c1ea141c207843c003018596290060f00340203008441001c1c080349004000d110041d1030070400a00d448207942c03a061050213480c6850f80f650004c6c10015402d1200300042d60701c100c41200340340414810341c1805000c03442d02c003859030614801c1d050b50f070300000c007401a412283c00e503e00c8502240801c071030141c03040c01c6c081d04030b41c1074902038640050306040e062400b06102710000d01180c045440c00c0381840c0d40e00e40750002240c01c641c03504007241200145a1031250703030100d0001c00c0c08181c024807901e0b49040e01c55044214090203c1c000109449401540c24401c030300 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 613284496 1250 613283246 613283249
    0x3060a06050a05282c01050f0d0212011b170c1c0e1f0606032702130f05070e03010c0e010e041409070504180507060e3025140109 57
    0x2240245800d5282e490821154080002a2081c01185d000c0d80100a2090040f01d040b45c0000c0d03e04075000c11034109001d0108a0420180e13089901ca42440320142800d1191007060134029071040a201c07141d5070010146000054104101102c0301c7c2844080e41d02c540456980b0280741c1e600100d0001c4108030080a0a54010302e00d1450082842c8a200100007080c1c0b60a035241d0100104031141d120382040c0c00302c0d007182d1903410001d141c00f000c01410320030110318a19100e0005203007500003010601034800f0f54010b90030001d0541e44607021b10203520b400034203081252004400034041c03c0310701d8100030000003403251801c0c10019600c0c12201251590f9000d888a155a81c0c0746143c070345080141e0507aa81050301c5041d0080745808440394800402c4003909034404d9100014050291504104039840c1e001d100380c0b01c2c0e010100c0e402c401100c0f207020b121452555002c9100c200b20ba5103084080e03007000704030300c81905c60a1100c04140000f14900c00d071101942d500c1a00b09421148507001210034000e075 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 613285746 1250 613284496 613284559
    0x51c020a1103210a1e0207060b0603091b040b010c060c11010228170109050406060e16021b030d08090a0b07020604060b030c0108060f15041403060a06050a05 69
    0x6030fa42d801d5002d00580c2c2002c00f0074401000c1c210f4840411101c111070342e8000100c0c0500741079520030000c50b0070340c000305080c600a000c046a02d41c40c0038001480c2c0d81c001d40e440001640069544c58000709400428450000111030800103070803404006015008501d0004200b290b50307030034000c00503008103010001d1940c96402151100d0040100c4520f424007403035050281d046852800264520648000404214204001c4016482c0007506e401030030000d8002c540e45620380303401080034146890294400d85440c20032215800e00c011019041000320f4100213245407008400384c10540307000520484440b810300d8001c1c90b55582200c442d06181d01c030743d8010031500d502002e0007400340d80010164010303030040004000500302c4030105660794511303002d181d000c50308580000e411031038205040403010740c024046082d9049240170400c2998800d03040091142400c552041c100d04003041038039072007001071a04101490500000034074008813445242c0c41041c10351800c4841040c40113046582404 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 613286996 1250 613285746 613285753
    0x7181a041d03031006201c0203070609030815150412060906090b01061205090721060903022d0705210d3f11040e100f0501051c020a11 59
    0x400c0c840131420030816104210021316283d40581a40700c2500102c41c1d80b0044034000c0101c24940382200e56510301c12003c00d01580418030003100400e0b01805a0114240310f696101c4140c9001024980300d2440312884a028150301900346c50b07d80b900e03400b280c09580d06100b82c903481e0074091070080040e00108100511507420700c0155420821042007144c10381c0e455803030b0304001286a59112084a02c2107070380c504a0b50041404002450f0f4200c5c04085440e2002c078484154421750301c034102507901c0030b82c2c1240140d104155004540c420749000904407248201ca020104da038a4050a54401c041e0140b02e2081c0140d1045450161103c0d6081c40c02c0031500082e26000070749100c0280911030010312602c0264840c8101c0780003848100010180010f266002c01201c4941d41121001058007900e109450300b420000400c80304c59441c00f141c4105038800c9600402c50408240c01c01000e030030341c0242d040c00018404000c1141c102c46c0c0d00710041040702c10060b191005100e04403030070113440150601600 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 613288246 1250 613286996 613287001
    0x102007060209040e0f19170703020606030d1701030b06181602011a09070c0309180b0310020304050304031b090c0203031f1404240807181a041d0303 65
    0x4454024125641e01103504005008100c030744c0a80768444000103056540041801d01074080000340003240d428010301102e20712610001503072019510510044e0003581c070020820003140350401c2800b4240300b103440c01c045484a10209440c4629044c00014046000760b0002283c42d2910100d240e00c0110448800c001c030700304030315450301120070ba00000c8015401c1c00300840c6581c00c0403400e1400200040c1c107a21103503461074000c90f0803030040d51085003000400080001c1c080e4000100080c0000c00b0394000840304075140c2003614041c055007403140c13458014020032001c030f0004000e5074100c0f900048040c421301900405154040c0b0180c100e4401a481d1203001410183c5c004091849400795680c2c0c0040c4440b0482000d000030715921a20700e21043c00c000c00300060810340c11484901c00301581c00c3c9582841800b1807803a04440e41c0001c011980542c404000b015076171015480d5040301c07400b08021180b980c0d444081d070350007205051801075445152244002c0100c0d481c9244c03070007600098035102d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 613289496 1250 613288246 613288253
    0xc0c060a05130905150402071a010923010f0b1806030c1c090506180114071107060e0d06090f0609230102040b0304140f1c110d02102007 60
    0x341c00000c44030000c07003800300002c14240d0710340c807131031340210280180300d01c0000d020002c100196100d01c2d421600b510100c4c4c69080c840c5201c581290280034510300200ea48100713180c0c03146080080094046500040c00010400d0910380040350701911000d01d406a921080001030381d032565221001c45404c48000010040c03600010f40180030f00c01c0903a41c0810707a9405000100741511010000541a90420700100c1c02424451030032401e2480e910001040c0b69098040ca45001182214244040b44d0040056503c8500030700190000e0021814031400c410300103c0811101200710b0401820b5641d6001910140a000c2d00000c06403544100705215064851400d040040e00c00000b40d1580741070711203060b04076401070003960700f540c4000c048181503603141d8070703150908024940118180e01a10302c034104441c50500c0519a03041d005481c24442101a0b2001480ea03842440c1686441e00100e41c90840e450317010503d088000c20082c00401c11a040d40d05000e9112201d01c01d0707562404000440340d040 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 613290746 1250 613289496 613289507
    0x316020114070f08041a0a0f0807030f15030b0f01030c030b040c0e190c090806040f081e0a020615010c1416090b030709050606030103080a0e040e06240105040b0c0c060a 74
    0xa40700c960301c1800303041506c3c84056149004070401c680c04200c10604c0210200d2003400c0b426030148051601042a22041c4807420881d440100c200c01002032104051060000c842411030300030840e002c2c140d07032941c07460311408220f030002d00000b00007018000104082c8101c1c0300043c40078010a40f040700c110300b8800b146030445040d003039a026140d403c0403003400426010b4450401140c46403c007509441d521b030303a200c000c41c000b4040200c030303c5502071140e01ca48030f5a6816107010b0240103185980d031400c1841000c0c0ca0110010700400315241818060185a6800307590740390a181d114550004038030a03c484581008002154150140b500c3d200c00201c0407500e820007400601c050f0107032207482c0e40701d01102d0265042110030b0344d0402c008200400010b21100c005080c034103074030302e0301c000911300b61800681030712200b50949905622050a00c403024004401c1881e008003520b81466142d80801d0000e00140194030441e00361010100d0900150442070000d51000300000306090b58500851501a00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 613291996 1250 613290746 613290749
    0x317090a06180e0903040e0405070306050c0307031802060a0f020c121608030a020613050109020406030c05030606040605010f030c09030c030308160503040302030f091809100b01020316020114070f0804 88
    0x2c46449803400103522002074030300e600501001c1c0145240ca030410038401100100584112040d00c5800710010118800d441034030f010b60b22203000380d42d0b60b0070120b9000781502c02151052694010b043e081d400107a5801c070413203801d5251410003a525450312007003079050a24134000c0c02c0c1c0040040e08081d403c2400816071a0780008040703042c444642e114031b51346940e80602d41d003407030240e400500070503c52201c00c44020080e5202d40b0001c601240c20ba8042000d8501d154400c07250700b080300341c0031710051500344100d40d400402540c080003810300c4c14000a007003c1066044c2403d159503400c0700d99000344519071501c0a140c000445c00351a665030700d40180300090444200d800c0402c0e84081a030b456114404503401075800d6170086003490064500800e095103c000030070750203900350380708040c501da0142d50140300e64006005452038201c407005d208192050049181d0454000b04910300c0d50021150400000ea90280303403400301d5000081107040c052051040141001d60291607050030010700340700400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 613293246 1250 613291996 613292027
    0x2090907060219020a0e13170306100f12020f07061b081e040206130509091510061d0a0509040501060609060804080711061b250f0317090a06 62
    0x603000351401c4000f80c403101510070001c0d031282c80c0e040c0402c0602101e060071a0045803c141e4211104a1550340c0c05080d00302100f8601c0540d0044208469882c007400742940f0300d150750070031f420000d40b0098001c0c120841d00c500c4507d5aa408100d0301240d41e04042a0b54038154800da0030408000c5c05685500c10307803240c00360840003d10b40301c00100b244d807840c80f00a01c0303040c2a0080d40da00340c80340d908000302a0083d81034050180390743c20002400e0764030400c0d003c2c041c00348c07040545208001110401030707404000707220113802940058100042644400d61002050040003ca40d00c8507012000400c1c07150982e10040d8000c94840a01c01880b006500c03440032108240c0359091115038412007076450010840e0080c0014009000c3c9001042114031007a95800e0010f158902d003400b41c0191004040d28442e40704142d0b40083c1101142c0d07000c0740050001c3c2010507825540462500700c0c120380d0107400e40002800b41301c0c00f0440540604075041507076a032032002444100300f19140d00c00103116200052001c1d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 613294496 1250 613293246 613293253
    0x30301050f0604031716171e04050109050f040f06030309240e01080a06181401050418032a0803250504052202070302031b0c030c0906010507020909070602 68
    0x79805141450490b8200c0e580b0446241c02e0f030f24440c4103204135410008082c003402c2c85890560b4001061000d01c0242c094a004180d42c0b100134103034401c200d16914440d401040c08081200b44982da822400c0322080310400c58000b0042074401c03010801030001c40040b80c0d000b5080102c04020141c000c44590251100c84c0208000d03204400f540c800c88050f07880c280b03c04503c803100518a10f5124204065003e2014900840d145503248800145104010a10f07030074203590300c410140d040024902240100401c0700c06002402c08006c0104440020307a40007800e1012007011010560903a8420340c80080039400d600d0f9642e40982082181584201e0700d135903114241855030b540c103141508070640041e030181c6d50581040d04140a1240011101103a102421800e403448441c1441d180018100303a807003940550341742c0420b0810313104081c4036444005c805400c02d01c041ea41c00d45002031404001081220100e0707051311803d0040e0b900d8454810065003101e000003c10440c0200015120b08031041a4200c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 613295746 1250 613294496 613294519
    0xf100207051612150b0d05010509010f0e030a050a1824020105070c2003061e070903051218030d03150f030206040902030c16030804020102161d190c0203030105 70
    0x101d80100c0b503180114040300e04205050300104d00c00c080c0c0403205100744000020074001001c00180c108041b40320032600d0b030307445e41c00b0008400c0080c0504840c1c4140850107005400308149030716242d0042030380d03440c100000070803c007007114404c80f80e0008070748010070080a032903119011080d04c00001e00c0b03400260000c64070300f040200e2052054601c641850f648213624a24140c1d10718100b15904140803a03200c0f80e10501ea81240d6082c062640900f140b07099005d03840007140c840c1282c4030030013004d210510649200410201c0c00200302c1e0000a0029030289a079080000a0441200c0204003c988c0520035501d00a045a0701903000721801070160032071401690703940102c41ca5a05e01c0340402504a40c05100030441c0b00e81d1b5401440c1c004550b42811800c1c451288416012004c40c408180c00160561040c0000d55806000c1039aa4284c0400c214a496040c680585c4200074640513070540714080e0800101074110440016800b10b81c0e1030000d00c407903241264006e41c2c0750030a00610344100c808212 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 613296996 1250 613295746 613295773
    0x503090907050f16060204080706030509010c0905010512100b030702060f160c06020304151b08070804032c0301241e0513110a03020a0e03010902031c020f10020705 72
    0x684590206840f00c041c9044203000004040d10407089003160201d409000c00b03d00c0c0541072000c2d00107000550340020309480c080d651142502c400e0344a000a1107290740c000d22032660f02104a0740c2e61900b803036480065440c0d221300105251020360003a40301e56404402c3c004017660200c0d81d01c2c001c0c8940b60b481e81d4162244260301c40b002c01001c0b10746021600ca0351050001a105402840e8054040e0341d0025a1002801414054815240c1c040c096142c1c4200c0c010740b42604015102e03040003403032070100060314040c0e90181101d1148810036400c2c000c02901c7c855681140e030207484407a48094001e00440800e0f41d10800b065031007403525a84034141c02c0000ca420760b00121741603900c203018a02031070f4003440e003c18420319443c0703a04041902a1034800f48500c518a90004080a40a0b640c005036200904070700203005a49859034030b07210b641042c0121015a900141c940041c03800803610407003041000c40e099141c40e00e4080300517464081c103031034420004180c0d0701600901e4003c0091b126460034207070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 613298246 1250 613296996 613297007
    0x81b07180516051608090a09060512150a180f0804150c020607110a0305030a0215010e150f03030c0a0c030c050d12180915170318091003020d0503090907 67
    0x320303500051800c1c0000032903a138100903080b103200e00511025140c440310f0030102d000d100840e001000c2072515440c0803c15404c000c1d2442c064480100e0180500d1050b12541c10402c0101622000b10161102c5880c2c84070405c41c3d804400965220880c00682942407030542082d40062203082640b044500321110118014140c082405900030895850440036a84070007000501441490b00300602d0100880010010802061002003d400130006820302070002c00d0000c0c0160000c034a4003484200380200d00350301c276071003a5180783c1c1182d11001c00b982c0f0201081c65030182e0240028148504000b10040c850b104010805603405103800c80c074925141d400380412140031100080845110030450b0003441d2180001006950a1700c9040060a55500107001659804070110700038041d007160402589a20400c0c076141084100702440c1804070617038540781c0210a5144050040a00c02d0006201a44600011010f90346c0141004114545420b145a482c1c00c10b0301440d000b60f0580011480b00360080 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 613299496 1250 613298246 613298281
    0x105010309080304021903080307111006050d0b070522030b0a020703090e07090e070f0f0f02030d1a0a08030c010b0f1c02130e0c010905090c07081b071805 68
    0x10465034038645031380d800d101c82c41202440036a8581c04010300480090030040040d80183e0090780c0e581000f030034611006060005000060b00c41d9864403504002c1c0f501c800c81218a2076802602e0b550301c0744e0b031704032007074906104000e05880084503a0180320f6881007410541e2059a000d4050882c0c6941d903191030600b284119640038000c40c00111041001d101c03503d9546610181074903224820035500c1d0b43c150300d181803e0b030b07002c808120b03013078900c1c07807038651260000c5800d1403d8070b04400d242c04c1440300039459220b0712600010190300e61045030550340e1940c414141014003e420304050f1307941e0b0020503440790440e03c08040594201020b054442c40c2c600184613a203a001031404080010b59030038941141d204a5040360005442e0461810182d001c0c4540940402081c000e0b10403240007038001403c0d01e100e81c01c9a803041c501364003070003030f80d1141c80203803080c0503800b0311000d41e038602d0f03821200011121240244d069200342c0401054040207144500004c40e60010280300d141c4801c1a08003281100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 613300746 1250 613299496 613299503
    0x105062a160b1620030a03030b0f0d020105030a0f0204050d0c1d0114120a0b2404050c121308030c211303140d0525080106050703032703170105010309 66
    0x4988046505040c0300010301d8013030909030302000d0b401000b00e400c00b80343c2c04050b000b003075030f641a0030f02d64284801549041d0700c2c00c48422110145540c0085e01c1800043c0540c00d0040d5039213004020780a01e80c1c1180c0103000d00600c444104002880e083c14000c001d402581200d52560020340d0307904070149030782d80c141c40300b104410203420f070b8480c1803211000c00541d18150b140b14940c5848081514600341c50f014410302c4082c00022056079004450784100320010030301440c80d00e400c01c15081a014117582d02c030001c40c2d41d100c103681c80360b040c5144025039480b80030301407040c0041444500c07c0d50000824034400443e48025101c24084101c2c00710f040121111000d504010030340b83c0000f4411401d050f1890401c00c2a541491069118403040b200308489240c00c2d5011550303851a10100010320300c1100c05586002c5000e90305203031000f04580a1214000c1c10b05403242c030414094004400c0d190080f0621450386c01035240c803802d0050804481011008030b0a40c1000082130a5100303005a0310525007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 613301996 1250 613300746 613300777
    0x20c011410030b070903020613080d0c030503010e040f050d0e03010b100537020a0501050603164101090602010e0a0f0507030c030b0a230105062a160b 66
    0x61034031043d0442800406250411251140c0413005030743d00170151040c0000c000c0c2002e50241003d106510b0000818402c0c0103100008007003100081e40902201e0540c3c10414104c9c40d6922135203880307503900e140400c004080c1d00460001510a55001c003141d644403404800074000d0074491130034004085801d80100d070011f01c0401c2007950a50003806a06640a52044c0c282c210030910442000704224012400e03006030000d081c02030920034240101d0350080c1c002c90140c6202e5080c1c04980c60800100c1c0703d0848514004102c01e000c0d01c200f40c0024076100c008810050400f54070000c60a440c520002e07031107001c20b82c06071001c5101481445442c4d22980184000d10303505800d80c840080b8a07890349170444592203000800b02c00a03569515400081d031050001c4030190524914441c1610040780410400c5000c61b02c82401050304009640d04546003554000e031b44842c8401c0400f880110040254040004203481c2c05081800007107440100000c410407081c10f035101c855800980c8240307100e601030400c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 613303246 1250 613301996 613301999
    0x190306050c0d1413030e030709020c010b0306060a082d010f0606180b0301090b1c03020c0a15050414030a3009050303070206450102060603120d09021201020c011410 72
    0x203010b0821b2901c8403c009049440b001e5a445005062742c2c00300298100701e0b51222130300c12160074100314081d0070100c1100d81d640100c1c103000c4400e965504010003030b6a540c040003550f2a1b06418410840404201d170f5000b80b041406104001000e08000d11072940081c143c2c03e08103a61084200510f0190390024014030718507484c1c02007480c0a40f4010b904c3c3d650007403e21042800d100302e051803850400748250040c0c000c2c4c406075000c000081c08194810250850b02e1000522440e031702104a03030a83d101d803540c80708450f840c48046441c02c80800340051003150300702003094061080c000105000380e0891103a480c41003840030119404e564505c030b443c1c2c0642c400e0203071500614040000d8120005450182d12464008810503a030401030301100140c5a101c0f0b0703000b051030802241200c42003500a00040c02c40342803c1002c00e540d800c190f00113524136000418148005074281e000302d040340d90020b10214900c1e0b28143d480303000354055200b032146903203051040c111a40500014038400c013003e0387d40e5103080303 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 613304496 1250 613303246 613303253
    0x117060103050903161101030606090e071d0904030806100c0506010b030a090519030318020306070c0501060b0a0e0a150f0324150329190306050c0d1413 67
    0x505014001c40310902007480182175645290000321020390054000e2403c0c004c003000054100c4d03565401c110b0070884454004d2240c1481c3c00c004039009299450701400c51280340392051105221246400d40c40800d107410300040c03540c81000d0b00c2c05200110b40d007541496020605840b510101c18008126401510042204540d50000f171607000b081103c001c1403849003a81c1d030b00d042c202c51080c00003d074060070750020281741d40344c4282c10310041d54502c185421080c03600040da42d850300410034400c001c494030740002000401e40010000b050821b000544880480c100a1f10056180300c02078010000030400080512202c0360000c6084820f40381c12990090310003088019000b40c045009000340a0b04400f040d211049041c20010524544040c100d0302d0705d9030008003600c0c0f0204031070072150402020440d40070441c03e1001002d410403100c110b10200e411031494a50b06413507201401070b900d40410040c03646100c20081c0403d4041e039004102542ca8404540704600085d00c130300644004c1c0f00e0780e45000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 613305746 1250 613304496 613304501
    0x1030c05090a0e190219141c09060e030a090509060301090c050d0c0f030c0305060f070905040b030a06020f0c0f0f0309040c03090506012301260601090b04090203060f0117060103 78
    0x191021560741384250144621500340d0b03009915488036050b603001000c01d00d41d0302244a01092403e040c01519100307010030901d604420300040e0700348d0745030344940050400c1120b510200d00341d801001500e80f01d0001e50006440d03940148203441c000d110303101c0003072130f6460306215600c0341c0d80c0d00c01c00300ca8003607003440f091013180d642100d030440c0d60454a400225525100141401c0110322401140c281d0606500c1c01c1d6080013030103840380c000c610181e02441000c1360840c203900240c5109440000303c900340d00300000d2074007201d89005401350340700203440c00c1e0008000001f0312010309840110341c126044c5407034682d5078211400007042290418804407002d890070750440b000e5081c0074070b004201c112142e11080e0501d54280d00c180d0070b030b02c10740900c0c0c803210303d00c030310206548202400c1001107038444a607018100503460715010690000c42c400620207a00030241c030030203008802c071556103c030f407240c45000c002d51060390f14a2241030440038034080c81d03110318012054048000c01010b41030701d03404015000b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 613306996 1250 613305746 613305751
    0x1090507030620030112030e090402030d0807050f0c030c07080f0604110d240c030e0616170103050723010509092505030a1104030c0b0d02040914040201030c05090a0e 73
    0x200301c2e9650f0f039811070748007800e000386001c1c1c10440c6040510b000b8619001d00b0105a1481460164030352004200c0503940115003054241600e0904a0082d0b44c6c9100460340d81c81241c0f9071429900020600803220207000002d42076404011003124110381c1c6860a550380da00c03005402850540c4010001000154240303002270b03c1083c0504035484001c01640e94400022140300d00c4490035035102c402c61000300c05800741540425003804c0c1042000440001c082d05c0300001003086803241c4041286903d8948140040c600c8011603060510f195610b80c80c0054072004288515800c860510100c00c0c090040110542c07000d01b4141c5505140100c0c400910185807001000d8040c200204281d042c0c850801c0c80c51081d004081d540c0b42903592420036070000c1113900c8a14618a00d020904c41070000450280244040e680003c4e0350700d40340d04a03482000081e20903508000300d40c50920b51846084000100102d004034801d0300c06001d900041001100c0e54054068000d071301c00554030040100c0a150400d030394 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 613308246 1250 613306996 613307021
    0x602121b01090618200a0501111c020d0801060203030135030406110f06041106030a0b100507120c03020d12020d0204080c0a0b0307021e100e010b040e010905070306 72
    0x10300d2507801d485400444034005040c41c1c1c0840140115020004a00d03402d5045a50036100490794942917400301e10b404105015040c14484141040c801001c01044808401141030a01510088801c00b0007500ca07200e050304000894480300000c69800d0010007a84e0580382c10618103d0303101c0c06420034440303d403211905611b2018404590420703000040c030042010386455110b1058180d03140c101203150001c0d090b04030417650032101c18000003030407140307040d000c140c000c54440d62292104031560000b0203d001c3c0256103c101c3e4450301c0012504030b000360500501500300c04400c070b1600d407c140d9002485030700080040c1c0000c0702003c441c07805010000d0002122045c0141001814240312080364002c0e00004c8096101d0300380c9101c545000d03180b14015225001d04182141801a000795540000b000d11802407604915240a42041040309908880c0c0070101445288140c0d210503008000b105140c40c0600d080020442ca01035050151011040c0e200c40140609403031038a0304001440d41c1001134 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 613309352 1106 613308246 613308251
    0x3051902011b1701050f1302030103060f0e0c09160504090e0703060b0102070605030a0902011713021906170901020f04030b060306100e04060b2b0209010602121b01 72
    0x2130458100351405000710401000080e0780b0608007221312040d6101000001c01d0000315040021541038140c0100215008000c00580341d08041400a80103007004001c100d40d803500e41540d40c1e481055190040c00c0075103070b280c1038040e203090204d010200e510104060080c03143e948103603098860300340010004207103023510141084c000144004072855031844104103590080c07401c804840004445100c0525020a4003203c091010074241d0060038040fa90031460013461020034107954884d180d01d1407004d042c640460301c80c1d40c001c1481c20030755003d00003041e0b600300d1140a800075500c50b054a030b20500c1e2010a25150600040c002031218a0300c01042000f2181e001b0f503035030030542044021070041b101d000480c4010301d180110704c2c1c26400609510000310801c82c004c0100c14030880d1080c00707990383c6140490741e400015230001c200c000100321f1056040414443c1f00c141d5020500007 = true := by decide +kernel

theorem cover : BRFrame.Cov 613129496 613309352 := by
  have h0 := BRFrame.cov_init 613129496
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613129496 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 613129496 ≤ n) (h2 : n < 613309352) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
