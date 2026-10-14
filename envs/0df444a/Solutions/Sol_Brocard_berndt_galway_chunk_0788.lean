-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0788
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:47:46.14163+00:00
-- url     : https://prove2.me/submissions/117ddf55-e7db-450e-8883-8101b7768b76

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 141546762 ≤ n < 141726618 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 141548012 1250 141546762 141546787
    0x10e0a14180106180503012d0f09080403111503010b090f0409050604050d050c03030402011b0f060209040b040605060919080a03051201080a030905280815011a0405010c020604050402 80
    0x9440414004c000e40c4030b4006414507050244444034054071000101c03030380c0707401748962603e40d03603100300d903125a11804400350040b041c0c817480040394080d6084035151419850000c0014003102c01091242d4052070441d124210b88404603070456102d41d800741d5440b41c00c403021402c03003010700044e250b110385408006000d0000200740d40c2d202e18456804d4412203074000800341d80c140540c409460180e40207000282c0154002d410000152920242e4140180c03841d646040850002d20340031500281c022501400b00c2c1064020490703000d804031003d21542e401c0c000400c00b1402100700c554030401901082d100400a881006e0000d0001981036031211b9031241800340070350f0700c004030b03017610402c00200018010348003050781c030100740d415a189544203251108209483c90003e8498100d07807101c031000555600d20892180c010480708015104900c41c1c600c0e00d924261059004586020910800590107039040c000c41d8141c91007402c0207070140a05001182c494000d94106a4002c2e03c002411904400b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 141549262 1250 141548012 141548027
    0xb220b0a0801020c060f0702030301061e110f0a0201021b030307060513080304060c021605010503040303090516030309090f150308030903090d0b06030601080f070603050603010b040606110c010e0a14180106 90
    0x664030301c1c0c0a19179120f4080407039a030300c0244208400a4110340c6400c250240c008115007801d0b881ced203024020b90a441f8045400c1012181682d8030a0b480803483e80115601440a400700d0080d4055461080b450000426201d100f41c03040206840da40300000303050442001020752000b0740141046889240ca4600303200142407211040015100e1848559020010362203c801a0360741a9207443c19901c41da94160003170003d1301421600c5000e4000a41541c142c2c2c04208070040d4029602e006143c1e10301410b203012504000c0b0050000e41c104081d0005410400580d80c089992218210340c1e0707aa04c0d030b070b003160641c0240644290303c02d5402035800107002c10056401c0c02200e04600792822079a0f076001081d40c030403040303d058650342c0014208210050080d80a5948030780080e0002c980701c3c5806001038100d80103a0041c00100714210745609401004201080c0c40c1d400a0901a0307904070504001000f03919548988014849811302c0d1144584130300700c58182d80602c018844a0b00d5848020103000903 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 141550512 1250 141549262 141549271
    0x313030323030402010e09040303091b090e06010b03040212070503060f04020f09060310020a1803060c0f090b121509010305061503010504080a0f050f03010f05040b220b0a0801020c06 80
    0x840759840e188990980030411a40202e9058451030660340c4000284144142c00400580071305a43c1d115200108500407503018050a1040141c51602d080a0f4000c00715010700c081010554080001801568552021640c00c1038045a200d1104607a0014051074401150040394140c00361100340503401d040c010100740190310031540751f003d10803410203000300071004441c0e140c0d1652200c1e098468034412580240040380041c6041020b04100c07070081c040443c2c240c0d0084465a995203201a9140e44c001070090249500d407610505581c0340025040040c081e03140000081054213000c00c040b101d40e28201d111016024010a420750b07074a04140344c491008607500700b1034070b078514403160707840c9010b214082c0710316031042c030040c1000f94410048848210212194003400340c100038011018003002e02644c000c0171140341a1014030700304000c0c001607640c41001c10b4003841a99203c18188200046801c032000036188000030301c40c0350326000440001107584400c0c115480060205044940443c0d0148503 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 141551762 1250 141550512 141550547
    0x150c152405010c03090302041806020f091c030509100306171b040204030b2205061305160303050d0509010b0a080714010512010603021e0c01150f1503090503130303 72
    0x115611401076507a1003520b00000d000842c40c5c0d00900051901303074014061440351000d6140a001c4640d070b0365040b0391010f80807011110340410f20444c1447c181d601006410302402c0e040c50b03804c1c100d540c003420728015a0308580c85501501030580546100b58800030080c1801210780652803d01e01ca03154540b00407260100d41019100c4501555003414000c94044a9015200c0120369440401010303180d00702d98810080d50b5804210040814010000c20303016113080b0010360307001442c074030300369142c50442d40480030811090b40302080804e4004055898400e29540041a10380d20000c000c1d0041417001005540265100e4003c0340701c0800007200c20503a101c038034910454a0303010300151020300550520604c00c0e4040c00050040c244250043c20356500c140c241e00c0d50100c030385a01e0030b8107a00f1266074061303503039554506050210b148003103400003041c0320395034504510b01707103402c2a50b20703181d03d00302100307241d115590a020004104111002034203507a003079610958880c40d005121a0303c108ac48882c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 141553012 1250 141551762 141551831
    0xa0207060501030b041b18090f05060f010e0f150103051e0c0a0e040504050c0d050a0c0b0a020c040b130b01020f07060801080d020309030318010516060f0e0106150c15 73
    0x400401b0104180165000358080c4c001c082c0c504030050019080e07641045030761000022001001403c1000058000c17185480c0140c802d604082c08074450b120003c1210f0703441c018a10510000507241001f10035030b01c4085c600402c0651b90000140d805001600b0008103610b41e180030009000d001c5009484001c82c60341e00d0b00c007941034420411040d0380d000d940280441e00154100e040380e1402c0d03507010440c90710403804c0c1c4049100685401c00c100c181c0c1c2e404034458040c0050526a000d41c1400303100c280c500c00315070420101036400041b9400c100705440e100b004a07a201807810243e03000b040390052120070301080301d1003242c07980700061140c4005c0c032960b4980d204404184070501e0000c0159078079400040c00030360420400b035507172110081381c207100c1c0e505000c802c0020304150205c1c07401440700c65018007404151803906203200001c641003000030308103592621100380040342c06110f44410030101403420a200203018100f180e24401c041c45a20507880c6000a1081844c60a050bc1c49c004c0345110010746 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 141554262 1250 141553012 141553043
    0x10e0405040c0603021309060605090901061b020906040204090e070504050c04080a23030d05090607050c030702040507170103110114030702030318070503030c0328080a050a0207060501030b04 84
    0x161581030303070001c101c108118400c1c04080e220358080c0c01180302d1551115540c5507100751f400c04442454022800042c4d0000d0340b1404c50601d02229401441e1078542500c03a03444130032040a240c480e0100003407040e42d83c50b011580da40c0e56901a1006400042c3d4100039101a0046013550380d045403107418001d0381000c0008100e1281442036500b11050007011b81030303c202a544118110340f9072501022094180d14070b0752182041000505428034072030b4800141703410914801840c0074001014031080203020001080764000200507244600c1c1d064501103001d07200c07898299560040d29100b2044044640000018802c00c80c001000e001000e0b03c034000359080d031f8007401500380320854401c005070b41304001185d031602d90403840c01402d1112401b5111490b450300002821584200c2014203242d00200745030128100040c2051003503c400c0c5645044181c0d02d103806403020000505481c2e0880d5108005158019141c0442e42140e0344100304001c90343c1c4920f80b010207400240d4055480001110644 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 141555512 1250 141554262 141554269
    0x204050307090902010c080c120304050604060e0304060e0d0501020904090506070314060a03020f0a050402040902040f050307080a080304080403021512060307050306011215020406031b0f0e01050c01091a06010e 92
    0x200e00f40d8060f5621039a6980c1e41d110107104d507001d5440038100348100080f441740300402e6005540602e1040c40034081604007418464295401418901e0841d001040200701c00c82e00b01e0b101c1c40d01884d05842c0e500841405050840c024003803104d0b100d8115051444034410010f022440e60f00c1120151820070840c0350715104c0e00c20488085800e15088030281d803050025150420060202110091403502c1241d140c1010a050b80c106511540100d80c0200d401d100e40000c40b8100c101400d0150000c0c00c803c0d16210741280c3e0781c0140c087c00352000000002050600141d54100c401550300178181200c400f4008021035441d5000c8041c0c1074078080c840001c10b196150102e8198121170004004021590901700058110f0107503000031601050b0190380240348011500180c0010891518005101e00840e007580103042141d00c070a02c2001041c02c2d442001c0c94000c445403070703800028030b0041d88400c154400d050040651080181403110b5580001a518401c81d450a224070030a03610b6090082c0740c40f050 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 141556762 1250 141555512 141555521
    0x1509050d08090d2109060e0a1e090c120c03020c070e07020307061d0607020a120804020a0b160311010c050301140609100f020d0509060d0b010918020405030709 70
    0x1040d601001592400340400c29010240c041820024145082e00c1c1003507450a5440c1c00107195500c035203101011072a4041c0d0000e43d5500288000d00b0903030140c46403030001911604a40c0211071100c105032900f9020b000303d020030b0102078034800500b0011100b403500d002d0112207002031028011402c01402038081440ba00030741e4840b1500760020000e103400c3c11414542003400409100440c841401103101044c803901031141204030304005140490388100d00c460a01d140180001c00307540c40b204c0e0707803400558034140948000741700c0e203014023107900e4610004030140465441041101404a4010a07041d0b0113456103004c6482070f1510036080c100c1c051501d098644014a1001160041c40100060b455000e01e000e80314000030050b80c44d20150700000344d135400b52480340c0000100306800c18400c0c07940404c0100000b420314104a4100707006400050b40034030540b0421880141c0716050700e09280d004192030005000700140200050340c0213004080250042e204841c420311070b070b000005003071300c0074400c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 141558012 1250 141556762 141556769
    0x50f070915030b0112150513050c070b1306051f091811040b0904150c0e0a0501120603060507030c0311041a2203030e0f090702030405130e0d05041509 66
    0x150744040040c10390701540101449401c25050110f405403a280248952282a83c104580c0c00e02c00940390a004c24003602107003080840c16000d1400301485404131090381555001680402540c885039204440b8055840d01c0c140020083c50a0100b8005950a41142220401c0041e80804606a41c61611100365142c01da5028000003040711580045400b074501c0055052003e040880e00500303074030120b90b90110844081d214000701391603a890079850780c00b543c421079141b0328160300c0885102d00011400d0706144143c80c1070000c000e1104040c54038a401503030045400c0b0a08100034944841d0142c054001d1030041c60009180c0070b851400780300f0003c20307602529032103c0401000d04d10007040c81b52640c40400b8071a0405007403514454020b141031040c0002c0c51207941d818004c0d6a01c0000d00c40715100300e5880304d00c2070589000b00310480380d0020079502101c00c202d9902c1c0030f842003403018100505400300d100e800b5004e10401c43c0e40140c3c0000040048402000c00201c00041204044403500079902 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 141559262 1250 141558012 141558029
    0xf0303022109010b0f1e0a030c03030c03090603020f04121407030506160206041a06130e0a060e0303040b1b0d090c030b010605040602060103081b060703050114030c060f0706090c0801050f0709 84
    0x4040281b664041c0090440c0c0000545030a180c40e40381c2c0c41d410200c012a034000c0300015010344050040583c03080d01d42005000d9414154141055170004d40075500650080f2007104541001500c244aa101403059021440700c01f80c0341440d0b140c0c00e040742c880400f00c0f1758240181d1a910045495403002662070b00c40e9401260050351713102c1420580600d00405007400d1341c410b40c1c41020841c911071503c284036074500040000d2030720b500549041c6059420500400c4c249400034000c000100d6800320a8036402140d00d02d405e0b01c0c5800581d034004490241400307080c142c919000281080000c039100c0041941c4c002d0f107400503907a07030300c0030200e845220318020f01c001600300f0801000052950781c00790200d03090b110420703561601c2452002e45480310807030b4090300180d20703071004202a8003c0b03220303801d68602c143e01908505082801050a503c1050f03d1088541000030b05c000c02e001c2117030310404100382d0241e41403023043e03558450240a4501a2401d6030301700c543c400469011402120300305c04540b6601b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 141560512 1250 141559262 141559279
    0x7030e0a08120c071b06020706030c081314010609060314030301051e030a080a020d0909020f04120c05060a02030c300a090905070504030c080c09040f0303022109010b0f 74
    0xc18030440c0b0403005070010005100a00100002407011541c00d1001c8207175a03121500b06140410007071401d407260344010141841c0421003954550710100a40d40300310440000c4511104511b0f100c8640c14082503070302065440c0c84001301d401c13661034101030b00b101d0140f2a0b40c058075503160262a140d1000f0310070315500c1120421414400c18014410340490701e001821b8507504142902c509800b03034420340481005030084c1600f14001a00010960082c00300381c803046081c00709891540c4801e00ca20f000c2c034444182c000200d038040211f4160014007400000e8201520751102140180d03581d000f5010f070032407034013440400600c500350b030f0703c1d280e050030144070b03c03a00d000b01c82d54814005135801190104208503044001159081090160754041d00041d904c9070303915459410010b4034415540c1145501d904100103404032a514108540d42140d04440100207200c80c80c030313098000f441143d43c107030030603918009009121000345510301d22900e94080280a0a00200108062500124061644000003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 141561762 1250 141560512 141560527
    0x7061403090c1527130e03090f040f0c081915050405040201020a0606080616110a0201111c030617060601140d06121b0b13090209042307030e0a08 64
    0x9080f120700d0300ca001649003840c2000c040d00c021440640c84030300442100106440031800c0c100044d04281c15640c02504000044090360307990340340c0c410f84020601c15030003048110a141d03125800a8205400183d040080d003031081c00c00b030300f420310807034154226188c0d0030200c00003040c0c54054001c0102092481808184c00c10041100820020344268114420424102d000925900c200741c0a00351120090481d85003080d206080741100488060400903a072100c4030702944001803aa0805a0908050981e00c2c03003135903d145000d4142085030b1910801200341c21a00303416030f100b142600c0c8a1400003000d084d403d031b44e039a9914401e5840ba030000b0890a0400c079491448406446170301c01c480740100744156034415054143e0b95101003900c50002e0607805a030381c90720440c4000020217030340840b10305110f00c40c010541c81c4940c07841900c20213034001800350086e0313a0b294800050030303401d90802c1790b09628804800c009002e0403156030011915242c3c05031001c1c580040d10501481d03000c2c3c60f85281461 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 141563012 1250 141561762 141561769
    0x40e010b0304030915021c0f021509010e030d0b0102010605011e0c1b0b090907090302030d050c01110403080a0e0405010b0403020d0203030405040e15010f060507141e07061403090c 79
    0x100a2041e400c004007960081082c4141710428425200e640d401000e10103801c41c40d00303150b0b820110f4410140805c0800340c1d21000e40109001d00c484624001c00b00ca00d544403120b060250005207401c0400e030000040c20081c04605520070001c410382a40204515520313000156481c03800e0412100c080380072407207a518818407484800945504c03440ca0495a41004c2d51744281d902d0032030b00040489100807951840c241040400268880500d02c0e250641e0342c910740200c1d0311407010a0f00d030030400c1800540b5141082d03003500209441d2450022075503889507282010388081c2c00c00e10280001421900d10601285820701401707040e1229507000c83e191529607404c00240104507102243c042c00107000c0040d01c0e980710f02c1001e20030701920001d48001c464013800310149a40581114000210102083c4181613000c01921942035000c1c0c00c400079a15959103107884c0060041d440481d04800403c0c4500c1d40d030022810b0000c603a071030b8031105081451003247d4100c0b0b0008891030303407859000e41c10880c82071a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 141564262 1250 141563012 141563017
    0x82215020310080303101d0c041a040e0709030201170919020f0303040902072303070f0212101b03051905071b060518010e100c050405030a060c020c06040e010b 70
    0x801c001140c1102590f4001d400d0840e0821a49a50b5100f44050104505c11104095045000d01c081c02001c8521340040011024000d0b401041c0350440943c540c0c0f034624aa0303500f26005043c20508800302440e0040008051182e140030032400505905c10800750b281c40c00d0f0301d1074002c0e594100500701149620145030140004c00500341c0e80802d641c0d141c641140c5081c00148060600c03078402581d40c0c411400c14001001d00c0d1006100c02202d10904405003540100640342203980c480b200c03c0c40917076140002016042074960300d0b1b24a01038100d90840581d1164030840c5d080e010440b0100c032544005074260101d03081225540d80006200d0400710700c0f00310581c40940d0040260070129880c405800040350381100b03490040710015500e0051090020894a034030a584040100a010740056905540e40792038440135000151522200303440c10040c0903205850103000d0180c100d0325000c10034100320001d00380d4080301d8409030181c2d80110401d414a803040b1029244420b003400c1c1207910b049600e00030b55 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 141565512 1250 141564262 141564271
    0x10306270206090315150102010c090b03040213230907080a0c03020423150109090c120f06080d03050f13030807050c0102070f030e03060c1809040f02100822150203 72
    0x14044d00840044030701c5e034110b40c140600c0103c0481c116485402e000a421180c1c0a0310304024001c031640c4c1000100c2182084a0f400355050f034001c51782d224500f03620405481054400e404000c54604103a01850054100d036203d60980c4080b5520713165624809501e032a420724024002584844040c03003d41401e0300154505100025020030041c0e0089104282a02c01e031101440700000d0b801a401075a440824000540116941040742800401000d001402880991881c207074a60340520600c8590f0352084005288050607200310011048000b00182403c0318191580d50001c0d02040c010101d2101045407164103448807020fa032180502656a5003064403404d03070564080085e900001c482180b8070920a1080d281d01c03008941c01d038101810300c9001030014524034420302c0203081000e049410001c40020607070302800a51110706246518130301115000e50085000c0c8001d007280b590200c0034905c1190241c02c0d414810f520618404612081c002002d40100700300408455a4005a401140c01 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 141566762 1250 141565512 141565519
    0x51e0f040e1509011707080309060a0c02010311030a0b0405090303090c01110a0c0e01080606010815060a02010609110702100c050d031e050103031d0613140613030b01030627020609 79
    0x6001e038030000b00f404009810a100c6503200821000c071103c020004080a080c0c000b02031828202d8040120b90b05014961000d81040848003518081d64003030750110100103c1c14034120f03504c2c98600d010700d001e84441c01c4401e00403490b01000400117240401900e000b43d100d10b0150480b109000300454182007000600c00072800b074841250000b420181d6120014900c00400e00300f00d40c948003e03d400d110005050030706115105e0100807200c0200d800e050032444003201c6168540003114404c038010f00d0141c01c030486061038550030803146503201028107109e5200325464400710f0400c103011243c1c95000c4074000c01640c414208103101d28001e421685e441160801c2d02e81c0104480b00000f0140c84080c0d1050b4003040c81d004015100d1000b0349611842c195083e80c03040d2424a907010002d65081e506e105004078914498542e4080b507460404a41e0308181c1c07140b6003e401912400c242540101c203200842c0c2d0123140200e10110800041c80b00c07107840c4244240e4001003101502408240c1d404120303056403 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 141568012 1250 141566762 141566791
    0x20705031e16080a03030b1e060f090a031433130602070308040c0f061e0323070315050303090d02130e1506010216060c061803051e0f040e 61
    0x5103030900502d2000a00002000301003c0d451410040c0880751040c18650181103c926000c1c95031542c0ca0020701c040405490841d6201030b0450001c246008084171103500204c220000001d21860707907030400040031040c0c29034120b1814101c0c2174106070300e0310408004080a1018001104420043c420b42c000c9902c0d0031451440042d03030f0381e081240c0c00311008902040c640c1c4144014007810307000410240c40348031482060701c2d041c12805407020780c0560203055500b90b800e000515140c0700b0740112100640c0c00341c15007104000c00e081c0321140700b42182e08000003442c12990240b14403545c04800300321003014025502d03001540d420300c030a0600450050340c010710561001305045445201e004800e031507103005491042103d4007181403000000c0c1925046611000d4018225031403020924126075007400e00074a4800c4503d8044003034203070180040e8180c2d8908182005040d0003030011300381c059a11258030035000080b00308046d18051565041c00c041c000340010300c00710441007074841d0010202e485044 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 141569262 1250 141568012 141568033
    0x702010201110a1107050306190207020307030b0c03070f020309060706050a0b0627040903052b060e010602060a060f0b070303020c010608071e050d0b0a0905011a030706020705031e 79
    0x1600e588243c01040005202540a0b120ba450070b1080c0070280900710040e203082d040441c00c0c00101007400c402583c1d12980000c0380821544c007081284015540f0000703100140c031f45080300ea480c0707400481e00310020a19035001c40032010300c0803007122040c2c0030040c4001c1c1001c0c0d0705d403500402040c00502c6103a545640d100d0036051940e555020704610241620503000c0c031281881080c44841c801c0c4101c1d401107050441500020b038000c8207503440c020040d11000c0710794000030401c0346000c91141d207050f41c8a10344180442d000510210941c140c0f0a6602281d1294485001c0c0f013007252800c2c444d01d04241e40b100c1c0b05100100c4144010600a4020315000d420142094002800c4454982c822046907001c540e00300985103914801840b64031048004610340d9252802050710341d41c80190040c99601c050340042c01c020461b600000c060b91300503000304a151120480d417440d030450f070600030744a0720401c840002c6042c8000b80c01025600f01034090906044101480000c0702c030310941000d5580541c80e00b11 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 141570512 1250 141569262 141569291
    0x807060f031d0304090c081317160501060e06030f07090c030605060c0703050105060121020304061b23130b070804080604060501050418050d0806010e100206060909070501090306020702010201 84
    0xd4550101e01c001d142c0e19880c01740305004035921613a41006001180003081303400080c12503406d0700340d40c00c94158601035802c070002c05140d10800500041410040100406001055002c40c0540342d500d240d648103601c900c006c16540c1c034580800302e1050340c0501402d0020440f00d810001a0b901c1c00c1c00d01154075501c400018065130082c400f00442c56010940c00c00500400b4068aa0881c1c001e080c404113842c440810007101c0d100081150a509800002240800c0a42d9122103080385d03007041c000665113014035008050700c0c20401e60558841014504079101110001104d039010160002c02e00000e2605820034016000703c0425600c401c401d1000080c005024407001d48114840d550000311981010100300440d14000b103500464110782142400080c40003400340c1d541406824480c91542d60308004031580f05c280060603070444100442421459000910940103000445d6a8039007552032007842a82c51046208036800a40e240b6010404110b0030790003024000c2c01880041598101c0401701c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 141571762 1250 141570512 141570551
    0x9060a0c11070602010f0c0302072a050406090209041406010905040b0f0307260d0e04090c05040e031b06040308160212040b09120a260c12070507080105010807060f03 73
    0x148090f035100c00a1b00c040709854800c521190086050031030520f1541d0b101e40140c01a000440c02c01c92000c1c50171140b0141c0a4526803005290040c030034400703962035a00c2c00b0b010f9000503030194081c0342081d580d0707900c40c09000344291180d00103030f54584505e0704d00010003000c0d2000c0d441d400c0d0402d810036000d000c5a1001d2107080041d10002c00c0f03020341807004000c40703501c82d03510880350200b5821252910078a254031211803140c003001107501007070080070703402c01d01104009039011310381c01485e04d4092142c004020019021103032960b00521794103981c40284a440f0141241c000b8005000840007601c0810798207140c074140e04c4284112030402c06000200d594552281d00b1140d0400e50202c0d083c0e01c1d0b880c1000012140302000c3d4041c10400c2c0140c1e40314408145404240c085175421600c0c0f00c122044500103954886201ca41150800780d80744008074030640c03110b9001e46e10340c09000c8011641d800140940c90403541c0c03580003000b409150000c12685481090180c504243c0c039100c05480c41c009000b83d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 141573012 1250 141571762 141571769
    0x70c201206161403060607150e0d020609070504021207030c0c0609030e090601020102070b0118021e03010f17060a05060414150118050105040b0c0f030301090509060105060309060a0c1107 82
    0x107103880c8800800281241c141010f0128010004000b04651134030b43c44242c03000507500548540784810000020030260141c03801018180c400d044c0100702e810745c0012094001c1002c44140e07980f250301d0360140300980c442e0508070303000aa40c060100e00310300d120354090b0107945900d04c1d00350150003040d03660b071050f0380d4951003d03800103852503101d0400c0c2c03078003001ca2a00407000340021840e0a0407a41c0d4030210316014401c00032840f40300d2110808000d1541c0440707200740d6454200b9001141403e6612019800a008100c0455805040070420300c1c003155002d920308150400500055461528440181030001c001303540040e00c030521040c3c4814805940750049804010301c03866100004001010400c524120450307001844a0800241c0d0b0007508030b81c203541200c06920f0b92403d44c40082841c03c42d00d0074540101744000400010403207003a0b030129000d08009020740c0c1007a66241c041010900041d14252280d400900102e120702c00c1c1d80d07000c21680d03100f81c181400300f0b80029070040d08200c0c0c03550 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 141574262 1250 141573012 141573031
    0x110c030309060a0207110f0a0801020a08010e07030b0603150a050913121b08030402150a02100b0316060302160203100b0f1e0919060b040e070c201206 66
    0x50040e40303882400311a501c601030f07140441c101190b07901c449040d05034004c005801011500c0c5c460a840c3c44811100c0003424144000350b582c2c4407540310083c403404003441200b01450400c004503040d6846400340c5410050300801680c115111403003201c10021100100315400700d01c90000041d96201c02000c144034941440c800600710311981009416a081400a941005440200f40f1840031000240a040719041440d458407a03940344046501d81d04c10700d4015064010108052a006038001405007032310b0490f000c280048a5803405140e41d403070180409492089400ca4144403051199020704000806201c1109031884d00c3d802003030034403154800380b0311400d888507400c0d1103900f0001100c0d101c203035082c0c4100c43c0300c800e0b2041c12140581e0800c0f190b8801c1d009200800e6244a015200e4048085500740402c20a0766803894043d01c2c0e48103204100d4000c09400001e04200c2c010b403c00300d946500319080804403114906443c1500d010b210300550b02041000c9034903c44407080205511900705d09 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 141575512 1250 141574262 141574267
    0xd0905120403021816120902030109060606020f03040f0e0415050a02210105090f0712050108060115050a0e150d060b070b0f15010804030e0d0f0309120f020d030201110c03 75
    0x5005001060f00c02038130321100301c0f03131070803d015456800c1d000100c0040e81e40d1420b000d50113041c90900c4040d040c581c0c0b0181d415030905000d80c0038410140d0114003114000e4080341c045c1d015000c800c9480340114850a00c6201c4002000c100038010f54540c1c40c0d01a01c6140c5641260f8080b13a07400007118030903510609050741c00b01d004040d03040711b50041141c5c03c0c0449440300c850761601001414400009145591454507a0041000d1b540101c00c0764615020b0f001e424040740da1201310055680e0030910801c0800101031031500c11180c0140f0071a030810a6503620007000c0108001404a0b01400095500504404110301d010307808240c45036001501c007485100741e4841032410800e44000001c0c202d04000d410311014000b0811048010228000080c24081c00c20390340e908040c2c5000310707014040358000640c00c0b0258200113407111107103c50b610a03202c3d0724042d615501e200d840284681c80081c8503152841816002d403801e0702940154a100e84008540c1040c2000d080071190054920041c003507101 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 141576762 1250 141575512 141575519
    0x13020a02060a06050a0503060c07140303011202040b06040509060d031202040b0418020c07140f1804060e0d0f05030c090a06020f0c180c13170c0a080d0807050d09051204 74
    0x80c02107000400040f80d013066906d08041c00a91107100142461408600005890080003a200144041c8a20f80c109480c0c49603945c00c0048070030420014200d115a01e003075aa0038540c505142074406868000d043c0300b01075641c0c01c2c05d01c070856940203015070600c030160300120071101c40742c00140080d0404043c0135454614003c01d50580c40c051405034900c05005104048201c1000038154040315600d00300c0c400c0c0c1000610120b0b0030208000c6800750410040101007500003d15000c1070300481c850075041104440d45142c407901c5003540c1d20040000b844c0d520007481040c2c07107540035640101c0d520341042d140541c007034001480f1910340d51262015070400e003036180c0c15170000d0204801c0d45905540e0340201e00d2603000180c6010100400400036080040b4507500210403450f980b80c0940b002c085140303041800098003954a0311400b40603407041c00405e40101e46028003080f200b0060102c0c0e11148002c4e1030f03848040c0c0f442d4003c000394003c615030301c2d542780004c5001044251124411000c11982d234508 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 141578012 1250 141576762 141576781
    0x50a020916090905090d1b0c060c030e18070e0301060801090f020306091f0c030b03010603060e0c01090b030c07030c150f05090d0207030809010e150903280b040213020a0206 76
    0x1d41c0000022072828040001c40c910100e0611140a414508401c0181307c41c607a0030000c61820101911085200e0404200c80d0f17000004203240c40c0c081d89410783c4020103d41002002c208038040311503070840b18404240c106001d106030544612004001003942900c8054103407c5680d1100199220020b6240410a5080030b114054000c0c410201401342d0001600026a0840880070700105141d80c0e00f0030701d804103200354040e00002c88014005c0c40044d13921f04005000e02003441c0d03800442e0040030f0016006602554280c001c03112006145421552807207403c1c0800e400c84a03054092000039507031600000c034440c05603203840007107160024040702c81e64816800c481c0e00901d100041c0d0304c0501142c103026000200c41f81140e034000c501035170319109000108c0f40c0a4851119030380100fa00758869144101b444090404610203034100c900c00503080038007500074020380f0341244042c014200010045000c62604652060014040c031410956903c0359a040341c2c40031a01400581200301031180101 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 141579262 1250 141578012 141578027
    0xc1b060411010207030b010501050d090506090c0f0607020108131a040305030f0106030e0627100b03010513020a0306091707030806010e0105030622060b04030b0709091107060504050a020916 83
    0x14001c1c401010410300717682d18610105018007905040c800003003000004981e0f180c000c2101e05500000343c40c072900f45190780598540300840030910410303040384203084d01d040c4041a00c015680507510500c15486804504035950032600084d5009140c0d8004010303020204144070340610300c0303503a0715a501c0c40c0041a030400c609041c0c00000c03c042c10580c800a180f0710000710759030050300d1541140140380c01180103404410403d15684d8031406051106006e001c0c1e5644005616203081d8001d002c02d41d0b80c04c0b801e000c5020000d0009500581c040010300100302c8503400541ea5504c82c0b11604102c610080c180ba02541007000100c0009413000100561541d014001e5502c1c01001c0c2819400d5051150008282c080b6080d2017241050b440c250024501600b078201c10b004003a800c9086940329200d0411858004003103862001043c202a8001030f10100c0d072159468400c5016141c82c244030640d0307aa00050030b0050001d480c1445200c0001d400350b555048100c0c010140c1400c14500001a09400340804 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 141580512 1250 141579262 141579293
    0x30c080a051902030406060306110d050f151207090e030a110706020a0f03020f06010f050f090106050d0e120a031512030c1121010b0114030c04092301030812130507030303050c1b0604 80
    0x2c0120740038418030ee078070100600c100c1002112404410304403008882d24004580c1d1298180c2d6007848000c0d80c480c0008001801c40b11302e15034507101911008100399a803521240700d8800160701c11524103000c1001c1d8084002d03643e20030b105944102c0c2100e003003c4e181c82020b800c11411600020001c008604d440031202120140655000d0f2556140160141c0b40740507030881c200c840e83e29011b6a01c40440c090011520610310a0690350b202c3c00f03080300040081105c441c0d60000045040e901140c405106a0004801d6502d1f540e081c074010010350b1046100289901110f41098218403151426404100741c120140c018070b0000401085800004080160380c809100d030f0003030100140300b00c4035140400c0b5003d9a071000d10100e59544150003d1500c200040b20004404031403400110400c0b04034801171200c110759040094a076103541a01800c80380e00d2000042c00e5238404501040068001d401c080d50249000000d58102151003161080003988001408a190400c034100800c10415400c40e102c179 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 141581762 1250 141580512 141580531
    0x3060509041703060a03020909010209120a2109090f0c0311070213050615070606081509030a0e060d0f0f06090203090703151803030c080a051902030406060306110d05 73
    0x441c00c15488600a003280032280015a4200200103000d644030550118021980541492994902040e415000f0740061806500c01c642e44840004240741c009440b44d5403d0700303c504000031000c1c5043c0c90304041540d045a00c180030b64900300041c2c902e464410003e2820320183c001c144801000c1e00101100c1100c0c04041504a091000c100075032034848005a05038400c0c6070000700c0343c803803200150441002c01011003204400142e04400c101e0b030b07508600e08442c0040c0c121085a042120560150f00c0c04a40710519035005000040c0c080b449150628100a0040e000c2850300c5c808024490603220135a01c2010a681ca41100701a0864603210360390040040c010f08500358100100e0040d00c94000d44000380030b00288040065010b0102e60245907143e401c070540d03200040c014039024004d48040c42a07040810203820010311350300000e000d818445d9a030000521040e10303410602e0030003900043c1c0143d85590307a45001200061072481608002c0c0400c1071035031313141d40080358113406490004014881 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 141583012 1250 141581762 141581779
    0x30b190c120e030c030a0507050606030106031a040204060f090e071401050412030509041e050a0504080a2304090209100309050601051c12030f0c0905090f130b07050406030605 77
    0x419510050703460700c5008002010580c4009500341616500038401c072040940000140b90b001981c1000c010014030348036805440503591000c081508179041ca20018207415107898025402da08840b4280380e015100410010784d48e516940320506080807600040143da6541121107128030003040080001d015407418a03c183e842c000c0000c0c070501641c8192040c00344118500c808041c068001d40c0c008020141c400c100715803480400000711010140302e01230b0149045d0108010464500419200f50303040083c191511280507421100f982d40240500d000ca801810100fa1036030b800c0e0001c0001340090f160150716a2503036400c0000858070102e0503401c0c18507066071240025008201c60b41120000c03910b00c0200180103070555a80c00600e40c00810754850039026400c015007591204030400040710b42004174158890040d10118a140a01030380038892000140c81c5444082071240d000340e0a484002000c01c0999520080e48010344020000c5140401d0a0121580c184180002003a00301c48000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 141584262 1250 141583012 141583031
    0x30b0603151017030409230c030403090308090a05030109151401080628090c0e131a13020d1a0f1501081503070b09040f061a030916030b19 61
    0xd0702c14506200b868200c45660015091040050003510014500420144540e9140c1c45a00c1481880c0c40c0408040c2c141c00340110307031f040a070f88050b2482640c0c55200c1080d06402d6172039982c541c1d0410040e95900520a0074003144940342802580c0d0554450b9070a040000100110341041c1e0f4540c603051810030381008010840300a00148054100c0504500b81e40804e60310b0010100b03c0d039915064001c22400c241401c1d04129481d002102100c50001c441925900c0368903080e0101070001402600c1081184220b605202480c400180c11a210746d02d180200000756011482c0300b5201d83c820740d404180c00c40401c0c2e02035585046240e0060201c0c102c07000ca85412202d12415160b003007075407410000100c1c0050408140348101407460716000b001c80740a80e9540501a00c19442000a0741c0107070300380507500741c0c1682680680e100f07079108107410f002c0d26001281c03c89aa50001008481c441c030481c3e10034103260303500d00101130285000d6041c10007289044418150fa001e050183d46c48094904040070 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 141585512 1250 141584262 141584281
    0x308070210020a023a050d020609070501050d230408030708010b07020105040303030e0c130c020f070807061b0209070c020102060f04051c1e050406090603020903060a0e0a0507030b060315 82
    0x24120030200841d045c45900403440d540c205030707000c044000300e8044050740c20810f01000143c00f6800c1086039086402c640d43c0c24400c503403184540d2090901113403040c4040440610f1541110402e8000c02400303004c008203001c1c0b207411164054034180c0b00c82c01d000003480030359680b2001090142840c291110f00e031084503400201030303209a1002800305a46c80c003001011071418055002c0e0303a5801459112183c6280c1e143d10001c0191031480701c007520840081c00741c64580803505004994210026000c15842c041c001e403200d0b410302466040005854030414016503840c83c01c240100c00d50ba4a8010010707503840064504800030b80040c03c088000c0e0700b0040000d20000b0302c0d034640d000342e10005401ea03024000a59550304420001d0301800f40400d030b08a900d03948040a0001c6074400c0e81e56170015136582c4010340c00c92054040b000e40503003021340001c3c200c240940180020703a042c94115441001c054440a0070411290001c680300ca1600041c0211843c0400c0070300405039503100300b81c45a040050f440c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 141586762 1250 141585512 141585529
    0x501171009020d0b100201060602070503150a0b060d110a090501110607050d0b09011202030c0105070c050603060d0209100501031d03070f03090f0e040c170c22060308070210020a02 79
    0x45101842d00058500342000807034124070a0f000e009080441d8084c80c104001e8080c0803540035400c010310410500042524000600b0310084104000c1c0d03140980350902d10901404480d0042d54001104021801107000b4034410b0900800914140549820709114002c200c00d406512030350422030042d030718100b004404181250070800e48d05005990b442d0300740382c03107014281403014254080e010a0000901d09508030359060594804c4058544030340c00c0c0b000544890040c07250140450110207001d12444c01c0200c01190000030041c54403600a005900007416014120381220f4020301c0d000041000356018090303403c400138103900010340e160403440125924018610041d202801400c0400103044c0152409000341c000a5607840140e600d0316807040308440c0a44040b907003645c41d03500010341681011007a1000243c4000074106044409040284070000c040c1d1580000782e0440c0d401c0341d0b030045481644025482081101d4031a01c0030700402414603c04039009066410038195440103070b40e12440d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 141588012 1250 141586762 141586769
    0x305010b010e18060f1e1807051602060f030a020a110f030f03180d05040e160804030804030210020d09110d0209280f050604050a2007050309090406020405011710 71
    0x2110465903a0300340004044511001724942c10210b203c0800200010100c80d00c1c42009044c0d0b82450354441c0d01c070804581d044104c0750040001c01c207000c03a1015002809210f014240018482070600c1941c9014141517401035541003080c907400a00e140c840c5400c900c0c288002c503c00302c0a0104424481c031030a440b0b2141803241802c90200000051040c070451604643e1000d001d01241c1e00c021803c24050010f07031040c01400901c8100e078001810109040c83e65059000060351076500d40d44840c0d074140c600030400340088045d0f004920042000b1800e51029000000400c00c010811100905000e01000b08070510307907008024501c450800358440000098020620540c07040c040c1c401300d01412103076540038102d0040942030074100e0260701d0351a08101d01a280480c0c1c104910b403258882581140e407103142c10034003503030050781e04a1604008006014010301810a892030f00c50000300042c0c2e580000c55048814a80c0490144041d5a1201e070381c504c000e80c0038804a40508080c400202d400c000c030710 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 141589262 1250 141588012 141588049
    0x30c090b01050d0603060203010f0b0f04091a0d03080118020c031218010504050c01090e06030c0112020c0708030712080f010312050c151b1c0b030a0b0109060305010b010e 75
    0x54001606900c02d0341200c0318080394800c2040300c291207282031000b9520070f1007a5400500780800c0401d030070310f50b4400c031a85070000c008014a41850401031101130052260040381003110982c42c600d1907290366214028042c0700c1c1c0d64030766480d070614186541a181541000c00f105206000c00110803038000101c980c80324013007422146903914080051140315003003034100c070254200028041013040008a034990b80741d09898145490b03480f035441c40b420140440c0c2c00d640c1540503a0391070216500810220420020b4a1005880c2005004945103030021a0740484a154400034034075081c005000c8082c440c0309a6440c0c003810314146900002e06200c010701010781254903201c5031880c030500500c1198123100329141030b92550049504440c0e800c11003140c0c02180d000c00c000a405504503010112401d40180c1e800c010100440011120010040f00d0142501417141c180c1079000701c0c1540603018000d01d00240080340b03a60851501900750b0706040001d90600c101d20000010503a50f9611090301d055901 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 141590512 1250 141589262 141589271
    0x60b03010e0a05061821040501030b040b1305040c170708010c02030405090103080f1c09050c0306070f03050903040b0f1c0603030f2102030c0405090f06060921011b0315030c09 77
    0x214800c0703003050a41301a50744c9011b000054100d2541500b40500101c8401742c13402c0121050760810300040d030b03500108070384d406402054000182c080d2176000360b401500403e141407140da141c00304680301c08440000034200358400903042004010034011010449824030145061900d840f010030501c02d03040c0001000c008020030180074100c1e1480588404440d44000c54036061100c0e03000d08021306540d1015681b0b03000e0000c13040d0079400e0029505000c1e0441d45d56403a0b801213449011401401d01502c1000c4070302040000080100c10308011740410301c0d402d808950341e005811070b0300030100f002e0070300720490030f0400784100046904460000d41c010010b0800c54414008071410100400e42c440444102c00c6c4040248610a080c0001400035030780161a00191501d402e6809210890102d480a500000810003400746007040c8241c0000b40204801320003041012604031420340b503031200000e017000018070003034210390b0741401201c0302c01501410900240b411038a401e40b113071500340904145107488 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 141591762 1250 141590512 141590551
    0x4080303160e0a0303260c0a030b12030403050706091517060102030c0a0c090606020c0a090b03031303030c020a0e0403140318070f08070e0c0a0327060b03010e0a0506 73
    0x500b401c400c6a2000070041c0e404a5141e00e0090050b004404e400b00c0c9a80d1000d160300003010f68011814003984880880c203042c004950000c4024222076100d09801c0240c80c140390443c90b2040003d032003c1d45c4110060203105040c00d000802d421902d0b4441111200d0761040d40c144250030500c030440911500d45008000e54910006074079510880803040018803c8200d15400d000414200c881542c0782c1c0c40c2d05126069031410100d0b9103000780b00a0366800300141c00c0030003003007800b83e00c01000d0b0180036044e00c3c101400d4500e07580d404019a8416000310700580e9034201140380030101e05010300145100800c0703605041d100108150310410600750384680c0040032400701a02007003100032440c2400102d032100368440010342e03800d4140c2d100d0345400b44100c000102d1040092104980301e080704076201070800811044c2140604074440500b0041c6074000c0c0300c6a03003600d04404041046001e040c0116410901601b85401c54800c2c1e948408690040c1000b200003c0000c0340c0e1703a8200c4060340e61540040f10 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 141593012 1250 141591762 141591767
    0x9040204060b0309061611120a0903080c06010f0b0a050d0504080c070605070506070c020d12050409090614060901230a0e07080a0c05040506030121050f03070204110408030316 77
    0x10741d045448004408030411100b03507800130710140309258004644d0011403c00c0f0b000c0d10181c0f0520068529074000c08414103071049050003414036071080c1c0c030700701000c2581c0c1c0c1ca8070180c40e4000a42c0c1c4609170090b000510480c010310311001c009096850146180000c0808010114090741e114900e82c1074540c4041401c0c00003c0060302e0020600d0415200b100c3d95695002d0304541c0040f804840c41c1c010100011005801a4941c0010b0754001d03050255119841c0e03141180300c04051418024400b0038080411320782914811300c1e1b42075201d840c0004e00d0f40312100305a0403445009068074441c010030f07070061080184181c0d4003200105010b81f05803d011504000a40302170043d001001c04800d00010084510760040d01c450060000241c1000704011003282156284518043e090708600100010483d4100280700c249851041032408100074045603101410a1025203c000c8980d0001c45d1301415841c10b8810a50b0340c00304911640e107058507180d14a034480c00002e103c054158210b00c1c0c503030031590 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 141594262 1250 141593012 141593021
    0x8071b02061809010503060f04020d03110d0905011d060f16061a09010f03030c0b0603011407021c0309050703080a05041809110105070c0e0603030c030d0507030e1b09040204 76
    0x40e8000c1019440780d1440d50b50300352400c9001c4001e031040c4050000051682130100307080e400364804000340341c034070b40e6281c00384440d40081000c110208400403004c001d41d80c10a002c0300d149803105540e43e02d81a07141000041240c1c0c0004007c072020101c3c0e20740c40b04103554000481d2007107903087c440d490711b4407844031411194014071130300946020700340203480f0036501d00ca0003141001d2504407891440c40c1d0b21002c16050110b447d000042c04a201c2201c0034011548031440280d200700d0003000894981c10040c003200c200d140540300440540e2003c45004058640000d45190084440c50100300c01c0d00e141e100c1540d102c95500c070141075080001b4031004d000e40314600300c8020340400e0a104c80484062003400d0005c0110910075242528140320607080d541c416401ca07000c0b160400c8074804518201035010b00a04409080107a15120401241c420f10b00c0a002511880c3d246000c0000d01d40f034000c501405841c1e40c2c241c40d9060b0f400196a00380d040c0700b24250110b001c541600c0343d04056480d80b01040050 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 141595512 1250 141594262 141594317
    0xf0c16030e041e091412030103021302040504020c0f010b0111030409050703152306090d060c0201061214071a0a0503061504140406051905090c070218010f12030807 72
    0x28160240c41075040b4844d002103030841c0c07040000b00300440c80f11401e0b0b600d814481118004d85041003004102518050b1020800b582d25284014075046c0d681001501b2684005040c1d011500302c0c03002c1c1c00000100380b0509040074820700f042c0700b002005d8103030030f034403031041c4d0042c41066682c80c40405d64592203a031020300210510045018010b40701e00032a0840c0e00801d2206500c01c10310180c0008506050b402d50b407007e2000b5007001c0e803c0d800c1e507031000c1c040c108502e00c00003159078400e40016494500522560b00034060005c03607a03682e0900122508003a91500040802c80c170580154920311080411650300d0302031460310544030b4980200080c0c44009a40403038001d1840410f0214030700766810710320041c03275408650410809584105200c008048a54884a6514800c072b0801c000e00300201650350082c440750400b40380c001c081c2c0c009081c402c0c085a8229170200c0120050180310480400c60307000d418462150a1441e08a80e001040e1301401070400c81000464078400c00c19a07010000308051 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 141596762 1250 141595512 141595541
    0x50106050301090803191506050714031c0b060915130b07080406020c0f1012020409020f0406080a0e1905030705060901021305043c02030106080f0c16030e04 69
    0x10512a0704100b20b858000380c2c1c40c140e940242c54034010703520034148a00301c54840141c0080d0500788c50003405542c25081072809a90034000e2146180707095600788002e00110211074601005901200c0c014811543c0300041e8a00400b030070081404a0350301d150500c1c0da48981d10754040e686800c01c0007c1c9889003401d40c40480009004100c050400c074080300600f080c1c4103250301300c40307410602000b040f200410003007205410141d02d03c4282c01c0360b80704901e00460803014a070094074140e42c48410300f089034440040c0030354006c0089000d21132031b5032281000e50013200c080824030802d03c41c2c01000d601c075664003001d0030380c01c001c801d5003004002c014000e4484c074681040030340c2d803e8903060b001075010754083e8154101000032002c000c6030618003486004040d031000d40da40060481443c82c0c10704900304004119451565200400f90310b101c10380000d40c080d0640c0d030345092842c01d140c00c4048864a01401400d40300c4028401515000c120000004401360580b406000999101c0c02180003040c3c40c2004420 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 141598012 1250 141596762 141596771
    0x1e030712020303040201030b03240a02130306092a1e031b03110102071206020903031902010b010f050405030a02091807080a0b0906070f05090102100501060810171009050106050301 79
    0xc00e81c0d008405144118000c1c0c8040c4800d038022410141c035000400035021082511140310301040c1c00d1519400c2c1c0c00b58849500525244070790a205120442d280e00440d04984c03924003a2040000f058a040c62140003145000c03035808601018165200c1e4600500320074901c1c6400080d4407140f0404803034011174005082c04a01c2d60100242034020440b40420348040f40e103208254030b15440000c00d54201c0c1c043c052085c18a2005544800c065800030b4449581072105104400e4900203a0706c0081c0e942800e07800020b14020071400140c0b41c01003044040050083c00d102c20041b0703450108441c0a9141e0480d12181d181e40d0b200c1c3c4410511001e0424030b010340c81000d001040004000841303111181c0101d00b24a1242c1ea80d20509646040c100c41a600041110340298800f42c0504003a001c90f1105005451000b071032210ba005c1118030903070200e40040c40f203c05101c80c864521102030301410074000500b0000034455242c5070307110700d61000700c4035241c3d4a000c240706022080d4001009003070010000e00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 141599262 1250 141598012 141598043
    0x6180c040609051b04060e0d02032d15060a09020a031401080102040503060a0e0d0c050a0b0a1406010c021e04020702030304030309060f090501020c0111030c0d050a201e0307 76
    0x1000348000c95504c200ca4a00ea25100000a01081510100c5d00a661082e40b40314802c0c003444000c0d4200581240c0501c900c00c000c0c9800500e00004c091502c89240c1c0c0958044d086000035441c080034241d040c80103044650a000c3e061301d903c8003110a4401c400c40c0580d446110020407002082c140080c41c0c0704c14203640c00429118410340040041300c88c101c048a00c2c645aa1410b003080f00e1170456107030015404000c210316898050428004464090026a0500285510f5440180070111307414004142c0c0c8050401e00602542c4501c0e070004400e01c2c00c001c0404a0380c5c0400c0000e0304040e07520080c45200c0100c082d01c0d58460301150403041c0d000c4c0540780c9503983c2c2e1a000c0d10501d040c0c01413401184c2c10309144080c0b80c2c403840100701103800580c000c10b03011180600540d08011203141ca0001c03408200400d540080b010426800d50400c5603880703c1d541d802c00f11009040e6004a007554003504601d000c4691000c00010f10181d6078401c0201419400300500102d030315600c15000c3c0100000100801706 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 141600512 1250 141599262 141599279
    0x110706020c030111040e063003090108090a030206040b060a080a0f2607120509031506011103040305100f0b090403020c01030f0e1510081b100e0306180c0406 69
    0x1c901c81c10550090140da425003540d41103034041e50003408112040d030750000c0d540b8580440a04101001d034403540c8000c09070400c5090b0030303408845101001d5400040c43c1300041d40d1040c2070740e901208020203800b0221082e03400030f45901001c4c001a01e00705894000c0341c2c1d80d80d40e81e01c60200170f00055084031000109490400625202c688041e03c0140400c032603402d070507102041060b07120720704034110f41c58440c09940e205400c4040202030300411030188142c280301d03201040307545180c1d40c8041894080c0d240c08000180700081c0e005c1c2c10310b11a0030510080000860028030702041c0313407901c000414a101d1209422000b07042c03222080d503000780c40c0420310003450380104500300381e8071081e40e0511840c00340c810760b401580d00d50b025406450307011b401c42600d9181c0c400303500e41d00301a070760a815a0f10356440500341e241c8600c0407400302c141070030622081490320306104000482c0d000f03070620030410011100040e85922005000c4018851000802c2c0c0e1034681c00e12a100100c24002d104020807a143c0a00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 141601762 1250 141600512 141600523
    0x20115060305040c0b1e03040f241b0f270303092903070804150e01020c19031b150f020304031d0303030a15030609030203090a090c0909050711070602 66
    0x30744e580c0e4180c04010070710303e4040003180c80c0c14901403102440d440d20f5004400b56648024000d480c0610b5030b059000008460010800d9060b2840c8800c10f50b010300070108800300e810f0382d146442d42e55542d071803a004c4c464110308800d0996425051446403407048485da030060480ca1042c2407074000004602008040d002041c0300705403020295100c400300c282003e00300424030b00301d803081101081800002d02d141d1145152603800340c401c402540340d0840c20340c41e14043e10844030030501075940104140305101c2c1c040201c2c0c1d0307046002c40032803021314081d49c50280c048904030503400040c00300900c4013414000744201c501901c225401c0704001c4070f55081c1d007040007900700f40e6044000841050800003013004940019036002c41c010007440c9180c4070038920380d0003400e07141200310381c51320712017400004078150b480760103410f500a401540e90340c9000c40800c012035a0a400610800c1d261010607420564001d21b85001c0e502c00e5840000c0c0c40d2114441071340d256000a000c10707503074481c1c0100495040c1c2d0108a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 141603012 1250 141601762 141601771
    0x30f010207030f020d08010306020f0c2a0604120303091703040f0b010e0f06010813020a080a0605010b030c040b183c1c02060405090a060806010504110702040903020115060305 77
    0x89101e0f000b042100e049840317911030300d12400007640d002c0050022030110381c01094460074500e203451034480000403c900b060300040200c0515840c8200c410701d9070100c54410b80c40d041c01190082d01d4203060003000c2c1910b129a03035014040542d540700070402c001900c032442285902e426440c42d107134030341403030304031424004010219220303901d07200002011040d0550803406150817810f0b00c0045d41d5020011610700b8002480020b0320b544407900040076890b4030003804050f28010000d4000107030383e428030300155001a400710400c401c040007084010b160001c19102030721001708161340d5824040390b48120101014084036802005650b480402445202c010031a035811195003070344410034810360401d00d981b08402d4a410090103040618040c4141c61070340c0000380f0080540c2e080c01e40f0760002c505507400880d5100461659200c0038001d402c41008882d0041c28100e42c18002248001d104441c5400b41c031b4002070041c1d4489590404050007034118025000741d01c5c0351401001c3d46c0303440c010301811090f01c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 141604262 1250 141603012 141603017
    0xa030f1209141f0504150914060a08010b0a05040f09050a050a0203090706120f02040806090124050616051f061202061e0906040b0c06060a0315090503040302030f01020703 75
    0x29800900d451006003410182c85008000f000481e000050320f502000300c6500d0402000801c002c049009010254010030719020366440c9502141000d8180e120008510b8000d88542c0d01030140b0096a0750016001e8192014080d10545455420744282c03064000c0380c010003142d040c000340206004c5201e41c003091082c07108640620142d101d13503845800304e1005503074000894025150070f01010340980402c04a003480c940c1c0000e08020940340000072600a500701d0b040d641c11400602c000701d00d00340590300e0001a9621640f0032801000c124008140c0d542c4185070042d10302080c1c0725803040a0516000105420505079180d289054001e166500301c0e01c00c1401c4114903081340842c510f000781c4294401c00da8040c0106280c40e104ca9035000064a400c00f80b81840340c0c0c10055080180c407918042c000404803842d075162103400c503241b100d04240f00140880e0190750001401c0010440e541c0800c26140d010342d20019100a1604200d42580308030b40029405102d210b501480781007055000f403070804d000303a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 141605512 1250 141604262 141604277
    0x20711010c080405120f030a0806120303271507020304090e0303010506041a0d06030804150f0e0f010e0301051302040c0f05120a090b04030804030206010812040308090a030f12 77
    0x28005403000c02042030301500c0740c1800d00041c02141002012040c44201040480f260015445849465039000b0200c42c00018511010300c080741c00c0240c850030203030b03404501450071460145000c0c1801d40020500100729048002155030000092100300d4502204640d40c659506d026030001e507503940240f1a1800e103915103125000d40500100544e4181c03003000b0105480c003454202504141e0004c1407905d01450010011000191361074824140294450701d0040c1c1c8440c60802500c445840d081100b0b8240b001c0c0b6281ca0210661045045c80b40c00021545802d0f0981c1702d10040760504083d210564040d0328000a00c100d45060f07404101400d8800c0320140402c1030361400031208142169107400c0851002c0c8007a40003a8071442c102688452966070000740ea00e0135485113078509c1d03410340d01034003c284e44506000c2455414070440740075240d1280200190406816864000d01c10391001401c0f01a001c11085810755840100d40015900f0220069040000d806e151a844040070030b5007000c200b82 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 141606762 1250 141605512 141605543
    0x906060a06050a0509040b041d0703060c050702030c10142b06060c0605040819050a11060c090d080d0c050a0e04111204020f100e010206010806040b040312020702040903030207 77
    0x602c1103030014011036441c0c80c20804d00b5400d1001a14250058942c00b40d290701444c2180945940c00320342091400b4001d15813203156040c014215100040c40c0030030003e081210f0710140e10009040003c070682501c08440400c40290202c540a45440e403504070000c0000e840042c0a10416801c0038007091450090100c0c4946071545085440ea4425600440d2018070075101041c10350780207a0741315020b040303854500121030245c8200f4035481d5110101080c00810003c64090b40f28405d070348414800c40081446080034800d01100e07001d41000507100c0c61041503004200424131060703500d0301d031007180300340701004440b900070307040e9080b076800c8000142c006803100c50245030038052810b01410b001720581ca0408000ca010814a0005000b660040c0380e4024003400c035214110200b917004090f903076215559034600002030400e1010380c071032032176030707115005000200f0422120a0340266050070041032407221082100040e00a03200d0103540b05d86130030104400e250b016002001f034544603491440305e101c0e0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 141608012 1250 141606762 141606767
    0x30109020402160b0c0c07260a0f14120f0c0c0301140613110702040f0b0a0603060f060e090705070201020703050a0506160224070e0406080102070614160c03050d02030906060a06 78
    0x2a12485091076001800401282200123000713102210716050005029110460031440c20aa600003100c2c200e010310400800d003e00c0803560203440815101a1107000e00c0700b24904024015243c0c142c4108500180050302c81c04100b00c1172010100107402440395030f81c580680c004116046854a000c0d4255080340040c4400c144200c2e10703502504102135040c56541d40a10005240d0b410a003a45542e850344e4250280c3d0b1658007000003007845640c0403c40c0c50400c1410030147c07115600030802d101d4140380d07815240d5140c12034550701c4002490700c01e49420840c00101c0c60308a1960014010b03001c0d40b1002414040c000c255240708070454101900344801c078100485e501c0d00485141441d4005412140301d6182880c0842a00401185440108924507038001030444034581d001140320fa500145100030408035004401c0707a0100c1c940030500c00d00c0d19402c91880000e050940500700001c0349040000c0500520070f031a004c0c04203102c1152207240607007031140d071080141c07003117841000001030000300c562 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 141609262 1250 141608012 141608017
    0x3020d0b010e090f071505040b0d2708040b0c010b060c01020c0d0905030604021e03010c0e09100b040e220308040302010506030609120306030304050d03080a0c031b0e030109020402160b0c 82
    0x7130a6002030034007078600403081080340b0042d1076113010403808000003d401e0003c50041e0052481c0b85000080324a0318400740ea650b508400b51300d4900c2c6c2d8942001d00e0109050200b41c8045a11f05241c890745c504544034401c2c01080e0209031160700c100041000800c0c424158040d02100002608403101c0321850341c420307a00103503503114081e4160b00c004005001401d00c030842d00854540031404100c43c1000e01c00207800d6031030070000000080d1401074054014a00000b00a400500700a001d00d0000d0808600c0d100c1c0f445140961031700600344401281c0004c2c151801c00b00110160020000c40e41c09a18001701440800c0c0c8080d0015800c00000c121145008180d60340200e298000070700a45500c3c0d2a56007071508024006c650501040c4800561500c0d044000011340b4400e41d0b400c551890b100640034101c40f02010110101450b0200a41402001102e0746290821a0038071440310005140028007604101000030340050000c50090100c03045650485150380c0301e201d40c407035250788440c000c40460 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 141610512 1250 141609262 141609283
    0x30103051b0a0e18100501120c0905011202060c070f0e010504050708060f0d020406150203040e070305040201050717070f0809012309090c130305070e07030b01020a031803020d0b010e09 81
    0x88809001084d11251240400b071104010346003a500d501d8411086481100d80903030001c0c0420142071800ca0070040803c0c620400707001d08141c10009541400110070540081320002405204002441c854654003080711100400521110400c0d0b02d40f12a60f000e5000028450340e4007403400c00c03000c1002036004100340d520900c5c001c0c2c030441a01480004015400d881d80809a0f005551503501040d406010700d040f05050703025030003d5540f907142c8400c52114490041002c0c04151501c07060000507070340507085420040e00803180107046404414689443c0c4101c40b40103010b184020035000c10044100040c0c210401e098030780c2e4540c013131212038050303403044408682190080304010034422072800c80f0080ba0441d0403591b407a401c1c10144240d042c03c00600f0342040e01c10307500c00c400030011200c26024640d8440c10318a01440008080b0001070350b0b8890100c070041c00d06c10b4282c00c000b030541c0038251801c0299001481c0fa25100d00500340280b2065082c00345054003036905000a110081c0000c102c5000e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 141611762 1250 141610512 141610529
    0x60f12140601050d1d061006020a17030c0408061005131104030b070212030c0c010b0d02060a080718060809060c040e010e06030a0614060901060f02030d050a060902030103051b0a 78
    0x603580c40300111002e9005465007030711580c0d52500311482c2140149505c80100c03009000300040c0c10302070311040b00500e04d0b52000046620580307603240000e010103041c20740c40d00490801c54590309c07040010451405141c10101da14840d440c00c000b09010300b54001f07812540203544034080300c44038652a0341610b56200340071400d500100710401c0094000b410142e03024950340306490750701c21104802c441c107500c10703030b6007680c1c59002081c0d003041008288149240100110f0300f0021003013003980855000d01070f4013880c81c14000f8020000341064000d513081004140365040c4030213944e0b19100058038444007070316545003500c103a000140c2280005000c4a041c0c0301007104000d0280e1030180180460303040103200940502442c2196070000304540500850243c0c3c500002005140c541c061091500c030591050017004544d0120700c1185801100711408034242d041c000c030b40c2e40c0d074014113a80545020380c4183e001d10300c00000081232000c0800c80071000c60011002c1c042c10303203c82d41004101c01107030003078052 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 141613012 1250 141611762 141611801
    0x120906010609030f140604150e01020315010e180c1c09110904080f04030809090f04031d190b03070809010902010f05090d020301060605041404050f1302031006060f12 73
    0x401d901404c5580761611514020b01003180c240c10b49401c214060b901107488074103000c00790b106240c1500600114504a41c004c50943c82c2c25150312068000c455102410300c88000b0500b44241c0340d8441081d00f06522020b66034007400c100e81009443d51003450321941d17514102070f4201c4004014040c0b01d02d150b821007aa2030101d1204010404e19807000740046407580c0d02040b00102800c0000d001e000118081c841c91901c4144160600000181c0240705000748201d0a0410001035085030141145442000e0000103401a07500400c0f032100f00f41e0200001c0301c01c071080004092204900941c8038049603611402c0544842200314283c545d1400028040740e40e0380c85a40c0c40b140716801800c20b020000f0024008203c0f10380210b400c42d6010b0300300c18005500004c00303100c98422145d100940040a0340e0411541c40d049120128250000e4020a071155a40201e4401d45d60300300149030300203461210800c01c941d5200740240011140080081c081030070b004109080c09403c2c864206a5001c1c1c3c3c64498 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 141614262 1250 141613012 141613019
    0x100306030f02211920091603060803030903130501080412030b060403080c0a0b013002011106091609020703271203030902090a0b0604060c03020c090903120906010609 73
    0x100c40c9140480880b00002e14050350011180100001c6035003420400080910280c1d90a060314135090305c1420030380801d8015100d6090b41c07142440b680c0d20444c016101808400c10a90841c0035004691080d1801c6c070002c014040e41c0c41d0003000a00c0302184660200440310740c0d840054aa905080b14064100c5101c1054840258083c0e0403100200c203000b081c0c1d03481c05840c1da541500036002003502c0c0c0110b90012850b03000b045120035015000d0411080200f20300181c0a00088200302418511144410300401110031a40182c1e0801700901c801c5040e2501c41c5420002190303150303c948800300b0090314840000810040901c2106c18180c1c043d41e03407902e9003d040b00700728013003d00820700082400b0014000201c10480b603a90031945446640c010941c18958010405240c40141110201c1850b01d0400c58041c0d98040440702140c2c0181002c2c04c0007911810140d04001094410079080900881040041c00c0040b00401c110100c0b94041704107602c0d5406003903a5058240240300124000550a0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 141615512 1250 141614262 141614269
    0xe0d03181203020a020d0801050616050a020a15030c0f050315010908010c02010b0a140904020913050a0803090d0305160c0c090f020a17061e030c040515100306030f02 73
    0x9016100180551400e0603000e03a01d080c00c08010401100019030b0110342e2020031541031048030140c4084c0d1401d04219410400042e9051064588000306a4140c9160350308000d81880301040440c0c0040802c01102c2d43c031101d1050313246a40540d500064501550408014040c440c241c1d12400180d82c0c0034103640d41e900c020800d05c0c01403814941404000880014418000d00484001c0a9a54004200c080441080c031115520756081070b0001e80c0b801007800c5881e1200385020343d00c80d0701251001d0b02c54840f00707600d1100d5800c0e50b4002e00240900e00c602d1050207030050041d070207441032404903426403401e61412822900151a0000850f007120400199503200e85051051640148502007503039664500810848200050744c010301600404d004051580203060480342084d2007100115034503050000600c451002600c480d02420307502c0401450f40c50400c0602a01800039000f00f00604220240020410b041064136105c1e91042c0000c06199220b030180b00c084175031028024405c1e42c0a40c0c03c2 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 141616762 1250 141615512 141615521
    0x12141204080a030b130c0215010506030c1b15010f05060903060a020f0f070605070e03031c0203070509060304030804061a0a0b0304080702030a1208011505030601030e16060e040506040e0d03 83
    0xb06820191110141002540e403591502c3c00200b0380c0340c00081d01503500c00301a042800307031011201c0c5c44c0b81420040150745c0328070f01101d40c0310425049103907071880c0c2a201c50101801400b01020a4800c1d8500481c10310b04d2103005505a800201402540b9070703444003007101d14801c070641d240e01604510b0204160181303540180c45844003d0140504200768220340c50301c1c9401c462019603da54a40041c8030300c0b0f513005038010311154010740103149881c000d09003505441060600395056140c2c0000001c222500c254159580300d10028205075407400d190074000d140365001e803001c2d03c0f0249407100314039589000350f41000d2440d40180c0829020340c502034421040380c0004000703580c001c2c001c000070310042c2e5085c02600162446440280201020440f00604076901600a01315000501030704131000343d00441a13a40c030a0091801241e00000b03c8440d6042c50f00d90000b58103914080100422070300c1d0000e0300c2070105030301030740c0400550395103d08100a540d07454602c110079803c00514000654820b820 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 141618012 1250 141616762 141616777
    0x5100f0917030306040506040b01020a0b190203070e0102160807291606052d0907090e0703150204120206070c0e070302030708070903030906030905070506071214120408 74
    0x8011a9681daa4240140003449110190321a0303000003040144a14003803040d0360b003000c02501c04010120103840040c0d5507000c04007011740300d11000170006141c164200c0310290911a550340564a81c1006140584012340c9140142e002d03000d40200ca101000354000c002003120603140080c100d46141c00b5000a051070002c01544903442030000720341269a50b840100305102000b880c40c02001981e04024003212009001c08000e40c40800c3c1c14068198100c003000e0301510180444945501c400303c82624140d01e03648101209424894440884000420356508489c090030f501c00e400c111021803182280b280e801002d10000041c0c1c1c0d2a0003609008010300076451042c3c0b503014400e601d03600142000b2004403804400240c0000402400d0f0754002c1c040c0e508008203042c801c0b2a1400c40d64085c0c14018140201c604042c0e69400c21020302204225540c001c082c0581819903c0781503003811450700707020001032008200201561205100c440b0304a452580b1140c441452a032102e0b90f03440066840b001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 141619262 1250 141618012 141618017
    0x91e042018010905030f0c01020706090305060c28030e0c0402040b0f030603150a090c090207030807030b030a0b01030c05010f020d050d09020103020c010f0504150e0c04020307110d180f05100f 84
    0x2c501103a45e480030040000444000343c010301e10750107401d00082c07414020740c000d1420032000400400026900040c807541254840002c6502c0b154070b0898154a40b01451400100082000c05034a01c5d507003592080c048010000182c0e40141c03a482d0902040e4441c501c03605448810030000b042c40107c2e110051900007200406684140c0348495842d610343c542038441b01c50b05960340801d0010403020814120060540300c04c29420901a624040c240c020002c0611080c507480381000038050b5014043d40d11102d9014150789003e5840382040320f80d142180c05160301007a100070000040e5400003e00501c8040790781d031080d2500040c40c1950014000f1140c08174140341d0240300711a0380c540d0a0180754010700e18402d002895240c1400c1110000c1006500d05140300e1030320003880d10160011070203850740c03042950003503542e481e4024200d45030340c41c021000010340a080c04500b005684054800400303800006600d9085480d29060040e4007600c0c070a803580080103040e02201d2600605200a105000b030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 141620512 1250 141619262 141619277
    0x17060402270f0108010f0b030c0405060a05060c010204090b0a15230a0c05070b0310030f0206090d0f0b011e090c0306050907020304060206010803160f0602091e04201801 74
    0x50300c5401e0405058620030b45140c02c0000520000c0024815603074244880c40040c401814440f0102e52903a610a0080d8001c0d615100000d500f61220b40c5050300030300c4042c4c141d580d0740500001d06030007504031b8041c2e0341034a428804c104483d882d01891010640300d40144c040110f15a03c501642c000300e40d524040354030f400010070a103480d030580003c0e01c5141030540310135503201d585251190134160180c004400d2406e0a000b4800140c100c6010b200680c0d030b00003ea010b0814027400020641e0082e124551f40c0305a0300420030303080002008452902c80d1044d001c440f02640c88010305600b0300821403103018149502d00301084002d0031908542c44001c41410700007401511080030030700748070b402c84049001d6800003504100c0550b040000c180100a07030005141800b28203001142c1622100720064002e214901040c001d1000590496094860003000b51010752590413540320030107142d024891049241001500000180305c80b65620129004805494408403800d4a416007121200c0c16040240c071 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 141621762 1250 141620512 141620569
    0x1a0304030309020907031b020706021e0c030708011d01060b0f0307052802100e0601060309150507081605161203060305060f0a06050a120204021608130306050117060402 74
    0x4da481c141c2c010206540d0200d002e07500002d00000d81000701c0400750071980110b000304610380d1702042c00c4041e107062134807003c502d150640c040e84c6003a00c0003000581c0340c05407040c00a6001c00540c80180ca420a04c0008503000d051421000e08070741041c401d00d1448041008890050180d0100460f880300060405c2810060050589007000c1080b00c06155141071300e04052191070f8040002c158404140c500034081d2180e1900456142e0307070706124038400d05032100c1000d010070110744814259040714010800482c601110010500701040d40c05013406001c9030003490320b00344907608072100040e81c0850022032600ea0359600351100700f1300c0e000004240d510306c8048001031307003400b480d40111101d001d00d035818100b500b202c00c1141e086500091051800c0e880400035019a0f071000758940340c0443c3c0c0142c0740c0c10007000d000300c50680f2038001401c6100c0001c0c24000007220020841c00d49000340703402c04c4503a0702d894001c0c5401d80e80071841041948241c000800502e8403c0ea0452401c05404038076108121 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 141623012 1250 141621762 141621769
    0x7050705010903030506010201180f02240d06060f080708062b0f0203160f0909081216031a06040302060d09170307020615060d020306040b0a080102070b0f011a030403030902 76
    0xb02c1500450000e40c0355005d1016a40e42400f441c910300000407584090241503036111407210449501c002c1c0a00751300d1100c0c000f1411071158048490000c03801c001d03602c0405480c03120007041c041c05441c1c049130500d14000300c40c600c90b020842c420300c010740b1601e100344c44240410500c210500401c1407060045848003003000426550b246407203124100003509650f52b441050304142110f00703208450b8421203410080c0c0c0c1104100c03401107a45031140000e180e100c070b060509176485010310300c00b460081481803280c105c19482a02041c141659400c004680080c1d502c05071545442031000c0e40000240302c00d1003d4603000e40140004080a08001900d0615596400ca040c80d0301020703081032040030040180481e01402020780c09800f0304103514a150401000541c103005013070b001125580e010000405544031680228200000105107404065850760400c1c043d41c002181110400001c0d00426030403030394450a0360507291289070ad00b6503040301ca0a0401c040d0801030017681010b4840e144d010150300e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 141624262 1250 141623012 141623021
    0x120f0210030204060305090d0f0f020a0b07170708060a090b0a090c09080f0c01021b0102011d010c0e010201050c180d0602040f060801060c020f0405180102040b09190e010b030705070501 81
    0x6640e500d0250300ca510f0110f01a086801c0100340c031080340c100000c107011140d4840d4401e00101c14a0614035508440c0c41012803800d00241c3c4c1c024400314042c0c080c043c02d0f54000d80c0a00341c840400400d000d060b46c4141040340c0c1c040040c2c0340585c0118620b030017480156029044084011006010300d0465940d804804017956020302c14400401d44220090205620500c040210302d07100d0390041000a05045c0001e607503110000c6c0c410482c016210381c04005a1003900040038072550013a400350078801c120542d500815241c03034600301040c0340240381a4035500600405103c0c84141d0003d50411110b6803030016010902a0721035440820b15550400040340d07840680b020303004c0b902400d20002c1c208440a090440c0681140040c000041100c10051b03650841c0303c117003010280d07004940c1c1d0b1503c0c0380714041c041350070305007040550000c140416102a618003500e0300b120300311242e4140310201801200d200d80381c0d010b44003c6141c940d005109242d5100021500401c2c2450200d1400c10031341c64403030849 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 141625512 1250 141624262 141624289
    0x1140f0f030405011b020309191205060703150608061002160b0d0b15031314010c031a01050903030a1b080c0a17031303080a24060f0206010e01120f02 66
    0x9503000c4180001d000c400d1041d40e100a100784400c1346000103115003c1d580740165565588200405482c0450309003000040100514484901161154140c60981e07122403046030140002494203000c48454042d0a20340c008444c3c990302c807402d5984a0303500340103102005940f00d4003903104070035400d940e14140003421030090403a4680395495283e0039964405035080b81501902c100c440e0003495140c1500041240c1d0000000551550044000e103807003030a28640c0795020059500e001e11020000d0f4241c1c0010301200d19480c0c0603210004c04200540d02c501806480c0ca415500c10301c50300c450103002d1a0a054500c40c000d451401d640d0345542e0340c0c1010742c01002c00003400c2e00140c020008100050465540f444581403c0e207046103841003c0030748007107104401600700325150010850b03c0c040355000700080e10703c001a4a0868881076543d0340200302a109100000d0485450586203501c003040b002c0c180d8481003419070159107844950310020b0604001a00c20000c1c0494100041ea510090400c51 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 141626762 1250 141625512 141625537
    0x11d0306161e2109020307090e07080a0803040b090a02102006010803160f02180601080901090b0103030c020f120601180e03030a05070516030914040903090501140f 72
    0x581049000405011001c0ea540b00302ca44081e19032804180c115600ca400848003e450f0061141c40b40c1c1120301411032094041e403d401811000b00f52002d450708442003025000044500301a502c055041d55520151006030000006201003030010310300b010104d0308204d0300c40442e100f16003a0740000340c000003d95a804082540c01080c3c0025191607440d2481104500700904001e40c5056082500c03440358020110310300100050980401c071b0100e02d8140c586030042c0612807490314544c0b00e06001c80c0c0541c0c9a901054290340011880300301401009902c0d5070000c0c9150a6918540d0140d600d0429500101e9100707041c860300075420f880c0c0f00286031a4030843c00082000d940f40104861504900006400e0200e0501e01c0700ca01d04000002101e800482c000800642c0c0d81c1c036144222024040c0592005444101080172000d040c0e2240d64841611801c0e0400b05070b81c61100c08000c00c40b81107110042c0440c0400a00304005d40c000e162107421180071210321413410500036075070485030f8084044981c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 141628012 1250 141626762 141626791
    0x303040f0e0f01050d030c0303200d0f0b0d030e1e03010c0c03140909190207050a0f03091d0a09050309060c010912030e1015030c2c01050d02011d0306 66
    0x15007428581540b0f00410701624090004001a10010060b000c0c0b0607018003819110a42c19100c1c2106d0703210b2003641e078400201e20f600c81e040744034210090490180c03c12145810407513482c0d21468103683d50070065900d40c89422240001e00d080c05050002010798400c3d5221000040000e500c00380101e003144030640d5142c401e0610030b45000b501c0710a842151948007a01400a00300359102d05606c03541164a100700300c03181071704000d4a000607110304100107000d07000d0f030005901040100065903210301d109884003a0748030f445140e18108226181a0a40c540100c1800b04002130140d900201c500b5000e5410b41e0702c0d005241010526507800601c42003000d0b07646000e1802403215002e412004580035250901403001600305503030b56403190007440c102903036a0b0480c2c240141c5121024800660b0f1041c203002c241c80da030380d1140722000a414030b2440c181884104000112000c42071070380c16168000e203501d01482c0c0603001120403c0118425040b400640d00c40c054480e50200406481390f0782c040000c14 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 141629262 1250 141628012 141628021
    0x319140d0203401104111b0d0e1305061809030904110a020c011803060504080909070903020102030f1b06010b0307171b030705130b0c0d08160e0303040f0e 68
    0x52022500c00180f210100084600d2818144003d5a4000b550001091500c1c2c0c4808000a8014903148403c0a19200300040710301d41414041280d401070200b0000f5200e00d60040e82003510f0446c03040c5240c560251442c04500e01c0c42c2a50340c042500900064500c040c0050804802040504280d41c45803443d40041040001d40c90680182e00e92041d0b6212020b0501543c0d41010703566285600e0540d0600030700c0342d040710b000f101300131810b0b00860b040780c0144114142410b0035400341d03001c8c031103160282841c1030020744228000d0494a044a9044c1d000314644540301d0700b4410141c200d0036401e040304142a1060044490800025001e01910100140c3e641803088000c1e052201141c4160380442c0c5001c01c102841c60407492920701001da03407010550302d994599045a85110700a080d030154002040045182044d40004d08010350b0108212510540840420b4401038400c48203400203451500c0341441582c40307981034240c0304001900300c07030500313841e00420000103546400c0021000340200030030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 141630512 1250 141629262 141629311
    0x50114070504170111040e0601050c01020708040302120c0d06020a05220501180308040308070609080d050103020a050307142803050c0118062304090905030c0d020319140d0203 77
    0x3200038900c0f210080068441d8403030851924003452203844030481d0310a0010b00103034020740445010703040c0400210343c0e0b900301e85011401c680041c001030740110640d002c0040410b10000d066030405000038210181002196140f20103035201403c040c0070400240400c501ca00c10b0f0340c0c0f103c00c0d40c00040300c10002d4607013004c00041c07041510080340940030400210800101d2481c008503400d8980101e5880d9945201d410300300064101d550b001480c4460000307449036002010703030000f4180c80c400c03103448418a940700708060381c5014500988040c07e0691030840b14070724100f210804904940c0c0d402e904071540c2645427640383d802a51066486800002c00d01c2050340c3e221243d02035269a00c0400301c00d10b810200005d0283c0d000714100d04012480c50b02044809031034005640007494844024020444149006500c0b5081035141e400341e84590041c00700c059002100362a0441820310a01e00c03101c84c52101141e680003080c1e03080307420320390030460481c02103c00c1c0011403244d010a100701988854000c3c11 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 141631762 1250 141630512 141630539
    0x30507050c0609100f090b16060f0c120915020a02100c0215070c020103090b15040509071505030c04090513030e01030605400905060a0e03090607050114070504 70
    0x92032044208010161169880c5880407055441ca40340c500214045c0100a480c058016009610740410205403106031400106051010605c60b080c180900d400c1c1a03841e000f960390f1000c0503804141c4040c100000d80040354007041303c1034041d0045060846c4540007140c00c903030001d0861030058100481c1c1803180b142600450100b000700703100a01c41c00b1180c505200000d140602000d080288032410304041d03a00c04c1e0031106032941c0001d600900c6040094035042c1082654042c98001c03410100094001000428140c049410110b0800c44150041c038040f038181e40005c014084041061002040c01300103403107000e10820510150821686050038090401c00700c0d00102410182802d000780225254010785402e00d03040d0f01154130b0070000503415101c00104440ca65211900e0101c0b05445002a40e0082c42c0c40780e0261040c1c460684a416182069030380d000c0245407564802c118448090410300010f02000780688000030fa14000f000d14a112000d0566912000a00114060140781c1100300b0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 141633012 1250 141631762 141631783
    0x103030815010c0b09031c0614120a06180803040605010f0b03090d03020a090e0411011b0803010302100e10020c01110d0914060717030406060f03020102031207020705060703050705 79
    0x101c050004a028000070030742032204000600300a240000314007030580c00c100340c80d044165051250700c4075807890b400500900c140c1c40b50040080c94940e682003e4106a01c00c8403841310203501404104003240c55000180c61402c1001640484114000d00464803487c065030146210348400b20350f40d454007603441c0d003152041e0004400030008205102c000403001840c01e01e0741d0b810b818007603254000200c041c0c58018165128101d00e050300d0302000b0070481d032034140416080090b02c6e00c140346699882154540d031300c048801844c440702000117001510300880380d07032015170861034002c585420050214007405601150301c0c0c05a030101440c0c1c1c2e595a000401c810300c0310003040003411000c0c0c0c0c0030710060408000d03100c0c0c2e40747d116001c0d00e2440c00c0d803103010480710059040501a451200205020309030355000f220241c3d8801d140c01d0022400752912078168040fa601640118204010302c0c095180510010386180306610940c00d000030303a0f8031000c0207480302ca40203485540d2558070342c1c145036040210580d03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 141634262 1250 141633012 141633031
    0x6040312081503100e0304050a06030506030106090e0709020d1b0804060c0f17060312040602060406060905101403160602030702040608010c051e1c0603060c030506090105060c100203040b01030308 86
    0x24a0502c858500190540341d490742c01d040400d4100140550908522850700901e40156854001044003901a0401c3c3d000e06c82c103500804c40c0b1a82d40501600312400394803180c00c642c111010402000d0a16006881c480c12210000660316801265105020040c1032500012840c11070800c0203000403407085000d21042810b00e04808104503030014441d150010041c5007a50300000403901a4504002503060f0550400b039459a80e84c80d840060b590315812a001c5840e94100380780818594271074024180259070018002d50400e0030304c03003010b400174804c0090a405229418000500541d5002c00e9030003040c00360040d560701d008070700510040e10102d4121040d903a0501d4002490a81d20604540d0340b400a02924000500b502c1c8900d09940306807401b110341950083d46041d9041150ba00841c00c0b223104500030040d20b60764400130303801c1d181d0803203040da0700ca0440d6004012038201400140b80d03200000050f6100c0040d11401d0030100e0300295010f039141d03040c0d4401401050f412140803900301d002c55 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 141635512 1250 141634262 141634291
    0xb0102010c0c0b0a0903050904020408070f080a050c101101051918020f2106010602160602010b0918070308031512060f060f04063204020f07200604031208 68
    0xa444a8090303141c0506105011a6640f0700d001c04c6c10b1049082c0d07031040b200284295030f01c0350f0794901c5660320ba00c58024440e002981e11800210b9230000a84032400c254083c01500d219141e0324200004412407261000074030121400b818400c00007881041d00c1881c41e00c00000e0045c42030050036003180c800b084401800002f940355140542d4950f2000300e68000c00b01c2e0400c24142210785210381c9000b003800103428603c0340d10000702e10305801081006461148580056401e6514002203003a50a262409600a100c070707804034006500c001a016901c1e80100221400385907256604400c9500440c0c0c5040c007007864245943c0c442c44c201c2e169404012a482c0109100d00381560f40106508002c4c02592190f20041ca515860b61201c2c0c0000b0024150010410b60307540c4011024503034005130f400b8000c01e002c0700b4650020103241c80c0c401d4490800c2a031180c00e05100140d628010300c0528070800c0e28242001c80c86001c669504c4400510181d48103d6a00007007222892000e09030003c05895401c0031940c2c03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 141636762 1250 141635512 141635537
    0x16030f0204080601030b2208030a0b04090323041d1008160b0715020720091006082e1701020a17130b090a0302060606030103080316090510030b0102010c 67
    0x43c10b941502d0b003140d480103054980802001c002c003401140c40d9080075902c0b000300140130241001e18442d04181400f440303540e03100c45c108001c83e0b00d144801000300320b405030307260000c010003041c01d804000404012860a80c5500201c00400403914410700045158801c00a595004214407002000300000602c4504000a1201d5031084103008001c940703c0c0101307001c02807101241105000d1210a081159034015500745011446204550725010102d0b000107040304d410030100852240c614a4401c94140381010801c4132407180140a6641800e510f4881503000503242210144481a5000c4400e8051404c1d0709240540e0b507060403000981d20500c891900307581c00c42b0f0309545412224003c90030f02d98940e0444540301c448407601415203040d00381000a201d10008501d0800c030300940840e107466803448200030082c8024000105003050500110300000720782d560b490b007103c1140c20038024050701c94010410140e82400000002030702c6842c9480d00d0350b020720458040c040d0925100400650 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 141638012 1250 141636762 141636779
    0x1e03030708040503040510030504140a0b060607050a06150305060702030307020304060509040e06070905030c0616060b220f0b041803110309040e0106030308010b0705070509071716030f0204 83
    0x80c800e0050111000000c1c04010090046030040c103402442038001d00500d070801001450100c404880c198050300310f00403480c400040540410350f0150210301e4594440040c4003c41d004610102c0d07942c450ba00360180013814902071070226250806a0902103032642c186140740c03003405004a019500300300706110501d9408021601901c1c454117085a031100440c01082c000d084907801c00440c2d015403c184455180c3c00600402201d200f102181d114014501c208502441226000e0640d03112030075840f000160203800c5441140401000c90611041d0303955240d440d4210a0410344484c0c1c0c4e41e00907a5180340691048a501c40c101350340c1007100700d190f03446105503669480800781c01d210710b0640c00584075008008072083c3d0b660150007401240762044801d4040c00305808202c1c0455200f000100344202c0405c00e490000b6040001005000e00d80030910000c0b207000b9141c41c081102000e038001c010142e0f4a8902c1c05107407a9403440314188600200103080720000c50880c10100d00402003000180d1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 141639262 1250 141638012 141638017
    0x15090604020d0c090510090f062907020319030f030c050d0e010e01151d240a030803130303060f08030a1103070512030103030e010c0c0e180712051e03 66
    0x290305492407003070b078542e41c104040480c0d2241c1c0985641030a00c000c001482c04564800f500300c4004107400d103d80c5481c1c000d1502035035424044e800d010026405004081c03000f603c580170129000c54841c5190440035001300b401c107900c41410711040140c00d0400300400d83c0c4140e405003141308900e0100b100d100a2100145148a001c1c00c80b1042d07a2140a000306002e000c0d802404a0702c0ca010007041304c1103501003000071000c014815501d1444640043e403440c042107000040c840d100c000980d400010440c01d044800306890280389410041141000c0700181c04040114050200502c00126075641031400505842c0e541e040b61406140700c0004104640780001a640441c0032400c081c1c0c01148804107031131950280640141803480340c19844081a1150700007181030703d01039941c40c220010b24a0042d5403910500c1e41c0100703130300340030441004500540c201403500a100e0701140ea00c6011221a69441c04841d80c100c03090b0850024804420040d04201c0164208a194141c01c003038800c03001c07500e4907030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 141640512 1250 141639262 141639271
    0x40e0a060b0f07051507020c01120203070e1e0d0b090d110c010e0316030305071a040203030f0c2409011d1b011202040303051c02280c150b03150906 65
    0x140d80204500f4104a02408208010025142034002c00c2c907080c40000d58610321001030902080d1440810180b40030540210303031040c880e503180e051640c034010040c800f08104240380c16990510303010040340d6980d41c2c0556480814001c65040d0018200404036a06003c91407000c1e0062000c141c02d42c11900c40081903080640d01d00342804840310800b840403a080002d1b422002d560304d072800c903000c0b08254006002d007100d503001e04800012950358813049a001074003510003030b606030300c1409416800a03d803402080c0d400d000c0c00603101c90403040ca0140c0c000a901d00303110b040c125000f01c10008c5800c0c09108070303070003003581500c51105d448800b600c40b501d4030340809020311a64805803030309015034042d0700211010f4400c00411581c4695074180140140c2001034081c00da99904c0844880d070340442c1c000c0d140c180080603041c0030070710055589520500b1400c0e5406080c0040020324801048001804040c80000800041924000c0c20300b01401c114580c0e8000e10b84914039424081600c8000030074a500 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 141641762 1250 141640512 141640537
    0xa05060f06030703060e0d0305071701230607061a0301090f060c02010207020607030e150c031b071706090d09030c0306020711041b0e101403040f050d05040e0a060b 72
    0x4540710030001c80c0c1800340b55007010b09158100a50200640c0001a002d410502280c1d81081241c8a24000316039440c0460042024031404c10b00502c40d1102c00303200a107152020f1001701081c40501000703c0e611303130031a82c42681d110b40d9075568103d400240801d20840c548048000b003100143d69960000f42a101e2180940003541d42d0000c00c003098000d60464020380c0d0003d140b00c0e241c54a40c40d0042440f40d032402114048c45a0240a10480458070709072644801c10304069824040410217814110740d080c20950628401c20200007500c41d0060071418000f140c0303d02030440b5141600c103883c036100e404072218041240441041001c28081e10421094a0340700c0005030f0354194030b00b040700300d101c0201d941d0b41d8050310b0420b4046d000c207410401e510300208252924490740d0920320402000c80074051061001c00d1a20542c1903c1003034481c02598050b1089000d403410044079200c00d460484201d00f40c20200d070000406114060380c1201c01c4d54803c4c0c0e4a0014000375003060b441c1d0703041c2c1c019034403c5000c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 141643012 1250 141641762 141641791
    0x90f081c140414031501030f11040605060d05150a080318030309151309050c04050306060907021c05130305010c14070201050904090809030d031a06040e040f14100506010f020a0506 79
    0x2a999402c2c80101d04200c5810385c00c0d501942c40341000304e28080303201000c5a19003d400c0212009080a01a98046a100801807410b00820401c0407019000040c0911a44401c2c022590740c03996503030850f0405804540d004540324113592040c03c510451040341980710f94020b00004000341d07160b401504460f950244069203400843c00040c00404440e0408a03420381000104403c0201d02406041116007c60880d4103c0e2030301e401703020300c1d140107030f0700c01005800c46880004243c6203038540100742c0105280280c41c1000241d03506985900c5c2c2e0700b0444d41c0340d44513503220b581d0360740c031002c4440e20701072140f4141d25101035980060204e100e80e003001c50003141c5414805040c4202c50007560b84402c1c010b0140d07206400201d600030000c01079020741040d10008441c0c44101420000151b03820f4512000c48010540c0315901c2d01e02c003030708560b00101c2d0b5940c40000c0c1c40403445c00034440c8a0750081d03480404620303803c02d480054800321031000e1810131948a0511440440c400113541904031244586259 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 141644262 1250 141643012 141643049
    0x717040f080a110a050c0907051201140a080a0b0105040c0212070b1302100206070912020a05060921070e01050d03080712020918010302040501090c02030d0b01090f081c1404 76
    0x5070b12500c0e070f001c00505801506120710074424040b8082810080441d2482c92036601d42c00c3c103641c58020141d5910410407004010300c1800024010810340c180002d0150900d2685c5114003460603580c0407040701c1000444004010340e05050154070301d4148540040c10441902160f482c002c0d000c0c554000d003002001c20b010500100d4842006103503e40c0180081241d15140c2401955800c0c05840000c0040d08074132000545440420f4030705030f80e81d0700030b1800c2c410502c3c0c07404010098100450150384070040004440034807096400000f0413a941d80007810300b01e480c1c24800e11242c803050740b0490190704246007040010f40c2c0136080171380c80143e904028400b41003402403c80240680d50220b900304c24640154142c825504021504032442110140116a261f9904501392002514040c0259005021403030526103241c10606010740c041c1b40091031a580d64040312042d403081d501c5002c3e80d402c025485114180c40241c1000c441e00c1905008840d450b0361400f0040314880d034444d40f0810710500d010b01 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 141645512 1250 141644262 141644267
    0x11407121407050a0507170c0f0310060f080c010503130303150302060c010f050c09010203040608180601060302030105031006050f010c0204240501020714030c27040503030717040f080a 81
    0x10742041644000c4544401451a002d540c4075500c3e4003d071a68031460b0800a10401507821080145a100000c2c2030144011018070a54041c503d0400b5030600038440c0c1c101030f02119104d1040244041941000900d02d454041410076403030013982030400804200b040b040b802c110031813888081d410302c0d00140c0394542c50b851440e40f41d042e420017503219200055810101c041500505601121207000700200d40300c0320942c51291183c0c00e0081d0160300240010000700e8007a01da096400040400188450740c40e8081d01820408240c10002c0480d501100506c4182010007852858080405003000f07510b00304400a03d00040401d1254100200c60394104210348503a080403985030612504840310303080610440214050314000e16006108401e00090020b8172590050a4440d0150103442d420a02ca4140030404201800b00540d00c0400941c14000280007009036110380d00641c0503548034200810000e04070850042090031a0351041c00f44004a03200c2c50913400010350004201d591403501e003005 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 141646762 1250 141645512 141645527
    0x112030c24050702030301170613080309070b4e0c0c03040801091a010608060613030b070e0111011e020d0605090c070b0a050903180f06040b0c070501140712 69
    0x80e0750308074100070500001c07640000c041c40c161081c0d608044c05011a200720380d0741d210001c444103200705102c1000354010500d0000216084504003040c0c462072a02d030405007400364400e148944c2e10f1155600520050700100c1c0030389c03080030030b9000310400316001008407110a4501000c0520b2003007904002c1a103d00380b4004407102e0405480c00c1c0c0352925174590955000700809802910031107a0744141c21a0300c81c0e0030703d081c3c0c10303100b02c0e460b2490742d078580005000c05038108040c052112000e440c00400800d062042c6144680825a6102c5e12440c0f1400010328044401c0c0d05105903a04040e111003842a240100c0500511100d00c0180c0b82c1e41c00014190240c4055400107802c902c094040c84140050980100742050046c48000d005440301c05020046400c00c41d000389194105104101e540d1240350b040075160f100052910317085e0420400001c0c05035005a019180c40f030390009001c0410441403056030002d080900740028000040c100c948210b104003000140a0742840c58080d103003c0c050b1070f8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 141648012 1250 141646762 141646823
    0x10f030b04090614150a06080919150e1204030314040909030f1b020a03020f040f05010618080d0c021504031a0f100612020f0d05040602070b0112030c 66
    0x10034002c0100a040c840700030109070044912440710040080c8445070040201d0304e400c0d01c0601400c480030f2030030400300c500d45c0c4042e00d40c1c26a40074504001e1004a50b03080e80410b00c500688a03807100f1210902c5130421984007801801c081e421081901e01564903a105440c21240c06080100b18244000300b43d101d14843c6810210000346008400e800b8154440c1d02e1311048602615a18145028003800c480f8020541c5002980b04008001c1400103082c500c1d15070b40300080c050000b00e1070880141c0350b01c2c00e49102360045d0700042c1028003498180208185050000c00c0400c01a0845c262136900c0140f419031680c0307011b8043e00904580b03554014a41c0201c1d402181c2024400c1005018082c4c61700c2003000c250785900d032580c5108086042c44240000660403113480d500d83c020f10802420b8128040d401070700101451100500c01cac102c1c00c0006000d000e2107940326103c0143d07622260b162010b954241030b0070842244600c445840b0011b900f01107603483c0703283c0100c41c2041c010107201020f10100403c0c0c2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 141649262 1250 141648012 141648019
    0x516020d022505040c031b05090a1701020c0a03020d0912080901080702030403050a150605040e0d0e1206040506040b1e0403050f0f07110913050a020d020a05030d02030307020c06030402030c010f030b 87
    0x2d9210a0706a061f84811007800000c0f007078441019a8050454041c058070100c01d910484031802049100c080414140800042c0030001d41003600d014030660603c10742c1c040540140e00050401003150b0b40c0410a60007414441580d242103401e6510341d442680200702000741481048000300c0c07003a07402002034070000d40d031000c200e80800c800c9182510100003880d01d25045507040450106840c0f8003330103450072890340080100305a04c90000704803803407142d80e0500780e000f804070016821040001d102c054891406030004141b142000d181080b90041c000b80000e80d03900d08035202d1400451038090312034201380c043c601282c0740c013540c4c040807640d82324254100c040c1210009200c402c1140d0503240c5240c00c1000c81c0c2a80b0a1f070348442c609000007801040c010300c82c0c0c0151410000500e0700980d03080c109130002c1c04c1c8101c41511030f00480d1410350100c2c20000136038004001c2200b00786d8100b280006441042d6036644c2181001d5000c01e039a034154a46140c1846071240c84030944c64403981c032921a000009 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 141650512 1250 141649262 141649271
    0x103090b040219150908060115051204060b030a05070e09070f120302011d1c090513050c0903030a0206040c060e0609090406110a0f0305060303120c0703020f01020d0516020d02250504 80
    0x160042c2c80c0180d11b1040303650900418000140d580120140d4100340030aa84500e40b9041c900308210b491079600803c21203e0550361038001a1648040142d400214407501c001c204484c140358004084c0c500040050840c1d612411081c0400c1311420b00d4039044550160010440c0e8149160a1b809098401c3c1c000446d845a8200c80e5000480015220304092540300c008603036107058402215a81040c2c020703281c100360300003040c40d80105036900c9181d01240e141202420683c090000a003958416034660380168400c1042c031050149000d1028010403950601c0c0c01805480d2010030940c2c05500034103841420854000307402d201c445e4208a100c0e50281c004256030304141840580350b04151010b03c00000e20f001c0018400e4100002102c00414500820903450390b582038820358180d1280308218118000c1f400c001450b0b071001d00180116085d01c200c01301d00e40c0303000601c80100b1110f4182402c01c640c0704990030b5010a4010031040c7c85074036000007500c5405940490800c000391150b02054125150 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 141651762 1250 141650512 141650549
    0x50d02070b0708060d050c060903010f0c080f0109090b01030f0206070c06053006040c02070305070b180409110105030a090c0312030e1c0e0409080d060e060103090b040219 75
    0x1110054465001c40e10f03044600d0b1550000d2001540e04007a0081141c2d01029012803585410009064a8080103002045440700b50886400756441a0340310b20104180c0e0050090b8a243c55044a001d0b04001c80d041025000503181c0344a11001803101429501c00307220001d082d511744200301c0320580e401050380c0c0c03039031540c40800400d01d41c0401c02d10070568840c1c140303200b0300707440d006002001c0703c0d0031242c1440d203901d4100c100320092031b00340504001d5200e00310000001501c14081c0350010f00002040e1a2191281480c80c0c90118507031000034407641c9000d0b88040000c01c9062140b018901c02e28021391a5a01d00d4242001440e026070f0160040391244d200004000041d002d10401c0c0070155402c1c80a4101781425070f0340c0d0325541400102d000481d00601900d14845c2c0d400c429480300040c0041107141c207585648540d07a000068600307840752160410312070b00b2044076110b90003090038a801c001d494000d4480075400d52002d03200a105d41c0040004d406101c00c1c03800c684011b0001030078034200c1680d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 141653012 1250 141651762 141651773
    0x13050a0b1503030a0818010212070206010612050c070b15032e09080703080405030d0603110a06080709030b06040e2a010215010303030b0d08160c0506040b19050d0207 73
    0x90448030311038101c0070040030a00905020040d1041d42c0a80d44601400e502c0700c044036220040c0e0705a07150381541d400e11041e10804440451140240c0032a00981000c0d41000002002408044010403200c0e0a084c217000d20160400c1c00c4906a0380c001d030008480c0d4590307408103158914548491070f45440703200d03007181403481d038802c80c2d00c1c1e18001003100b10b804402248015041c0c07440707208040c000d07190a11505021034050442254094440c8003a03078940094440101c0454116803c1607488440d9548804018100306030100d000e4001c5080c414030b40d107000980102140c4480c00000c2038a0100001b103a100d0312036400c9201d4040030700003038404000410005012000c651300d01001800001050310205500105400c0801c07060004490f41c16821914181c019044204040350084541480d02011880860103841d5000280007640d1a10f8264205a12195810b030000c500c94042007200304080004c58048681c1c0d05940c0121380e0842200704010340301402030342c03045902d20b40002000c004004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 141654262 1250 141653012 141653033
    0xb0601110a05330c0403120306030c1403010f06051c0203010b0402030c030603070914070825120605030303010f1a040b0403050309040e0a020a050103180524160c0b13050a 75
    0x90b41d4100001c05aa80c00c1d00911040c4810741e182e112135a4200000c0c0b0214001c0c24060740998418280862410380d240d5a00300754080e0341d4005854440f008000207010301e02805a00000350700d80384140030107801c0000098903c3c0043c20401048200c83d0404811500e084d005840f6a00009000710744038980250701000e254000c0392090f1003030040c4c60700494a0009440394420302e80300203485e4420740d5220341c03095820304000f81c140c0058100030692003081c02007045010955680684d5002060022105918240d80c02c94115901c603410a1006105052084c00400e0880342500c80305044031034200f580481c184581d4001c88800a0b00182c0071042c4200080144540d0700300703690411001c0c005902d0f8503145d29440300c000b5800b40c030019040000390300c45d07000a1b44000c010728241c0440c80055079407920f003402c4a502c111365000d941c0303070301012401c0a01140358007126034100c00200c8144000c005000080c8030400801410032040850b010110610841c00c01940c04000c03a6000701d041e003011070410 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 141655512 1250 141654262 141654313
    0x9020309010b090709030f080f1804180215070602120a020c070506071a0a0f18140319081f0602010509100e030a03050603010908070317060103090b0601110a05 70
    0x641c2007910050040c00c041d07204910803c04d6a031540c0c502c90840d80c91179110032400c030f029a81584140649060304152a005041c03942c00c0692451000e1841000e0005684904004030260128402503001586812100d0f035818200381c640c603a0b85101034a40700c802401a00382003000030070150300308001c00c407090307000700942c503c000110f40f50385603a80304100c03192281d9031008001c004054500d4621030080388407260031003030940d408507030940c1c2e00c92624103c4d0890704004640c500042000306c1801080a10592101095406545495038119642168086107060502005a21000580c240352081104c0729001440c01030140d5560f03964100a018000549103218140100c403a0321038031240a21501c461072000001075420f00022901c164003c1070000d080603059520740d002223000800c0e1100401885100341c0b503540d44a0120140340365240d000812044c181441c200e0441d012034568030320310ba4840401d2030545808841ca000242c01c1c00c043c000010030310f1283c41c9a01007801504045101c81 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 141656762 1250 141655512 141655531
    0x3091b030302060a110432092a030106050901050a03110f030406050a060302010905131e060e01080109020901050906010e030a0309060f0318060b01090b0703080103030e191404060b0301090203 84
    0x44002c176040e4118071443c410300c0d10000c4031900c0c2802c10361402e211900c40c241c18000203041500c0440c08104490811907041c240a580d0300c06000703844ea003680c190400e518007024420705540c10101d004e4254815004920306001c40441c0e01101c080c030942004842c07003180803c0030b0320740e854415040b40c1600180d4007111000d0070320000070800003c500c81c05080342c1e0143e652001007403901d018020703840d41403420b0118194031201d10407141d00811000c905c8501500800198981c500f07040d1902c80501170b04041d946034100001c40e40941c4d90380710340906443c01203c00281d2501c610006803100e5010030603158150107001e40c020207041d0880081d03412a0702540f0b0f81103485030002c01c12011602d000b68a44244070030714114201044c06070f4031000210138181405403c140d12110440d802c0c3d00404421030028089a0040c400c1680c800f00740361020200303903104044103c211b400008010010b000b0081c0740c3c20f07001c03070611580c0c7d25a013042d4024180030750705aa8039611840040065442241d80300349 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 141658012 1250 141656762 141656771
    0x50a150c031a030618030d02030c0406080112080d0c050702130f0c0c0f080c030f070b060310050103050d121e0515120709021806030708180303060303090103091b030302060a 76
    0x110700c652031420480c01e9070010f01030300707040e69420001c407500b60788081d0201d0341d440309006110520741c4c103100035801944008202c03034445182c12001418010160007107a00c0346010350400c000030b41d40409440d59a8003102c004201110726030421140d038025a03801035880b9014442d01e0901c1e507002c3c1c6c8000b48641c0303009000d00c41000140410380381c1001900009000c00004040c01002c900040701400c8800180000d0303c0c546070311400c2000064201403402d070b031130b5400502800794601e4100800312202c0320b080007d10140d807560301c2c0c1c1c03500c44007216000d8051108201207240703118a554401013404641031131003074074025002d084900500301282d41541e0004080e052940d9840c20104500c44601071100422015007880110320107508001464254003120001e0540710b5600d0310040d40c410441666070400710f03d02600400d01d0510b143d500d481c0607804c01c005201030341d1000700844020010030300300840c3c2a03a1602e8203034000500081500741c05a0613200200c10907074007080d03c50080914031700070311 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 141659262 1250 141658012 141658031
    0x9050709051b130302030312010819020109050d03171302030c03061302010f020f03031602061005060d1104030204090302010c08180a2a0b03160507110607050a150c03 73
    0x21600151001008000d9803051480121070510080420f901d440c48803142a030369a501182c0f40d80c00c10540841540100d41c011300040108002c01e401042c40080d0342c04003140203400280c00111701740511030041c0c1c031200014003410b01880c1d40c0141c1c00108401c1510304d19107401c290000e040108004ca04c00e01441c501c800b0940b03800628940203100d5000c0c05254100300303500548408002c21008003d40c0038038030f54103d0010040c80a103101c1c0e01c01c0c05040f0108909108024202032005150041c00002e03042d050200c3d44800301a1070220078114000140454958002ca41c18041c0c1e42c002503000d41005902001c16134190400c075020b4599482e0702c0010340300c100d001700624500c40c1c1010026400a8104000700f002c1c01140407a11040011036002d1040741400c0d1000401170390007030800504008207111200140b00d254004c03140492400909180c00e03565155079030560304c40c01520426000c540c01c401d110085c031001040a912140c04841001031125031005403204c242c000000c43d14040020 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 141660512 1250 141659262 141659279
    0x4050102070b0f03160c061107060c080702060f0703020d020c160b041a180907030e060603030f040e0709080a03020106031e080d090c0f0b1e0a0507031202120703090507 74
    0x103d00a0102c803440c542142d66007450b0311644c6548621160400000b5141c0b2404520b00d445914074904168003400c0d030360b8142d41802810344a07500d000c001004940801c20041310381c08030b400c035008201e4403000e40c01e030348664100310041d020b80104c0e812410300c00940b030031001d84001000c40d0321081a070a01000701d0742d43c01c00d000081c025803046410300308540e034518405190440041681440703807004a080c1c12503079008604000350031140d80e00030980d6201d20303000c04102000b0080c0d01840440042d441d000d028901c0c40030500492240300c20000341c49020a690380c0c00f170401070019285401c2110b10007203140c20001c1c080c01003032200381c2c1c001c014180c2d44004110802202c0c7c0c40f0681045061b8902000d2000e02c20040c04064002c1c0c6900034002d034081000425490f000303000344041581180c8a0b08a44568014100640b141c802165020019122100e4000c42690781c0c4039098103010011078418441d000107407254040e0060700c05490810000826015400500030034012001c81c0d131816111200c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 141661762 1250 141660512 141660517
    0xa05070c030c06020c07030f06051015091a04090c0203040f05010309020a05220606020703170405090708070215010e010617010503030919080132190903030e0609010204050102070b 79
    0x50001200c0ba014000410000d800a108040584086580040d03a0391902040e60078035550443e81e031501c2d481480b032a0000c003000d00c405049120403403040c1c400a9107001e0001c1a041c440e10b00034445072900c5407500324203c015a030003000c14010520521920000080d20782d4454082d404c18600c0d91440841e040d446403085040d49940074001c000d0450610007046043c0890281d005440d25a80340000b00300c0c1c1d01401007a0041035150001e04007103046143c0428421030300181150f0044080c002040b140d615400400d402c400141003103440c41e22140022404c004410f07280100080300341c0c0c0000f8161140c040c1050494800b5a02c3c40c110740e000d00c4c4100805402031142d81d602d030340309206804c0a0301e40306030a510719000800030854015a150640da0070b541126101150380090390104a0a0b4000c600180c40e4004240c0d031400d54a01e4008078210f00b0b8846411a18802c681e1051000f08040c06540000e0010380300c0c504903885880c0426809010398000d009107401809011400103007078142c40107 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 141663012 1250 141661762 141661787
    0x4180b090c150d0b0a080d09060e0906090405030f1201050f04020316030b03030d0612020103050f040510050403051b0a02011805090402060c1f0501140108010b070f0c05030f0102030a0507 82
    0x2c1104512410114012a0303003101e003010b41c00781d6950048054554945020400901c84000a0902d03202c07200700240c4079035a07541c00348061103040c0007120704942c1c44e1a0280d0f03011008841c40403250701d850500e20314500236007801c50705000001508d882c482c081d00040700e0403a40215803242031144003105110982c04159010a085200c0400c1c151a090081e0407c0e500c1c8000602204d0030150b006418030240c9445501058014070104940c6065582c140a1240d0241a010b0030419600f080d0b9941e1743e0b24080601030343c031440d071790702c000c2010036101d401140c22106540480e1019440303080000c1b0344445a40800320f004c10403000f001600d840c0100b100a08480005291060715602d0740c003407103540c2c1c0c09428589814003441c003a0074818900140c06005c1c00b138000b50300190b15814104c141d0300d140e1007600d003141403041c00001081684490340488190710340c41180c2568030782c9036191603590345645420196040c059108900900c03c0150701640c8240c003454014011500d50300001da88582c140381 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 141664262 1250 141663012 141663019
    0xe0f0f0c0909060f1306140a0902070209010b0f040e0118050603060919021315180218061804060b070507050d020102030316050d05070f0305070e22020904180b090c 72
    0x1000454501e046030142500000261104d844a80f6240b003905c2110140c1e008500c205a400c102e0b05031504040801c403018044000c41149403903d2030300020908141442820ba01c00e500085074810410f84a042d6401003c0001c041062540c403a00d911a20b50401000b00746003a01e004000b03012072400249d51402146050050448441c0400701d6140066003c8403d90304285103420305414100184141000c0c8980060b6000f14503040a1601e402c60146940c4514070a00510070700d803031081040c001c1d40400c881143c0c00d941d100006100f0102e01c42000c416a176026250010014244007104000d00c0c095204205454045441da410050420b030405006070050380b0500c0040e6403500150101549050320b801c1507810030302e03c11100c40a42c0d004a81d0040010030341404410201c0d05030280d00d8200e2007034100000c5541f1040d01044600212940c01c2c0c150354101c081001d04041e09604490000d10041c1051212000d20542000301035000c640c2100d4510003d000560312102c0441d003410b0048005 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 141665512 1250 141664262 141664279
    0xc0201200a05160c0801060e0703020f0f160c091a03030f03060f0a171c0f1d0105040902030a0207021906020a08070c0e070906080a2a090e0f0f0c09 65
    0x5038111250f030010503d1190b010409070108001c40c1460b40c1c4038006103011400411900c1c1841c1480b40000c101034072074000c0c03500600c007445410b542002529002000200c0c070a8881e4010285c800c4140d00030040982600184440881c03000d4071908080040d039810f510100035819442d0134190390b8810107042050304402030001c84d01510302005c103a90380da800100401500c03525109001030480315420754845d5940f000140f4181481a50501607114003642048c005807a4080c0002c1c020242c01d100d03003004214282c0082429a01402c15075000e0300404008544a142240005000394410321045c1d200f1500122a080d049410000d10000c3d1171080c0d0141c5003d0642c4d545048480d000103000300c0311b80840e00000300300c4c0c9000c0011284101c00941d02c400050303140240c00313400c2036000b82c2043c0320681420721510003900d82441c2e04240d4100c0064000c02a16625012075407400c3c0c5400c11a000c1030a1405d004041c05040483e40c0212200800d14000392101e4220000394491691069000b0020 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 141666762 1250 141665512 141665527
    0x3120f0d050a0e030301060e030c0f010815060f130825030f0f08030a05040b060f030d05070c0f080a14060103020906100210021303062f1303020604090c020120 70
    0x203640120b07400650181e4003050854a0343d8a40f42150070981100340084c0316914600c409140400170302140c040c0c1075440d41604211040001c0403001300910781c440d225909403080302c0b00e40b905001c41e114001d222084c20b84032172980b554680307607805600c9010b003544030300705484100101c1c2c2e101203000319408604401341a80b45542d070b41d010341a1401c00760740001080c6040808951440010341c420507501100003400c0c40c11389090340402030082c004d18000c0030b000701d241465403000684d0b000104954148113440361414501031503070302955080032802c5148a9000a076280340040c420710802d228a44e5680f600c03103540f02155441d1000d00c0046d611460140102c0c0c0c00e824481c840040c828401d10507141440801034140c8c06982c803460f180c0e0b440313640243c020402d2010b03d00ca0264120071b250b080e2130304079840c035000e010340c0355450360002203140c0300180c0b03100d0745107184400350002c603400b802198445945151030401400b14290040140d420000308a20245405500c081c52160783c4121a040401 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 141668012 1250 141666762 141666787
    0x30417100608071806030f0b07081302010503150f0d0b0613020315040f020c0607080a06060e09040201030209010c0b040c060f050903100b01030f05010906080f030c0606100903020907080603120f 85
    0x340c4d805071081d5039a03030f840c0403000c0b8608007500750319079004111011007420054030040c04004c0041c8018903102680c1c00d6040180e81c82001c403a042114944402c0507170740e803180081d44690947c0c0c040360b880010720170280f0400c0009004640f01c0c80c82104d1040e49400c1210b0310206910013203a014a40d88100c1e06511214540b9030700c00203900c03d03046001424254903100c80d42ca045402e56a00c0d0101e40800b04001c250501405980040c0007d86421074260084030007258141c02c1c09480281456000304074280564880e419100750f040d0085040c00c0181010b0403d84076510160103188009401f00380e40741d0001d4059000c44d100401d0150080400c02c0c040311b400c10041c00801410350425464400c0546035240d28002e9501030308403c40d00007001c1d131a000c200d074503142c1002d02845e01c0750810b01c101e070321120010410b40d0780301c00240c5106440d06400c3c90f0440391a205500020745c01a07520302481600d80e40b1882c0c1900c20581941210350880003036401f4019401501e0000c8007280003041008491030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 141669262 1250 141668012 141668039
    0x10204121b03030c1b080d3504110613300f02010804050c04020a051b1908030a060b0c0309210a080d110f0705120f042603041710060807 60
    0x5c0803485400c40c0180c0781c90105007402c100010400001d100070000034101c0361445030b010750070130302e0310341d980b00e502140340a0303200410005002410f4003050800201540d1150002c42e14491110207a0155103515042c03102c12004464403482d8001000107074070001504820050303400c05400541d822a0408607600440c2e618200401c02c170744e60f0090501d4440035448500260400d5491a02d5854440d91b010a40380241d40001c80c8007041030b070010b10b16080310f285406c016448240c00c0300c5e1a55036607865181c60310180180381d1003000d458000242e0b0a00380c00707000c009045250130403102c0155580c0903c42c40111251260036591540d040211a000014800350081c109840d450101250840c07444440c27980b99080b240f211340131540006030b1442005000c3c01500c112406103500107003408843c1c91505058052806100c0647c000c4441060700356006040340020030084d407080300d40d92911344e00105102c8440108107082d511446d070034506c0058042c002c0100391a6054001e100c840e2a0482081720403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 141670512 1250 141669262 141669293
    0xb0402030106081603020112060e13050f1002070b09010b01140a033903090807030e04090605010f14090402130903050d140f2401050306010e03010204121b03030c 71
    0x641d40c480c1d0000f191401400341c60040c1a5840e450408503103140000352407101d00d02484030340d25150071400d22071b10350403400054002d070700c080e0308296900b4180b030701a10b80400c00888810521840840a1500c1020f4008100b0544980c41c0c8848544a2480e62803ea83e00404e030b19001c2034680c1e60030b1901100207409048a0003262901003001c0700080710b151800500c107005142511441180c201c985c01c00024140c0b40c0690500c1c082180c0822600c41440d913006a980c02403c2166100d00080e0580e165000b140301d480d04840f0401032940d48070560750310340342c03a4480c01c01d0400080d80c1036032940c0350a6011a1040750050b150400081c600000d031401800c501b0421800d0100a00c420140b0008910640854100040c600c2d40c0c0c50070085504250078000901031200c030156190350b80480c40041d5000300b940c1e02c003800c0035a00c81c4c45520040e0b44e5002c0e016032440d010341c408500001d01740611041201c0e0b440c0070b41c0e81d0703501e00480c18510700f47e82c00f150b000107008181002d00000015000c0703400e030300c4036 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 141671762 1250 141670512 141670519
    0x60302180603010315060f0b0913060503060a0b04050903090105030402190e0406090302070b0c1e011116020f041103240409050c12011505060904020c0d180801090804030b0402 77
    0x1a140c0080064900c0d00280c005880d55000c0300e200c400000f19500ca02c0014025084080d100685861040308492054149490041d24a8003c0f4101e60201e508450090000102592840d03d89680a90010940d200446124a085c000860340c0c030600401140c800040695410b85541d550b0340a1189188249600301c0c4940f010320000100011301e401541c1c000e45c411900800c1034201820021726152264103c42100081040442900d00002610500c2002c650030325203242e1200322091801480d19102c000d41640c40010175a54140b04d2680070403416108445a921004085081c04105c5440c02c0c1c00803910380d010008101040450840040745640020100108031003407000315050319801ca408030340d1540702444442003880c0030301544a04458420007000381100300c0a04540c41c040a00c0742a004800005922501e070312560110350f01c0f0040982141d01c00074500200802d8881e1100310f414072261a550701161610043c058100040c0d0402ca441d81071501355103546444100282003243d2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 141673012 1250 141671762 141671797
    0x20d030209061e03040b010509070f0806030c031609270b041e081801030b010210090f0812060306070e01140d1b0e010e1c031103071703060a06050c07060302 69
    0x700b08518042e030f01a9040e00d00070040c1c50b4181864640d02081040e04024444c0100b0010402120340c0036495a103454802c0c904a0390076155000464209503070130304060f80501614101e9455401968040c070100e903844201001003009081384a0400d0101c01c5a00c08020600303071601d00401c0c080844243c1080c00307008401516600c00c411883d00b1366640c4412581d451010070030248090351820309000070102800c040c0800410800001d4884040b20800c1041c1c582d03600702c0d5028041c800c0000c0300b42c23070303070003c6410303500c85070b5044651280c04126038a0303110f03102c8c0400188800d88106a048500e000c1a19040d503200d0400d0444590303500030704a4075000942d42c0a0f04013075102002c1c01412030310950348a003e41403122200041100d0a0b00c0e590b207000d0b20b080c00302450701d1080007081c0d00d841d582500d000c03011503403c40c0c01241144100c45026116410782c44403859140f00c1c0e500150300030101151081200c40d80c1d07030002d503060301650251211075007003440100800ca00070b4004110258010780c0022 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 141674262 1250 141673012 141673027
    0x105010f051b0106030b07020105041a10030f05070305060603150411010c0501021b0d09081504050a0b0106031a09070e0f13020a030f060504050108030706020906040e1602010c050a020d03020906 85
    0x18500024210082c6030746440040090142e00045c05401403181e01c024401e074035180d04c60180c003c940040318038540c881ca000046403002003800c3c4501031a800201c40108034524104950b0b20740907400140c615020307900110360207190009010303c2207a4480441c44140d55070303132030b950f044045c40303184941440100105140095428401402003130781900e6600402c1c070000091a2910151454000c203200100d00c041c00000c2d40051000a0b86119401501070b6a0b1686401801d1a1803180c004011005c1030f00049401a0140c1220f41c00d45e42e03410401440c202c10740208021800162014000710341110b09070820b41c00c14081040c0100380c090041c100b00e10b60700e004441240d1004003484000b071760f42c1e0009143e201d1030b805080300920080350244015410440d2580e242c0c031030b0001c0204040d82c0010034109540b144001d8034024041d03800d150003603142c6440351051104680c0801c10055203000c4000441d075014a003541c00b0f4030302a500034207841c01000016070095000700e4100394004828860030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 141675512 1250 141674262 141674287
    0x10e0901080a0c091505040b190305070e0702030a08040308040203070b0301090c020106050612060d03030605031207020310050115120213080307050d0203030106020c09060f040908090f0114030105010f05 89
    0x80c020000c40c4000e158540325030403c030030700e840c8a03005440102e06043c50411160201003842083d00c1044500062507002840020485e03100803070003d00915020320004244080820100100e91140900c1c3c42255501e0004903280e01c100b604040c08241928041000b1a22030415207038010705c00f07800c80e50043d4540810901c1074000343d1102003407980300c04040c1e14195080c0a013a00400e0300f40d506504214250704110321810300144428003c1d01c01201c01814540b0a0b000301000b413034081c060b100485160760a40217103602c190403c2e40288515070514500c58042e2058504032410003400100d80c0d0014181254690050742c1c41f00b4066409000103142c1c2254100c0c418010242c4a0065036240d81a20303181e8108031501c00341509640041c001004002d0300440e0340300d030108040300d01403a140d640100148080c0407240304c480e0050310b0000446d0410154500170038240504a600703082d200c9246004461903220300e074130f119000e0000d00040160754020643c0700503180490034500c1c207105000f41003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 141676762 1250 141675512 141675529
    0x1021009080306121606051e0c0d0318120e12150708011a04090207212109021e040212070f0305070e0d17040b180906101b02010e 57
    0x241c03614640041400220710f0400000d5070f81907110360181c010089458000800140f451064500344540002d01042c0c01d2000107001c016101140091703030f00c5264142525984401500904000c02e1401d280320080c04000c520418249902c518549031584001c401100d002480c045010740004107940c000098090074031107540b14501e4069543d82900e04518001c100340ba042e4012194003d02600c06d04c002005081100d06542441da805640ca041c540f6207409400c4000051604042e90101d40c2c010007a8000402c4000600301c40300d02c400c030880103400204481001200035448a6011114070140f0344030110003400a000800040c1000307150040f00c0d114074021104030000500040310401f0301038051141941000d4146031051103001d81c0004103a00c10003481016042c410b442030f540c03000d0f2943d203040f50090041c110540c0d46400a65100d1241030740c560a04500c10320300c9000050107400e120317824091860303070ba607581d03490001c4096a90130402c0c2c81c600260b042001616030700483e070310350080 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 141678012 1250 141676762 141676781
    0x30412061401050607080a11120d0203150a0b09010c02040b09040b0106180f03140f03040605040503010e0c010c1707120f02010b010f02030406031a040606090e070c0c14010210 77
    0x40410703440d15166803141c00001c160840c500c00c1905118100220b60600c058a4840809061500341400096100340c83c5c4102c0391141003c1e2800040c4041541d0300540256000b10041c035000e41c00c80303040004014140c41180614103031a00144101c8030607601c9001d0000e08079002410001e01020144085a00710104507020703524541000c0041064641c0190841032001c804074070507070005d00b0254a410310080740d12003c1c104000e400e41481d04204148490f0b000b8103500c0f82100da03100ea0b03903000030b0110342140c0301d06031095103020424440090b02040b0314510f14416519503214105607910207851400300c05051103a04011b1010303100045010801001414035511000312a94901c24001e0a60306124441810040803c250150305600003059806440c81828040341080310001030060f0065400394042d4080c2c24900002003250300700e422902035665101450f00c85035940310342910350008080c13000381b0710a00c43c442046070180801e407003103107081d051040d00d490100c2901200f05403195000b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 141679262 1250 141678012 141678023
    0x5032701060305250f0b0307050c061503070b0c28061112090c010c2301090b07020715050f07021305040303061701060302010e0907020c09090d170c090111030412 71
    0xc0c0208070725200a01c10381080c0b1904c080701400d80d410200045010b0700c0030b04c115022140040089480d09000c0d809844d041c18000701180d480d4501a0034840c4010011982203010303000b4148046000f1a000d4101d804e0111020000e000300c90100b10440d03c1c0550b12582c980d660900c688801000030180d010340000442d82c800e1345501c82d2039103210800003240140400303c0139400800340c4d412030798008140020264200448007103074666000c0610180950f4000c0002c0c0b9480c1c6440c14003000004000240100c60726422101c400c1d481e0764400742a984612240e0307002c00c4050040c100440b510703d0003807010b103101900322100c445850100d902611000c1c1e500700c02080e100c0d10b0621070022048509010005600e0080c08000d20310b4002a1503100d00e2038031071f0302500c110030010303c2c0d4600800c0001500030000c3c10034101484d0029070340d5101c0310604041d000088008041c8101e801c2240d5070140500360318092180380000315070054904002041040c00381c1c0c00240710008401c0c0c10b1500c0e5210070390042 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 141680512 1250 141679262 141679273
    0x503060703020a1803020d2301020403080705010b010c0b0c0c3f030601120218061216020a0b01150e0411041403071a0c10090f030f0f05032701060305 66
    0x15200500907881c0f800131154411401081040942d03a40c64101c080e15402c180700c201c0341c45c01030000482c400000c04c031065496000280020400071058001c00600303003e0b1000300400307042c50b801118050190711000d003042400340c000c101c0715043c0300020710550b00c49608855031f55440101c1d000054443d04d0305240c4078a0224401020b00801d8035110b112031103008401895490700d04000703003184200c59400c0340807079804290140d1124032005100c400c640010115074445152413249148501d0071100d69101d200310030300754030a03240000355035130f0050344c084a412500c3e03003003d0140710001038900041c0d00300f000e0040e0394071283d02e030f034455031122a20304214556950304024001c900000742d2111180030390300c0444104014000310b801d0303960401d03100c0c40d00c3c1d5590174050642480c001e41c120210312028900900e80040018000000254600c241c440c010045822441130310b0b10314000016001050b403c100080d60184480108241c0d60040382d80c2c04169441e03001c10a003160f5403070304110380b1036010 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 141681762 1250 141680512 141680527
    0x140111010222140d051009020a030204060305031c060e0c0a1701170f030306061812030a08010905061807030c03110d060812130306050a0207020910051201020f030f0907050306070302 80
    0x712088020b4882041e503941340b0705003642c3d0380c8550f030f4418808001e00722a65141c00004564403110400700035a0010000e0000c2d0307445e400c016440307034450070b0070001c17500b401e040c030030250038003401030750111104000e042c03049541e081041161540001050400c2240101c60000f2511400340d40c0c0b4080c00c2142503040309080c0c5800c440d40b40c01000000720801c2c0c2d0040c03080221641c0c3e40390440c2da08054545041850079000008520b00f0322020840350f41c1404040340c034080389688820380c98102d5507455030034003803074a03141e00707210a61251000c1e40c114410004c1c000351425001f604000e4114040f480c1c0055082c0c07141c01c4c9112a504982210b00210f40c45c0d10042259500030840480c207170002c4410749160000205034032180180a12005280d5074071a00003583c480c4c07a5034141d500075030b0082c150400600c0d100240628003803583c0102c501c1500011000b185403c814170a1728000c10101100381d20759203900704070f200b600c1e030001e01c0302c0c0117807141c00004121030301c1c180310007402003000340c40160b128041c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 141683012 1250 141681762 141681779
    0x70c03020907020c0a1505070b010b03060a0504180b04051906140105120303071202090901240f0905130f0908070605010506090607080a030603080a02070915140111010222 75
    0x5071002c0c0071503000800400256840003841004c80303205401048a581d01c50303000b80d0340740c0a0f0481c0541800a1080001b4001c0c0071880154441c0c80d041b1450f59802c0d40ba0f0b0108801c94102c02034401c2211140b405070070010711040c0716103400038010800c840c101d21400306150036410b02d08004a400546032555526605044107459024107422583c0140110a1001c21380e07032408000d05002c10802e0104c0080f940141d682d0448010040c00b820a0003550703102c8820803100341948000380e0041c440d001c510003c4070f00c5034402045400450b50340300416440d050800440282c802c1880b583c16075a00048100c040d070511421000900c80c504080d22540d842c10400100c0700305a1120b0700500042104814550b24102182c6400303034454515500c2c0c0001c280c0460082040313400051000750001030360020b0302e0300003030701c20210740742c200084c0140f00c031106082c140c140240c4030302d2840078210000d109242d8080c1c0380140101f0400320005081c00301c1f002c0069985081680c0d0107981e0301207802d05011f0000f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 141684262 1250 141683012 141683029
    0x10f03020112050c120a09060c080105010206360705130e06010803120a240602100b060f180105130f030204060611061b042606070908070306020904060506070c0302 72
    0x51001020420303481c1100034a9100e1003140b07917443ca40c1c8481000140020500c0d800120520341041040001e4031000c43d01a1041d00c2c00e004890140c401c4000180003122201c90050305c00030440c0301200401900034904030b10319540d000100781c2d405100400304080d11039404207440000203080c00b0420309c824000302410440103810070492a0803c00a43d01c0620000400d182c110901420000b82068080c50408800b01c0c03900390002945003130500002d54a034001051500c18002150800c121000d8800f000124443c2030020340c0030000903c88043c0121400d02015500392040c10443e10b0301d0b404c21300c04119011242c10075a4a007030021402d00a5003401e1149902800352801d1822000e1804d8012542c0c07107a0007041e505005807040000c281d0b610b8444d080e130b401810b810a80c008070984c0e0284d0074540303040e0103080303200603c9400e00150780c0c076111740d00b1201111004000f904d20981552550800b0f0b40c00001c00942042d210100003d1340c1e21000002c0c400301d405450511043e13401d5104114040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 141685512 1250 141684262 141684287
    0x90109080303010e0705070804080f0604020406050a120b0c0408030d060e10030b181c110d0c02010906030c02070302060c030903010b2407050c040509070311010503010608011517010f030201 83
    0x150301c20300041c01080d1032440c2c5181c010685007025038a0b0111450402540d01c990b4004a0540c0607100502d441e001000a1550140b8400c883c1442001e031160103010130303503519200d5410004c001040003008510f034050b1158000c141618040d140513145c00649165511000041c5111a1b035400100101c3c14800340701504041c081c02d014490714030b15155007804000140ca50100c640070307144402c695620801140300611314503284081c0e0b500c980000642904a6290b100107a1700400c0b040c120340b070b845041d14901720359058440e04c500c0d50804008500400c10b29134031900f90310640b45d000c400340e600e41003d40f282441d558011a80c0d85c010b4010316081d00c0e10b6800a600807032440c11a140030410f0321800f000259040c544041d141c008504006160007491549070740c0080c68602440780301c07440443c42c01d06503030103800400440000c650045500e48801d100343d2000520b6940140b0180401005500c02e84030549801d1004090000501c41c0c40e207401e90095107606200a001c10455801002c8124030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 141686762 1250 141685512 141685529
    0xe1e04050c040e1816050a0b0d0615030207020f0303090607031107080a12020f0706020c040c0e040501120215070f03111606021023060108041407060201091e02010c0b131502090109 79
    0x61506d44400314449804030300400d19440c00101d90903548403c0341c0e01c40310081c61501b2511b80300030b850356006002944103a10607400340c585502c44040c141000012502c5607000503041624058103901c040b42c04140040c2c40390031600525200180c4141c0800100c01c046018038030480781c1c020a44000f0b45805801c1480c10b200341c11000c420071078140c002c501c5451380c3c0310a03540814401e80305141101e00070070361150b0562080c60000085a40703040c01070094012482514a00500c0480103841442805002c40003480841c9000c6010f000030b218038a0141c215885004668940510075000203418296420400050380b0040082c00d00c501c56000d44040598401c001198900c007541c801d0110510081c0b066040c840d00e08081070801544c0130451007400b03841c0302034581d07044d11000020302900302c4042c140c89404ca42800e01051070740d901100e000c1d05038140c65030307882c1c0360f100c4c0e842c04c1541d40000d108880c1d4100041194010404c1c060503880380645030900141d4910410300090710110540c3c00c003040 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 141688012 1250 141686762 141686803
    0x705010b090601080f040b0a0b06041202010207050118030809010c0b13060b0d021324080106030506010b12070807050f0c01060807091401090906060314010203070e1e04050c040e18 79
    0x364590745d50026034015401c02c0b0f0103801951551303003480c081c0c00018074054200e100002d000076202c8064140d8070341035100340d00340d480c020354400046610824005028104210b840c10420004078154000c0c000901c3c18180307030760650800e48403040c210000b210102010701c40c11040c281000741c0340c0320f6095450303000c0340e8501c3c0040c2e440d00800c241401103036010f91001ea40d002012411020038000c0000c0040000303645001c41d071200794603030203080c99200c00c0f2070501c914030000c01e40004050654460404000002c14580c0d103440f803c0750442c60281050080c80300404c00320b00c3e244815001000d0010300240007041c51881e002646141c0b0240382d102c405820700e010030016036400e20600c401d04540107110040303001d5003141842c44c014040c5600060602011440c0118800e0044d0059807180450b501da503100103a1800500c01300c100c2007500c40b5001001c500e81c8500a2a040c2d01c41a005151820568246501c800100030140c4041e40d01214040c100c0c1c145450440b002c004824013061041e40000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 141689262 1250 141688012 141688021
    0x9010608011a03130212100b0609012c0909071d06030303181603061a19050409060b09090601150c0302061303020a20040b01020102030906060409080f0705010b09060108 74
    0x40d00080c0780301c010344400c0b41c0080800c1007161403030760142c6543d070001c1003480192001a003903035481100121441015051050300884c03482c041c1d080e1803038010107854547e034406540e00301401e45506200d200b4000c4280c800302d225981c5074204d800d407282403003200074004581028000002d0f1120651404e0241c03000c00100101d0791004802c0c0c80d0410040c0d0302d0850143c103049045401e12400d0f4802c0c4040c82c1403001e0020070321440d60040c99a18840308103d00b1a1740591043c490300346144168111203800d15081042182403940c098208603009980000340f0786588000590005c40c252213101c5280d026500500c8000c80d845511458181c0754200f0842c1d81403650f034003a460390001071901c41d01c3c0703400440c540d040c58028040c074480d25a020b504038218401d881c062515032a14407000c940645c1c60b00d03815501e00d50051003264000c058020003400c9075a1003204020280800c101c04035005403040c0480201d802c00c08020748507082c45140045003c038124401c0c4001c04400400150411100d44d0911 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 141690512 1250 141689262 141689279
    0x81501030f0206160b0a06170606030a0b0c0702130209010e0d0b07031d0607110706020a081902030705031318090b041b0f0b0d050a111b010f02030a0207020901060801 73
    0xc59400d074161183c03074440059079000c0462811804001e4031011301c5c5010072001101079840b1409454008403624000d41c0c518400030342e1018101c0f4001d42507800300e02c0c0350010500b14551154404400300c0c01a16011480e8003054a00d140031254050950b0040b42040c020340e0440c011034004201680c80b10250000703521661440740015009206142d51081b400205940d804098054030086a046031940d00700400001d20018280c100115503010b40200031030010b10204000003c107070400036841c104071034076810448001e015407002c1d0540c80100041400141d003800070b008030742201d81580001a2820310303102811800c11418001c190b02d07140030711002905558800781c125070081c2c034081c2c12100c00c000e01941140d003900014021207001100103103c072400c500070031030806120003e00061321040e00b48000c0d108010700d102c200700f5003032100e032910b030608406400442e0042c500118402581060020407640140d03850410940c001501c0d8055040040780207005000902d0868074039071410001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 141691762 1250 141690512 141690533
    0x606050c0d0c0f060e0a05060916140613080f060903090d110f0402040b070302010f0603170d1119110c1c1a09010504021306140108190e0708150103 65
    0x22000c0c480c500c80b0240a02030000144120540d0004040060304a810400d590750107010800303c82a125010024000da540400c0c1591400c4001c11800119805d203402041c09602011240c2e4104a061000080d140c600b00740d45802441c104001d046100e444140803410702070300038111882e80e1b10800c540301680d140c1041e9883c00c0c60300032008204040000000506903c400d0002c0c40c0c0c8180003040210703000f02400001c0075032901c48e8000300b1a001c0c00d03180c1d01050391003510024041c205c3c09600e15081c402d00c0e00c024002c5040040000a40c6012960f41f404270360801220395000700c4620704003008003600070050014220a01e0014007000c0c500f08001401410000b0541550607124004a000c1141d521500100d0036280c10700c16013289001304520b0300034501190141d1160140c20740c100e038090b25520500056543d00c4000b45070054000005603409070f40680803909160211203510700519882c443c0c65911800600030f07002c6503240411f01703031030030340bd0625960904005c000108005401800c9 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 141693012 1250 141691762 141691783
    0x150103030503180a02040e03220e0109110f031003150e0709020c1011031b0703050306040209120604050a0b07090e13061b051908090c01110708031c0606050c 69
    0x403403c48414000300e010341803101c0701c100250068141600d06a070410044064500724090302e079902c42c04402c5640c240c14021161090038819030b0844018000c1054a4000340d105071060300b02c05180c01c0480303208000b2680111000e05002800c000c00f4030820018008517140500d000200740a2400b00c106400c2e05d407400c610541d500241e00044024182d5018000c0c05841c14a640d0f04101800e213841d401c02803a8003c640d00041ca50180240070010761091096502c0c0a81564a1a06685d02e94041c00000e500c0407243daa84541170700c6102104000400005124911030b1000e04150360142c64040d4108001034401418030a2a500c144540e221003926654401101500b4501044240c00c1581c002d0240c1d02a8040451000d00c5c000380b00354101300100003002d10740e007803501400e102d04011580c80100750f60740c81d5190400d428000d1558440d8000c0d20400c9010016034514503500c490103851580046040721040120112181c0209034512901f4010200e0b802e100e840e00c1c400848036502e5542068 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 141694262 1250 141693012 141693031
    0xe0d0b06040e16030516050a060f080403091208070308101211040f0e070303022e020306031e0d02100603080304030c0c050405070302190c020105091002010b090f0108150103030503 79
    0x40b41d000900d6010020f180c0c02d0340c03410046602c0c003902c07400c0107511003002c1518040038445c00100001c15003425954441290b20300c0e0f44000c0e00e80340c003000480d07803814050025020401101c82c08511400b9880d80041d059102d170100c240d5590492901901d166002482d0304000311014000f040892f84103a050f4911580c00b5030b030042100390880c0041e0050201d18078902c4e502d8601000102080000500c5000740c9001c0c0e0211914070060342107072100d80480302204401240542c07604406600680c01554200e40000c040d166240b13190070880c2c038140d5414042e8800b07540700c3c00c0c841d6105078050010101e05030b82c403c000d210007802c607242c0411034440504003c0c100086c0b10a100305000c000c0380814040c0c0b03802002440b181c1400e0310f004029402803c0f000380b08840440002041d0740c00b4048101c001e6a040c0c44042c2041c0c0344500300300e01c03030042010394415552140020b0010303566410a50f031040d00352074150002035042c040c1451030105003442c003c0380000c280c4010f0000c40c4d00001030340e0b8041d903840e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 141695512 1250 141694262 141694271
    0x305040b10230102010f050406061701020315040209040f0504060c031406061e0c0a1101090602010b0f060d06080703230703030c061d0609010e060601050a090b071a0405010603030e0d0b0604 83
    0x142c0040b070040c803401991062032440e010502040040030b820810441350011159261803943c0f2550318200e100030f03a401d52a48010070401c5401c1e0a0a4024050304640200000f480b82c140003518000d4610880d400c0710703c01c0d59001459140c1c0d4040c0b180403c0c480e03c0c0a5001190301c5c003200070071b41e1803203440d805010030b01c00d549007488261105400c88480c05514011354000c5180351134103542c0c061070300342168013150001c14003040e440d10500c01c0742000308006000c05000900780050080e2588039004020045031141c0000c10082e104100301c0005510810b074401c102615100b940802610131107108442e50402c010810100c3d038480344451400d0f4001400003001d21100080065000200c83d10707003000c2c00354908001d0322460642c000107016100009541440da80c1a00444d190310814028001041c2a01003d0005d10036041c05000c0c02d40c0f04082400c1c048c080b1001860241e10121070854090f91525003d04c20140e00440180c100300e8151010b10300c507602c40d56030b0600b02c2e100402d90383c00b8540e103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 141696762 1250 141695512 141695579
    0x2c06070213061203020c01120b09040b04020321180a0b07150204030b040506040516061b080c030c25050108040b04110402030a0902040b0a030804030320030a0305040b10 74
    0xd51202c0000d01600f1a1401c1c0c102d891301d00a9100c00080c810b050114048045a00004041d4081d003800c4043c0208450041d0382ca6036514000840041d000b0f982602c9000780410318075000d503d080b5000e41d070f500a09501d0382ca45011580c04070920046032400b508110104100d08030440c8207403070103517512030010354012090100700c0f0300a010b0f603030015040b40f000e102030105002d0003040641c002c5000360203035124000c10441c0d01074140020700c079a50002d81d920384d00c0c114041116110031a0581300784041450f000c42d0607a045c0c51600443d02c0d205090300406d0440c5041c02c41590060740000d29065185800c0d890031001a10791940200090004110500003404111102c1a0310500141c01001192a07041461002005002c00a02240514030707007071142c000303850156915030403603511040e810329145c01c0d9076007150214016103208240e02c980c81044443d04101f0b2002e8038071001c041c1d80c00500d0389000e046c01065188040c000803250f00d40b59600703200c01103102c1b01003094880280c1c0c0c0010301804 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 141698012 1250 141696762 141696799
    0x317071e080f030106030605091e0117010b0a06090602071505030a022b0b040c020a08030c1e04060305040c150c0311031303050f0606090f1605090d032c060702 70
    0x20842c0714954614004004640315070513a100302c0950344c1c2503c946820350341c0c41086844400e40c2c0610080d0701d003074020041005407034800090144880d001d001080a00e0300e0300120b1509155504000e010030a400020300c102c5504002d0003005041001403c041e50031401c40103040c80c80081c04205074540c001404404551007001401000310b604d244083c5440703104451030b001040c4508001f44568206040110510b00c00170391401c00b2030f0001c0d06149036072241805019143d00c90290a0741f03c40352460720403c0c030845400900b0080400c0d032000f06481c0f40501e80140460300c0c0d90800180780e4058440c981310316501520145042e94907041c50310500804940b500d1450080a0b110385488010080c04002c005020541200c2110000203c42c002d860b000c0c108102c60b81e0480b00c00d0b060320705c240d0000c5e1010b1100c074080c010b0510701d41040c5160490703110101e808240d450800f60080745042c0a00d5035140300288802c005503022041100d0340c6610040014101e01c0340b42d4001c0d00c17038820050002c45801 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 141699262 1250 141698012 141698017
    0x30a0813061d060103051009020603190902030a110a0609140108040305040801090305090301050a06050904150207081204020a14180603010f061d010e1501030c030b0a06090317071e08 80
    0x110741c42c0000c07030100010340c9540c0d00c40d030900040350b950049020700d808202d503500075282d019600905583c00c1d40d80d41c402e44802d49031031340c010100071a115980e600140e10700b4002d40042500a0210320b031892814010b00105560b20b23030020b403c10280394802c000c034814407180400403000901e807444040e141c6090442e403902071508940d116500c0c004100080581000c010034600c0401e030000e00c2580c0c3c031041d101c8203e422a100c1e00307030490302c248006030020304040300210210b940c2030401410400036407280402038100d12910130240007c03509001c00d51900b004454014042e1a4801c000119084007041192601c9210403481e500c0340b2012900700da0302034201d84c40d08810340c03804008a0f070f52000c24000006030500880c414050003800881c50308804007003c5d11441c404903001500c00c2c034580044000703107040030224082558400102d10580e030349507440c071300405d12542d031240003d0450522540b0252039446420b036000c82000f801002596866112070910801d200f4403402d00f000303003000d09452 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 141700512 1250 141699262 141699281
    0x307020114070c021e031f06030507030b0f18120a0c021002030a170112120302120c0a02070b071a0c190807031802031b0a0e01080c0909030a081306 65
    0x1003269000700b06070503502c45407942d0101d008035072244a00c60000c220030a00c079403a460f40b58154002c400e10781d4000f0604807013828008511200092007540c0ca4850604001d61340d0812506070740524280003440d1090380390a07820201140b0200c014944100d032050b40d404110301c0b4010701035400b04035900041c2c0600c0c0404d03200d94024102c1d0048403c0220025100d03070000d401e000108040a005000031040f40d0070982c181c41180a10780080031a6031038408160046402c1d1a04050b000c000011801415256041c020600503098580b103c5003524041c3c00c000403504803104440041c00810046840040344041815880350380e10402d13220440161060711480d00c1c2c0403004240707048040c0081d540304006600c101c00d03d98040100d5101d144400c805e401c2000c074082e41c0344d40b004c900303d0b00c60042d15405018803500103280410060341c5003080d0728003800c00d81c485185900881c5103a011b5003041d500156005105101030f5203040b48540c00601000c9000d044a0300b200c03001c00c450f00c10010f095000c034021 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 141701762 1250 141700512 141700541
    0x3040803030a092f040519020706061701021e090105040317030a14190c02030c0a0b0f07030b031e0c060d1d070b0f0c070308030103030206040c1e06030203070201 71
    0x1c80c42d1440400024103500101254003001140300030000031040b03000e03212462034541082000d88107070710030071001c0d000c082c0128002c030b2029000340d180460903100501c005407041c03002240340787c6000c001ca0000c408400781c500480e401004442c4040d06034000c1280c1a450800380c03d40c80e4982880126500d01031900300074900980710042601c00b0340d048000c0c6200303400c408014044811020590045040e050301d00c2a110f005000f07a080c4142c80542100c04000700520403207040640401c0a28a06000c0e1142603c00c0c80406040c8014000c81c1000c03268464450b050500582d5070080100780d40703007103d51003a19540039000680056440900c1002040c0d00001d042c00e0701c80520303000080c002c00d08c14070518110584000d0700601540e000c138012080740c0681c0388103810812410300600040d80013100e00a158040c0c6540440081e045001640c0650b02a600a0001c3d2030246032646441d042071f0000d070303150f8166041003080c10590701440c10507190245405030301c0380c4a5000581c058914110800e91 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 141703012 1250 141701762 141701767
    0x90c061b01020f18060f0d0c030e0601120b0105030303041a040f0602071a060d0203060106030e07080708010608101503110607020901030302010b040c0e0f01080c070519020103060e060a0e060303040803 88
    0x20100c0e000018101d003002036040c13649840c07148010041c80d8420000101e1400f502408030041a601c56402025007203e541004109003046840e01070420034260007150a15a001d80b07040c00707020741040303103501510341a001145981055120502e4240c0d5400301d1300540c0c007140000508202551240a985c0384e4081003d54441240c1e1500420180062540500d504074450000c1c40034038110140c101c030180c01030060107050342003280c01c4000e007006c0001c0c04c070700380f01c0d01000054400c001c004401c0205401400020260304001d04d2608101c4030318548140c05d41451900e05d06000c00308003090850b5480200c4403071010204001c20135900450070003a40c004110000003040c0340e019040041901c204032401c20941ca1800380c01d550441c5000b003510b401080b00c082958403940207504640d00700102e0004982841c2130340d501c55152481c3d0070a40d0440c82d183c0c01030001196010300030344003e004240304036031780ca280c00e10201e200b0601da84900080065581c0100300107032028000c803809081e805050382d9 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 141704262 1250 141703012 141703027
    0x302091918140a0b0402120f0f0102040504050f01030c180f021b010c050421050c210c04060b0306100329181006030903050405040504121106090c061b0102 68
    0x1c0c030018030884260350000d6109042c040001d804241005904d900840303240c05921a03400307000e24001c031008840c8482c8036000309003216100030010171640c1e401040c00903981e18106410700c0190340d00540b0b014807a121040040c000280e0840b885002c4d1511003c14081c0c00c0125095403004d0486a01d801d001c4c240300042900700301f45030410300b502d40e03040c0000a000c001a18602241c05125500c07a9055800320f2500381204501120030001e2541e005204941c81101c0c1d80c0e0000e07401c84d010550000155000d01c010001c00501400321299100c1308880c2002098070f0000644100e12000b051184a0b510301d0303854481d800d0280c1d014198103181b05119610781c2d44820a4810246040c0513042d10a00541281000240709620f0051103100e90011310594a450000c00354003602103e90201c060180621000c61940c441c0d00c1040e20a90141c80e4000e0f80e40084800500202c02d0085128500e030441401c108495000080101d032400c03007a10119030710301040e203104031400582c0d84000c00315400040d004 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 141705512 1250 141704262 141704291
    0xc030406060b0318010501150e191e08060105300f01060f170102090105070213020d110712021506010f0207171e01020a0c03050315040c03020a0e01140403020919 71
    0x61180411300200702d2643c903000c4105c850600039410100140c1c080b070b2090181d041141c2c1c01d009410060301d103032164a4444403e005040105914690301ca200c200301009400b2080029a0040c1410360721094035550030001500481036100227102e44800c083c080d501c80d000100241c41c2141c0003940204285030b140c3c0b4105410034003503c1a45c09244003111000c07618501807080b1801d085058460340d1404000c0e500784044046000002041c00d036080c8aa01ca5415070350141e0482d0320324078107000b41d4603581c91400c41c950580b03421640382154130800e00180999070800c0301070340014007420844a071901000e800c924048031600040c0c010b10b84014110076562000034208030444691000c01703e41810f6026203801c038041c50151381d000030014800d02d00841e0140c40299003010440104111421100b0081010b840b6404d103010300081d40011101c101503442140110301205c2481c000c0b00400e5110312810f640e01940c00041e109240c0034011030480c0c03044019005400d200944280b18041d0400300c50b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 141706762 1250 141705512 141705541
    0x80d11030601030b03070b0a030c18080303070f0c0510020f0c010204120b0112030e1309052e090b010306050c0909070f03051012030f090b220e070203030c030406060b03 74
    0x24602103814080742c13500d1494086403031400d070343c0b03225440c601f4844030b500f08402912944c003240040c07040c28941900074410102c801e070b0107800a50b00950b560b0034080c0d0000c00910030020224100803190800c080098800b199604d25a01003100140c0c07034080407803c1c01700341c0c8140d5001800b40e610008000440c5084400c6045206004a4902d40143c1e80d42807901761010110307100800040e056280e40100385441d62103080c0440980500180d0300c1c1d5262303142860300c40d03828140e211810041003c4504251b100340e241c9800c002c0c3e05000c0c4010806d594864138001d03810701006040e29242e000203185030000e4401d071003081c3c0000748804c2850400034009000441d042034850b0009027448005921412003c03a817004450202003142049402610216100b6203084060004c0049060000a4815100d0b025082400a03507008201c0c3d04204c1058202c070320010781c0081191440081007140c0030750048140c99000d4a50030740140da943e501d280060090143d50802c4403011000f0007400100c8810220 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 141708012 1250 141706762 141706771
    0x40b0402090d1b090905100e030706090602031501030b06181302040605270a0b1309020409021b0604020114070c08060106030c1107030c1a0433031e0504080d1103 71
    0x120f00e8015484401000a403a41d0040183c4503030300004542c0c0203842294400d1588200802c182c074107100c00c60b5115007e503142e401068400759000310900c1051104400581c0b500d4209003030030002c10000c90b000c030b0705070300030780a0311014022807210054541d00c031503080100c0206001c004644d120b4480d034018015410500c9404c1c01100c80f8940140c9010407203050100c0d2810081031340d01c031545440c440142c1603000c0c40004088603109000000c000740c0500160003d02030340e05015841e13034508603c150000041461071034095020300c0c140b1000d030f60458050b29440068820795640c0d42e55906040b07000a1a581c0408800c0c0b0800000150f480c0d80356102072600352240e03841d01702505646181d9543c9076050300001e040342c0f071f50007400c028103400c9110411000040701d4100c0d09082d40c41090300340000c0e194032602010300396001541c0d241c03281607985d00d460700c1c1c0c607060070070280c1014180c1c031206c400c201c85213080f400e03559800305081c06900401d446c1d0910203c00309108400c030301158940150425107 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 141709262 1250 141708012 141708053
    0x2b0323010f060305090a060221070818011a010807020319090f0b03151e0d0b0103020111070f0b0a0905060a09080d0302040617040201090f08031206011d040b0402090d 73
    0x1030108603a40f00340601401540c40c0341c01003107505c40725101c1c007000350301540550310034180191540200100c2d2910b5684503200a4498041a2a10007003210302c440080d803202500340d141c000012980c007609044016107060a2030200c031550345101c000c1e031640c4038084004503011446d1811280046c5d001c06020203441d08200c062140590b9000c50f82a1408144c540e40490b00740388103c000103080100954081c01c0103041d10f4581d0045100101e040d5150300305042e10104407180061055580024901c3d402000d0040207108130b9251980c118003c1d205405401d144140000d8450030240c4a40b9000380542001040381e641d515000c800508004040e02c07441134207000b40005e00f12514044d2003070790b040320700d15240c059101e1501e490b4140c80a00c001e10481c1403150300500440e1819199120b9030140030368038011507444009965031074070b4080040140b4104581900000c2420484903c014000daa0554012800300300c20000200a8041c081403140c01c44002110701003800f2844900d00664000c14 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 141710512 1250 141709262 141709289
    0x4050a0f0303080a050406060b0c0f012304151d010b01090e0603031c090b13050c030106030c050d140d020106050a09140f070e04020f0d0506032b032301 67
    0x100105050050103120180106083c4800214205040e80103241c1c414030030500042d21a840d07204008958201d010881d4032640500210903540c0003d103e845207a500d82c014400303120240848550008078020801020803001c4a0910b0003000316811904079200b000701d0074050801241e05140c02854804070450004502ea00b000644916a00105001d41e50240146250130082000b21a25044038290911030690304c001000129410800e500d00076003010418030900035840c10b1513480c2c031042c2103c1c94401e9141010402c00a032000003000200da8081da0310f800b00741c409050280c941c00d074007010b810190040004071111a541944101d087c0e480858034160704988414194048501440201e10a4096500464078640308001074550286c90352510080e1102600040340698009505401c130f02e05003c20040110040c0d030260590148081c0c00800c48c009190314844d418010700e810310884a80c40000c3c02c44100d109402403800550b4170743c07252802128828941c140054240704540090303010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 141711762 1250 141710512 141710519
    0x9030309110a1a070203030403020402040b1c0b0d060c020f01050c04060210050c09010c020a0807030c05041b080604050912030c2203031d010903020d0b06040c141603090302120304050a 81
    0x561154015902250440610a003d0320f0b80d0702c60741d500003c400ea074184810b1200000503910381c001000540320007081a519405051034070b801d80d480c015020380c0b1090900e80700b405c0c81c0c0c40e4401c5603a841c1d6000500400c500348185810b03800c01480c0d0405d12820b5007040c0c204030410b810900144100d4589074226101901400324600c11a00c1c15109855015006c120b0301a10b9841a203403008810300040400100c555210364480c6803443c036074002c80d100a603100d010807039031600d4400d260b510480300c616046d8810b07400d8001130840d035005041c50312596070750010038100841044044a20041e103808982d40707050600f1003400c9a0042c105503100d1483c800c580d42980c00c44010582c049139855202e004aa100ca030900e035030712400c80c224460410041c641e0000c0540c3c0c881039001d007050700400040855042c62000e1000b96942e800c00d801c1485035107541d07040d0700c071800012246103101080410382e850009217821204428180e0010354010b50388480c94406c000040700501c12250101c9580460315034 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 141713012 1250 141711762 141711769
    0x50106031118010b0306060408030a030c033c021905030412030e0d050a0e0405040f02030601050105160f02151b15100b03090a0c150e04140601110a060903030911 71
    0x10b052180c0c448002c00100915490360340034640040b0020442e41c2040e440e071507014596003007211a440043d44612201c140e440c0c26100d190b40d0103801114004010404501c6040307000c284506071914500c1134842e0004c204440e0781550800642c2100400054072030600061094005840c2600d050b80521305081506029128000252002901406903440c039218241c900f600f2400e41a001e202d00024102d80304d03aa1845540e10480c810306045804400d00d00502d450144140c010f281404002c01c0304901a5902c484100b14543d03000c01c8040d42c4010078404203200c0400d03540b000f03941100c0880e90800385182c425414806204506c2218010301c000f90540120320380a481d070340003503810710106214148130640110b0b0700120f0401180d403c40b03050342d2141324001d0300707130710035036042e152000b48410740c030b42c415040e0550b071008030380c1400940f03040c030000900364001600250610280b00030f4500441414400c4c40240c0703401c40c0d0300300044980d9080c0540038018282c0c0071608440ca4032031900a519 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 141714262 1250 141713012 141713029
    0x6162f040204060903151410091518020c070b070c17010203010b03040b04060e060c03180f0c0f1503010801020301030b06030d0903030806030a050a11100c05030d0507090e040501060311 81
    0x50740d5aa4000c0a05e145848540307403001c40f030100b040c510380c032003a0004150702070488140c041c3c4030340541e1014161518030000e04840b603032441054a284003820803c807070710080300100d60503002440c1c0140e0703e001210310a40703800c069511144499201003880c07024400c0108811049504802c0002e0306489061420741c201d204c04d00684819103024008100030448800ca4076070310621400d400145a200c1c6410300d2f00d400703011506080400c80001c00c00910a5412802c00300d1582c9204c000c120316800c0e1014191105509070206000300e00d90741518030707540d6070340d040d0848140302e0518840d41d958680c082c0c58041c1d8003d0100b56034485034a0041125030070005203c48607030100d44c0c1c0d04160300c1d06564007211060400340c030403545841500a528003040c4180f102400e40c03446441ca15038610101014445007805202d4840207201c0d201c800c00c00071603070100403140a40c0c41000e0004007071765182010346005c0c105070084140d17042038000300000c00505500c42c1c0706503405900d103009440da4080800650700d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 141715512 1250 141714262 141714269
    0x11104090e07061d221b110a0f080f03040606230108040605090f0114040212070506040e060409060c05030f01050411070201030e0307050f07211106162f040204 70
    0xc4083d0303000c0c038510355002c100340c403880304c000d102e08844000301030707004041d00000d4041c040b0039546240b1107424035040d070440800d6052900300f801e1500c01c1155100d840c4c680c07180c17028144910803600b44003041b104e81c085955401c1076800c05512030410307040640c01440180201d0510210f031028030005c001214948040c03110050f951418280c0e035950341c0202400300a01581103500c9100c561400c0d8400c2030050601c040001c010511030780c58680104a071244074500002101e800481041c0b2460b140c1c201200d040e20500b0401001036210240440c0080c0003000d0098030651030201c0a0814940c0310001b1800b40e207a540c055105030b40c030750080208943c1280312281001c40100310290055000343c0140302202400d40c01d4908100554880341d0408001c140708044a4024220521080e03c0701080d0100b969900c01c2d0000304074455940e00c012407010786580606c80c030b001058800d001403a42c0ca01c0d03030140340d000c180c0841c1503002450700f1034030100c1080b0164090502d284941001d0a140c401d49084 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 141716762 1250 141715512 141715517
    0x6090f09020c0106090618110c06041407080307030804060f151401020a170903060702030702010903060504050313060504090b0f0d06021b1207060b030d170c0408011104090e0706 78
    0x5040c640301000c002940300ea0340841d269521640b0005240d1100d1145074028000011040f4808403075443d008100c1e80c20801c1d800c918a014844c40850150029980742d100750300084614580d0b5a40007d01e1418a10742d2204046200005083c1c0c100340e4007451b0305008034801c1030140300800d140c0100d14161421a0070104400381c060908000080345030350f4100307885506006a8220013030315181c074200c21501c02d8950011700000100c040c01c40c01d040140c2540704040344061424000d0640c002062200300c1c2c40090300e680d4076a000300e0b05100007407040350580c0000a85008445a0721540034002c2d030072501c52001c10310314040e03444a003401d10002e03900800000070021465800655140c0000350800e60008420241c640401340c0358603170402c100710050508521198490841d450040150390310019a01c1c025040b0103910303003061741c2100001c28072111280850005a03079505400703005014603441041a58205800702c418400514000c0050328501c90b420b118480d200d1507003603507071003e0f0b2040c01e00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 141718012 1250 141716762 141716789
    0x2130e0912030703060803040902090102060708010b090402030406060b030f041e0201021c27030c0b0f19030e0712020a060203030c040b090406052706030c0102030a0c140a03050301080105010609 85
    0x1100750807080290b6110039241800211580c45071492459a003040e0009002c3c1540000c6e014a20740c0c041140d030754411114a010212036040110b120114050014494040c540100210b0b00304040c6400075005002035000c10b0b40c40345400203140c02c915005480903150824003082610b00740c40c9000c0d00417940c1c1d806030020711285a5055000ba1450b1100781720804003c0b81b076404d00361b203070081401400f4000f00080c0c851221811810200e401c28520b51000f510000c04100a4248103459000e50744040d2203264a41c0320140d00070015406044918800840c5009514001c10040790780d0b080b0f2100303d40280e40240b030003911407406903660700c000d80d1002c0c00404148010003102041030700402031902c000d0300205240d41c1d100040303442011003158001000250b03040601c00d9083e00380242d584503800310020114030840c40c002035120301c0f07959101c4081004a1180380d043c8a0f4900b21040c41c03403203600c1110200b2005040051042e003007030068810550a0000005440344261a0348087d9480c0c0c4c004a074 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 141719262 1250 141718012 141718033
    0x305060909190b1807030b1b070c0b0306030717010903020f0d0e1507060c030b03010e0d2708030408030703021506210a17090f12070302240304050102130e09 69
    0x1a03030f04000411101440f0002240c0c0c0c44408030901c10b1100840c8202080340044c103041b84c0000c1c0c0a0715032940c84d0b80c4002d0501120002c83c2071002c410084134071245040d80c4d240c944601003802c01c1c1d280d03040302c8514500050360002204c070540c00400704038060f9003650f17008101400c07065210807a45020500040d03500480305c070319240c820b8404003400c0c038025103a071900c1d00c01e030b84042c00d0703c0c9010b100c803007c42c0da2901e507001d0074203081c040c5003510350405011307011840000340d0281030102ca8900b02400780c2401e00c01c8038074840c04103044101400400040300c0d00d0b180c2d01d21602c1d550340e001e96011401030050284070352115030ba110041d4040c2c1c000501c4501645807294030410410803e007aa030a0703c1c4100600300e00407402c0c4904081070003d05254045e0f4031041c01c0c0c00d020700c5c484644110340c040c40d1440c2001100c01404101d440503654111108500a0212820352185480a482e0b400900c00d000090208103c0705500030320040c980060089000343e568600c0104507881166558203a0b00083c0400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 141720512 1250 141719262 141719273
    0x1b03031e09100e01020a030b0105090a06030c050c190303060501080f0408090d1b05091e0c030c0c1f0b060a1b02060408070303170906090a0f03030209060a030506090919 74
    0x180d00180303039011101100c1c500620702c0306072003000d580d0301c0f402d0b540022151004c903030501800f200d4040a0800c0d5192604642c00300d10070381c455100311410150b45010202d084c40c4070b0740441e03070711101060031140c8a10070110700101161261038201d0101e4903180f40061154050440c80d0711a15901508010079512500c48400d254411200540d10448201c08800000c64090300c902440b8110000140b0860500c000d1003c89030000e482042040d10010710440f4625030084000da0041000440c141c5903102da0782c0da00c8190081ca0712001050241410866901502404405e049a0451030506c101e1800b00c061010074441c1302c000340c00280e843e15400300c1030080c03001111400f071b10144c10f80c0d15261703a90380301030304021098000b240050b814140301801c2c0c0e032151048a03003000704500503003464104851540d5688481c0c5400411441c802014070040c0b5000f941a0b40143d10040e006a98504d64504020000e1500316070b40c138030402c41c5101055000e40002646019140c400e80040c0ca00c00f40c1d500c54 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 141721762 1250 141720512 141720571
    0x8070605040312060e0601030e06162a03112107020603040c150201020403110604050a0e09070305010c090503010c0c050303070509040b040e0307030f020c030705040905010e01060b1b0303 82
    0xd0382031000400c500b00100843d446002c1c018005a1030070001e50603d50001810340c1c24090310054981c0c1705405101c00b03d82c1c000c6050030303500c000e8200000400907010240e00410b00d242040043c0c0340b41e0200c28070038140c03c5020b10241d03c0340c100c281d82202842d01c0f034103070755101aa03000741d0441000b8860400141000380096402c1030003140581c1c0c0103a40d903522110703414140c0503d400141d4000c2010802c202a0b0264100c010900b114258207180c1028041810b0600611841c41180d0701c40f00480e485203000c1c080b080166800c80000d00c81002d0805016008402034840e49000e9880c1044034031301d4070720030010384030515440b0001d10302c0e64a070410101e400d070700301e07044c0c2c180d02c0395854a000c41c05540390703c03c000a0704c0707203440a5503c0e4085810068910600c880d0401c0039504030a9182e0240d5902246840986030111400900a80c03582082401401c800028588940c68400d020030030744480c2000e414000d900c1024180c0b11035941b000e140d1039010079a9840c0c242800501445281c4909454 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 141723012 1250 141721762 141721771
    0x150b070c0b03070c0609060b0102011503020907030203070c0f061b08040b15010504050405090a020f03030a0903080f04090c090302030709020903100b060f2b06030b0619050d05010219080408070605 86
    0x20203d4280c6055185c501c100c54443c0300c1210001d59036a10707805a07507028003800b10004488a841440546150046441e0b00170040000e02019800400610314500901c40004080d80002c00780681c0c00c0d440c03a01034003d002e28100e0800344c41c034003960419810f104410071881a0b80c8590410101e44651508524400300030800c1c5040c04010b000c0429603072120700c00c0038030400140d0700170051012103006000750300c41100b64142c001c1d0820403241d41c0d0950011f0300b82046962210140f95a1041d8807440389135030249400c5200440e04080840d40001d5001c0112010f407402101130b00c9000743d44072151012403040e0f10304940c05130810340344015001c49a5100031810324002c0d1601e49040030b081080c1159a106116201d1a920307580030141d280004508401d804c10b401040410500e402c5845042032130300001c0541d0300c43d5088600083c03900005ea002980140005880c0c940c245980c4d00d8040d01035000b10141c04441c080000703004400d288210307102809a41c10000320f6142505584412018000040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 141724262 1250 141723012 141723017
    0x110c0a0204050105100e040c140c060117010e0a11131406010f020304140d060f050709080d1407060b0f060d0905061e0103030c03020708030403060e1009110d020f060c01150b070c0b0307 81
    0x15409c905a4010310061103407810050240081e581401c203c3c81c0402103100e4411440da1500e5040c1035580340004800d0441c91b00200140346d03003140080040c91810020780c02d000342c00d09007003c0921051304020b1040c042d60090700d0721040000512405c1f40d80c1d015501c80c100c0506c112442a40060920701c0d44118900d00410000c01c6040f901c075088001d80e0001c1e141080061041c2e5401c208025043c040365003c0380041ca0240d8411480c082c94003028015a070300541217641d41d44440307610380d81d05445010920340240426440310924005403008168480d000d94490087d0360014401c0190040540ea003604284041c2d605a425a03c0407162545000001c6081d8400c2d040f001c01c604000b000500019881400082082116800d0b50760402c2c0c070280180d058141440c0b440000102031220040e241a425145805001002e0002805c2e6078074032039103e42c00101c000b80d40803a0b400190010401d03540408104044141e40750202c95a600c1120405440301d2070045050100018040041da000b43d41803 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 141725512 1250 141724262 141724277
    0xb031912110a060e0c090703060806010b03060607151d010e0d051c090b07170601091a04030606030b0109060509090d0f0903120c0c08010204080c13110c0a0204050105100e040c 77
    0x25503c5104503100350700803450320741c051031661041e80b4105440583c00401803030244001850005401d50700d07241070180c0440800080000340464580c10191046540c0100c841d60300c0e08181c165480c024402103410390880d80320140f0ba50b00300101401003002844c04030005100001c04038008a900b03411564401559020050401c642411940101d5603031030300495426059060032100030344680c881200c10302e98a00484104080391780c1150100b021903d505061000c4000c018012403a1071042d60401028a40381a00c0031051028800cd0341b41a200f59030400c100881e160401c014080314202d40300358696004181d5007014a12a00c041101d910060400ba41c02c55120359680f0be07966a19200ba00004032046400014002c0c2208042c004008060085183c1410030050f261502c02e05001e10b030148c00c042400343d0080990b944450541021412a161030f000c00c554820b0311200381c1c0205070311407410900046800c0c0380c02d03100f550b03041000741c482400914824080c0310160800c408004103003c40d6 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 141726618 1106 141725512 141725533
    0xd0506100804020d02060f0a08040219030804030f060902040608030d1b0207090e0c03010c1d0109050a030204090c030803070908160503070b03090f0106090b03191211 73
    0x541c1c90000c044c0c032034004500c03107202e42440142c840e4030005045000940c010a0680294401c170f8807400f283d05030350410007100d01a40030107400203808001c07c00008189040c4034408910a40000c10f13031030031a0700040c0881b100d40d0f0154020340c100180301c00325030189110b5005040c1456540708030b083d40451009644442c04d005502a140da1106601d006103406c000c00c6241c408020024400c8020754440107040852192514601e4141e904200c8065800345c091f0006858000d0140302c0402e2941d02004041e2501c5482034801618064011020541c1000110702c101d00366203034201d1440ca800d003502c1c0740034040c24115001c140c140c0800d01c025940442d0810413a0b902080043d103e44824078040e041c03010600140380150318040000550f034030182c00030301407410f0071400d03681c182c20b8200c00c0da40c010201c040c000b81882c00701011348000d280140c091589240d81e1a00b110307003c2c49d4 = true := by decide +kernel

theorem cover : BRFrame.Cov 141546762 141726618 := by
  have h0 := BRFrame.cov_init 141546762
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141546762 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 141546762 ≤ n) (h2 : n < 141726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
