-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1045
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:59:17.132831+00:00
-- url     : https://prove2.me/submissions/7fa70ea5-1df1-4ccd-958e-fda5541ad092

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 187769784 ≤ n < 187949640 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 187771034 1250 187769784 187769819
    0x9060810080d080a09020a0b093a031403010915090b0102060c0f070b070203030a0c0206250908070f03060e0d0e240c030301170a0b1f05061210 63
    0x1da4025440e08100c1074403410040741d002c6801c0d507010410980da6801700e452840d496210300140b0801045180a5113400c4501c0380e0f0b4420310a0310969440c083c00e0f14500d10106071480c050829400c0184a01091b0040b120141d07441c00b100c96040d129079464040a0213032a60941c02e021844c5190f9010615804521641c00020010307401001d00c1c0e9a080100c00031a84800c080c00462002800300c0c4002a541601c1540b01d504180d01443c3c42c1d051a1043e00140d60309540e10030191b42001b82001424026261200382445008078070740d0041d641c8040540f01921907400403a801d001310030010820304e5000d02ca02c81243c0c8280b0040080644083d407681c0c44208003c6c0810015160099000b00d034a44114414400c40b0384458041100059180010307459104c05000842030f080400100500c1011300003156411310510064a0340407000d0780e54102e207120040142d02030b0344403808000850704469406201606002d4141d554a0400709180000e000b4101c403090704111220502007100d00200b03c06145 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 187772284 1250 187771034 187771049
    0x30310080606060f191209060f05060d050c0d0c05090c040302010f08060d11041512020a120510150b070f110102070b0901050c0a061d01060608040b130c05060a09060810 74
    0x4100c0d40c0d08070a9800d40c0000c0d048400c0007818401b104440480e0710a60180300d1292400084070003440d650402500d00c010245031040d1003600f090800305401280700c008410046494461410241c500070418141310b42103280c0000700380d000c10481d40e1b00e16000708240c9000762104001009050300031650090100c64a6420800029240c000030306151400340e40368200620105c1e0381400100c1c1e0310a08c6903594480300c064203250a013641582400e00f00e14001d054a005054142c030340d2030b15465590707440c1030003040e41d0075561030240d903900e030140c400310003c1c01c18590000e07550105803c1204036449500c0007610561000c0c440589150700004a80c4116619a4400c50920181400541d5280c000540350001d902401c40d402000031582d02c1114400321014010654034020003500c41d00310b80d0182c10440500407010300b80404138107015641030340f0070300e41440d032066102186004450100140c2c4950342001011030b446680720b4000300e17940103580e842d6464042a90b00d480c0c1d945400d00680c0301c3d41c0c2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 187773534 1250 187772284 187772287
    0xb0d02010804020102011e020406030b0f24090607060b0102010c030605090c13080f0a0b0c071106030703090b0f0108010b151902030c071d06010507020a05090a0905030310080606060f 80
    0x4006502a046041e481401400005039900d0843e151180c04000b0380350b241030086e8002014000300da014031800c800e50500b9202a07107182540400324007295030441407040c0045101c88040300240035042124503816010340700a407208200c0c41c03d64040c04595641c3c40c090350034074103580ca0240c864425103003103683c02030104540d0303100c0d80c4140105902c078941745c249030000ca07a8041580001003142d901003000f41d000401e2202c040341020496104040d1072516413010400007400030402c078040e06480100d007242e886a80761a410000d80080c4000b01c002402c0030004d00c20008084c000c0700c2c5450407624401c0c020b0050200a1041082542d07178201a5801c00d002441925014801610204000b400500469150900340d184991908038140d2020f0342c01e40044c500f201ca8551400c1140350000c00a00381a800c0841907400181405030b0f41c0190350042c0701e40e40c0007a0050407903400c688080b94201065a17500d00740160744481c0b04c0c80c0c50140214512604010820604000040714070804080c0c4005 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 187774784 1250 187773534 187773559
    0x915010905120f070305100510150521040f0611090303030c0d1509050901061410080903040906080309030705011713112e030e0703031b0506131103010b 67
    0x11400900341c46410b0701512802070840321040040124001441c010790007007588820107004c1205451b4000e04415040300c0c132035002c20030154070320018818603038681403107500c5803103045030030a9107406a440c4541c460503000610050045c1400c100c108117000709010b000788a40c00248501ca4802c00f507084e41c00d6481000002c070b43d01d001501030001e9021900000c54515141d1002c0380400d8940e0b080318142c980e541741800201d6100748100c1005180c890048103c0441c03042c00038400300300b00d03503d51007404031410005603441014400ca5010b0078031400c04104c3c00d0b84034900c450b5280c20061841d8080e100d4400040b0722503002d0f034031040010702164071a070b0007590b444109004010518808071040005081060625502e0003080c042c041c5900038500340c407214040d40300c1c040502220080c401d16150420794604007101082410559401d410400030f10100c4044008a00104000290403409101300303000c420001c3d00f40c8200c0240c080c10305800d004030048201422541c041001c0d903481a0f541c600e0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 187776034 1250 187774784 187774789
    0x307021c0905010e060d0e030c06220f11040c1110020f0417071a030a1d03043503130f0b090103111b0705030d140a0302090a090216020915010905 64
    0x1104c296140142400c0d0a00f0101c0c00070704241ca40d2841c55030866040426407180b14481000304560000c0d00021100d8511611100b651820341c1c6c042c4c0c050400c0c5100c1007001c040c40707a02844205800d2000e4070030011302c0305501004040c00c0b8214410740c4140a6641c070804420040d000f03940d0420409070001303150500d407580440744000d101e20346803120702070f0711000504000801450046200c103007041c0340e581c0c42c24000443c102c030300064480c14402070f002c2160044600000589054031700e460a869910f4001c1042c01d02400b52810500140b0780d0580034000712010080050110585040070310034072291102110069104070f40940008440203105030f0055604c0781e00003580c40720700c21103914504031031050003e422002c7d00c61041c1403640850020800d1b03003000c00c4040043c051038500321240529006030b02105114a524010402d0340108a0b80d41a968405c842e5008004100b011076a0700b05e40100c00307051074400034040e0310900300100001c414001c80c5000705a0740700d05035200002e903410a800c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 187777284 1250 187776034 187776047
    0x13031b230402071704090518030a020c040b010908030313030e06070f0b040602070b16080109110301030b070e03030705010c030605040b1807090f060903060f06030201170603031306050307021c090501 87
    0x38103a03011101c012124020101c4c1200070405040100d00105091402403542c0400040c251070040f02984100428581d0035404103503c41c88180c21180401c00d84401001243c00311155006105280000810700c02c4186032140c40041c114030a0321a030107418100c00c10007400d4011000c021b405000d21018680000707000b915929845417281030f006007400101c3c1c942c0c250b01079007160203402c1440c1c80d08030340c06500e40003410680100140c9909108001c1402c24641c0c4c1030006200040c0020a00004540303070901805c1c540402c2d10002d0100c076120a15418114040c1c01e030140700e0340c0402d2408601281c141440e0168403c120805003800c0c0a06070310b10070720302000100510800c02c020040034082928440d80741c2c40001400c0741e43e1130309042411420072a0860701d83c00580325009182c00743c2040140d030401c400e48190003145040302c6060b41ca0002181c194426a80301c0b203411110700802242291300030b40590f0041c080c0c3c0d030031a229001d415040341d040300c10150300360380480c040000400041d8420728 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 187778534 1250 187777284 187777297
    0x301090f0c0e090f094605030d0c17071701051905060904060e070503011e0317030a0915141e010e040609020a060c1a01030c09020c150f0601080903030c030c0f13031b230402 76
    0x14054004541030400201cbd00041602d0040019010468a402c803040511902c1e0250030212603501c00c078041044030300404c50845c442c0c10b001b05004100083c050f51640d01c40002040000a40420361611040c02003503640240199020a01e09945802ca44030034411a0801d40c1d5104c0400c286103400312064804917007008020200d10fa85400300480042d144c203a840b0b03c1c0c40c08007200070424175207100c122001d140000b860080039002844140b5080000500107a044032580d12000065480b03500345500504080f500107900012082000103043e940440310b05041d40c014001106841090040c880b442c0100303200143c01c14040d05403d0044114942c024030303c3c1051081102c000052101245004000c01c0302c5204584602d40304004941d40c009181c59801901080958554505945802d50f0f501003e072201d0941080410391444988861044600202160390f24904103690f0740b070004d10003420060380b080035403501301d0009001410100700085080191070060081e102d4a41400300941114 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 187779784 1250 187778534 187778537
    0xe01030203150d050105070324050906060f0f030601030506030a0c09110705100f180b04060b1c051b01020109050705060c120301090f0c0e090f094605030d0c 69
    0x1001040703156580085490340b0391050300089010301c0e0448003e07080b249c074044020a42c540810b4100d0038080e4003004d01c4141c400445100310345844000105101380251400303038a13a20310004201600f40050405103210319000d80c0c1c10300103503440340306041d00c1d54803006000f0324000e0031290910144505400070038450040100e80390510040c0d48032103181ca407040050a810b1a6a202e41c41706400ca41d0148420385244a01140c07481c1c006580c80442c401001400603008950301c54860320796580e480e080402d1760515010404036600d0f2410620345402c4100300d0030540605640c150310700d0f540180226040d16030048058200301d4503000900000c0e5100718040100c902446290390481c0004502035401b80c09032680001c0c40b01a000312080c01c9608c024031850070b101e1414014081c0742c0d600028240d0140c0d922001c00300ca51201c00507e80751804507103072050b4070100094810300c10000f03064044d001240794045014003061014000740030003440003015115802c1004074a922003001d070041703005c0310600d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 187781034 1250 187779784 187779811
    0x20405060f0301020f0909060f0a060e04110a170123121903020f06070c0b01150c2a0f0b0301030f050a12080f0912090111010b060313050d020109030e01030203 70
    0xa080000c0c2c22640415106981701c0350208030401e4a003011408a98030070010345181c085800764000048540040b4482d50040050300c80104031161550b400007805160f010310034030346500c2200030180071104140042d03400a95600c00003d031445401d5851201e04d004400b034113181d0300810701400300789030400300a1041441034000b4000c1a210103241c40491034042d9014000d403040e0143c40030b0510b10050204400c0100c40080400480c48071a0090704403070490004804408400c5004d0b01c0400901c9405000c03409240740e0b0388046400c459450120250303410b400340f0101d465036070400f0910040e0003190100007050005100091150000c00d0100740248120f400c0c0e404160b80350001040c8103410440050f481905010100741603461003074110b50054042d0050094021410305640911840a030400540246ca4004010290700c00c000007080a0100d83c1e6070b1628010400c0c12003002e4100300c40d140b0510881010040c810b01c10040a10b6055840c01003501c1100c00450203900007500c5030500300b01 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 187782284 1250 187781034 187781059
    0x120901030b01031508070501090e0610080402010c0609060204080d0504080c06091201020d020d0515011403060126090c010c0c051e0306090109120c080f030703060e0103080d0f020a0c02040506 84
    0x4e00d4030510010302405006100440c1014001080c1000c540d1054805141d03030b10900c0f241c0d070348450300d00211074030074980303030303c3d50b981b1400100c80100341c104000e0809840c00d0404001d0001a40041c000d0396500d108849103c4a00c043c103c032503105502c903100307880d0004810099503141640c014580590018280b81d00310080c2c0c82081e08a90124150343c101580c00290f0540910041c029158081519652661055403810010340f2500810b04071415a4800000044d900c0c1c1c0500b1801c16160b04924100710740102502c41c03803070f2188040d07a0003401071040611200480d881210213524080c0e005907498095440c000034070640e40e10f00080821141d5640a0540b51600c0400226100e203941c0d000100340c51010f810022403082d03008006c8800c2040c5000f00034042101d100445120a40107001d065499171000802c600a081c1c40c1c0224801107401000001400b0f1110017800c1d10030100c001c2041018210348040c001ca01c0340340664000318440e100140301600c1e20342c5c001e59000d100504413589254 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 187783534 1250 187782284 187782311
    0x302071401022a13020301080d0e060a12020d09050609070806040c1202030a080a020a020a0504060f180603050a05030703030e0d0c060b0112110d0f050705070b1b130e0603120901030b0103 82
    0x180c40d482103100c0300d0b80803004000d030340c2c001c1000c0214442c0c6420551080cac4c4400c0c021403424400c1d24070a10601000228621a0301c02581c1151030240180f00208407074441c40c80d1664407060265801e150b14400c0000100d0708100104545018070b80c8071190044071440c1a00d400b800c491501c9044e6814068000400042030800c0003d00d40c400302c86d80644000c0c061481089140c040c2d50700028007482c50100180086015241008143d41c25444500040503002c8400e1010f400d4542008080d8020a1000030401600001802d989407190303c05014400e00d611095170b271307030740b4070341c6141c0001e103408030024003040c01276200c4600c0d0401898602c80340c034611440502620013038100c041d40c503030700003c0901501007248203070300900c0c0d18000103002c40e040c500c40040940c040c0c00000f40840400c1c0003c51252a022480625880f1310440400c3c2c03100382403029140214407901c03800203401642d0002031071b00c5ca000b00d5000700d26615080800d05040c03122004400031300100007482d0500d0f40d10708000340443e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 187784784 1250 187783534 187783549
    0x5061807020a0501060b0a021608100f0608012307050306010e01200601170c0d080403060b03071d040c08160306020a09080609030415182c04030c0302071401022a 71
    0x2c00121100b51f54805070520000d19108494461080c032840725031080c40300c0c079004505003440c06c41c0e0500100d0310307542004203c402484658080c19641d0f00e030042e4400c0c1081054016450003c094183c0d0701c80e80d50380742c0d0a0ba614802151900d001810300100340107250300603081c0103440c06a0301010030450000c1844586454400c0c5c03c074812444406500750b40c02c1100704030b400349240302a0341ca83c0c120b82950b5150301c0640150300006108588418440300c2d1034034100400c10080c41010f041040c4102d10381c0e03401120f00707000c0c4c0342510007405481c004646840000703400c204455022301c600c90070524540b1400000c1d00210030900030042c200100060366501003044501408a130005180d69919040040607032240c002c450105012f2030031060b045d40014481d08034100c50f044102c00c1d4030829003560401d515100e11ba01c0b018211010000d1109141d40400c60440e403602c00c0d000c03650031036145d01484608081e401c1806005900c04261444030000c03402801c89030181c40c04801d1241c0b9403120010300e4a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 187786034 1250 187784784 187784789
    0x906020c0601031e080405060a0318030801181802090601050904091113050c0a030c020a06240605090d080c0c030303010305030a0306050109050a0308070201140f0d060905061807020a050106 83
    0x590701450051061100e5a10300d14004148400481c000d4101983d40e2440ca010303a108041c400e260115100100d14042d800110b0380709020703c00610b00c12034034900540200c50a000302818a114404120a900c40c0c503ca41d0a8010074440803948614a542c02c000f03070078400400941c1003101c140100040c503180c40c000c10700000c0c414404013070b078500340c00c0a120180a002030a505c007070303040400340100a42d0100494003004094030f0041651707180324000368074115400720000d00d1545408401049482e002c1e1606c2d11440c01c0218000380d241d40c2d400102d419000381084194030440c40411724000851300700007044864040004c1c0c03221554060002411034000b688180e4040d003001607400a6079605100e240050b01090804d80f00090400020a901242324000109500170014400c415a03000c0d150580d052140101180e80e900840d018003c030541004001220580c1004404582800c050184030321901c0701800c0d03c4860711080c002c040070010040c08060650081030003400228200b80140c401 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 187787284 1250 187786034 187786057
    0x1713030309050709270b040b09010905030d020301180e03270a08030c06180c01120209040f0b1503010b250f0305090108090a0c090e030904060906050102150f0402090a090602 76
    0x341d40c82c5007204401d10f6003002401181d80c000089a55001030301044001f90040e8010740000d0030ba68407000d080c0d004000c501406051448045107840400300550000e506a401c402298403030103807921510410b9500680503049190400d2000060900302841d40310010b5440c03108125103041c149002c41c25043e00c07600500100d400000d040130002c1d00812250360410742c00c0d00e40c41042c0c0c2d002500b060b00e501c421910303181048066036000b00901d81580589103201d0000380304000c14041c065103d402045000c518a0141b695000e081e121440e80c1c5050320304a0b00240c03001c81c5008030040c28400210400200210403807928202c4101250003210f800c05954841d880d038550301d000560000d00034150007046001c0942c0407400002c0058080800041110282c44003c9a00788282c000f103400d6010f100c4a1a0300a803808400140c2c60000d030f0803440c21a5021703000d40d010020b01d00b4a0b8400c0f1041203c1369100d6a600201060041c14084406030340294030b41c2c400100402c00750340311016030303212920f42e10303 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 187788534 1250 187787284 187787291
    0x10824010905060c0c0103060e01080d0f030b03011a0a06050a1d06040803040e01050a0909111e150304110d0503071101050d0906090528020420041e061713030309050709 74
    0x1c2da0351f050310480002d0401a040c01c0421344c034018410b503480350401c03203400400c10414030112509000743c20402009000030006d2003082d0111051032540d0110300200c901c00c0550781d81c00030722039016204482e501d4070250b644101100d0000416540c07108009502900000c0c200300000e0150410b00207400580000c604d0040700c2c0d49081c04000f1032152903004000428900075103900040d41c02100015011401d59064100c070b020200711040145400c9462904100c7d07900b1100c40c8010101e004501c11032050b211060b820103018207100302c240a030300c002003080e407003040f038480400c041c3c034421503e0381014503200f031400b22190856803d94983e20422145d1980b2103580c4400c20109000b01e51000d100021110b00d88201089499032030004802d010340120754075080c4650a0b42034a90307a068800044020541e26599412284c0351030000e107800b082081860103000c540c0912803213184036402000485281c1d241c45501d2540e01d02e20743d4240440a042e603910b42c08000400c1030200744010103ca40000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 187789784 1250 187788534 187788553
    0x40c0e010e090f0d0e010810050a062a02090103080c030d090f050c0f0f1e040203151504080a030509010c050109050102030a1104080a0305031e0103050a030e010824010905060c 77
    0x142c1ca04070590880350b80c113820004505111039403040b80380c03100380c1c000d103040700b240d48607106401d80010154004d290000315411001c00c000350441d99812107092000951401e4800740100b2042c0800b03140b90003036101c0880b40040020600120140600a581105903450050a59400002c480ca2803104840507078107803140e4414080140b0a454918030181c40c2e04003241440340004800045e031102e018810100701d1f16160200302c00d41c0c05407225010203001151349081c119844d0b00449102c1856910405520b000124181020003e03102201c60200040207070141c13990f0162a5038000042d140c1c10010b58544980115500340520415940180c0006990742400441c50b000d60b9200c0c1a4581d115404020420441400003000040b203038140c50925180c0d04c400c011104e00741c2c1c001c4140c0400c80212000803003031103000302d0b030700084a2290b00c82000c0d1400c0000103456006086640d4000c00300200e03102d2f200341e000d4070041c108004052601089498a030310001d007041c2c201141e0b01410354481e8141 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 187791034 1250 187789784 187789801
    0x120a03270c1701020a020d031a03030d0906200d050402011e080109110c07050411040509040b091506100c080d020c031803010b0d080d060f090504060506040e07030b040c0e010e 77
    0x580d8070040301c80c4000c4d4500f1458040103560394188100308820503540b85c0080c88400c0e5050340d80c0c01e40803c014141d030355a00d900700540c40a0002e080098540c580340c0f1808035100807a12441151a11110a00a04004002c42d6204c007c100050042c2d040c001480008006240808594050750b1a40c0c1c40f252010750424620174100c4006400da0344c1000c0c01084005c610040000f899811141d0448001c101014180d01e992041c1c045c0c4d911040d0441c10032420b010401c0120b00301c4a00c1151a40c2c01c40b2626207213011484000c9100b552983d801140c03280d00c4102c0144240201c5014134014101c2c035141240b1591504100c0e1f20550100706160004110300002c0a10607501030ba1242d000c400900c940611400001c0841176903110007081600005403009600c103182d00100000c0c403c0174002e2031143e5442160f24050300086a00702d0b003291030304c80011480d1510f88a11010400800003c100413821942d44071b21480c030207401581e40003440b10b40000e0fd056104c0e11306c0d020b00241c4411801ca03052402c00c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 187792284 1250 187791034 187791059
    0x11030c131506030c05270303070309080c04090b06190510020f010e060c0a08150607060906200a0309081c0e0609010c020d0804210206070908120a03270c 67
    0x800b108141c102081d14910903440420340b0b003003140880000d414006050403460f203079000080c199406004c0802e82000307054120360110105c45001c0151a43c49003190108411290310780d030300904842000000c6245070030020003040b02c03030640c071341c20301d201a464400240006031354800c50001a40096000c1e15803030000c3c054030450803070f2000144600c0c1004419506140101502c000c02c00452074001484000c81d400c02c07058040300500038a40e20744080c00d140020782030204050300d43d14201050485403400c04101d003c0315400108402d4140701d16054110040c1201560a4501c0321050040d00000202030599000300d440300c06000031b00f028003414090070300e880100f00d0f2038643d1400760341805207500442c809020910528010030103135564903012984040094100d00c000100c800841704080e000140540907040030b8544010450351602c6060307039003404542a1030701140900c002c1c01c4180c0070390000101d0384600f018001c41009008401c60035a1032080080d5007022619808010045403210b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 187793534 1250 187792284 187792289
    0x90b010515030c070201080720060a14070c020118180606030c180306052806080c0a06090504020a23190302070f150f0e101401050a0311030c1315 64
    0x116450b0940c900310744403010710301500300b010381400490300000d80740e030748121000d4041c0030750020b410009412000c0215620701342200d01c050792074074001408100541c1d103480584103114581c1d030301d142c1c01c01643c0111211204003c1101401d040000046a11002c040345480492582d12000031002d280c44001070039244821500d80c203120844034140203801c1c2e038000c0c820030b0301c0d0080c0003c01c55032104581e1800c045581859101280c1c6440c3c0928254407054100300202c45108085501d080c60800400c030300011540304d4080071500b0081d04025500301038010b042c40140d00d04105081042220041d203440c0701c140c121045143e0000780b50b400700e4040031921070035040d00d442d045040c40e08655900d00b00c040c4a01e005007600903540055008025603802c03980d01e800c4011000e100c0800016202c9980f1901d01c00c0030030900f4200325440718040405100541207420041100341c0882ca175445035500c0801c0c2050094041c01071440e108144d49403408420010760035494009888400100724440340e41268 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 187794784 1250 187793534 187793569
    0x30e0705010311070609020102030f27030304060f080a0612050f1011030103080c0a0204230901050c0a050c0304090507050a0e0315190b1c021504120809010c06090b0105 74
    0xd038140711050303d85815151002d13400740d00041c10700e10500050386540282da40c6480661400141c2c0181025034100c00c0c0d04501e0301d20090b0b11442c03441810162a40280d000c0e230030001e6000c0d403e403a14540b080a0254002d000c0042c0040ca01c0e4a803440180b44079506002502c01d0350002e1031186208508001130644010010401c11110040440105440c8418030003d0300f43c3e100460800d07a018000d01c1036211096004104100c1c02016070781112517818501c107034036240007103500003071201ca1701030240500c03880030f007020340d4500104100305841541046040c106148014080844d0601b954071500e80144ca00d610360b561581040d0200400818488032070030700a80101580e011074186d4400f44a0704110280b0840d9040d00d0b00420050007014102c104607072041c60700100440380c0c40110400003665000b501e401c0e00440500c0d0540086115900c100a82c00880c10000b4010a5455001d00f403a21414507000d041003260351141401d6919240c810707900034101c200100140e1604c003949881e0010b0a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 187796034 1250 187794784 187794791
    0x1212090201020309131814010b030c18040c030b010f050a080f100c05090303030117010e0319080c1209060601090609030201090302040e07031202060f01050a05030606011101110a030e07050103 84
    0x540c0000d490303001e14980c40f401002d080102e010b01c8003050700f013000040603c40803803490314440d050840c0c9000201031241d085518001c01a4903038200400c1064100340c1c047c02001803c0c00302c480c41c0ca050f000c01842902c00d041d40c104007200284100d20701c24000c240084640035501d080c54100705803603a0551040600341d20541d8540004000070407048903003031041c800082c401741d20389010b44680c070580510580c5400000008603502e881d000900c0210396281d0001c00070350345d000b4039490752031017891100315410003000c00b0080007510519110764850b0030342d0740642c1010341d0700e0b2085140101c280c0f03116016400040030441c132542d0001034540103005520700207007078525580000e80b5000031400080d001e543c465000031500c2c40204040d6008503400b4000340140c090840c0025120303481626440c0e102e1501d00000240c901d44007951034140d0700010302902864079140c0042d5126500246091902d5403150003e44040810714081e0003110000d031000701e00742d140501440c0c1805078070341103541410315 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 187797284 1250 187796034 187796051
    0x30f13050619030f020f0703030504050d170a02070201022a0108060603190203040204022b0605040c0504050603090708070f060215100b07030212030406020403050105070906050f07030905030304031212 88
    0xc4030700421601e1107641000100c4c0e441c074401e004040d1040002030070100f0b0000a20000701541980b01c0f62050b030044042c0d5011a500640440d96004032030003a0202402000c0440d4030301c1c8042d4002c1034020701c14012030340340b4070f00814550320010148201c1035050ba2402c50114865030090b04483d441501103400a15518080c002e00ba107021104902403023082d8007100090854940f03604403880650403880c0120010295800104408082c00b8400066810a400000c442c141070058000022454a0300c42c10a4200380512005070001890f82e001d034880e034000002d040c60140b0001c006051088480103800f410720708083d10f0310f013200507100084503001c8100a100300503840008280c0d030b450515180e40d80382c0e50800302c2c0342c003000b5100d0302880d903400810b1004014050f4028003c40744218003c0c01141d46048003a1160400b0f0720501001c21802c12001402650f10f40c002c002c9075201c0c0c10a802001c0d101c1c40401d245405c2070b0001c032110841480d508010540001810000705801842070103080b4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 187798534 1250 187797284 187797307
    0x320403110d0b011e030b0906060a090605030705011d0405090c0102010b0a05031902180a0501030606091b050f040e04080d0b0a080304060f0e031006050108070905180601030b03030f130506 82
    0x16051041101d007030104d2101092515941c03c070b100007981c01c094003251504041e151143c45580686d0b007944500800c000019034103244d4001d0508460f001805005160f162400566034001d003210500d840590b088030740701c41303541d4910030326004056002c010f0154440c401c0000e0308441c0100d420510500810900300200eaa00054080784941040b00ca441071855038804600708000c00c1c8000d143d032a0705030b000c0004440c4d940c1e00c400d040b0b85c060001841351958601c0d280045488840d00d94818428800091034898060790091150070300113403c2601d400d944820f110016282a50b007140e0445c00013171041d90420720341c02280c0c0a40401c55200002900c0d140a01e583ca1140d807003907000f441000400c101d0142d000355600b62607020083d09880556900d1100b240041486029041c003103100a4003040c0d4451080d940d540947d600a0054034204102c20010f0240b6000205154101500c0d207040c0401d586080c009410b401401d440019100d84031540c14000e40c001d1600b001e40030b03a8044c4000100351 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 187799784 1250 187798534 187798553
    0x41715010504090f02130b03030403060507080f04080909041b090212280506040212010b0306010f0540030f170a050a05160506011203090803030705040501320403110d 73
    0xb135034103d41d140c2c0141110103141d800381010814860307050101003030010a01400741c000611405d120b80d210390711031b5100042c841030094241c80c003404800003484550800d0a1034540a50814050504481c0321840000d4a08a100c040e1300000401500810540c00e07206020a819800483c1c800702c01840741303004407441c1d2400740407511030100c103078942010564a4945504460340f038050100900b00030340e100d040010032940243d0301d040c0020010101c005040e4899000d584a0880b20345507110074103903280c498002019a4443d8032150500702c88008040c8e00c0c21706100d030040d4458002900d10129600300f841c900d2445071002c0706098010840c525803540c3c1310302141d0725405c117810099152070120000b801c000302c0d45080140144640000130410b1010300d000e55240610980d111610607890701c44168813804141c1c0c0c0c9602150082c0f005010560160b8074034144800520000090421885200703007107a81c130310300b26040341d43d0002000e00c28889480100d4501d49425181c0c4204241c1a0343e40c40c0342e0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 187801034 1250 187799784 187799813
    0x609060b0c0d051602030102130e15010e060c070b0c0601051503010303080604050c0c01090302011a04091e0515190c0c20012c120609030a0e040204171501050409 71
    0x8200e030003c4d00f0b0078100000e50000400e035801800840d00c0d40074025058038154190300403000000040c0700000d004c02003168500c554014180d40310040399460308180b180c0c0b50045141b6611034010130101250800051004d401c0c0144460000c0001d9494001400070031400701c000c01d040810100300600200b904400b20036040001a07400180f266100f4007001014011810b400115508020310107080c150705400801512090240c207007440440728040100701c81c07a80c600104020503030801c00d44201d1940c200e06034000e0041096400d200543c4601140720b000403520010303a07140c0ca07611341403e446284203150071400107003020300000649844699104c14075021281c0080c031044030340321403640303e181c01401444e03104034440a1440029002c2c8010000051068024080c1c2d80c4410850000001d049000340701b2440903500c0d01c0341d03800041342c82c01c00c12a000c1c1d80040d001c00000845000600b00c440107800040043e110302000d20410102104040c4d009074802d905001c03042021036561101100d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 187802284 1250 187801034 187801037
    0x606010e03071a0f0405090a0614040b01080613090b181501270609020f07050c01030506100e03071508040303050702030306030c0402090d020409080301032109150216090609060b0c0d 80
    0x100c0e032001d440300390800d114031b420080c0c2224000c801d110b21484c0c2c5410080a503030150010f078203018128024003003150990908070b40010003201c0807a07010b0500340382c50b04000c4104680895004a035841e544002042540c42042c0d00b041c00c00000702409041c020030301c030413000d40d01c18180d551600504092031104548620364500300082840c10700308165010200420541c0320564403161018543e40060f0010b00050340d040c000c80a4020481d8800d108007407140c40028261000310412040c21a210f0001c0c0c1a41c0e501445000e20209000d800c04130100044882e0384d64169140c501413400074181c91010b0042000d550040c4180549590045003007008914156001a2101500d200041d00c000c8950f8000c1d401a1804900a041c40407060041d4140c078003500880c050711041401d0906d5241100102d41d0006200510034881010fa6050111240384a48115410f0f44d00c0f0a041c003140c09040d074070034010580d03624400c00850b6414004d50004106002c3c4090900d0b111b45032030780c1c551000071082070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 187803534 1250 187802284 187802287
    0x13020f0f130e03220e0c180a03060c020f07030201090506070312020a11071a030a02030a0e1006080708071508072303010e0f270a0f050606010e03071a 66
    0x3406920744160164030403401250a110100a0028482c1c40360310a201e0307900c4941202810060043c01d0351240011110004603607140e559030400d5030003464104010320301014995204014144c0e0380d002080c00614001c18000502c1c1b511640003030b1403e54030780c01001d0307a50032980702000540e0304508018102c81007a04d00507074940c024a412103000601c0c1070400344c1c103407010454410740c07540146039030043c103400d100f240c002685a400e0000045134550121011075030410000b40030b4203170303600070b1900070300c48403404100541c402350f1403402c0c1400542094a001d40c0c0310000c11108408211420040c03407180040c0c40610704110710700000d00103240c18071301445540340118400a1007110021750802e0783c44030460700000b00410b510b2040c0e00c00cac0308017400001c0340c80102c0d8142101d00ca1503406503982c060307190a202d468202a103201c0210246011035802500c1011010030488404048018405e001400b0503184c900d0014000c01c01c3d243c4000e02036445020144140303403031034507110800802e030014035 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 187804784 1250 187803534 187803559
    0x4020a0e0c0409060b07021206010f0902070f081b0601090612060b0d17040801061502030d2412140309030d0c02060409020a05120c09060a1407050d09030b13020f 71
    0x407458491a48540c202e2840c3c00700008004020001500f4a0b5200722031302c1e800c49150004e1265105000e003c0c0901482d403004081045c140c8540c02404842c0c4140d044204001c2d0684130b50005402c0039260400d004032180084424040c1403015034090001c40310100f001d0f03814100c8118074807d60500c01008655541e1a0310140e9880102d007a0b079480d4072514581e400a20840b07034107159001442006095803d280e4081011000f114000381c0c441e0301c0d5030096040100343c100d4880548031041c1041c0f00a00c104001c1806002480782e000301031b000c4114140300c01d030007a107048208403c070360729448030b5130300180490f008a0f5404038070000744808521703040301e01100c0782c00012242c1c410740d0300402402d0f10009600001e541c001000d410708400d40c060200300740e600c6031009140340c414000d11540c0003904000d001d0405001d0944c0341c402c0c141500f4941e0030304030607a03a090314041c1c004480310301240c0c6900782002048407119146502984110400120780003a9000ca620088003030304182c0304001041b0300 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 187806034 1250 187804784 187804801
    0x509071403040204181505011211010f0e10050c06010e04030c120908010207201207150c020a08010e060c120703020a02161415030c0d0b03070315060f0e04020a0e 71
    0x2620601800c002c642034451204d06d05001c0036500c003c070007102d103070901e8000141c43c0a00c5042215854211082010010b107000046800a000c0940481446401da481580307940f14120762440b00007080d260280d039460041170070f0b407816005a01100e0450220800c200010780e00903002c00c443c5a0022509140100c980e4064a49810642100081c0d40c03000c41c1036014805500240442101c0741c1201040d00c1c0c403d1020301040c004000c2400c581c03984410300c10440090344061445052407940351074440c80e1500c1d40050104412503201842c0c5130345404d650030140406110b11a0007410000301c4c0c41c601403040c011410141402014001819400301d0200101c900174000b003001004040300c0b11076002d480d54180c40e600c1620b805414001d101144881d4101d5420400322405038072a520941c3c00e100300800c10101920703070300710090707014000c25400200080d2aa040311030003850010000ca007860819951843e140ca0b2680300c41c0c41c0075941e109010168860f180c84800740c80c80c2c903204c6443c0390340700d610 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 187807284 1250 187806034 187806041
    0xd0f0b06090f03150a090b0a2009030a0203030408240727030204091a07020d1b02011b0602190504030b040f03031508060a0c0503100e0702100203010605030604060509071403040204 79
    0x35101344102003201007081100c6150300480d070291041c1070100c501c0e20b50040c0304003101c00c2e120244821110005014070003101c1080600304034180181243d0f03650402e43d000c00d003582c0143e4041e9549500c96000c540c58000303401c03007190443d07509030280495031500e480020000d4218010300022030440c0e24601c80441c0046003050041c58000d08284804105880e00d1401507025503031404d104185030010401c2c5038404141c41c5040d50329650f0b001c4070345608204024910440200c101c0c1882040000d503001d00500c501c00400383c5005540050311003040d800d0b901c0c21991402c1c3c050040060400080c0006540218102e40154211710700c076840312058a0145c1c010005103800384003400b090b403000110b0f02e00014100303115061480b4184000300043c08207071401c3c081558079000000d10b0307000c00c0c4890541803d650342d2120103481101c1c0c00100313205610089038001e030083d03c0015000010000345040038000d0b00001e02d0159410b48443c5001c58004045194066034201003401c00400705007556035580 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 187808534 1250 187807284 187807303
    0x5040504060b12010806011a0c0c19030b060306060d20031207020103060b040b04050d03020316030305010302030f06071409060c01050702010c301107060e030d0f0b06090f03 76
    0x2030041140359110004009580c0054440c0f0440b805284004501c100c00031079090304940800202e00d0800302d6010340c0944ea41c203c03001d640707030910480084101c9a59014004400704001540e403561913810b5050041d84400001c0070701d0f0081d40201c00b800380544420894000907600710700da1040181440742503071038640c840000c50742d1600c04c50541e40c403944065002050720794400d8808118450b07452003042003e0143d48203018500c40c06010070440d07400c0100701c17283c80c9482841901d24102e801d0600388015540c080042d03002907039903030040c02141030400c02c1450724800b00000f40158074003688002e200000100080c0f286110103d41d062241d110360045d6109950070000a004a141c07a00d0002d0090100c09040c00010b6240c20941500e01c144403458195203400303c15116400e69068440c1000d440105c1c55402c031200100400400308106114112840300e200b0302071513070742c8000d071174880030b40751309580c001002441c0501203405561160100c400e140015140c2e0003881d5204030000e41425200c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 187809784 1250 187808534 187808539
    0x40803070c112107050103090f0201080705040308030a09030806030f0a031b06020309010c2c09040f0609230f0a02090604060e090304030210140d05040503040b0a021e0105101203050405 81
    0x30010000342a444080c80c43d04411081103070384043e5104c0044040d180920405800b11140d66901c0025501c02c1c161070360300040900780149072580e680ea4010140e0b1003103c8805007603544113043d500300f41e4845030440d00040200e0040166a01c1c0a0441c0c0d107032060040b00805016410a4048912550314920345030319030884811520b030701c5c4c15444180a07020413a0349000190170805403424003001000321000b9182c5810400d08164041070500482d22005402a5184841102d4580000e0894051080380f035204182e6a20034542c08040c0f0300009010305ca140039690060414000765060000c0c1001c001e2350101c0e001d40d000d031150404078008188030780020b0701000c0000d04201d400d0707034000000d04c1100e101759450030824043e00412500c8801c041e20000c3c01c400d04003d041200c40c00b0303400c1560810300030030070340e17240640d6150001543e07400002944090f8110b05950468905c041a05a0b02038640e04c00a100628083c20001030520b4540250b03821441308140b19400d0603c5403003518007403d0003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 187811034 1250 187809784 187809799
    0x9032003011b0c0507061b03050306060d020406030b0307090621021c05071a040308030612070b0d0f0f05060619030603021c051b0609060f0904050c030402100206040803070c11 77
    0xb6400002c0801c410799400359041c0c85241000209284110006581010503030075401d41444550303400c4030b003640b000c1c000552100b020302400000350484d05c010070060840792000907040114105242c24449980e115140b080c6c0307040800c019400d8a4080c01c03102c1c001c0d48110075180b20103440000c00b04c0039006048205402c00700440401c00c1000900c1c2800c0d14001101c2003c5e0720000005520144100d0000428850b414800708646040c004050600000c1c03010941d00c101e07854814840945c0c0001d2881107109803100f030303d4040b40601d407040220801e50f1000904c403501d1f00902050302d601ca40072078406880c3c041c22000c2c40e55032183d4064800313154024844034410105025840103e02e1140c000d890034018030a00720a440c00700c164107000820042d000c1c60130046104200074ac2d03178100703100040d40c031141049038042960715882518410100c10754259260b04241c010702c160280910040829540a541440003007003801c03095a5011480345004150111540b410702c503501e40002c1d00c10b401c03148 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 187812284 1250 187811034 187811081
    0x70b1e03040b010e0112020604030f0503090d0309050a0902040b0a0513090603030801051203090a030206030a0f11041e06050d020d0e0f01050702010f06030b011719120f0903200301 79
    0x344600300074100c0d4284e00c00c2864590700e030404100314034280f150080d4080002c1008000003010002d880e81014001c40a070b031b04095030140490140c2450348000c0f000a110040140510b2410100d0070014120b05e040c06c500b000e003401c41d100030a01c1501000c1060140109118800308403240e1118083d00c4080c80c02c1c07240550301e2602424018080c0211482600b40070f039003185007040041a07541c540001001142c074203103142c0902c00c60354000341c1803200540e110016803070304103a2400b42c80d03640030075000c550340d03100d2408000207070f42004107111240c0c54446070010007034540e0282c1654061000503100507611054050254001c14002c01204a50300903030340505203020301036120364400e0003160028003800303120801000464000f030000410404c070070401404500c400c0034540c92002c2c224800c07600c5c91b5440c006109000f0200c0b0740c040300c03446107640b10481441d038444030340290041c40b400c024100d10f0442d600c40c055180c0c0200b1588811180315500c0c8140ea40942181900410110841c1075111 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 187813534 1250 187812284 187812293
    0x10c080310170c030c04020705030306010819060608011a071a06031006080604060b030f0d0c0c0e090d0f050a090326341a0a0905120c1509070b1e0304 66
    0x142000d501601c03e011701159050242024000c175011140c0c001c000d14a560303100c00055507250b1001c1e08030040c3d614034989040441c00340d88100d0f0003400b01a1a4400a0740c03400c03412041d181c60f6aa0b410304213490510075903002400c0000500000d12810900c0640b036030300c150206e0300d0b06555900b00b8010354107000b80000c2520700440c1441c02240141410b01608600c8420b00d5612413165100d88625404840c520264504c118841c072049071103201015070702c039603c001981600300161100d08694201c1c000d001c4406401c92041c00c05d015039030074064148000910050040c07000c074403018104034004c0c0b40c000a0701c0484038000160304a001e0341c40d6107a040b20203141c4103100080740918427104c0341205038020341e0082c81d80c0c41d00f12503000c5410f4404218040394071445520243c200a41c507030700d0310981d100140307060000310107401a803805280c441441071090b6141125241c84081c6500c04036007880416040031600c8010340d4414080180d450440204503034a490f04000390031889400841404100f1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 187814784 1250 187813534 187813543
    0x3030c051504060605010807020c010509040b150301030308070f0f0c1202010e061005010908010b03060604090c08010203090102030a0612120819021809160801210b0703050a1109010c08031017 84
    0x1711001ea0b00e10f48680d640d0380c000c1ea620000781e001140400c10a10100020340707000d801ca44440d4101601c031800122045103400510703082a003044020803241c50400c2020303588045500c44510151911000d09400c6540291004450000141401000200010f0940e0007508031000006290303003141c1c06d52802c40c0106007181ca45001d56400136141407000114990140141240c5100c000c0c081c0105807078a804004c018600d480d021100c03035440c003100096011080c0b02640c0310f503541000150362842e02e92200011100160060b04c1c00f01c50003001e0a0120303071005c5c80101c40d2125070810b000141c0f01e04400d051800e0555031181e001c00d0000843d460700801d0700c500c0085200c0241c84003000c80c1c0380c0080c02c0895005000042c000549014010040c8600c40d900d62129414050028440241e0740c2c0c0710201440022210745003c60b4442c0140f00b1303003502c28070500a50390701d1078640c5410440440002011407000d1440580110300110210301801411959000142040755880c0e8014035401781d195200c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 187816034 1250 187814784 187814789
    0x17160905030f120c010e07271107120509040903110706030605010f0e0a0e0c07020a081b010509180103031205010503060c04090905070f0902040f08120403030c0515040606 75
    0x2001510001003034100081c411210030015030290007000d4049901c0c0b030468020810281d055900c070380b81c803842800140460800b0700300203101c443c481e034240303c0300100d035001003400d02400c14078218488000d542c100090f04c205a500c802c1d00300c10030b0402c0d0b00403110f50142c0341c900b66209141524079030030141c00c00c0f00b80d501000010b080c0c4103010f584030000c0c0c00b141e0061140502248020480444062250000d10070a2000070710f104495900e5095580c4081c2c0b0403140c481021074002100015490450150700060070070200400542c21070408075082e008040002d181402030105980f442e664070100800d10b000384d00020018150303503d0800821092804154441161400e0004189800c011546520481390f4a20071468649054440c600234003103030f0f00554140c0244080070030b60700c55171f103120b030002d1a10301c00141e01c071801d24410880307008180e400030301d0350751108030031104080090064400b1a0b40505081101040c0c1e818002c0c100030340040680170140000c0d081004100590b4000c405 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 187817284 1250 187816034 187816037
    0x9040b060f1320070506060d080d0c091d0106052a0f0d170903030711011503120f0504050f040207020102030d0c2d020616050405060d0903030b0901030b0103080a1716 73
    0x41590350f81c040312074071410402a0050b0402070005006040c002500c05495101d00714051804c1d0178458903504440368080491f00141c046d240411048041600d000e40240d11407142c16040e52410b6000b80c12413113450911032100f94801d9602050041c0820348030b0301c030b00c40513050700d007000d010380c69481c2c803841c00d0f80d10000812541c0980b0040003004804052040a10200551854440e9a000d549821150404000b95900c6203030003040c0c0c1d42c0c0c2a00c078a000b5485000440b9241c401198051302e201d5916180c482041410b1000304601d6945495801c0c2d440c0c8203480040c0c0e10034107400100d085224131280640322504201c1800c400399071224280c1c039000e0300300c520740000c25680300782440c040031070444100042e40123401007161540d01c0224262041e0043c00d0140c64150703140d0200d01e050700503404034141503540f071000400303150301070181d080c5102007190070220542c1140d072812161349040c080074010b96000700c0c10700c03e002d000b03804a481d520700b000c82c000e4407494402803500d542c110300c1c140f140 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 187818534 1250 187817284 187817321
    0x904050c030403020705061305030a0b060102060a020c0a0219030218060907030905030d0b010201061a0c0d0c12110102040504020409050406111903150e0709150c0209040b060f13 78
    0x14520154802a24080d5900d03501030b26405e4501420000703960044241c406466040c410001080e603010800c428116119090702da43c2c42c0340a000281c01c0c500020450000c66004010850040c000468000443e0740e04031010200c01b00790744c040801a0403160402500030102144c441c0a0401e45251a8402ca10440358441c4e00c1d503404000706c0c1070f11403007c4020207640c0107120f000c03960700340ea8000a1a485041c400010815524044801014540c07009143c0c400000504a0709004080c4101100ca017101e06103051a03020780e65408120314082d84400b0108401003c0c850140b20080d0100c80060100500c25901d03282c07a501170400038002950b040381c40d146040c044400c0c111844056849100e4886490f0702c008201c050144d0180c0510418440c01603c1000040340c00c501e041c21090144501c3d40d51030724114104921510b00c1f0004002940a128500c032003800140d0300c65081680c803d46c803481010854846002155407695174402541c0c1c40034254013400720040850340544001e03002d200d60030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 187819784 1250 187818534 187818541
    0xe0f090708030702090f0a0e241807060507060222060206060d0206090f040204090c050307090b09060d020f0d0f020903070e0108150612160303110115180b04060308090405 75
    0x6540e03e125420000b50007080d50b00c00100c108400e14640b03a80402051008100510103130a4a41032254685189151b105500001c940d8040d184200c19807181040114064500c1e40c144041d40d581390500c607200c2006800200c0208000c0190140c81940204180b00043d04492405440c60710b2024082d5000500c00c4600007611494020000d0490a8001d040301c2c0c9091640c006006900b40481072698206408000c009645c240718030030b80511900a80d5040d4481c24031900082030b8074081c3d07010103062981803100030166130714107084541c102d2008200503521140d02d0420380d071a01518051030b01240c90078401001c80c6c2115002007a50701411019946031640b40c3c02d07007081480f000c0c090a011640214041c0e0010607481d650550040401080708600030300c072801c203900c1c0001d41c090a22000c54021003c1040542100c000610701e40010b0003800317004901d607009000c1811610640203401103520352101b100900e40c0c008011420003070020b2002c2d80d103d0902803807550001c071541d8080d5103040f001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 187821034 1250 187819784 187819799
    0x1050117060d0219030f0b090606012607090b070309030c1a0906030a290103060504050601020c0906060904110405101e03020711062106060a020705010c08040e0f0907 73
    0x64520800000b04880200c40c925001d10810101220780c00c044108071850220121722000903100180d4072400040001d89092402d003410240050702160500001034402d030058003269a1442041c0c20344a07800030b182e0345000040b14481074a621031440401c00240c2003040c1039229028105680c003d480e04400c080da00d88442ca441100d001c0a400000420300c81d0b80660700d012402183c105000c15404500d03403c0b802102c420301c0700c404a00103c042082c0c042d1480a581500440c0c0090400321070800c0300c0d24040c0000b030744501050f115244030303a1054000a40701d9541c4070584a103130002410030800078401e426160000e9100e802030f64070605000d0001d0820b288510300c003108a400e44c1c01244080380d503004059000e5000354034102c51850600b541c10b240c0d512036030003410b569141c6492018154500305500079403004050302860060710b041000c0c064a540004013882110428a09803091506030300700740d5080e004a80103281c00104203030900a40c021944009030142001e282590003640e0358824 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 187822284 1250 187821034 187821077
    0x8060a0e060610210c02030c0706020a08070204051e0a0204080f0601030302030a210228090f050f060705030c010b031e0d321312050a06090507030506040b010501 71
    0x20300720340c450010032040f0280c2e44181a54000030700070503001c01e01a20102410401e1310b510f003019400603880480d00c52081441009210010120b900180c9151010f9071a14245446000d0001e0301440e290002b0510200080c40381661216602c01c204900d41003203003101010f07502074454000035201c0c200b07084070200310202d1014101c0e58103800540c50241c18800644d00c01021050440721303034900900030340c0c41e2601400100015208082c51801e80048000c0045000e40c00c803800740100101c950007031140001404000003170340c00440321200f200021f0f82c0000e5191040c280c0042a900000c1210300c1c5121054101e018846422001c0d81c50700510840d990591424070030002c601644160a40344c0110b00403415060400c0d6504180e600030181c1c3d503560311518032080780004521400084a0007900044051813028092007242c800c0c080d1081e0315000d03079409103188040d24640d602d0480c881007101c10040ca034025035010059558a1800d0300301f00104007001d00c00c10340030402e809080d9049012166 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 187823534 1250 187822284 187822291
    0xc09021c020c0c0d1e0c06030c03020c0c0114132606070c0b07050910080603190c030605150a1409070c1e0201110114150d03090b0c031308060a0e06 65
    0x2c001d1002e50110010402c0611a102040d1810201180348120010800303019071285405245404407052605000604890070208043d0030540b0510043c16001408506c101100341309103421400408010f11500b100e00c125508040c0d412454180091070504581681054407860780c0c50268031040d600c9165159003040790307c007000900c104810800a121290b865810600340c2c070300207040a01100c0401d4102801d0700070840801d0f18802003260760f1a08101207440000c0829070b50040301c8059484010758500341c0030041125840d1000036420741e03030048001994050051121641a07520f4003c40001700e00c00a03070f140120f0001d0f00082c641d42c081d055100d80ca9034801c2c6d03c0032020410b000c91030741c01c0c0010308040b4104604000540003e0409009a10001005034503005407424401c1c5c2c1800340d104403110f400c0c00369920f0f60350b50000c2038112030b244045a14005105913510101c50b007150541c45584542c2c425501d40380780100b0420340016400d0b11030b05914800b001140c0c03968801d1a9031340703802c4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 187824784 1250 187823534 187823557
    0x305040309031e061e05090c061812150a14011208160203031b101506050310030b0c03010302041a0f0d05330c0f0708090d0c09021c02 59
    0x70201003000503c190120380ca180c002e500407400f00c500c19510300d0140d880c0c1d501c05050000c5040c3c51459416000d02c02ca5400401c414010000303401c001001c261117018205d003200720700700007a0418040d078403003801002d0302507040d900340d54101c2055017601000c1d240a8a44500c0c0d1403810018000b01c1441c412654140c80744280907682010255450b0b5565900420a0f8241414150103000058408001500e90910030a1000d0304102c0c800c612a46040101038140c2e42881c2000c000801b9080346503580421b0352050314066075269100e600c1c0d8841061158001442580741108000002e040d0201a6040e80d20803a42400000e10703007081c010601503d1000c4075807004c5110162500c528101200606035407181060310b61741040b441c0000d02d4800d000100d030340c642c9140e00509400080302603250340e000e25503100083c00d0030500f0095401602500c9401800032100260928180e40c42c248106d0005903c5401d001844c0c5c0c95511510294001d80400303490312215844102c200c070003034000d481184201 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 187826034 1250 187824784 187824797
    0x40b010e04020d080a200708010e1b0d0201090b13050901050d0335040c0602060709030b0105010e0a03080c0f0f0706021005180303040503072d0b070219110f0103050403 74
    0x182e84a042842d80130340711010031b000b081081802003040240b404513048500e00d02801000345048132030360035500c14900c0c104064004012650440d54000c074001110301c0c0640d181c2882a000d480180c0740341c21640c0010840060209640341101c0c40d4038810b5090313941c2030700c50900c04d136030721000d1003a000850000203010640c940090001c0501c004070707011031282040d07103241e00c071400081070508040065400303070340e10704550509200c03203501000402c0c1c01a04610b03100c00380910b107464082009406018a90410560780c1d08030070103030303905c0300386201540c0c00101169440f80c40342426559032410501041c40c6018124500c1c000100200300c450459200d5000341980c000c003039611000809005120b20b2181d4010500d0b10058601000a140302e0351203031008540d2040340d4289021680c0304a14900001c030305010000d0603c0901920380d01005a100032480c0d415115110241e06000b45040c00c801e0201d610307640e060912140b8031000b86007800c280c55410010326101c004600380d030000c482c05404241d2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 187827284 1250 187826034 187826059
    0x1b040b0d081803010f060b210c0703080903070605070201090203160b0f070203030c010203091e19120c0b19050109051b0c0309060a05030a1d0c191706040b010e0402 72
    0x1155401080b20398000c00001382c01c407203600200101c032603580200c0c03000c08004c101e61200e1900101d0306a40b00054103d1040a803800300404501807161220040406c920300d00420f642d01420015941e42540c8803070140158504164024028030595400707900c01e12441005001c20030404000201759259100a10300d440e8142102d854154410141240c0506c810445103950010a10185001d0386280015100101030300070b40703890f0605040c4101c1125008800c0202c8080088070744982c029600076400400c241403081e00b90f451101c0401c0c0074001491f03120810003440402d1201010b1140056410011070341c07a40418002c8803000c50f03214034103940c0c1c59585101ca42c030351000361024142c54000c4078901441e04000c9609a080782c03802c400402e0000c0140000c00c11580280c241016040030314a0048100c0000315540c0c01d041c0342c48501131900102d80440d40c0c02888092001b8000c010b440c801c0100f84814456a2500101c4081d40d20310031540001c54180021a03425000381e80046c41c1c10303400308 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 187828534 1250 187827284 187827307
    0x30301090b030a0f0507080706090509160c021009080d020c03060c03040c170c0f0301090f150b0405090604032303060603102103030e39031b040b0d08 66
    0xe5500710941c0c14411a0503403c009a843c110241e915031240c030242184500e4030f40310914085007908000140614644103201c89d4442842071a480041001c841640e016580c0c400d03241030703003c0900030350411446141100555000084034088030200d404032250b400003004100c2e110007264400d40d91581050b00420745d080c1546010b0b40d04030b4002c000e1250915558681588003806200490595410083da00340162410340c42c03180403001c080e002408600d649a680b0300c1d2140c10f0000c010074000034440b214100b11401e0b4001c0100b5403018008000d18105a555030340c1c0d40703100301c404800255100003440c10044000e01c03950700040c03400011500350b4441408029640d000246012000105200001a103a4210480148120040d00040c0c110041c038107004041e10420910400707107521981890483c8000d840c0c5944684d22082c040860fa4548911602c12071916030518551510440e00d07502c204504000f034404108908940c20004c00d5136120a20011089100c1c02408045e006d214020940 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 187829784 1250 187828534 187828541
    0xd09140f01021510080601050a080d0f1e0903021201060302090411040207061d010c1b0807080910210c0c141507030f0b0409020a050613030b040807050c0f0303030109 73
    0xc42050042e2420f2240304001c2d0383c0012401c03545800c110080031810010300c5d2061040502400040e00c5406510741000c041564a01e04401e03c0000c2160342900300c0402c51080c000c01901603800c8d45817002c0c5c0c9440e03d4000f450000580020382c865159140c2060040c0014816007007140c0e8050400d450300c2e07445490b0041d8907060058030030f4010340c0030000342c030001d81d07248a01051b900090003100d003803200e031910305403c5440c6100d2a000b031290200c05645100d00c1688540d11259201521961700c0d0741d5032074014454020f01e607405400018030b0400d28002604a55000c808504850520307991500320200202920308103020403011400046041c7d01007203600d810048402480001c48024459401d1903405128085074135600190391003d0312000c2401ca8018075506d203070200ca00317110307001c103075000500b6030f00d8a4820707144214000520340c40c0843070014030030000954002c0300f80c440720310300b904025415030301c02d0504984034000c051b00320340540b0b002c2d09404400c032404ac1c02035046a0a00d400403006 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 187831034 1250 187829784 187829809
    0x6090a030e090a0e0105010e150108100512101119031103070c050f1c26010504021b0f0102070204060915150c02130c08090a08030705090a030204140103050d0914 71
    0x1c0513180c1940140300803003405502d009142c0c45603514083d29094184441c01c03040c0d1000641040345032003c2c4005c2d0a000011700b019900c0c100c0704c0d080b8121480820520700600c4c0c0d56449480e03414010801000000c10001c2e140b0006400440d00c8458a840000c500321469034016041d006418004149407a11400012544178440c1e0121144680c64485451a000400c107510140e40c60a2060301035507175100310174515000d41c402907861705420500f101c80c07040b00140110b03030003168045203444015541d9480000c00400110555480401140c4824040d42c400740042c0d01441c1000e0b40029000064401d002d240d46441d0341000260b82010301c2106500c81e10762803902006428a81303180507130f481c14070b07180c405801c0748400241c5001c00c6001400c5100c00901c01c541e180c20541d83d8101007800e0b00112076120b40c0d02d01d801596030201304c0004d944075055401c007a41081c501075504044445075000c1c103060340e014004807050384603031105c101d030203000034003d8004244805044582030305150006288 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 187832284 1250 187831034 187831051
    0x15070302070515100801110412020d0f0b060915010f350109180803041b030b0703050a1401050d020402160f0507061103091c11030d020309010206090a030e09 69
    0x80e00140c0e031641c920f0580c8a00405010525400034010005020340f515802011600c0003444520720031012240ca500036842200c0940d015040d400c1c0441d940c0c83c4ca48241d156000e01a800084100e0405403030b644d4044440303901640340440400e040c0c07940e105841c42500c078140d442032001c3c8041d03c011154541c58910309845008030a060002c0101070310745200d006074400000405962500b951036090b2501d8858480d21800e04800c46c40100e04001c080341e034007503001004441d0912401c580c807000319019600150007038501e07900f0700c020f09505800940c000c0c030b8001c1091102c03040703410b2058102e01003032080d01e40c02003403038144a005050036006480803c2455070005210140780c1c803807410602c031059045540e60401881807103410341000c1c071203a0120400000f50700340711131000407840001000020000f0085000110010045072542e200e09806001d004c0c0c601202d80d200002c1d640350001c984c154007600881e400030306400e50000f821a0919015900c4044d004512014000401c00142036407a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 187833534 1250 187832284 187832287
    0x5010f0203310b01171203040201050427050106030905010e0c1f02010b040c0906120506130207050f0f0102030610080405060a02130f030c090506010c051011310506070515070302 78
    0x10082440f9502c114020041c808002c0c200c1c007070420525040c00d4031801003400c240828001c0c000540da01034141e40c00cbc0d4540880078290603030200980c61901c1c1441e60090708050525001103a2160716811440039140308900a010031600800c10603250b0170503000c1030717800ca450640c011001c07a402d002c80d04000841d500001424041d500c0115040d54400d240107804980300d1001006055031005050800381c0f0354400030005c500780800001c2081090f10715003040369802290420501c0001d001e00d004000c101011a06010030802d43c0300d010750011581a4403c002e8a1501c8a07024016011107204a5101c0007a00f003950358048108000d400c0034025001030f0f180030760007040303001a4020010295000da034a051101e860038060394185c030001041a4104041403261800051000035001e12880700d10030081221041c0240310307155409000024080103286222407001170040f03102808901140c0102d9034211034032102030041c00e20442ca80284254065000501c55031b44203151250000424500035 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 187834784 1250 187833534 187833631
    0x4050405061b0c01051302100f0e0409060b0d0f0209090703031407051203090105010305070f150837050a0e0604171209030a09050102010c05270612010305010f0203 72
    0x104c3c02c445c000c03a0030040f4400c294001b202580b600807601040c05006241500000d09949030042020010072a4a03000320b0b12070503620300300504d907000000388210107410b0440541250400c000010441030381030303004014040100e6407019001c25603405403505a03c038101d4000303003035810410b0b5900824003540c0600400300345051440480000714000e518031000850154150f08090b4145002035001144000c1710510401c1b000000a405007551030807800c03d02c1103550382110100c8410448080100d89100d00300101c4540241344200350709880014500700030395030360200580100c070110300c4d0351856588003000040004102420011000005000660500341c040320f04158411084d100407250760000706000100070383c00300b4824000c050903c02031004050621700500030b441006203964500358000d001411903192110032a09018001d88034036550701c442d4406a901c8042800120343c0f0b54200070302c180700880580282d900a481e1110b0100c9802180002d55281121043c4408030101d079141131b1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 187836034 1250 187834784 187834807
    0x807060503100e010e0405010605030a03140a1206080d0e0312040b18061324090603020d09021201141509010e04021305070e01110a0b01140d0602040801060f0504050405061b 76
    0x3c40d00038034030800c030079802d8109480d009095986540150740a81e12110005002c25805001c4500907600806844c0c1d9a503108503080b106806009219800d050410600045142c4000f502c207003403042982c0c41ca10004203100405443d092043e0140f60400c00c14081481840507120040800d40c696402464207100030101084041d042030030300320f110f51180b01d41013010601d0962031030400e1126055003202c000e03103000050249140b501a1324105035000c42d401101250035401039100300d40043c118610b860040c0c003601d0183c0b8048100308a5880c40784085200f4001c507400726040020001c0080c8103c0e8208121170b012800c0013041640e01145c41440010300c5025482424000e02d1940d035a00e90140d8084005003407050440da00d2806c2d64420b40780a008640f603100d00d2410341d087c0e503c21540c00c641940c001507a54611600141c42e252000600083e00750055209004446805009946003581d50003040112b030b40444000c0d1290700140b00043c031001c9005c2d5454071404074804202c1c2003440c02a103 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 187837284 1250 187836034 187836059
    0x9070f02100e0d05160b0f0a060510021f0b210c010503010f0909020a18150b0a0c020904170301060203091e090609060a08010c03061e12030e03151302011404080706050310 75
    0x1807006151f164501032085004040c040e140140000391b070700e2460347c0c050b000000d580c0c4001500303001c1da80d1210f5404c504070700243d400104140748003c119901c4510940020807202c9910400c101032440759150481140d4002e10540e81226100c03140713805124034101984008d0b0010380012607004c0100b003400b240c01c0006408441043d0041280003030b44080c54110f5290183e640c0d00301040010090041d01d58031039221030079032a429415a001c5c0000e80741d5107000305650046a441c2c10003e0004400456520350010150001c2c400407104031201e208010300204019120956076600000741c0300009159041042049400480c050079241c1041d0ba1240340b5421030b0400c1c003450380040d45071101081745060170895165980c10304140490182e142c11b4103034200c1c042c074071001000c0c0101007402480d0707a130b070a004200e004c0c03481c85120b070401d00c5c0c42d03454580100120b40089010620b001e4204500004210030348042d14000002003001504045e000d80703042d00f004282605690b440ca1010896a81614 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 187838534 1250 187837284 187837291
    0x60f0b06030103060209130b060f1303080f0a0207060c230a20040b09090d0f020307020402030115120c0801062a030804171908070e09070f02100e0d05160b 68
    0x2100146c81e124001c0400015240f001c80e5100c0305414584000030590761101100c08260900011958491140340c60065907005070384094040c2001080341d406c100c045400602404c1d00b036500f541c0765a03440311010764150005c02406000024a04c24000079800b1039a4103e81402120045400b103410075611026600e0100e4441c4090880d40c3d8450601802e19029107006000b0071128401107160101805035145002040340d010000da00300d00c0c01049000303100700d5001c141c000c0c07c150754a6858007204820185060032000004540900d4411141c00e82d12402605c40001e45d034580180e481d00c401102d50520041686c40d400828816000c408500380043c00e51540c4651a201040d14003410003202800f54021001ca80100810171000c100007100b03c0b51042005038181548151918102100c10140c00d00c0e402d0b400c0f0300320506210509410084944030001240c1c02c64113a2060a5050800d0300c0402407002055804a0a402c502c4c46c020b10103002d0b03520303041c880c5c3d440011403038845000464055 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 187839784 1250 187838534 187838543
    0x50a0c03110a2012100504080f07060605101809051f1d07090605030a02210403110d03020403020a0b03060d08030f060102160302010516060605060a180f050607060f0b06030103 77
    0x1150f400300c90310020602c02001e4048442070807440b10125502c0d1a110700f116115540d5980c0c500190412240d40c0503280b2600c21380c0803050301c640a0b403070801d00500d110f02880e482420030201c1644810311079050300746090030010341c0200b01c61801c600c640c05004080d2520000c0c1d80480100c40c2e445890f146000010402490400c06007400041c4181260401412a8040041d100410f02285800008998000c00801c00050b03885001000c80c1401c145250700c00e5203ca88402d0a000c02e141d4090038404a064411060ba403490317807a942d05070200c0c803840c88000e42008c041c01080200c091994080d680c008005401080380800c1642c41107210380c011a0101000840d050521502d9641008039208040c03400340407003030309030558001a02500444090010700108421110b080042d15000500241070142600b6212045014081c1815560396040c0c810500c5050000641600002555007100c40c05440280b070000d00f034558102501d42d400340f00103040d8442000c0700381511810011402907020b03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 187841034 1250 187839784 187839803
    0x911030d02031b030301050307140307030822050405061e030a0506130c08010501060e22020d1413020d02210a0305030403170f0c071b0e09060a0c050a0c03110a 70
    0xe104403d41001c0010b41450f482880180280d490025184060b9400e400b001c410307601e0380000103442c0649640004000013804280b00503d96215481c40d140d2545003121000700701d4540c0280011100111403056100801c04480004080078104012082a001d410b40d20f1440070754a9079032030943c040e80c0e220002c0c04407590a03002d100420910b1805031404030700a03c0b507540b6000004080080d2021546d2003214818a45c8400c0021002d02c03010800214606549440c0841901801001d05198290855a040000075114001840508180307075004000c05068060340d000d100000040f1203811b42504c1c1c80c80d51803507141e0001c0080d8030b07032144030b0f80d203295891505d40380003001c5404103181610045400c506210040c409aaaa03e90140ba4001c2c56520f50843c1e08080e01c2100f045040b800b409a2a400c000c5101a180300850b0302c241520400c442541d200c10300c0c000708568100060030300049090001d12425403240024099280c002d20384000c074080030350a0070f400d2141e511381c116280c509 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 187842284 1250 187841034 187841047
    0x5070f0f090b07111519050c03030105040c05070b0f0118090b0f040314040e010611010234080c100c081317070b0f0414010905060a0f1d0106080721060911030d0203 72
    0x86a10b80a052041b079032400504213072040500c540c0d240410301030a407040c0d4440c0110348200b8864818ec0b207601d604003902400360308203410040780c0d030f0000703000b0084000c481c69002c0c120000107000c1c0a14039948007012440546e0b40828131421444058011000c015000c2c0001f1505040c0b88040d20141c90709070418401c5514056000c1c3c20781480d8000d00c0a0360340140045542000b000c0103d400e042312202811480c0040d404c036480d28102e1107400101640004a84003410060000b18001c0c9440e00391000c00030aa0304000541e0340d14400c58440190b04107601c00000002c900c8060340c030b010b004482c041030500a00d55910240044100d070f1242d091125a402c21050200d041e103246421340ca2000200100340080d21442c0e102c2200810819103241c480c1035105c0c00d10850360104400a4614281004004094000d94060302d074520034001c6030310071080c0106007848114000080408400524921100305a50300c0f00940b2130414240d645200d40c01c19071030162824042e103040a0559800b0b95913540 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 187843534 1250 187842284 187842307
    0xf050907031a040e0c120f0c120d0309020a050904051501090b10141608070308090c0a03020f120313050301150b0a1209051005070f0f090b071115 64
    0x80000d004104050411124080700c00000d1608816108160360118034001d101400303e1030140018a0720f5080200803c41d801010004201c1104008801d02036905803280d480030480d00280302c0940c0d18040e00140814101c00307002c2c3d4408c10415201400540303030700d0342d01d000280c00c40754102c50a480355044603d48224881c10b2540c1e0b2800341c000c1d6002000300c0c07036002e8086040414400000800e2100603032400c2e8a005800040d18007100c444900781d60801e000385030409294005210442c085250070000c1041000f0206001e1036150300600b0100300203140d034003048000d04000c0f09a1b80c02590300014846120710510007020000d030a00f0701c081841c1c0c40c000500d400c44409099031019018126400d100c0364240404641c20030405180c40e021202900003040021b184c0528000c1a610541245050b0745116402180c41000140c540c1400c0010205042d500540150800800900744100030b021080c030503405000b0f42401101c3d080e81c141c8180f07022945000d0820305611040c103000c5000c020f580f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 187844784 1250 187843534 187843549
    0x30302090418080d0207020d080406170f1b030c0c070602061005010507050705040b190608160e0d12020c0405040503091f09030227130b16050d021803070f05 69
    0x5030214048281c4032200303510307143d000d03029185484000580009400303065603501592182030a402425043d41d8175507e140180c042600700008401e041d1714000000e103595900e0b0f204920820008060744c0300203010009c0181554401080100d0282c803d0117000300140b001c00407140a400341e60000c00041c113010300f5510a900841e0301c41d904101c0100090300002e000490301408a650a0341c002c42c03c10507440c0003403000d150b01691f000310401412400034402e17a00512060290700390401d520342100c59510100e4900340c0703003841030782c01902200c1480001110240003101614491041d00c030b40720010780c00101620800e07501518140e002040090082c9400001021100140c2c1d4403400b0303101c0f802030081c0c190344181c0b0000e8401e40182c622407400c85d01142c6100c1080c40e04685000c440e181c800303196900d1840c40036058400440401c001201610740d82103075880c95a440d114541003d0a1120341006540b1400d0017480364900c4004019158801300a940c0150515001c50700c046802d110901901 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 187846034 1250 187844784 187844801
    0x90c01110a030e06090319080307090e011d060a08011107120e0102100f0906021b010e01020c0309041a151b03031302060903150c040311030105060307230306040303020904 75
    0x80d80240382514000b0f5005456000760f550140c070040e07160405a800a410f2034103c451000c121000000e84504000722080254800e8206071640c5c40c00c50340701c00c0c004da00c440e002d015504084c0c02551880d080460308020701644010001c150492760307511600d066080d601072405440240c200800c1401c00c0040d900c0903c0d4403034900346424160f280e502c0c0c0000f0341e6040d00e8440985c089540d89525155103038150031100070150098419581c07074004034a141008040101d28181c2940380000d800458801030003151442e211000041d81056811001c22000f46400107181b5800303180042d0403552500c518040941d00f080902045880c0d285143c50540c81180f40c000040b41600b00700b0801660810030200040803030b406480541c1c0313404252010034a00b038043c0891f400320341c2c070004c00c00803c03000c180001c0058912a15110003800c02d0031040c1800e07100c00303a483c00c0d03068003c0c3c60180562040c010701080000881070300d5419145440300480c1c18000181c0c0d09400180d0000b503075590702d00301401150803 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 187847284 1250 187846034 187846067
    0xd080c031b03090a060c0303060f0605090f030109080d020c0309090403050721080a051e0901061a04260a0609031d09060a15031d0604121103070201081806090c01 71
    0x780458510010792044c02e9809643c080c02000c010560a051103a4000405040a40c885a511584401c40a4100d81000f1550b9100d40c4070105000c0650406016051440da0b010403a030342021a4031005d10b01a402c907140000180c40180240c0985a130f65402e264051802500e40d5640c940c0386050024a0503013004480402050b00c464007181194091481944020044000038050701c0740d0526141c10840014100f44c01840d1500340040102c0645c8000e003144d0601b6001190784816041a9655020b148120301c600303a0400d44202841100301c81310a8203600c000140c510101241c0c1d114001c881202000b81d000400c1c10800b00800300005110305a03104045031818101d00c0d1610002d0f500c25050300a040c0c801c0600906583c40340d000e5002454031a8035412280d903158402010b071903582004490560b014844132006004050041d900401110241c00245103000c0c1c040d0019140c4481c05480c0560900440001c0402ca6000b4440280034105040242c03c140c10322078001000d03013210390501d28 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 187848534 1250 187847284 187847287
    0x9060b030403021b04060302040c02151005090109090206070206030c0d0b0405010e1618080a1e050a11131a0102070501050906040306110904090308010801110a080105040b0d080c031b03 81
    0x1001c83d400013074880c94180081480e0007600600404078004d8440303940000d401c2410a010a140140c01094496007004000344d94461035842414940194205110340b41c1c001212100500c842001c0382c01580170f250014001c0d074544a22540410015402140c070410005000700e0000f14544450244c46003071401104c0034851541170890b09492128041d003d100030040351400e0404060042a01081900c004c060420307000e59540c2003140c6554040408546980b0071818074025608402002c10145400c60300070a0210403695804511022035803c2a90040c201d4000f140b29203054000e00500e0140c0c5c4481c03041c01445040064a001956080309060100600800040d61550004d0303a007101d030000340c081501452483c11090078840c900800ba089418140c003003080c1030304042411b048500300c1c0c0081244020b1011825071501400083c44c001800010040041d860680c11001c00824002c2c203119034040c1680e2450f03001d6108002020351a04003044400d00d801c0d120040044c0c02d1009806103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 187849784 1250 187848534 187848541
    0x1703070c091401050f040b031209030609070803090907031517010b010305010308160602070f141506010909021b01090b0105100302030105030d030e1207061a180a0e0a0501110409060b03 81
    0x4a50900b0501401d8001d000411480d03240f42c2d143e400c03c06500070080c0c2076a018a003203c003580070303035070010880c40d0081c810381e008284000c0c2c0004a501c2143c4042015600345250704c02013080608002c0d141d082003540307410681090043c034030084da00a00c2541c0b0b0f4906420340141c01c242c04d54000030006d40c141483d01c4010030120b503280044420926a84c029100c56030501e15055000340100000900700340e00556422040200000c0c00d40d000b40d5105c001c8490408080e003000002d02012501540040c0000d0010040e11000e03401034030b96401080149040c441c43e442e000360031030708450001d80d03060200c50010015400c12040c0b180103403a1925055281d5818403010994803010f0b410680c0c100342c0e6a60029190b00c0d0240410b40240b000c444800380c2c1d5403000c0c1030480c09400d0b05d01000c191442d041340b18008602d442c5891008074400460601100e0356800382d0040142030340402d44589000707045004001980a2040da030300c6444400300c2c2612582071100305c404552283e00700044980041051 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 187851034 1250 187849784 187849811
    0x30703060608130312020f130e28090204060b07060903080a06080c09150a080706030b060a080a0e0309130204080706030b0a1404020403080a020a050d08071b0501061703070c09 77
    0x72007802a4240c1400c10a10021103c0c40e170007071051205410b00180b01081c50208000c60180c810f0888080000b111410b898000008403a11801b000304101414000302e1a1030703c0324030390408008540000c20004030f40c0c2e5602c9400c800b43d40300e01011100035035286907110400d50400640350700b200c020a400c0044609224110b0341d00d01c1c0100c0750034480c8000500051400d08002845030802130082e011040c0281d540c41e4443e07551b40e0500401c0701280c100180d50f9264144603041d103c14400a54440b207158540c814408001c00910a445049020070030030501d80741c80c0c0091100740c0c170010701001640c89141000304c0d400e207d1290000002c040c00c02444c81010f6440310301da4000d4036851200c2082c3c48030b031040010024880c99000520442010610224194011920980c1c01d8003e2054800c00c041c1040111140c1004681ca0404035a5004d52a514080d040041408141c41440005116a102c0b101c102c100c08555004c0a5198000580502085261172401c1c005000540b02440b030900c03603124 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 187852284 1250 187851034 187851061
    0x90a14010f120e0d18150c062a021b091003120525031d061804150e061503070e04020a0512010b0405040e030702030309090702070812030703060608 65
    0x4010000725080b040c480601075440030482620f032000312030f2a4075540034007810200c5595400303050007159002c0018402412006400900036075a102e1090001d2a0780e410010958040010310340c040e0034102028146950152000c2601d02e9002040c40c2c0641002c0c01c0140c00040f0286070081c005402032200b1090340005c604160707a405078581c2d14400c402c4000700d59900505940c10004c080c1414001c0400c6030989401e40114000c1d5101e04138080705850001405101c4904203070030107000c0004d04600c0d0b00700606941030600042000c074010380c0b4240240a111182d403c41c400180c242018018503280200381050700207018086903082d0310300800d0181900860100c5a0701a540001d95114814481d40443e0400220440e064610b035071610403c0038603400500402d8007640c6000b0300118018000415903c405038001e0045142c00d03010400e2150988025007a40f055128681c0c020601d040103010500c0b03024060143c2541b24a0b050781d00409694a541c812414041038405010440d080140c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 187853534 1250 187852284 187852307
    0x90a0503070b0d0c1413090f020304050709020a0212030415060602150105300c01091a040311011419030f0b011b150e030712051c09060f0204030503090a1401 69
    0xa00004021000b0141030b07036078112104020b0400d282c00208100182d91b180d03c81c1040e1080c500d0100050b400500c1078408074481510301801a5202c41020055009143c00130140a40c051064402406010142e0255900f00382c0301203501c18450001075003c81020310840d0700905580c8002d06031868900211003c0610600841d8015440c2c15803907118070003500d0140c6821040a46201d07010220074a00d0798447c004012024001005003600141c5004c00c4080380b110340c440103000d5450076156540d03103d82803807a00304c0c141c148002820000c1e0b0700c5040b000542034091229190980300c0081d00307001000c07511013410000d08140362014644042e640490b107a56400c4080c0091840090141070081d68848811a2000c0d441d082c03a050010300400071000d00121442110103101860f003402c000c0e10280200c2c0c4007130019081d5603201500041c9181c1001c10b10601400f0002641140d2841c0da0040e03a0082c3c009442543c0f00040c02d80e22030402c0503580004200c03507000d80040200d030b680000c24100c00354 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 187854784 1250 187853534 187853557
    0x112020705030f16020102011d1506030c030a0c030606120f0f050a080a03060e180d05030705040305060a020405010810060e0609060d090f050601150509130e12090a0503070b 76
    0x308450082040410403186045141e02400e41c0310b030b2180391801921042030108900650806da9807900d0030949000b25040220120040c040d14000b14892242420b8010520b030303454403408040720042e80302400700d0301d246401105000c45150845c01c0540640303005501c03641d000b5010783c00210200d103c07922040782d555070102460707003542102d040080c1342201060014101d403000040e0303450555016480002141e07505940903c142d41e420041c0300b440c0e22502c000804a0700b01900c0800701e0340c800d10095034094050304101d03040603102d403038281c0f80550032114803002a40c002002e00156030000000c0703900a212030b0b1181c2d200c07030804000801403620b028615019000c08070b40c0100d955075075410b940c11551300c01e0040022042a081280182681c01d1003920540908000482c403004644443e846a41071616400d25002510341404071011010089418072941c40c40007416440050143e540740155020842da1500203040405c40045110b50245110340d01c0300344c00b089148612000d86821040700c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 187856034 1250 187854784 187854787
    0x30c0a030203090a020901080102180d021e010210060e0a05060f100e0604050306040501060e07020f150705040b0d09030906030606170a0b090108010509010501060e0603130507090227010503010302011202 89
    0x946004510b045010913009500c80340031000451099015070140c844460412030b020b103503000810a100c01c0304032249004c0e4000001d2008140b00f000316540b01c07d2882c0c03062048485400d06002ca0302c007220110b41000201c04c19442c10700c0008015405000c0e00300b1800c03113842102843d074000141d1052442e00075141400310781d041581c680da071a0402c0d01c00a00c4007500f40d50482c41d01d468081d000301494092400c1c02c040460102d0001d5100107200080c4106902c0100381c00348461820940202c030080a100400c1400c10004c0303000c625440c0608201c0509000c0465000074601d000350556545420000402d854501d04100c1140d005031078110580940c0c02e140c8080d2600d010785006403244950441c0c2007030441c0000501041e05600003482400b006000300301c141d880c0c1c0e070200e0b062180300b0300031a40300c18280003242c1c0600107480d4a1842074860340c01c4a50f2079580354540e00603078124040d13204246c0b1300101c51049511032550b10800010092804500d55819070380080c0c10144820300440106c3d60 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 187857284 1250 187856034 187856041
    0xa0605060a080a03020102210103080412171210150207050409051e07060329091e090c01140c190f081b010b030a0312090f0206030f040314030c0a030203 67
    0x440030218005004828142e940c3c0c200c19050103400303940300000f0040404548160211503180700256103040e01c3e0320444c45850140f91503260401c60001120a807000c0b042c1101103240d030341224004180015940603070006514220107000c0302d80285074403480584c0d2540d20200350442e4041905005e480c1c040320001150302550030841c0c0740001c00706400c681003413001002c0710045400641841154910303a02840590549641103500c402d2041c1260070078001004420101d10300032892a511074002841154402c0c10b01d0342042c0c0c0103c098486027216000300d010620556440303002071400301261140c440c41c0c84e400d051402d40d00c0c04003030301d0015030702035029460080103c2d103517842100580041074161543d2880c00c401807100036161400a0301d601c1c2c80216072140c00d011038450704960b0107840d00d20002c1030207815003001d007010310743c204c45c4043c5c0f40810b4001030366110051070041c40c10004110f500e141c1460090a1056519515880c015081c000c020422000c541207a112202500d0302580702c1e203 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 187858534 1250 187857284 187857289
    0x10c0e040203220c23090f040b06270106050301050a0602010608030405130b031c020d0518150f120105130911060c0a210906090b03060d031205090a0b060103060f030204020906120403030c02010c110a060506 90
    0x4bc001d08074221600c0380c03000005116904c480658180c030320445007880183ea40d40760507400c071811407040b03400507081884100040c0ca0f025480003501c08245501082c505c100c440003d0a00c500406041c650b06d801c482c12101d000d0b4104041071400809040540c90000c0600280f00748030418416a40f191600f440c00401c0b1034100709c02d03104c00c500001152515220390700300111061209004c0d2a000d0411840f40202c3d400160090210700c0340c000b41512608041078050240c01d82c41802e03c0791007440b0f404840380000d0b2541c0c0146204040e1080103820754031110f1401040d070b040c02d038014400c1081240d424828043c0075011030303070484011104651458150f15059601094020719803240da8074100c06c12002401c0070680d45002d504c1040205902d64a98006400700c3d00035000d000d4486900e4031041c401801c03d5402819005801407003141020154004110043c81c101c07001c400103500d030031960361032030307024060844060094101001c40d282160801650f580e0b82c040090105501c079004030300f440c1c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 187859784 1250 187858534 187858579
    0xc03120207020a18180c03050c06030708060409060b0303040801020706180b1f0e010b0a08070f0516021f0507060c17150f060c010c0e040203220c23090f040b06 70
    0x1400703400711100c06010b0305000c05d00c802a48401c8e0303030500582d035158017146040c43c200c1e4070940c442d8803a01510303166102444018030f40090102c1d201581e80c035114141c2c2d501080a040202998400580d071100240781050540f90390110074848080703d00441030010340c030900c0c0710f41e008001141d44002e07018003000a202c801000c3d400b259480e52188004110188110020440385003691100d0f1060f0700c91401c1129414000c00f0b01d00b001400500020305c20144203a200308410380010310046c0d500740105400200c00010004c0440442c000188003410003e45000b102000c4000703040840240e8508220100e0070400180260300380c500c40700841a050f0369180c60b510030484003a204a4a4200d1861001d000305029000c1c00040382a40507010002e10b45030003185d20a484101d005010040c00900b490721505c51024120b036004840312020401c00c060100e60308100012000000346401c03c01d00344070303031924041c01c1d03400032044900400000c21030070200c081c0c000b5403d448010b50740c01c9400a40310b41 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 187861034 1250 187859784 187859801
    0x3040c0b0a050720030c0f120f010203091608060406020c010e010507081005090c040515160302010b1c110603070c02061803010506030601180b0d050d0c03120207020a18 74
    0x4004000c203040c01e000e5408400360481074402d0060080c030b8499891050103400c0602d400c3d95156111002242050400c90704404681001500b407007d8180c050200030708044410511620681d400300030400c0560042094000b603803e4425481095428100221344485000780b026010715000280300a40751000d40c4402540181d24008101c1d60501510003090a001641d02c3d0011984940c0b01103420b140c00310010740101c0d482c100481c0f40ca4944000e1220003030100301c036103040520511017542104c0c0301080c48605180f00c0d9000140d80e040d040e04202010100c0c90318084004440252040060714510138900411022920141c0742e030b55581e41202c40280320345009402c9000461401c200d46610040541c0c011401ca0081c420340d0781d10414169111401d11540c100c0c68608010740241510702e5001c03d40e555009000940b1415040e00c84519040c000f0340584000b5003412051740c05d0503441a403012850449020552800e2080e8000400d081c440380030b4094a0807003800c00b04421040c0342d10510304c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 187862284 1250 187861034 187861049
    0x305070b0717010b1303110604030209070906030c08010803091509040603080325081503120a020a060b0406060507060f0216050a05060f07050406030902180c1b0c010c0803040c 77
    0x8103241a10008010035180b0709003100c0811241c0010440c84d8036141540c1c01e48002102c3c0c950001d145031a030344400b4411080190700140c04000220141e03e800d43c94034440c00b00790701d4482156107000320080440d000340d0a10000c1002400c014401070101000708d4140230002c440f0002440392a030301800c030078468200070650003407828a0001c01c00c40c041001d9440b039002c7c03c000f24140b81241600c2034800010080260020b040741c40090940100c1c081e9001001401508590003a144a1880e0140780c1c00718102c10301603485140841c0420140703024a81c035055003034a051107418038048001d0064004c022000349000c0d11003100400b048100d5041d900208040018190800414240039480e040002d50a0ba4280180c0700020400b281144005005604030ba841a00c0d1a180100440040250050072a404003501c2c4a01100004042c105802441040389080ea900e0100321980d54000b0107a5007003009800c01d141c040300c80c0ea00030b11042c4115030822410756986c0c5c1e651034007a000c01d030720740c21035003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 187863534 1250 187862284 187862303
    0x1050907090b13051201020403030509060f0d0501170f0a11060a020127020901080d0905120a0506070f020706090305030d180f060b090a0203190b0d050102031f06050322030507 77
    0x1c981c0103c8010300111441a60300720041c5212880c050b090348158080500030520070002a88907041003030003820b000781030a0f0308030f040500e5040c80a040c0d0744282d024204051007034482c100105000d10811414140c114001d201168450b500c440d0310541100a451040e900404c03900c0105000390004002c80105a142d140440c1210400440c208034010040e405042041c001156504001480c100946a030351100071840389000100300540c90f122464003180c0c0030781d0145030005102005042e00552032512100c00382251010000c1c40c00a15901c4901000594801080801c00c00f108440294031100300108412502410032002061b282d08020410141a05c1460901080d0350000c0c01c10501201e441200e501c4a0b1000c00582c0016680402d048155040301c2d94040d07800d501c8000030f4400605080072024440d04c440e4220780044503c81e40748102540d5a04c0300031800c419103409080d45c0c0c14501e00711300b072100e1074414808078103a4003115419007881034030a1600501c195030010750b0115103207 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 187864784 1250 187863534 187863547
    0x121b0c20120601030302010510080c060d090602031305060901021c150f03050616090311040b0418061a09220c050d110a080721061508030c0c01020105070801050907090b 74
    0x42d40e5620244402c1c1c0044d480c180c00700e02500d8003c0011004c98008074003c003030000c2c0000412295a11046249486603640c5a8540026000b400a54401c8408007460113044007541070603810040c000b0300f0000140d204200c49182040700e0900903005a08a06c8000340c990313086800300040307500c540c01981c0d0b02c0c84d04107800001c1100000d0781074862201c0444844140000120554042d802da01000300a0380c00d2264003003207420b00c0c3d482030141c180001c1c0b000c03c0c64810b0091001c150b04400f07005940c0c1584440e8100a5100d146100408080d411360300d03105a890720440b014543c09040c5441104040c2401d02681800203084416000e2b080040000000ca40586443d540454556403a1402210701290000e98035001007100c004640000020700c0d1a0504a400c0e0b1100701c1d000c0000700c5243c1d55400e0203496091625a002014280c0030000390f81c1c0d000070221003407624813801405811613040c0010401140d40c80b250440c1107940641d001d030f54985410200369995147c03504200c1c1c0304000407428 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 187866034 1250 187864784 187864819
    0x8130b1303020d0f080f04060b0a0815061023040929031c0f0201021605010506180615090105190206010f0b0f0a0f05040f0303121b0c20 60
    0x4a0020074800e07021a40240181d01c1c2c103582c800e840001840c041548000081e0509443c03044455000703204480010b505a5400c1c0020702c4081207410100d02c6a0218800e54859811900b8640d04400e0881da20110146e40f1800204443c1290880d1440c441340e9a6102c401820b1a005032806000c980d201030019141d070301002001c0c00d0b1080380702814a0401907402c20b00307003404a541d400725081021400c4078880c0007a4103807811500f21241c40115942004103a0280104504e61501e6600c80d00010400d418644d041220a80340d0345220700c0002c0d0031000f4003646070384604a000800480360304051303e80d008507005039014041e07041540e9500052541c0306031102d50100700c20b41030707403034201385600c1701c40c2c0f20a0001c0300b07400340e250b4414000504102d41848030717000e90300d95207442c1c00c09c1c50b1071894642c8800b0a801c40400c2d540c403c0700410048011010f51000c14011520741084110b40f0030780e20102d40790001d100e10749880d070143c8040c1100054a10078200102c0003540048090040074852040302807 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 187867284 1250 187866034 187866061
    0x2b0b0a05010b090f060a210c0e09101503020412120912050c0405090c0604080706140901020d0c06020c01020a02030d15060f0f02011407080403110601080d08130b 71
    0x660524240ca040c001094840d0454250307060308601410850511001384240040b582c440c000f4082804020480030b004002c040c16607442040c0300b001c01003a07089200102400c1102041d0150717100304490002c00401803175290214040312009040001b40c07260190040c0d00038031440d000002617108498a08042c8074011880d42c000a00315680c40d200307140d40b0f12418919800a400c01401c40d0050010910b0300c0c0303829005135411a1070501541c2102180a001480690041c2c2c031030310f2a5089107004000c0143c0008140d10700f8240d41440071715008400000030344807011700e0540014170041c80c00920030300005038165456111180000c6540c0c050540700a5569044101d1081c0d0480c00e143d030098400406442d280304594840e210280384500c1c6410988500300300111401c115035907100b24944441e40340364128094061622102c405060a003401402120744441c04521607010000402a85500184802c4016007628212050307464012510300003022800b001b0b010081c2da407041c0b001c03034540d004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 187868534 1250 187867284 187867291
    0x4060f0225020906030102031e0415090b070e010f09033003020c1002040f17280b060301111912150f0e0c030114010e040603030806032404022b0b 64
    0x121403c00654804d403c250a0b4072007166041942031036551800c0706080d5201000e504148103035261440c400b2048161400c031181e00c00103403030303a421070300601c440c9a4100302e11010040b001c0c40c0c801c6049004150182001015110041c5640c0082030a5840307010b04075505080c07007a0300c4922500035141d4140040c0a90000044400c0c3c80c003400e101c82c080c180c818030840341101c05503606601890310708070f007189418080019012132405a11140340c40940c00d00a075104c0c43e07035248417403d2400d00c54201000980401412140070b6850a004d140304040d41c54281e0301c441000350031100050342080400c9034201002d00252040300d0070249036082c0810346c542d501050714100c00f04014001d940f071280b8019440143d40d6102c064100300300621940c40b82e94102e4070f200c10107061408a00c0040f43c0480d080758460703070082d4002403a0000380261440c0038014400000d44030001c901000d001c220015101e9440600000d01c51042d40007040c030782c001784201c07800100c0b440701a030110302c14190030071050405d4100c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 187869784 1250 187868534 187868539
    0x1d06090f072f010b0108160f201b01020c0109170a0206040905010503010b030a03050901030207060b1801090e07080c09060301060e01180c09080607030506130207201804060f022502 79
    0x406062245e51161043c0da03c03d41a486d4200e554501e1101d0641d642c00c03000d0000c4080201c021505c450050b500d15104150704040c10090100c1121900100f01c841d0220000302c2c11500007500c140d05584e80000c3c4e140684e00d620f15004454440d914842c1d00c0c3c010444002500400007045c00035a880389588014103c2c0c03010707030003032025078602010551120072010b03000380454018080744425511a6010b441c03494450000050350850040c0003031481d6180c05107000181c070013000140700b001c20f01e00444c0c00c812103080041650030705148190703894010441021b80a11004000900581d03000d41140c07000f4001182c8080155860300d0504541c3d441140c14203010758100148100700e60b1003071000c0c2c4112440c2c000908505d407036441e0120040c00c030242141d80d01a6005041840720a402d100a1407054490000001e040c4021482c004503084800c61031881603810f031072004030301590300103160740c0f09a202d0380008400c25004079000003030150b40921001c0d070400c1c2110a6202d81144124020903008 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 187871034 1250 187869784 187869791
    0xe130e0a1b06020303070503070503070e0d050a050d03111e0f0c07031a010605040512010f0513030801080c030303040b070207030c0e0103140105010803190203071505011d06090f072f01 81
    0x120300b0241da50b4802a244a070014008000044116200c2d10242d03030000b03054946004180020b40004181200d2590309413101e030409003143d001c03c44200f01e0402c14000a0a0610694036141006000c2c1e00a45144890258400c03542e906440041e0084580b00050310a07078076202c1d60301080e41550380503940800c0342e251850901c4965420410745a890481c0e031940d45a500e45828075091020300e807601d100c2d03083c1c5992242e03040055203080c1d0062502c42c03a81c080c103c2d40082c40d90305000301180c506074000311541d008101d1200c0b10f500c0c044126a403154200e4801210fa13218000220b10308074060344060403032101e00a0108075445132003241c038101d900a4241d8820401c3c002030721801c9440a10810403d94002c114100d03d11182035540380d800b81d254010b683c24000c0c0383d1145199100300031806c120441d40ca43c01031105226110725021501c2c510607001505150210104500c03071406810301c05003140034170014529078424849070040721a0fa0859910454100901001d20050703004a10055401c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 187872284 1250 187871034 187871039
    0x409021b010203040b160203070c062a05070e19060305100b030c0f0f060d060806100b0c030f090d0f030819180f030201021b0f16060e130e0a1b 63
    0x203050090701e00403034000310030503043d13101c0034800b5041c04003852884055000c140304003008a0b20381c0441500038401d90310b84849a101d80004900b8152185040c10040046070b038021000c80c100044044c113407100164544400d45655a5400f01e002400030380c28803450524001108201010905800f209040b42062080004500401d0785611000c040b154001c500c0750318040061401d44015101a400603050701e04d8001619070071801d072591500305548647c401000c4c402480b02c08a111001080b90700071103401c00d03c44103215620fa100701650103000b0343d0701107180c401c90f540d5030f0104010356038009804d07540080c0074540600341040440d40c40341c005064454034021698140a00040002601c61a028828003951181003600403405c09804565080c450035003121030039000002c1203c0c4110060a080f10141085440c0001c0100e001d03490a480e07213000c01c03800340c001711403000d9160101c07106940500500c00c114014800024040c200d4410501c007030051011851025050001ca01103400000343c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 187873534 1250 187872284 187872337
    0x506040909050c041b03050c160c17030c06010603020a020c041e0b06091c05031b06181203070c06110307030b041503050a02090a1103190b1002120d0b06040902 70
    0x902550801c51940c0800c000c1e003050311b120360300142d03004903164000d505000c2c4071000545121041c86040310324060045041c00450740d803440501a6511003070081d4507015003020115201d070418440d84e402d0540110350800d8190080c0318500c81070800cc0c0080280c9402502c000036005190100c040e49149803c580b1030981c03d000003107410401015240040300780c0b00b43e800006038040302d0026900e80c0000e1000d0524114141d051748402d0310300d0401440b05007171100c0101c920101d500d00020003503010840d04003103840d600082d00c0d4030a5280c00d24403001c080c02e080070780c05000302000041031868000b0400080d036030960700050302220103480c1049800f00d003070080c600c880407a000144c61540605500030041ca0504c4407a80e00c8071300f080011896010b40000d21005030800d0710700c0101c1000d0130040701c54020485c454030b8900e40742110f5102ca244034a100107900c9139003482541c18400000102c464072701203660424a14524080c2090381d545907108800c00080d00b29641c0311302e9003086200c51503040f2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 187874784 1250 187873534 187873541
    0x3051c0b0109060507080d050c0910020a0b0103150e0d05030a0605010804020a050402030c0f03090321060a06050f091507030930020d06090606050a0632040506040909050c04 76
    0x600068507104081801c009003070310307141c0043c3c0c41106c1c43c1030200f05107540e004032806413502030040143c0c0161070b001c1180400c0449000040e6100840d480044541e01040030580480d04480d00310464198540c481e1072203402510000e050b48086220b500c403ea1034080d40880194811000c1b035404100c6c00307484000450703500300d041c2c0300a03500403d5440244014940740e401107411964000c452450445214401c080603081110302c0308583d0004150801d5482c070002100c4046010303920780d4800d5247c210000781c4940b1043c09428208100462030790381c0100f61104441070042c3c010000303204038860b01060241d07540900000c400054200310000303458011503011701100d16400050304140b03100b0003048425210b8191059a02504089400000c903490b072003200134041c040d03540410514103007018084082c1d2190300c08004c1000c0300d04036400c8100d48000203c904d41d10075503141c49c1c9175014070707110300c1038091900000d40c003800000307002541100e607501c04001940300d10103441c001050303401000100e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 187876034 1250 187874784 187874801
    0x50706180e0619141302250201120908030108120f0a05250602070605280f201206030c06120603010603060f02070b010503340e0403051c 60
    0x100103440007400000d900940095100350060000b42020240c0d02d444807161a80f680184400b110300e040041207800c00204114010803948001d51a0502031401404030b800b0f880e4900d200f0800507074018045a21803045824442e944c0d04e014042c3c2d8426040010141e807081c80303441124891405c21404480c00003040da0302c80030701100024105a200c62081d0741552004440070481121001c0c0400b00111401c10020100d02801c001611001e07180342500865070003030005002001402c100c00d12011400100c02c0b4004409070b80132a405e4180c544520240500c0c030007002c880c41a05010802c2004120041c1a1280800e150380e49107840e100181740c0c880e030041b10701c1a00220100200c0103d54020510650000005800040c40e903550b0b485a400716240e0068003041507030006156000e00c88140195805000110b0280c620902e119a0f4440c02110224009001c10007128076851400e403840540f800510280a0fa4241498280741c01807595101650b100303040c45a44c1034000301405e00c0d10a0040 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 187877284 1250 187876034 187876067
    0x4020c010b011220070807080a08010914151302070204090b07120e070521010c03061a1c0b011b110103050108030c1011090a0b0c060c07050c0405071e0804050706 71
    0x103021311049405007070754000307901910038500801c01e10340051103881c0244200030190784c854415504001c4c03560161215611804401d889600030b00c841c4c620240c43c81e4041c0c038000c03640200700e81140402d8801074000d4038400b95105181c0001d1030140841b130b8034064032807030055803400281103030700004904449004004003400ea00816060195041181d44040303000d150000303c00494107003221003400d551080e00c504001988403c8100f15810300325000983e034502c08100d0600341400c400e50b144280c141203455181c120f4903030f1038680550340100a05203280460180b04050201e1604159140c12509103c144c0000d2412000045401c004000d4840759600039000d00120f84a0840000c040c0c00e5002005909503001c200c0f1a000c0c0d91007800110003810f004030788507103840c0c03c00700ca01e0410310014032070800c0750000c0144000180780840d40c02c04011088800140c29161441d0403650314010842c440c1050890744414000701d038114158903c0350744180c0803905920303140c81c412039512500d11440711 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 187878534 1250 187877284 187877321
    0xc0a0b06090c07021309050d0c06060b0901050d0207031103040f180504050d0c0c0807060c12020a0201170a1d030903070b1312080f0301180516050702130b04020c010b0112 75
    0x300616210b0f100d8107011700080c902050541c40c1c1e440c1c040c00d2031040801380012a1003181e0120800905000f18002065100301441c1460113a0f00082d109104600c010711180364006241010035008402d800350a401c850110703512103840e0511072506060034080d078900004400e15012520006003c0d032481307194844050b0200c0889098240c3d801e40d4503000440d40f00485034400f1501c41020081c500061065070f48007200c0e03005070709000401504000d201c0046400009004001d0b0360031039154411100840c110b03488a6039807a4001d0b0042403068841c070711030040c5c120801002103001010b810100d100b201950314495881d4140c100034440d4a034011208611101c0c208407141000c90f5001740b840c0940981490400717203882031304103a4426000443c52000740915469403511070710819600c28101540c81918200300c5401074454014090024070030303410782669050400c0550041e07400d1000c00340003951101000c2c030026000e00402c1c0c1b41e4134002401d401c8541c6a90000b40612006030800f403006a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 187879784 1250 187878534 187878547
    0x4030c03060f060902030c09010801051c02062d07051006140f0f300a0b0c0c0a0203010e030903011a06040509130803070e09011508010902031003080c0a0b06090c 71
    0x68015060348082d0b0458540d03200c0c0e000072000c416000551007040748000d81031381c2c0ca010500141c403001c0c040e002503004a80d1848014903400041c0c880c0c500481d011160203032102c140d21b4055844052140340c2c1100c8240c5030941044440c081e8000e800c2c020b1040c0705965401400d40ca0103000c496548c4203926031007443c1c417140e00b10b9003003050140340c0310076020300149140041d080104c3c1d000101100442d0403030b9a133000c2040072507450494005ca090070039000c0d0001c001d2689600000c501c0140c1600d044400004080317025000c1000754041c000d030301600a1110307c404844150310381d00301942d41c44c000d50a000e243e8540d541103e040030040c600082c1110305042c100020b0020aa00090100001300303050017294012490040240d4420615591000700344244601409001c003810303807140d000d05335494411100103404c120403c0c10341c0c59400c0c0068507591014001082c0c111140e001800e0b130980040c102030011000714803015802c0c01241541c8442d00c8210a106c08001c08660ba0000d400051210 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 187881034 1250 187879784 187879793
    0x417150705270d0b0c0d060819061515020601080105010f08071401140f09040609090503070f051906021206030309010206010311060403150507020f0303130308091606090305100204030c03 82
    0x400080b500900880c0d1070000c550f032001082c0700c003650064140880814041c103c069180100c4015002d81d00c0070f003960b040c400b8880c1d210199242d400511590f02c80303242e521501c2c012410301004041050052082944100d0041e48401e000c1c06000741c25420000089010180503010381c0490b6026001406200c0c501058055074203128211107040041c40c004c08040c0038107000141060603501c42d4101e0341c4e54075a104000c00c40e0b031a644030103034080c241901d880205002000366901c0c01d4005116081800031854114180b4008481c1e1500c5851138010841c1401042c0d0301502d5070003004002107030035407075900405940307001d20000e69005a01503001800010494046003424000c054440d42c1402c0e240d03620440c031a040d03000a100076654034400c0100e2281d042042c50303590600d02d8051841c40c1046c1d01180c3d04003191a0000e8148408980132030400c010402020200b016500c2406085540b2414014008440c501c030540e090720a002020f00054603d10031201160b6200b14100ca00030f2070341d500d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 187882284 1250 187881034 187881097
    0xa0f09050607020423010f0f0906030b06060313050102030a140609011a0a0207090212090105360a02040e0f0d080106021515090f1b0c0303060103020309030417150705 73
    0x80e850215000c0d103c01002c1885061005c034007a0250645500c403083c104041c40c0061322031540300840d070504040302000400c95440c2c450760441c0c130071f45086a40366540c401801d1650209131000b020385d8130000c100a00b84005520010210725542c550f030846449610410103030600a001c0c0e48014050710846144480d400001403008040600507902a903544240c43c20485c0c00882c0d40c0c1405c030962400304100194280319440e4011100101c01195070a489a001c0c00d003d0b035101043e179481d556428006589904125210420754000c000b07119030342e2007003d9141c1361420040400c6003881800070001000c0e004130309160698078643e00030321143c28a07002100c02d02e8009004101c24454038440da0150781c8810403414454815054825090b040265540d071100c008424240c00740c86d01401242d400800c040300b1030340c0121092a000d40c4a031940d000361410b5110b5035002c041c0d40704291040b41003c40001c1810300c0c0d1940f414515088a98860105031418840c01d07504c000d40400440032843c00342d081d0351 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 187883534 1250 187882284 187882301
    0x1090510051003051f0e03130b090103181a07110c010c2306090609030412060507030b13091b03030804170c0d030207060c020a1e020d0807080a0f090506070204 70
    0x8880007007040c1d4a80701c04d410300541c81501030301001892580240d42200d40608205044090010351401d16028401d0014400318000c3c62000b1000040520141e03209070084456400d980c550804012501d1416038032941c40903220303040c0340c0c1e080700008050f0741c02000d411200c2c1e010341019298520051700111500e48940204a60715030001104103c0030710184071040500141b0700c010455814290b01151811000500c28801a40100700901120400b044181c0f003030341e88000003180e5a2940502a8090041078121507000190020411083c5165401c0152580d01400c1013816040360003102c201d0941c1030f0302010b00812410000704000030381c42a414001904406503041c20f00d8200982ca40c28030110071340102c002600443c0e039409000365413080c006110100c1c001840c5200c1c82d5a5000d0440d500f41c4030010803245c40e01751800a42d200d04450801081d484111103a4414252820398a16040703840c4040c00111500e040854243c0260002d5050300d1000740110305101c01a0300f00405420200c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 187884784 1250 187883534 187883551
    0x10b040e070c080a0c06050f0108030d05130602120406050106090f17010b030f1605101b0302010e060a1a090408030a0b0607050106080d11030405011407020f10120b030109051005 78
    0x4200c1c400100f80d140026158089883e5510101041d046c05c150080c0c9401925502020071404010860310344004100c4500d040100004607a50742e491418811950450401411050001404014030307021481c0951050348148401c006590f205d0000315500001070043d04000340d15440240400b6444086002c16612040f001041442101d400300c0c0c140344549101240c9588800301c50820600d1012240e8007a00e000c0da09203d06c000d4a24006212103144030075812502d120078840c4007814070070340100c01c5d002d207160115013003802e0548800006100030810f400d01c80300710000c00c104529000c11468052500030303611a0031501d03403044400082c000c039003c0c0743c4d00420800000380010030078020840242039620180120001e440d0001c0c08103085292040503d030400c01c41400540e80000d04180c501500510564072140180302061102050000f01e0350300900b00c0700c1d86444640e00400078400c034450320348140001e1684100307050030b80e10206002000758100c020032865208645d0b0099900c84884d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 187886034 1250 187884784 187884797
    0x20f0a03090204090215030105010e030c0f121005040803070e010c030905130207020405180105070809070614040801150501030f060501050306091b0415020106060c020105030a0504110402041806060503010b040e07 93
    0x4c40d400296880e03034540400c03079984000b0004201e10341e00b00c07004125000e02a000740861061800008081c0000d140c02a80b1845c0c00f80e5044001f01d50400041c054a5000c860401003408c10341400019508100d907000300290716040081c185500c41c5281c01c10a96064544207202da0030700741005040c4448c02c070581d010035070170302604015980e9405001d0140510102421401004c84500750a66800500e994140041502888005940020708004440307451512404008460110034518802d9620220582d820281b400d19403000d00542607089880c262400c002e070b1400401004240d0300305100341030200c0c0c4180b00050040c2000300b0318a50000042c1b5500f00200b000c5200c00010350050341085040041d9003d01c6400e40b5024410711001d8031032400c090741101407550008101e448020f001c1c00d0500d07183c002040400c4610101040c41c00c900a001b90348072610b6142d014003040d56a01c0c1c26103c00e040000000d0780314003800480781640c0010403100d16041c140a03011140410242801c0c00300a01c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 187887284 1250 187886034 187886051
    0x61407110f030a060905070611070e0403020102070609060516020111090d0c091407080f010e06040f0e070602030d0501090204050d0f050c06040f140907020d110c030d02060403020f01020f0a03090204 87
    0x1d040c80000f9490340304500000c0d0000030703820514642009a00850705000d070300c032180200b18a0019000701141c445041d10400c0d40e403140740c200d001e4020404002d0805040603503a104001a64114620800051600010340801d5180807070071307518440c000b030300040400c04c8007040c10309088009000d41c1d80201e001c0e5130f020303544803010b00031103074141a00b9401410300410711071010b5000c0613190700920010b5804420354105080b07243c240d080035144900c03c5903190140a062541900001440680d490558180030754958000c0d4881d80842c082c0014686400d0020450000c50b00c01c0d07601b510070246c4030040464455442880108421205690b1403140b40080c0c58150382d450014405812100c414008082c50202c800010300c01d1080781c2e0b03109910303820402c859075500003690351140d0804e241048001038528443d6080c2800114400c0e014000e030403040ba0050713000211a40038910945c04c69407642e003540020b80c01c07401148841c1e80c0200c0d081150b220400e00c260422180140001d0000a0040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 187888534 1250 187887284 187887289
    0x12060d0c1a0438090916111204090b060c0c0d260901120e0a08090607050303090312220303090c0918020a060e06031603060503060c04090501061407110f 67
    0x240816144101040c2e2070700d98611282d0240f2515107039002d903c9045042407901e60000319003900082100c00c1c1120900d03a40480588a110301c00c1c604c030149000d41c0c1400300f20114100141d07209000761800b240c01e00d4070048090401c002150300c0d242030344015106002407403041000d2014680c4017a541d4150450007680091952000c1083c10a034100440c3e6071118540f002401d0801d603001e10804051030541c41030040040846d501a0322a400030409175990150707800240d0307a00a82c003000e41135210100402c8000700d000070090500301036148001c040b035a21980c0c0c000100f200d001001a41048054010300040e01071340100028034070a0000482068581d0840822520302003052145100c14a01440540c1464124a4041c1032246880022240741c0c2c40071a060340301c0904613080241246008900f8140720350b02030f00c06464000c081e0340e80d500703006404040c150840d01a0003a218680000003c0c1c07580500c030303a00115030b0741c04442da00b030041503207420075001383d42c0481036007040ca8803daa18496 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 187889784 1250 187888534 187888559
    0x4030c0c06020601050f04020711010c0501020f0c0102180d0201140a0c2108070e0a0308070203030909040b010305161401050705010e03040f09060b18060705071a12060d0c1a04 77
    0x41450b40e00501c007562610b410042412904c00030540540c0c410803a6401064824004905524007030070518005986840c0c928020312400200e200356040114035403120510640040c0000c0440c444a0f0207812051010054658060b10000703001c144010a046c6000d09423002603c901c01e0103045c502c0c032061807a1640001d04030301c080c404c4076100e0001e90343e8462580155082d174110b411840c040d00320380340250225128030a00d020250880101207050030441d60100100c954100c00030340b034040350341441d16101100c3d083c00c2c00b0840f1361740a5140c04000625079410300c82d00f10703000c02c1c0408458600303601c019a02e5900c41802075815540b00d854040708158200010070007070000c02c072103034031007031421143c9001c1b0b610301d0b00024070a81041140b48119845000005900001144c95035034401c1a8034040b454240d0644c000b0543c0900160030b0ba01c04a090f001900f0414120805144165078450401078015820070004091141d003010500c580050030881c2c080c28004c10428515141d19801c0702d4104 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 187891034 1250 187889784 187889789
    0x50609131514030f07051c02040219090302030d03090c050103020c0307121206060e06040501030c110706090303030c020a020904061802030f01061e03080d0f020910030e01051305060a0504030c0c 85
    0x10100c80d5003902e1058241001003000c42e0498401404101d420500001c00310401a5645a03500201c1c00e04da00955440341d046400c0c0c15070240c8403c0311880d9041d00a801c03000684020f0740300380900c00c0c5004a25020380030785400168400060b450043c14000194002e4210070b0000b450391000f440030400003408006942c41e0905a5180c07800c5505181d2050020343e6200d4000c6020041c2c01002021580c44101c150b405440003401d011a106000200407503802d28010a03c8000c1d02c05c002000440b65000b10701007040c3c0e8000e54092144044807441aa9101c1842100035001a02070b400240480d01c02d43c800c01c410280c155030f040d4040c1d00c40c0c0009240109652074000725035034401c0c1c104064800c2041c5e4240d00030100109100142c42c541b071f210f2050041402100110f9141c40034a029903102d9811904298801400b1401880c201407000b0001c1c010b14a0ba120b55600c0d1401054001c950080e400c402c0583c440300502c4165203d403907440c003610011300f08070140300d541f07a40200000c040f10204d001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 187892284 1250 187891034 187891049
    0xb040b03100b0a1701090c02060a0504080903060708040204060e010b0a112a0a15050f07020f090c190806031f020d050117010f0c080112050a05010213050f06040506091315 75
    0x1003c00d03c410340602c24201170b440342c1c6c0514980051a0f894940200f116030b44882030480010313813a070b11400e01d00c980c2c0c801d04003c41d6050243d1030401c00629000b52031b09003c1c3d4002d44041040503214980221015001e00600304411000c1c8038070701c4400d100b18813102c0d00c1040704041d00c844221540a071202c4904100d20030790030042d6000c4400d6541040e00244000348007066041c4184001c001018001b44144d51501c0d004a0000402e80195210144921064040680f801c0e440307188c4601035944035005118922501c0481c8012807800c1c030b200da2111401200000c2c080c202c00020321550050190403414840d2030103800744810044a0305e6446014000d15100188006440d1001c4100b42110030780f102203003802d0710f07000c074071a03005600c240b155065460030940c040340c01d155400e0903440c00a44c520000c08942c00060105001110402114100c860560344005014440410008580940e011741508510180000d04192802003d4642c28040c190b00000b640d07680c02103a8120030b41c480c0c11500 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 187893534 1250 187892284 187892297
    0x30f08032e17030a0507021c020d11040510080607051c060602010212130b0109020c1005040501390e01090305030a1805010507020d03030b01030f0905070f0608010b040b03100b0a 78
    0x42d00c169141550103903000400f941c64420342180103081e500904101a0044041000740c0c9054804c00e1070100016400604000d004455031070441203aa050103152401f85003410082002906121040e10a40f8140700c060001d50750b4404084a840d003140300081d201190072982c8480030f09072846130001400d0103178000340c1d50f2280c00700040301403100904204128078144400c98003040b181002607040d949400400f580d40d140b01105a49008031803c3c100342c1107464041070104120056000c1461271041c4010690004200070030b6103501c030109010781310620075030a41545c00c2881014604041003050600d510110307100c5d1141891500034003c4d6a0100301491541400e407810005030000070402482c0c00e510b0444a42c0c08601d0807101180020249510b0b0403d4403460b038026080304d00c1c41062280d0422444266061043e60b4000301d104842030780001d50000f1812505c41c8c811170b0706030b07205021401c2c075181c41c050707404040e548010503000c04010b8921002c038450415000406c44000d1a5a418 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 187894784 1250 187893534 187893539
    0x60103090b0f04020306071704110609030115030b150d230303040f030e0d2303250204060501020606030a0b0613020d020d15060e15070f080a1701030f08032e 69
    0x140c600301d4050706400c103101d00d01c20440540348c20300c042e19901c030768030441a400911050010602c036014480030f3300d0303055007011505184c20040f02c0b10303c0c04480c010148602a901c0c2c3c03410b84070391201150080c0380c010303a454802c6000300c0e20003240c0410746092038000d0290380036000c009605581054804a490360085c4005406050303006580d0005004111660341c400c0c450b81d40c0303800400702d21032074680300d5404c0070b941103411000610940b150400c00e424444400f00302c1003038540744200050003c038803480c41c1c00300200f807035480082c420380318060182c003e1103190195141ca0012800043c00664442c0c0e01902641011209001601003203d01d180d01503141c8800d41080ca0a03581c80e501c0380703040d50411100c01c200180d4001c071084030f01c0c04162401c658200c1b22414a6490748510340011304440600e109101c2004051001000c0c2c280c81546c400013488498031031000740358020300c8054030b0204400003800c0401c6000b4011508a0511096054181d800000d940e20b4a840c003442107142803c1300030704 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 187896034 1250 187894784 187894789
    0x2070f021f1710031b0e090d1103070f08070c1a0301030203010b010c0201270b040e090d05040e071209140c0f010201140c1605011b09230405060103090b0f0402 70
    0x200c51003414601c42d0800c0d10f0b0052030080a50b8161202501d8880c0f01ca0320b00501981d40051940501840c0e69500050b180031a20740b0340e6401c560b682c2e100051110301180498090200c11340d03929a41c400c0c5000040301030703500e40307031009d07000f82e08162801002030303100050703402000c0a0740451042e410845902d80d0b241d03004160854001e490302030b0504c41c1e0380403001c0060383e00c034410a1810303140705041c0d1030385034030f81808113078201454020190006c00028041180d0402015080c403500c006401c0302c02c400c08002049400f40900d204603420039082c0400b05a49070f004100410450240850010365010141c4501c0f80520408540780c0e40340d00420000c0410f428411044030751000207000a000e4510400510400010b0007410140c1c580e07001700301c280310340c0c803550076080142c2d801000030300c440080d150681041342c5942c2c0b8401d01107580c0104c00103000314945104a482c541e81c400c245a18031180b0140009088000c02d6603040540d03d90405000400c03081c44a0301401048800070b401e89054410f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 187897284 1250 187896034 187896047
    0x20f101e020306010c03110a08041205061003050a020f06090d0609050f031c2c01020405010912050a060c140c1b04050103050703110310110c010b0603061302070f021f 73
    0x2001400300340100100001645c00451076190140c1c58a8910404094180c40b00d0800d1ba50103001440003400040000721200102002c0160900550039285a51190901d0400800ba140320003401e40d00318040c1e54025240c0071203880848500640000e1034448180002200e282d001c100031a50345075076800c8241442800c01c450707a1030b205020021483d00c0041281484600d900c407810350180c5403240c01030041a85420480b9440118000d419000307400c0086601d400b0f50040d0040c1c6001803465100010391960403a59001d04030303001001340070740c0b0720300c0c0d00c078240070b864020303041410320600035100e440c000302040007484000c1c003800c0075005130f51080320101210010790040c0d900c00e5041c54010b0000c50000700f040d4003100d520648078580d0a08070004203040012030301070701c595685400f40880c04615100c00812541c400c0c00020005d11050004101207070005075401c640002102c6400d0482c4c3c941540244802c41c0036101c00014a03000e640095002034103006001c1910742c0c452800f20030340750804e0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 187898534 1250 187897284 187897331
    0x10c020105070f0e090a020f120103030f050f0a05130f0603020702040b0405220311060a0903020f06040b1602150408040f0906081203040822050a0f14040c020f10 71
    0x607142102d50030001d001131410103c81150740c410040c01000c00c2060784254111004495103500c665102d0100100c40503001c8003d2000b6004035202000074800140300b90308440c0c260000c0700e40ca90400c801c442040701c103a004074003904c3c0031403c28000407401d401180d00d08170051410703542c09070341c842141c414407095480500c0028015410102030205040800d40042030302c21900300320340c4400401d41003c4030a40200005401640560803c0c890f4071588c6420000034039000341c08480311100080d958a903540c004481c0942100700c010081032039090100001c1141800600c1100c42101400c1d40a07030300c080c019101210b07824030002d010028429054080d000a000c000800c012061501c841384e91103c0307405800d840b034048000002000c000f200c1041d03600b59440b400840c1890040c0e2814502c3c0b07032455014113480b46900c040006010b1056030859016503d0904d070500d400e0084505010103403040c81000c03c19800340300c101c44c14001041104031000341480d0801301d40480c100900140b082c4141 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 187899784 1250 187898534 187898537
    0x4050f100506060904090c170705011b11093301021c080a180b040b0702100903020c0d030201022104060f02090f0f0630010f06020d0311040512010c02010507 69
    0xc08010b99030b80c841c010b50310240070564000c2070100c0c1902c0c1004007000990400800e00101e441102494403000462070b06442c800c0c1c03503001c41c052040e8003088001846070340007081500c0072610040c90f4205801d0361794100c9600709030400e41e0a60213181e86014101032030700419001c0c40480201d01584c0c10845502034040e0420030027240143c0d81c0000b00051001000340c05040d8550a07551861100d5001d88000707550414907084450400d0310700304460400c02c2d204c940c0188030b403508059800001e4840e5242241d41500140700c5628200113004000c845900140c003555400c0c0300d03003141c01ca10180204041c020460031074506181901d0488101d84150762118586032052100d246161280c01117100140c0080f00c0e07a0080c1660803000400758032452640d14000303201c4c680c0040007002c1d10ba0740d411810298030481c0601741e032184c00200c240c505038803800d0016840400c800c4d0081d8060340c0403220b2014003145d03a034605500d40d03000c15a50001168141d9071a07554084105079180d0a1003030300d400030b80e103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 187901034 1250 187899784 187899791
    0x2c060a1401080d0f05090a080105060415051012090204020c061e100902160501230604090206040e0405031e04050108100609051201061a0405180108102304050f10 71
    0x10809802d90f01c403040040030040c0000b40d205400494001c90540b01c1d13400c4014032009007a503d0760700c1c580c0640815034003c0d00a0f41810307100c104080d40e540403d000c1d40e13005800e04450132410a0115a9541c40708410901240e13155034410150b19075000030b01d400380300103000b1b0580342001c2c00441c0208842d403d1040440c0d02c81e005106500c003d4503618000c81e5070f5004050f86a220000354001c00c1254204000c182d5131802a01e60462181c0303180340d82c68800703082d0303d00300b01c1e45c2d030b001c18041500e4024500946c4068104410f004042d801c0c500e160b001801038003100e0030509400070b04000e16107902c4003050b0407031010804100542c0e1000340f4540c025801d2045400d00c2e460078401401c805501d0007664820f05c03001120003440a001d5110030028913088250b404100251101d06403283d0060044600807465080303240c0f4110105030850b030480d06c03810000c000003131031031241200800301c0ea1005480d01c11903c81040580e0501c1075624000c0b070058003e84803000e10005030528003403150b111070800c6801e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 187902284 1250 187901034 187901039
    0x3040b01060c110907030c0e0a030b010e13080c0606041a100819050a0b0109060206010f0b0d02070f150b03012a09050904031d010504030f02042c060a1401 68
    0x105495038111400c50602c909052242d240800c2040c0b0710080c5940c010200d031040164682d40b50300608800e001c41c1d2a0402c030303805611b00340f10140c1c40e0b50001503d8007104c00c004009018850740c4003a0300a6000480b22540c610301e581d01c1646a210280307041d840d90024050041d140b416110314240110400c102c59020408507000c074a001801c14901000c0c800340701d0000c1d000d45050b9035285442a00310004020a03d04805040020140c110104d8000303070718a240441d026000040c601e043e07803203c01520141b47d14181508146921000130300014540034000c803000105002c001845a5101d00400c2c1d0a02030181001c5007124503030f00403207110f83c2c1003a10184400300d0805c07201c2c0d14803e0030520303003003046000303402980d46c01d81d1a0300a6030042c0d800e4040105066100c90403c09507540200d00c0c2c0c16040510004451900980c00040c003c800e034607541c41c0041c40c0c198400f210404a1024104c0d001040f0440501c843e02d0300a00324002d0340100d4108a6001d140f481280d0800c085030308003549650 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 187903534 1250 187902284 187902293
    0xf0703030b0a090e0a03030b01030b0604080a0c060f050d050703090c0801020307110309060901050306040e07030312050705030f150d0206181305010e06060705010908190806030a0201021018060e0601060909020304 93
    0x5d00c0c8140203810b143da40c1d400d03050164880c1c1c02c071440440010340426511550f0380c0e0340a9407001c21540c184d0f041c0c216440e000c0b80692040990040080160352528145031051540c68014000545000709155542d40c45800003140c141c3d00714000d0182000040c1c4a04e080300c406081401e00c0314400702c030794004110011450362008261b0f60009002e00e071031901c83d619407001c00e006145209291401784030b621000410035500442c40e140c01940c5110034420303034403100001d598900003a545034000040c40b0002032804a030303140000030f01510042044900b401a6004141c49600c90b0b105807100b1000d81000900c14181032451071241050068104080d41c500300508250704005480a032240e0000211182030000940000030020303009024542d03549072003104900f02d4030007913a401c00030a110030300041d15840e001c0340032a00c1640680160a02c04030100e0714400404801513104244505100071002003002445400c0c226074103440200955418080054a000c119501010103240100108800607 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 187904784 1250 187903534 187903543
    0x201150501020d0302071112030a020d301506020708010e03030103200307090204060810060804030c0204151a04050f06031909020609061606051602030f0d020f0703030b0a090e 77
    0x10f202d034a07005840c0d11003480d0030000e03210080d207401c2e4006402e00d90321480313100110082840191a03000c90300e050000c40c5c41594001c5044441e40a0f040504040903500306a407141000b940e0741c1d850002410300b620341084035061445802c07100c016400580c05020140c0244180d07880f2028000045046601d9903441000b4031840740f0202c0c041c0c08042c14a9101c80d1400c00c800406071005803015516642c031050000c000d410204c4504114440301c2d600001c50364091440c4900030340d0542d50302d0341255075603001c0c0070103440000c0c01d0607000f80d40c1100001d260040510301d8030000c040041e5a9565601c1e290401141d11010300301d10307214260070014440b2007044418042d481984826000c80c00301918000100e040c011100440c2d0811800120f080703940d02404c1c10b6211030361285004010b15214a0001480a445c5a2407100580c0c01000107808810369840600315103101d805026190140103d4a07000b41d4200c44801c6010039240c440c8d4044c945411281c040c00b4111224080103040d002d81c0c000f0755135 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 187906034 1250 187904784 187904803
    0x60a080c040209180c03040308251d0a0807030b070203040e010315061203030e0f0105011404020c1615080c2703120c0703051504020907081008070b03010501020115050102 75
    0x71540020340040d10386543d4440703041d0382c100080702001460659100c01c000ea000700e600300c0000b1f03c034000003540c1c0d1005201c00303c45820003101d034820003042d80905a5008405c99104600102480c4c510f40042e504c1c61a010050103002024146041c50f618020b00030581c003820b1007080d5001407005000b412601c440d00c5046982107203208ca0314003181d1410b41c0c0202990713000384503004140c540e40803c0c550160084442c4801c0030046681c507005001019080f10000c0c0150310b40344090540d0400f00e0302e0607030050201041c0000c259641e4880b8412080b24420b02580240103c0c0c00384070b018040e00386c10100141d40080b84821042c03810031956035030120500758422400c800341d4004407103030540d10100030304080c40001861084d9100c1081450f90350f00d110521046031648200600f00841c07083c8005410302a03907014051100c583c580380c0c0240c5410b103000f4220102c2104002e000580960104000350007001c44688e141d59039410080024251000d00151030080e150303840d002c0000303036800500f6084 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 187907284 1250 187906034 187906039
    0x60221040e0606030a0608060f060f010f05221203020604021903030f0f2309030f01061202090402030a0b24030312040b07031e020301060e1e010309060209030604050a020108060a080c 80
    0x130b603595a41400c20090801da0010740703052185004200000109800503030113400211017003c6800c520b1401100d6015000c121000014014841a0701c4216290780086d81c071401c800c81d001c42c2c29103449691020340310401080d00180c0c4101e05000075400d2824441c1c00c00f080b4400306102c054210748000d0131020440341d14008002c980e00f00310441030320501d40d602c12420b843e80300d81c0701e006003a520310b0225006503608601c68050814005a010705c14400c1c14115480781c68075101841c159005c111440c44010820707605400707a480c54a00060400002a118541f061001e10941100e0b5003551864003285030384c18021f60003000185460394048908d47d50187e4003440c4601159a41442107001e04104200d50090311080d030103040d6600d0054020310b0595040f070784c40801d200d0030082000303240e80480d8500b541c1d0240034002c0c240154483e802c01000580202409031034900700e80c1c0800c3c68004202c82c02c4e0b41682022003c0c03821036070b0042040390820800c84516542c281403194540d00c4020f02c0400700d1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 187908534 1250 187907284 187907287
    0x190605060d0b0402090a2403022d0f01050f0703170f0103021c060b0d0303050906060301050417030721020904060e24030f010c020f010f0216020d060f0501060221040e0606 75
    0x1c1c03001405070400003114040407540c02c000c0c07100303002c507c03005803071804224440c00d42103e4042c8200a00410b00951034241215400011009010301804401100c80a4100a01006021038100ea544005c0c0500340c840d84e41c0d0740c140721a51504103108c5001410307a00d00b181c048001000580d440001c02c0ca44003104600080307814845141000c0100b110074115600000c0d61022403003410f801d51b01a034824410242580c24950303a0074101801c8401c110360050510174890f28140c640392681c40075603408281428100c1c1c0c1d20300c92800183c017140820802802183c1c000800e00c9c0e00b41410b0103510020306100f07071004034504104070640c00640d000c0300d070001110031362012817030590703030400800324410703c290000c010540003030310003d44589000311840f61940c00c2c1180b05d001060fa03442140c6424030140c5013880221907075400c2040c15070a41c003041d03411644406645445040d40d2051500074026500140061300c420040c0c0300c035101c200d46001044010a000801c00d01207800c140071707070002040701c0c1c56 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 187909784 1250 187908534 187908541
    0xc031801060f06020d03060503062502010b0303180f0a0b0414040f0c020106031b0303051b0c030f0102130e0c030103020d03110102040f053c01020c03190605060d0b040209 75
    0x45004150660002910b405007003000a45075402040c0b25880303107603a95083c407201d80c41d48203140d0b07036034020794548040903c84d4000000c8003010011816107118540f001251100e00040004e1968000032000c0708681c0181c0d00c0c09521340380c40424030310402010360b0001c001c5480c16002d00910b001d2441074000d10341510100040f04c8c2e840b52301c0384d00040c4181780704210b140ca0120009008183c907000486011004075503a0011100203c0803104480c0c4c159203442c41c140d61603242d03144030700b0941c0d200021032152020210301c9540502c0721203120440d0341e0006031141c00749881000218440e41c0581c0f4007030b0b50344090160b012003040849056a4040d244140d007800c0340c0c07500701c3d100400b080c5800e90a510108010504560a065181c02c0302c2d01212071100d625110345001c6440c0302141c0361898100c2d102612036000d491742071007401210b6014010b840c1583d9581c0046070920042c42c841c030720294005034204080001c6403282c5a0883e10940784802c2060040da00d5406d08803014001a01c038a0400001 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 187911034 1250 187909784 187909831
    0x30e1023011403160e06040209221e0b0604030803060a030b010308040e0609060d0b0c0d020a020c130606210b060a050a0824061303060e061602060c03 66
    0x1110910314040e031020200e9a941d030a035003075907031210015a2090150090f140f03e440d07800d00102c000e5400a02d00c5080c51388902007008000c0d0b1010300e01540001d11950050516100c2c002d64561950081202045490b03100f030316914418903008503919070a14244c06441a5103a0900340c4060701d9116134039941d281c480500042e040c041c07a6100600544d100b100200401040380058030494002545044040d19104104500002f08440741c9070040d44600d15400805c2c0400b8419400100b151400c0745050b61403c1c00109a80c0f20b402d01b8000341c0d0050003003e2031810155090140e00d21105020003055082460013031a050301c0120007110350142620761144892607078842504244010085655890829030191040c0c0102820754041070749030300010029203100000120003c003030150428803040c0340d4100701503030308148031a006403065420003000090a92241c040350034400700c01002e0341c0c60a40c480804d0002e03450310000864100c14180405110130310107494200e841001c0e054100c855007000c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 187912284 1250 187911034 187911071
    0x405011104030c1a0324010e06030a0e15040c1703040503101a0d15020f090307031103060c0a05181c08030601030e031306051b0601150f030e10 63
    0xc054000040014008200f01d4007403c08422107000e0041c0b200280904140c4c150300b8081128450308405041c040c0c4860704c200c2e0120110003130014100034032000010008509035810450b500c1e602199200c01e40c02014104111b2140c0443c4503085003d100d2a2940c0d030070780840c0c002c0c03168200c8d01501748410413015a040c819a005031070090122100016800200c40203841c00c060803803224000383c10325520a090800080700007e403c8018180c1c010700d112080030007136224800c501c0030202c091241c000656810701c44040150300800071003960a0b031440806042c0341c40a070079207000349002c004200d41940c0100607200402c800b1200c0610a44042022403001104e203010901c3c0304204003d6901044104000345020748000c0e40c0401805c3c5014003126501d00c500c0e04440030440c81c0c91004c21035a84038400801c15a076141011306800c81001071120f01d41320081e000713110510701040000042e260f1103500c0100c2094903240c1802a82c42d094001a00d80072500c0009110640f42c462820368a8655207 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 187913534 1250 187912284 187912301
    0xa0f0f08030405031806030411011d06130303030e06070c0209060112090b0a0605010e061801052503030f051302090414030a050d060902070203030d0504020a150c0506010501090b04030b040501 84
    0x50306281d991425280c155140d921200c1c074010001940c05498084d8103044054a10495000085650412070b0000543c0c4115401218068041c0c03215400503a5484c6d4001034501c64503440d01281c4d60390308519018007642c0300a2000e410691040040101580d0311540507504070703406441e5401c050325a813004840c200d01c030303403c40c414050600319407504124005060074071505240d20100689901c40700111000e00c00425403990200c0c05200c51300100000a00250007050141000d81ca800740754800c201040703150412015050100401d11410b164142c01400c0301094003400402103807800280704d8418103840d10b00603015101810020301042085d4404a1000016070212521060b01c6031004000d5445036124a1000781091000100400380303009541040703600402660070400000400c0009000c01001680d204542540000342c0c140400031580a44030301d5aa03607402c1540c0c9062071850548103034846070400200388010440500c41e2800d50381940d60004102c6440e4480781001030140100c803 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 187914784 1250 187913534 187913543
    0x310090c03120c14031e0901020304061206092f0f120a0905161d0405030f03070509090f060405100312050703020a05060702030c0f060f0601050a170106120e010207050a0f0f 76
    0x540400a2140002000d006c11003140c001503451611800a0782181b8021008014056802440144280340c0140505032201048460005489030703240c03140c805035420000d200c00d01c500c0303105034a4000311444214603404100c1e090800e10f40301130a0360341e800921415000a41c002007a002085025501e1f82010008507000070403100385020560441c003200c0070303d100d0000615804512140e52000c01802c0901c1140c200001d14148291013501c241d06910007003040041200800603000303503558081105004002a1504032060700d0004180300c00c89202400501400c0c9142c0340400c0041c403000c3d03480070348851900d0116140c4259250982c9800701840e0018032900403032081201495002024001a001040844400317a4103e8907042c1c8605040c1c41d0900103540402c0052525400f030002032001403c5854082d0309040c9180d0319500031142a08140300040d04100004000300c00ca000d601c406180d03541c0214940142aa1a80d5450700c46d141c00411076030310f5003024414071030f1082600403200d400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 187916034 1250 187914784 187914803
    0x20711010804050c090a06090609050606031302031e0c010311130621060306020a081807030803040317091c0e01020604020904020301110c01090516140d230c0310090c03120c 76
    0xc0d80106c4068000c6001e40f20095103441000155400140109400b9104c050217080c55622011100e614017499554141e8040c480c4445c48004e0b9070b203040741032480d0840c1401030100c0941e804001404d40d0200784200211810600c420320304c46410351030130303000ca85041c200441c100b184100313501c495580c80c00c05820020b1900d5000418880d5a0b0010161001c19548808036903443c9520703018007001d0620795015950240c141800000e1800f0010342e00607019040c501e000000100d02d41540400403146018640c06c14505508500c00075900b8000c404510308100007042c800c0030000390364032001403001c1d105414000204095440a42c03104032040c82e40140255a40300701c1500c0c5010f4040040c00301c07928820311a8140e10450103000e071a05503600d900d115161804a8010499141d5200c0810384813401010014160401c1404032051602440d6024017400c0c41c01f1010107081841c07107a2100c0c0c10a041481c008001021302d000c000aa0707620042246034580c07501c030200c40707916006034028500c800 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 187917284 1250 187916034 187916041
    0x6050a201002180315010305070e04030302090402070f031806020d081003082a0102030105010527030118020a0b0906071203020f0a050d1a031b120d180603020711010804050c09 77
    0x6600d42c000c0d201c1e01044c3e0490300e0a02c1c1c00780b41450b5100c001d1001400701d8010a40501003490301142a5401a00034500541499a468001001c90344840402c0b590b00204180c004101900128062001002111003c0c041d900d4500080c5d19a0f02030b800840c1008070100008043c0703a101c0e9005005074ae041482c554480c05e008142143c4000094021703180040e80000d100040c40c014000c60b416150183d44460400b0100080d40351004603845e949807007401c00318101e4501e91024841d002008a12002009400405005100904080d130700401c0300c00d00b00f0806490103854280444418a03400140000d01c00f000a2086000340076801078455000310010b000018076600c040901088a4101410080082c4086505481100300402c0e42d0301608540710244034040d50800f215221071020b409034120080001407581031002e00c5000402050415000700605900d4050101c05842d5500b42145858000d4a540d500343c140b90103030604028450300040c0c1048401c0c810049480c4002e40f660f80c4508 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 187918534 1250 187917284 187917307
    0x7080a03020706020609120d05220c180501081207080f0c010501060e040e0a0305030606070c1508061005030402041a0d0c0509060d11150705030a080a0606050a201002 73
    0x32083d00c01d110043c8201400f04404107004544408403614241c1020300d01541440c0810140c9001809400e00110541c04c07440a00c00762003403206401d10070320380c01220030b05107101031034800c4080d99014030701d0b1300d8900144030984c070004c0c1d60300384605110a0380751900f003a454031511503c03030744241401c00000803c00104c520f1054204030b068a0254455003203080f030307000a00040318550780b807510391948040c40341e00c00329000d1001960012009843c0138502580c9403249400f00c100c0c0c1c0e000540c21146062a603450382d07405100c4a07005241250800440429900010000e000150001e4070442e0355008030340c2681c51800408030f540d54050100384188000c1d042510f040701e0207100f0b09004040e003c00152052406040c1704030420b0f40905091040c140050a11a1240d441c0c040c0e468800b6003000b500f00800c004001a001c0186142d586685600e45950742e001601c07110388c041c209200d82070000c0852160000c071002500180300090701d15007030100c003900707144c00e01618811944910004d540c40005 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 187919784 1250 187918534 187918543
    0x603120705070303090e0f1513020f09040f11030703230f040302010c020c01090303030f020412140115050609300d111b011b020402030a0207030806030a020f040e07080a0302 76
    0x1280241c495a800e580e862a21b0326407614202c900c0000111444001003065040315034021250717001901c1d480d459008035441504030b900181c481c0e04144804a11502d03c0c4c40c15001d105c82c00d0f0f9000b44140a0640c0807507e0043d035003c09800c1d0700900d9250200c10000c0002d20b0144106003c2c1806004900c0c00c04900302840c202007614180c0040d400e04524050045c0006040c071240301d81031350749001c99803458038118000d01c004074018008580803c00003a4102d02041441c08035400f44010114112035012040d084810700002d000322001c512204018541c0c442c400c0d00d04886043d148049141d1b691002d08510001c0c40781e0480b05031107030a20b24021002c00003020101d500240d01c4410392942800f5045589020702e060407030300b10040c0416100154803417072021140b911a440cac0c6c42200720f0315a0008003a038104603100d0380c0d641d5020850300305041d4406074042e0810302c02d401601541d07102d5000308903070303065042d445401240c40b141a102c540e81c04000d060002c3c410401500c02030081c601e4002d448 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 187921034 1250 187919784 187919789
    0x304060c060906060603021b06010e061c08030106030209011701050a0509060d05060405010b031b03030306010f0908190b060f130c0207030203030d05070809070e01031722060201110f03010905060312070507 90
    0x3188d034042c80c21061040002070307144c10b075480000e1954082e42c0d90401c0200d80700e1865608101e40729035800d01400101e5010156010700001d032030250302c89501c0b80005007a0402404403054a030401401000a500c418003078200341c03001a5400e02460795007002052642010400c014901c1c41410b041000380b101c19800100d00e07680840a80e203a00138103492503000e28154600c07070366054104001040181d0700550144240503030700c1c01c201061a50b100c15403820426a0441201c3c40303400030040c4c904010100201503032150044030144420b41452020400300c20207070210480d200d9951201610490003001180300859006041720307a50514420704d41c003e48000c2d10450081504040401c100d55004035500090b24040109141160300c4c50312152080c5041d80b13440c05144804202c0c2451580c00c040140031711303201c4c181c81d0a012900c1c086009084480c2c40d050448140d4007408030b002c945115504a9045031611040400d582c1c40b00c40000f4107002e400c2000d0000301000145141c200200490507004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 187922284 1250 187921034 187921057
    0x10e0607200d1e05070807030503090907080c090d0c050415050f01020601060c03080417040803071407060f081902040f21030f03150e0106170c07050304060c06090606060302 76
    0x320364040c8030502086940007500100b100c1542041d503108a4442c0e0800703c0a01e0148046844940d5140411814580c1176001920590000540c001403420141582904613106181503001d601d00045201528041d040354988591114103050003071145180040c4064000100f0400402c0403e00081d00e16120a1140a0084680c60710011141d8000708025048403181d485010081015680c01c8032169001002214500071108009482d04600c02c06840507200c0000155907841690600b040d030f46400d00d205c125580d108220610289030f02002c0c3c0b01408555082c42065926802c51a0004010790383c180e0710094070200d40000c814504003003010448029072135070210001c195222960443d5810805004192020700c0c0c000000c2c841d80c0070b002c8000b0028212404907441e40d82c404000c00342a071000f00000e4419150105d002130045030580c00044108803149401100d40ea40c0e030702c9004500c9104207019003001d102c0248400c075007105062550100080022548500002d402504190305201 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 187923534 1250 187922284 187922333
    0x3100b070201030e070f0614030c161505190e0a020a0b0a030b060708040302130c212a030c0203031003110d050a2103090f061e050103060c0806010504030309050f010e0607 75
    0x421123211001241d014440072044d1510700000700019000c0c010130f62004440c0d8407041c40900c5981c04161041900503006680c443d02c481e00383c0b08410003551036084c1ca07181103802c10080000147d0b40c1c0308003c012100701c90501c580390780b41044258003d0641908042c1c02030400144402004a818001e20580744210781da61105040280020104c800300c0c019407011502c9081d04445d03a14450782c011a4030a8000e50115002e60003014001544003041c03205c0031594603e0103180d00c0c1036090701a00000002c984021829031920190b4001c1036600b610014150341c0b1035121184c15611010310151401385c000742140d0700851a858506030720343e041480404c0381482c0142003a641c51090080040c06a0045803868240105071038902c02020940c2c402a289201070040b03014a00f06402a00e0013180503a50004038114206409024550028092410000c0030002030001030341002410040d140309540002100c003030b00b0016140c5280a0321050744c40807000c100e81d4204880700c6180c5800340348002446 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 187924784 1250 187923534 187923557
    0x30c020f190c0f14041e0c0306080106150206040803130b090d1409220204090603140c090601080a0e0304030c0b0901030605010e0114072d0605090303100b070201030e070f06 76
    0x1214007800500070180c14220360074490540307140c583c0081d50540c00c1e01d410540c6c52500c842261080f80e481c680c1300e101013501c0300d00412070100d00b8494a00101510150648240114a0003c2d01e5070802840105500804400300304d250030004241c0c0c0f990750b400103809180d41407807000c159035072702d01120450019100352031004000c540e280a81d040400050546400741480075000d101c030b024000c050060207030b800e12000ae51120780b40211030055016800b101d00c4c1c900c2d0000d01e142090b180007203240c01407a0743c8040c0b00c01e990b40302d088594801200500006c804409a0000d81180701741d520140c044001c0240104000000b10020450450309032410003450b40e45078015241c0503401c40ca21408210380140a501e1144044001d0400d24820214413449859aa500e4151a01c408201c030f441d103031a0b1026401000018072840b601308555800950951400c2100010148075500448181c90030219031041164026007001c203400e448a819244181c2d110010b4200003001480380780000396144004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 187926034 1250 187924784 187924799
    0x30c0c01020a020f04050a380a1208030a020403020627091b0a0221090907050705030a1209020d060b010e0a080304060f020f0d09030b01081507030c020f190c 69
    0x19016070742c060600c4d80e110340510100300080c14020400e02d98140c96501a000a401e4880c5104410440e10155440c03030b5001e084564680b01c02c50764160088503170b0b44c0140000040120148070459010b16125603940d40c1d9512403010b400307107500094220b000421080f0149031002160210b40d001780e81c1100c6c05900140800000d01d805841d0750302290104036545900c50202001462001c007a40100d6608050651780b0b915490700f41d262300c807400c1c80040b03215030280ca040064250043c10a1600754103029aa0711115120301c92101110148000c524407003481418640004c03580783d40007070042000c01c0503030400c40042c14000c034101c0e0000c0c606100d001d02e1032801070084425101c89000a50a003070528409613400c201d412104415481141600c14110340100545041e04645940b00074070645189054141e001040e000f50300c19410007a0580080e0a0503044160b0110180c0b9010440d544200800da092000c404400300d2940145000010070110388500980d49c948901c80300b15000303648068 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 187927284 1250 187926034 187926043
    0x10e0c07030804120903051608070501020703050316030c02130b090705070b040f020a05090a06080c0103060501020607030f06120c03140c0a03240f0519180201050d060e0702030c0c0102 81
    0xd010440b2140450040341e50200301d40c48051031420151501512a2112441c1016080200159007a840340604c043c141c28046000105820700007001c2023419551000d840f80500b105401c00c084843d034418040c948210140b8000c01d40141c0219039203c07800c2007001c0607140098225000b0041e103004615442c0c0b00300d00325085290080d111100b103440c0c507030754203011008080c426640150400004120b03a51015640c50051070450300000701c02c0c1c60306036480d041a02407aa510705040c5000c0c0c08014990300840c060f51302000c64900007503042d0103014540000d00c40c50300035802407400b120303810003008403002807075054a01510401701b00c02c50400c600c40c1d4440d41291200d4102034644400c00c00100e0602c4d00600380c030014031200318198100340880302198900100320389055110420302448503000001008000c0403588148020010442c031000c080b00310030320083c100800000c4403500c48807241d20440c09800c1e207140503072080c10310410096586d000a40c1c550700c1c50041c032030303103038141e41c00042d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 187928534 1250 187927284 187927297
    0x15030c0a0b04050d0602070501050f0906070c0c170111040801020a02010501090b030d0807020c090406050f090d0221070606060f1808100207110a06080703290d0c0b040b03010e0c 78
    0x204210b240504040500a0442c2c2d0108201e038556000d100010006800303000d524030602e041300a0125a2400503003d501d006000f8041000707000451007140c1c0400c1c5141d941d0402d80e0484005514070101d0125080e004220406100c0d410180110300071403031000c190001c0c010028244c1c000e106698883c60041c0840f000420ba6540c5a407015031180304190160400c150b1240007801510b09283c031040105550314000c45044542c02e40d90000c210f0740c80c03140403400340c000700003800824400380046006036441112000f0100c0c0102c2c60310100740d00311100c01c201c510603940900180820390383c0e00e00142c0404035440c1041c01151134103045414420390390304504216400c800040041000c044100c00095122003002d403818140301c03011280740d485c1e002003c4000c10495880107014903218000a0440c1c051500100640641040d96001542540046412900100e990720428070f00c5160156200000d64848803004c140480c000800702c0c0c0c15005541250454507080000340e0b115039182169201c1e80c0e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 187929784 1250 187928534 187928549
    0xc09061115061306030c1a0c070512030d020f120c0a0c060510051008010e0a02070f0803060604080d09031b12060b0609060f0304050c0406050d120909020315030c0a 72
    0x304192034001164241c00c80d040392000d80410b406002666454003a20030343c0c0c000703a0704040262402c004034a11061610711280701c0410351400e11200b0f4103440e48400d06880348604c90005031444866100d41401140c00c01c001041003155111008451028541c0050310401c00c03440c1540700065841c880003085440f080920303558001d0018080d510b600c02004094034401c0c805203401008138064643c0c0c18031101520807a1594200e9616000d0000d8006d00c000f008184203074018070001000501d01d20001c1e04280d8441052034895036040c0c040f0302e40e80125803140005105501550300d03040e801c004035070b041d00c1c0102e0010105610010581d819002c0603c1800c15012030380240b080031881c542e00c681000c00000704000c1ca0412058005010340d00090b01e40049801c00009200411070100244180a8801d9a00748100c6150800185004104140261140001400c0d03070140f28480d03080038024140c84402152281844500c1c0ca0f0b8141d00c50310a40d000e440340c0d5204540f00d00d0440840340440d2101c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 187931034 1250 187929784 187929793
    0x50604021c051c0c0c090f0501140f04090501020723070603020a080109090c03060227040504050319120501030317070801050303190903121707050306030c0120100c090611 75
    0x501c10b00c2c40c07030000b1100725502040300101310200001d184403040303001810342c504c01085010340c0002243c00c440042e071001075003d403110342c41482605c440e410140801c104407000190b403081030130301178003911940d00007d240c0c0c0e4081c049041e6002400300703022034100240044482058541c0740c01e40c00c0b4450f103401c0c5404030700f942004104015242e000340c80590f100c0d1491100755652540c0304400d0341c100724141c0d4026101e80c01d1001220020254000d840381d0115828840e50610303840b65a141c2c4101e00c040c115505044851526640c02014070400c1000410710402c803540c2d49040085c139408079035548001d0300050b41c01080103a441044c0c5a8165000100914641200c1014081002d004179015405200300d5020001c0410100c0851000c046090b4581102c11000e02100c4010004024032850501ca0b0038000d000e04c40c0c40008042c0000c45080c20030395469111221090100503107910459510b21420280c250f240001c0d4000301001251516140c81c1280c070b07501c0035110b081900500382c485511 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 187932284 1250 187931034 187931053
    0x20d020102090a0e0c1603020607120902090109150b030103210c0b2a120105030708030f070320010903031515140a03110a0509010207060f39050604021c05 68
    0x402c00c041340d0400307000ba2020f89030180780320343d40d550f05441040550258119004000104e80c2140d001d03082500c0c2c840c030400540c0745030780c001006c0c1c0b40c0c18094900d43c141c0d94402455040840c070121005000c40741416a01e947e0740740b0f0704a000c85420800041d030406144801c80c3c106008107004142958010380500e01d40d620000c0040006c0451040501300c0e01c40c020399440c09003040f400420880c4d02c1500d04541035070616051500e8241e1070781c0020340c281e10410251940c945004107903801e440c0d00d807812550118030040300001e009a003c0385a01f5552802c04010101034044d88900d8813101a0700440da1007942d05d480e00c42d04c0c40c500070b00d00804582c50b80b2549404404030001820170702200e0030b0010b9a90700c0034402c4012030f081604e100001c650006070404242d0f0701044900e00419281c5000700c1d54440340c0d80000c2802e2414400706540076424416400c002e000c02030300d0105502c004030951440b5119040c45a036034107090717034140d0280700c1201010380c0c0032914030030b81c3c10101d4200006000541 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 187933534 1250 187932284 187932299
    0xc02190b0f0901021c0914030a1403060f04050106020a02120c15070203031603020d03060f0b0406030e07082a0301180206070f120801140a051003020f070b01030b07020d020102090a 79
    0x1c00041042989540c2001104200300f1a0312504d4008440d000340000c90b40340070720b4886d0f502c0001c50981c034825030048c803174107009a5211b504081038014200f0ba6981301e880c0c08001c6182c8200c1ca5251325171050400e800402e4143d0700044002c5030354001c481403091025032880139500e03113034050800c1d1b4125044419040e10420b040c00140051840070302161b1034079120345001c52180240d80c4040303005802c001401035410340c2c14040c01c0f000d483c0c1c04240080c00383c50080950a180304e640b0900d02811f40395024100d12800078001400104041801e4800800c0c90580d0412101107901e8150440250b5040c440464181403284001c0c10310364000c00d020a03034040c2c00f0800f10703400c9010207c8160204041304030004013610100660f01c41281c89241055041a8040103100c01540006006a2800d0810801950340d42d1803400a900b05040060f500c040180c82c40030640704c1c04001800cbe2140940c0004104100c0c021103034482c2004ea800d9802100d240f08041b4241c1c820700c6601a44000480400d22204 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 187934784 1250 187933534 187933561
    0x41b0302070f1b05031b01202b1b020a0302010c080c030f030709080610050111011d1c0813080a030209190311010e0306042a090c02190b 60
    0x707000d100b41100071005980d40a001c0100f59600b0b041214021100708200d0038200407042100d40d070105804503145a050009011440348508602c86808100c00200b002c1070500c5040a081440b00a84048008117410500d846140301c098000081c8151600154598041440014580d000b002c0c96825481e5400469039105e40610030785602c01d0130041c04c428540c080000f40950b11950b00601d07200d2800c0e4071701a0210780c0d15030000317869402c00e808005501a9900350710041d0740013424000c0307000c90540c07041d5004241110360498001c0300802d4138405881c00041e03132100d40800fa0344440341040c07042c20817141480199100610005e803001000c1c001079480001d4a01d40740c51346001401c1a200314001084000803080d07641100d01d40701030901c2804250b01d481e60481800b801e01000440c1e00402080d41d4410040025080c0d468280088034201c4101c464410044084088440f695032119140001410b41c422000058850580307030031070807101c040c41d6100003034010031180e81c05c1d0765640c0d001185 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 187936034 1250 187934784 187934797
    0x3080c0310050a030b0415020702280906030c0f140603070c0809040c39081303050a1203050f060a0501050a020c0909011d0c0604150e220b041b0302 65
    0x700d114545021515440310540c030300041d0b000d141610b041d41018280306030410710611032403210a004020400150701d0340c0c00000d1401c00c070783d04041840003c41c0381e5046d070244150016511542030440001c248030962140c0c8055502600c00c070700030155600c0642981da4400c1d190350750041e800740005a201401402c40c4000640100c2da02c528120800b4002002c4450380c04040740402e4a980c0020342a003106100410038501c40b03a0b140001080c000309947e6a0f0703011400c020040d91002400c000f400c0141d0700440e0083d0786c040700f2282045800d01d009034842c180240d1000c00645071100040300c12034140c0e40c180c0210000b804a030390701030911004440e1540850104400d41c4036a000d1038a264451001c414464003141d000012000140c4000703c032601c01c0d4048031005035005148078a684d070358050454049036880c0f100103030b6040d20381b05c055401103200950154482030142039010300421403444400301d808801c008008042c1d0900c00c0108503004005540707511009284001e410768000c1c0c4c0100794 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 187937284 1250 187936034 187936051
    0xf09051606020a1e05060117010c020d080c07050708010606170912040b030406020c0604060608070f050906061c0903080f061903030305060a23090f04080d09031b050606011101060303080c03 83
    0x1c130384000c2d210189803110a03030104410f1400d0915684d0b0544083c400c06000e1000340c03002e4101001010b800a18419020346844000200013801070f041010130806a4024440c90307000707012150781d41d40003410380c5008442c0c49410007603101c0061500d420105881d00d030340194642c407604040c2426031644464000900485486608100c00080000c007088010302c6140303d600082003450910404c1414006c9550290910441c1040b052080d5a40c0c0d41340301c0d6002405a51040d1160042040c12042142e416482c4820300d1501802800345075000142512a02c000040031415498200034803032202c540241c03007203142111300c3c800d1000911a822464110200a002e00d18031a2210702c080e510109800a0350805010310006200350b0a02201855100c0001800c0044920342512004524411010180002c5555903d100e08240c007442102c951508850000081c140c49031800568407070042c4c1da1503022500c500614030424405000703e1042e03980c90b41e90310325141c4400040a07002d8001406408 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 187938534 1250 187937284 187937333
    0x7210504260304050304031121070807090b0105031305011b09150801030203060402041d150a0b0102070803070312110c010203190e0c090c040902070b0709050a120f02010309060f09051606020a 84
    0x105009d100c1000e401d5400054005095400d14021f8420303d40665076009001c1302c0c0c02e02403072074081da030400c00b903942c0310b01c184c1c0c55500710340d00e039143c033303a0042180a034144600d18400650501e00c0768840c5425054502030250b18000c8080d42a0649001d4401d2000940c19442100013038018105a04284021702d00d0034030058405084909090804912107960b840781c040083c100a003088050060500c200e40030b002608586007001c2c40701d900c03842034040c0501480004580e0300200c01d0a50311004201c84400c113000e440d0802c441005000c0d60040d03a09081000c042c001d80010801d09102d2440b0390003807080100b000d420704406212203680001e02c2032607150030520002440c40140e00052000c2441018018030318074061201611480701500120301130100403005000305203d0440c00c4040c4c64100d054036010711400e20048020703050b0060300801c55330a140a072801d610140d00040b4091344110f09450340c1355103020909540102c0d6201c2c03400164024034260f00030400701881440900f503120883e0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 187939784 1250 187938534 187938559
    0x19030e030f01050c0901170405250e01060c26031b0d0c030203060a0819060218030703050f01061205031207050d0e1c080f072105042603040503040311 66
    0xb400c4a2044414513421440010754140075039104141928401c3c00070004d0242d42003540f125503581c0410f8103160018113100303242090702d0300e8010f2114000c014002c640ba01c80e40e1150030090100080f41401c582d680b07100b02a0200865030407412000d507220011449055a07078040c40060250144501903040200401c04017903000d1084c000c15103902c1a940300542d0f01e0616409104074802c40d5070181809420207003441140142200090014980001025131110b0310105120102c04440084a03410702c9051400010420007140d211000c05114000300012a0340c0c2c05003c152503a41c48004116070030070412010404003908500f0b8011a5a245c03690404d500004800c0032030300000ca0340c4020b0307800100540d00b440740000070b00703c010750f240c0b800d00498245030490001025005e059001481109040c161035510704509050f4108440a010302031400c5c01e0520010400301c0d6101c0e600314120001c034048250707100c14207c0e4066640b0000940c6001c1ca180c035624583c0d0581c1c010f555009451004c0d0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 187941034 1250 187939784 187939813
    0x122309280806010f0305070503030c0604030f030605090907080c060c03090904110d080408070504020910140c0102042603160b040201030b0406090b130507090b0306120304060804030201060819030e03 87
    0x2ca40c041c2c60a11102a826401c60030400e1030f190148c0e104a01c242d00400507100d02d8940071071780b1307600654181068a503a8003400c4040e0040d1540d50030803a003000070b04040005103403000840c00c0c121645201940c00c04c840800901c50301d0312038641d0681c130300d52082040c900141400c0c1d442a0f44075000f805100801d06441c2e0015094181c10042610301a03008141400200d0b01440214000e00c01203030210320301005500400e010040301c0480d2014010301200380100d445039902158208101c00c0021940c5940300c81c400008079004031085014200509030102046400000315030117007865410104070040e80b540c80e11003000d0300400c12410152a9000005661540d01031903015050261010425110079028071890f0203c3c3d0704c11250340f50511040c00b410300d402001d44802d45280c40011b0b9565562800070407000c3d04c400201071998400060005945a408440d49000324400d900a0104903031b074464140c2d842d41c08070500c1c10220b085d0196500002d0142107400035014010b825208000103a954 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 187942284 1250 187941034 187941043
    0x5010b07200a08030d0605040b18100302060a021608030405031c120c1101050604090b0601120b0603010305070608010e010311010f1205012309010b0403030305060d1223092808 77
    0x1003900a0b610124070203201c3c149071b0094101a00080e1820440c501040001884019051109052144404020484481d42c01c8520406145c0161040d80d507121a0f0000a5541580a0150b60034003945000402e1185000c0110380850b80002c0080558070300580c80500c4095a902c030345800d0107842d2207041d2004100780240c5001001688a50700411045401d840c2034800040403188154a043c218200080c519100c83c0d1b0070400c00c6c03900b41090111039030404001c20b403880203a0343c04280403000104105000030020113a84155071031095030303640c40e41703910a203640a020080201441c020010b506500c2802004030914841c540205080898000042150b5003038021096981c1520f42042c00d0701510700c04441c4444040e15889505c0d85485da807600d00340190b010007010951500045075150380e41b10090003080f41c1004c5100d504091700c040c040d10500ca0070008403501d4a10042401404444c2010b8901c4007a01510f4904c20072881c441c0600518459103200e004850655000309000c0010403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 187943534 1250 187942284 187942289
    0x130b01110a050114070c0f08090a090905030301080d14120c2106040e03070b0615130902070201181508060102032104111504030311031c020d050a05010b07200a 70
    0x800014010903d13482d0403c01100108200b046c040c645228400088409184000c5036400c13001d035640f15055080041d044021030b030301c1101c80b09e081c403071308105120380400114121100401110104000c03035100380c03038414078903124201e02c0400303101140f8040b5041e03803400d50244100400b140360800e90b0f9035100c4102d07500b0032040c24030182c0f041046030340e0030b082c8100e408a81344040114142001d542c0c6144070a0380c001c129074040d406015581d11032060300c0c0c041d5412455603882c00c681403921440c0c1706009401c404030990014003000c1194092160038940b12041e07440c0d0410710740490f00c906100380e40056000d0304003411844101700d10b035001111800c03d10011190070004044074201802e100410500140c1058032410b20503030402c040c1d01c0c00b141224100c07035050520b140340649032102c079070a6010300b01419041c1c0d21114003000e038140d0030b0740c0204449030910000308881e894002e402012907009000b001e8401c0c03007c0040d40c020030308034504019020302401c000c0a001c02c1c0303480030507852210366 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 187944784 1250 187943534 187943543
    0xf020a0302090a05100b0903100b04111c1103060603150117090d0e0405101a041e06120c021f1b050712020c0307060c03020307021e0a050d02130b01110a 67
    0x4c0040c130407100e4109080710020441c1c52204c6080031844000291505807013004a0095559821400119141c54001c0303010078003215880380c1c4614007905444d681d030149a144602051800211205190052040c2ca001d13400c00380406085a032200102c13060f07090005085418071020032032201e01c7e14801ca410921804018015005800c800c0703402402c0512501e0310b2905c44c6040100b0480400402c03034856080702c1007490180f03542c40600d841000300d8031807500408e103d02c0c240c401e840c481e02500d9000c1d4044420341e07034074011b040102c2c2e8640c40c12075104800c0f103001a040901e00341c075911083c100b44843d140a051001500801c2c1c0c0100004102e60030782c41001240000c02c1d1b40b818003030134400032041803541d4005081d21ba07540b4000070b41c80f10194061030f018000c0c003424080616108005503000745601500107500b181713101c0d43c1050fa4908805407580301d00312088001c80c0c1404c0052211515940c05820315182c0103018000300050607690701003074100141206040582d1008104a100703080c000c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 187946034 1250 187944784 187944791
    0x7170c091f0314040f2402030702031218060c03060a05090a0608010c0207030b13060204090e070302040f06080307020f0d021309060b0a031110021c1e0c0309030f020a0302090a 77
    0x90714090207a4041c4400c80c4480d00b4420b0801c40483c04012804100a510141078004081c481402c0d588a80104080c40b4225102008000381c1640020003008440001c0302880b10540c3c03101190f1001400d080148d082e06e810002c042a5900c031900051600204001c0c0000c0c0c465844078045100b06c60200c070b5070070055481e9907080008440a00c10040260b040d440900301003801c40c1c88a04403150098024015142098418810300074694180c0740600084401404030410005202c1e59405507030000383e201c0c1d4540b22910003651080c0c410002243c014030042d42c2000000d030201f00ea96140c98281c180c000135941742c118016980c0d030601c194140f00030000010102c0940c01c143d8212400344804502901e26103809001203404981751480910040751619918213015000720f0030300d581450440e007030340540381c42c2c00201c58029500d0f0700d0210500f051010000d0100e801207034480310b03101c0058040b81a4003028400309403a4014840900c0c000740011800d40c2d0340e94003041549904507420754820340d8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 187947284 1250 187946034 187946089
    0x1030b060f03100911030106081302130c080601091809050309030d0c170301120b04051c090509160804031202040803031e0f01030308131106030703051603020307170c09 74
    0x840f84558014040d0303030104000c0010b40300c0e510041d600c01800744205104140b40080c1c480100003000034032042c1e01500001042c0d04006500019052102006001c80c0c1850b00160255102c0e8101070201c410700c9204880720780700c2841d00e4004045400741030b5110b000c1004251415101003092003d41000c0c0d6a0f00034170080c0a041500c20b80c0d840e01c2c1c3d11580c1000c05c2004102180e12031501c1c01511fa08051006500c2d219454058605000d03240500020784009031940f014076040002c0104480f020340701c02d0303141e40d02da08110085050204145006c80d0038103001c40c0c08a4441c1e41400c01806035000014a459254013400303140d030308101c42851101207807041581012101c03201003504003149000001d11941199005807a40d40010900c0e50010780052198060105155007000303542d00140140e541e030b00f4000c01c02000b801007220310b0b030314030500c203544108036511030702c21a0300c21000c541d00c1141c04046600d400884240142500c1a4414103103c507526541c1d070b040050000c007071440c10301c920550 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 187948534 1250 187947284 187947301
    0xd03151d010e0703060501020606010f1e051801020102070203060f06030a0503040906050103060b030601080c03090106031e0c05090c07080708040b031302090a020406120c0908060f04111c060b01030b060f03 90
    0x2c009061208241c00c003801001282d800080c1250010400d0070702c00c5803480c08200840e0b10000108204c01d06248003203080035160740000050111902d540c0c00300d240300daa1280164241e00c00c21303a00030b40561140c80010004255414007a401c618000c0a86821080c945c40762031664120f49c0041911580d1580c041100f9a010301c60706004009540041e4154504400003034502040200340540400d0000b0015560400039404000619807008a0b10592006d401d800d18000800030412641d070700507050003080d14501049000e11800042441e00c0c50603c403541c81c0e10b200d40024004503036620302840b001c030741240020301540c810069405c1c0c6411218950041041401014103402e040510410044c46999408a90304c0546201084049510140d004044628280680c8191200d0048000340300d881c02c0c20700c40050080e4001c078207c420f000440410484034051811036603541b030b0342024048001403115000710034002814100014131104000c0454a00e40c003044070f00c502c04000008000c07600 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 187949640 1106 187948534 187948559
    0x3030a0915020a17010902160f051009081e04080304030215070804030b01140f06090907020a08040b070c0e010501050f0705010902130911040e0d03151d01 68
    0x200010f500050607200e5903400805212940000010f113070110b4000c7d1400948860720610038040c0c02c1d5158045800400e070100c1e940e0103846035180c4109500c0c0b05460005002d00415551f03070f074214900b05003680340003408011181b810302c0f0603c00380e0800400d48064a50560390505ca00d02c5030755420300d0303d0042e114000d0090b0000100481045420b01c061412aa42003805040702110b240c208425035a03050b224980001042c8a01c820724a81003060641013402801900c0c100354040d00c1c0c01c11030b54000d402c10110610b0006884040000d803989150041c0780d180c08101403075042138002411031084207005d90031900c1c08201801401000c0d44021003007640200f410b044584d182172030070094410f00200350703800c489203560840e05040a000360210b030665136015100d901c014070350940041410107400c405100500c13101040340755440c050240c0a40e07100c80b20700c115614044103500d44 = true := by decide +kernel

theorem cover : BRFrame.Cov 187769784 187949640 := by
  have h0 := BRFrame.cov_init 187769784
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187769784 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 187769784 ≤ n) (h2 : n < 187949640) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
