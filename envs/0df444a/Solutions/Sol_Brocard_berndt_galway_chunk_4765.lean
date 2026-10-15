-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4765
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:39:37.179978+00:00
-- url     : https://prove2.me/submissions/0166ca3c-cfdf-4c5e-acc8-066db0e5c3ee

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 856834532 ≤ n < 857014388 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 856835782 1250 856834532 856834541
    0x312050702190807050a0e041b09060b04050316030f0807020118080a0b0906010b2a010e0a031106190203070903060e0a03080114060a11010908120f0a0c050a0f0201 72
    0x390010700e4800420b9000b0304411007402c40d4001c03614940501e42e00440d83d403c003402c055040300c0d0915080340311a5a15220704000c50001d01e80541d030040d40703000005031308a4500944015003501c001c01d0395550314200070540b0b0038104040d06c1c0001c050001c0100017040002e8042144507801a5050b9504c500920040785c49202030382d0150503203100c2c4034000c10380520000c3d180c254244243c82803401915410301c620340d079580c2441110000c440401404003519469140040b166050328006200101c20b0380c401801e440010034000629071155020105155204c008003030b29013035104c041c14481c20845000c142c48144c1c9000c052a594000010030141071040c0021801150400c20410108948000c2c9035100d44902d1000d40000b0001000440c80d48000b007144000040d0080045240c04004201a112600f4200d500c80d2503551721102070012170307081e000802211500d03500d03000c640e2600da4062020070801038642c0090514080600c81ca850b00b200888409600500b003140082804c07180480c05030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 856837032 1250 856835782 856835797
    0x1315120c1a0d0906022a0c220c081f061202031306090308070e0a14010f050c0601062d020d080a0f11070309051e04050a0e0303090a021306060801031205 67
    0xb034507050b1080c09101041d030150400f10b582007008851003000c812002a0780b2500710302d81d40b0f0742c5c1000740b00340c529203003403904d00843c99080484034500c00c1d0072a10603070403201c0c101200c402040011042264000c102c5e0602074900007000b6014085030f0402130000d240b080481c00850740e895000000c1005031000a0007840301c5c6030320500900c0142d03503d19000b040d0a10035240c07140400d80c01312851030b2515040344040300707483c401d006008200d080e10004440b8008901c0920b01407120802070b400c0348a10a02020b8060609078449080421380341d0500c80d5802c40c4600c1e00c001c0107200341c4100111a5000c1406900900c3c60701d0540d0b4503403210041040248030400b55641442e107001c1035011040c0c00c150140c59641e000e501c800712030950b101c0603c80c030504480040035040071200c0c8480920301e0243d001ba0782082011000041820403022a58a141e10035030b4030f00e040340c0c0000c592008601c1c0010501381c980c04c043c4410300c1b07540d26104010701102c006005c000c01802c80301c420203c81d180701d40140d6a26 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 856838282 1250 856837032 856837057
    0xa11030d06050a09020408120708070503030a0e0c01212d050105040b030705180a09020a03030e190810020711090f040b09060f0606090f1315120c1a 65
    0x200c4a2911014005054520400380201ca10090000b9264241d01c2a00c1c201e1301c403034002d009400c240c00c00212140d8401801116109401c0c000d450118a007003002d14071540841c0000030b14025900e041e54a0101c240b03051904004e11002011140c690a1442c00c41d809461280460801600c0e954601c0c60f00301c1d000f61901d41184170290f00445540340d00032604945054608100d03104d0080141500d0300614014150481948200315007030809000d040c03580040000000912413006500281c2c0c17020107135000b0340c0090b88600300311a8520704100e41441d0200380d401c4540c826490810a103403502050134009141e25030215528007806890300001c6540100100104103034030f444468400d10f0403094600340c1e01c40c84550005404650000f40c20341c029103080110003515034907078040083c1544034074852a08580151038000294441c0709040401d03a410a80c04583c0e41c0c4443e910040d55941940300030002d011040146002c940700b152180c1c1502d4100c1150417594030f40c0c0261301c25520408510400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 856839532 1250 856838282 856838287
    0x18090f01051f08070f030326180c0a0e130819020d0f0c3233060a030f17070609031d090606031905090d030606081b0a1103 54
    0x81c01c032109510700034400e2080ca40741e6a560b1240510f0f56100070a001d84015500131034800c1c00404d0082e100e100031100100da900c000711440c01040a041c03103058030340f40802801062521100581486104006e1000751101c0030110b14203510b46001186c0907103c0140d411aa202030024070842500301d5400a03c0407020190504200380000e43d80e280705044c00c000540852a8108518810701140c0081500710540c51800c1c03c01c04421504021456030400e2800403c0e00344000b22038050000c5159074040d9000c00c08416212000b004034415035812200d61120b08804201d0b00740d850b0035803401540c0d04172510819146c02da19202940350341c010107030201210042424000c1282135004044c3d450f2090f500e40c01181c9444442041d5000000c3c3c2850703004982400190701424a100030b0740d400341020402c0e01d800e101041c0820304442c02541c1c0e080094111341c200c0c1c280d40f5014091040144107a152040840c070300016112403a00c1c040f414251182030005e02c8001841c814025810b074500040c00382c0b40d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 856840782 1250 856839532 856839541
    0x603070e0a0e01061202030c0108071e030b030d03091103150c0702031504080409110a1b0c050d03050702040c05041a130e07080910151a04120804140f18090f0105 71
    0x2092110170040c1280710b485611102841380d48610343d4640583c555417100482061091300401c2c1170752402d02d0510406584125044095070b0030010062102032a407030000f0300208605200e40f000282d82120b5009a10a10151204905405005038803904000c44552140c10341e1000906045140507050300d034042c110140814801410010021945a1401000400314280c02203036140070701c1110801180c5195043e9030854054230550302d0103032140551a080c41e0719280000d00d0416580002d0380041c42c081410350850403e4880c00c0f508111605089040516103a001c00a88e036101c00200034844c404144114040040b1031000080e260005102d261490041e00c018001c0364100c911701d50324459080e40e00789000d02c1e480758252802102c50306c0104c03103007400f4881c0c1c1c03a0100720414101c24507080000050f03258800b624004440d224a040fa070707465150070040c4200062907840c1d03500c00c250701612000540e89103445903a0341e042490001885503a010b0006040c180f11403045440d0b5400c210401 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 856842032 1250 856840782 856840799
    0x61413050a060f0e09160f1103030c0912011503080f1c0905011505030c011412101517040f02060d0c02100e1207030848030603070e0a0e0106 62
    0x8843e809003e607200b015009480e0100000d03604103032500c1000c100090580c0e48a503200d01580b00082c0c4071400c200c51249409614580380d503000f107800040041e0080740c0b150741c0786824400114072401c044024024004003002c456075504080c070000b0042840003409206681d003030010707100e07100980581c0d4100d9030250200305000d000607110841d0b46500c0c0ca1440007421100241d11810340b200036004081c0041504010348802e03410810110000b08140042400b091040002c0b911941c01c41c900100c40c1c925003489400d500942120800600c100c40d41c92401c4050001d840c298130a41110030601d070705205001049091260312401d6400c01d0502c0d1141d03004a030001a0342d124418160410009032102145140e2250f10365001c884202004014800100e80b02ba001d43d504100d0400200441002d6480302003844501d01c201000380f4195421010320380c042020185840515024038a4510702e00034002a03104c60300d90090001c1010080d021070010b280e150300200c55036100c04020803c254450314103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 856843282 1250 856842032 856842047
    0x1501170a1e0615080105060c0705040b06120c1306021507030f0902041406090c07030c080306030c120f071203050a080403020705040e06090606040c0504031101050706020a0509010e030304061413050a06 88
    0x100c0703000c113031404000206400c0100854075896101006000c45034207100412020b4176a03414100c0d80058103120740c191340030310105254000c84003d0746141c0d030b603007000c417402149132035550000c03013903411006180c0d02161155a40c158041210301c3d00041c07401c404921800102111000a50814a4410f0003903d0040c0b001c24540548811a8610381036520301c0000e00b500d1042800060014000840d41000512900c1c043c40c0c20507002000e0718125050709001c41d140300054000c0d03110981c4204c1000168410611681c0c0191042456903d03060324130380c4003c0c0031841030700f120030300300075040d8006411306109010640c05040018414000c4502c008a0300359248019907401005010340c80c00300b59180340611655081500d10785656042c40e16645817501d800c051942c4c80f030305125040107200002161480101001d1059444490300d80454000040c0340c00c080e041224080d40c01044180b02058218a84011541a414007159503030400c8070706000030031256000580141c000640410802d400c00c3c0c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 856844532 1250 856843282 856843319
    0x1090c0611071e0605090307031703041202011104030807060609020307030f06050f15031305120307110703080d150b07050607020d08100e091606081501170a1e06 71
    0x1101c9000d40c55540e0f408483c0c5200c50950640d403407000302040b5850284014041c400702c000e060300c0c500b0f07550341c80d000c11402000042845003e800810001001224444108180894402040101c1465600d8045403065000281003a80c010034a01c2c1081400d400c03c8024241d000c0080d5264100381d0b20260107024103045020055050a0000c03d880c1043e810704001c60341c00501c6a0402d0300d04c011003010302e0740f01a118075030344040e003031054001c2481000126450009881d003a41c0e2880d010720000d08404100d00000000e8100b0101040410582019a020b00d9640e450004840030404c0900450003c41e0340003000c002c4021482d0740a011010643da44134074459001d540d090004003404071898007080b00c517003448440084040c03003885044a10030703900208410072116160a100c0ca00400350080e0b5100c600002c0c1040d0130400503040288900c2041d103420308164800d8201c003014011320300001000c5000447d035407a00d00300318192010b01401e445441c860200b15054840f459010341050524 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 856845782 1250 856844532 856844567
    0x606040614030c04020a09031703010906050102010216060f090c1e2103050a050f12041218032d0b06041a1818010f0921020a08090301090c06 62
    0x10000c1d1086801c20711844404009014000100c00e600802009400000740102004110b00300840001e40b0480307000c40700813a4000b899100e6142c40c0d0880182e1310903401090459006111200d41c1a0010030603a454a43c44080802c00f051403150710070081808a0002e082140d406400050701841152002e00c80054080c1808155845026460100010001008828907081207010202c2d21400180940d0300f018038204c1d01e809185281d80b0000d13003214148444a05c00c0400707000800000d254403c1c140643c600380303007000440c0d0114080300d4002c036110203403106d10039500100e1404c049240300c0001000c40300c0d18a103990381501344500d4940044845c00e024a14000c0f181d284042c001c40030440c110740043c0200b1050040701404c00120101034980c17281c140301651b000491230401c0c000c4c15000c0700201030000380c0b481c00d0300784008001d4190394400800c20820300c618000c26400b01c4c3c50384419410003a5165904c0151020900520f1001d034040e28034410b811000c103801c0d0340042e10044010541 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 856847032 1250 856845782 856845791
    0x305030609090a03020a06050408120405010b040c180504020c01020c1204060806013b030f030d0b0603010e011a0903011d150c180d0203010504060b19050306130f060e060604 76
    0x100c50b41640d4201c40c03180980540e218001000c00140309401c8903600c03900c60380e200d504100f04803035944d14244060b241294140d444007042105814244241c0d15100e0841c43c1010390101c0c0e0f45180c40d142440303170003441e004d0341d00015080044442501101c4220a080c009c4440c1c40925504641c42600030703000309030008401070041159580720f211841c49550b04002005a40c500c00c0b0f09208400b4041484400c0740023040c94601c4881c0c2e000c1c88240700d1080020069503585841055039030840703031718180817840380070280018000c617103100740302074151015a00140071000707607684080380c140155100581d2541c00c100310012810207243d001c600c10360b9160b0440b0b41c1d030380544000164060342100c070500d00e2102448a04140000e400e59810b03000800340c008100c0500a8000c80d0968a0484058605580f02d82140d0b5560a01c003c00c207a11b40c40c00290b0003045c80c02d1078002511a40058069201e01000740300d40c0040c00300c10284800c2c2294020380070042c143e9400703402a10b62604aa5a62260349007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 856848282 1250 856847032 856847041
    0x3030406060315050c0a0c030c050d11011409191a0411010e03030a270f090b010801080f060105010503040305190801062a08220f0f0902070312270305030609 69
    0x8502800e40540302d65285c00d030404040140032210818140000d0f0100312804c0411401301d0020b10140c40121041c0d6544401201200915400d41c0c10340000d01d04c807443c0100803c1081000410100550080c1113210928400141414800f5001304800a4101c5802c039090008108081441c0f212608082e2164141d00011a003019180e0182501c2d00001c503091400d210080b20801600486000d1101528410740d6102c00311a9240f551701d40000f88056910700e2034000560303701200d240107151500040c2400a043c9070129203801d0180f18582c14400040003150805000c6c10690f01c80501c402e6484802000070000140341880a215880200361442c1001c0c2810f21f20380e540141241c0b05154805541586079641c134040c1e07001501450715014400c040340d90850581c0c442000408034034080440d128149244051040d4240e40504080c0f032041117150004de40000c44403200d05000d0a00040394081000d05514504454103034540b1500f007101c182c000c05400030040c41c02058141c0300740c50207659 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 856849532 1250 856848282 856848323
    0x80d120504202b1b03081b010f0c0e01090b0c0d1101020d061e05030d0f050c0f0706020d03150501170c0d0c050403031d100e010c05030304060603 64
    0x7640c001e810b85060301e1100e24030500300c00309288904800b40094501c551040b41c0c1c4502d01d04108a10082095210401014446030281c0108045080c03010307501e00d14a10303540c03134a5501ca2208071007142d03114104882141107080d800108031215488081c0420300e07002100034510515040b149000c1845600d01003060700e07280c0191207507401c088008040001c02a041034401c1c4440e00581c0704159000c01026540e003e840c02050010407078640e420010031081c41401188440c650043c5010703503c8072030b410b203100b90310580702d00354100381e81003581d955004003184c40c1c2008141c6141e1400c85c4120f000c000780403580000e011300114010750b07040000c031200100114081000340702361030001d841050054505140342031070301e8100500c1c500d41032a00035000d00c480705440002e554070001c55400f040801c103054004084941c0400c40c0700f000144041600c0004e1a0030342d204140c4001c1100b0101c4018169010304200344400d90003804503070310707850f01c0e1620101400e11404102c0b441e020403107544942c01c2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 856850782 1250 856849532 856849541
    0xa0f09030f030b06070f0803160507050705090916032301090209011a0c0703030306170606100e0d050102130311011b0f0809040c020d080106090503030301180b0307080d12 75
    0x140d041c0e541d011100e0300c0080440c09001c800c2a8254007a0003049104001a0480c44103d032107441000340710380f0303031501026000c04002c0820400017441002c200f08d400041c4003250f1901036134400c0b80c004c0304c191201b640041c6000200c03007400d00380101a8070048188010007440620f0b070b0f100104c1140d41003a0740c000d403078207840310914000d400000b2030005001f000d40400c0c41c4c190060701e11800a040c618464946442c04505074015004240c0d103040520680c0080e200c628050b1030f51500800d01e0f4181030000c1011401c4400f8001c003004003803144230100342e0300c42d446042d41c20b81242c002e43d26503010641c0100c104405220440d010401d10026101070b5000d101500820400507a003a4030801241d00d400500550011080f00c240d2810071103030b40c81d5a500d10591440000f00c2c2d008059a0070000c0001d0040c10701078000c041407000d026410000e554001040f40c3c1520014180403880044001090b00984854100c040c1d060150b40d0010800d010001000340e1211090740d2526482d0203189000811113 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 856852032 1250 856850782 856850801
    0xf021b06100e0a11310504020c1b0301110a0305090c0d1a06010504030206030109140903031012080d0c0237080a1101020a0e1305072c0a06080a0f 64
    0x40031040000d42e030003001e61014407542c200740b40031440c003007902c0c01020715084042d8500304050902403080c80014170030401c090151200703580442c5041c05600d91582d440318114a01071040001c410201c8603a1400c0d044800e1040c00e5103040d0740c645404034800b401425044403040200c6c440c07410403624918048a151076500d40082840d0f00100702c5d40071100080303400815450521004010020041c1c59080083d0300a02807a003001440c4801c00349030310441100500080210362051003440703084102c66405808442544180002a400ae858004128000e03204c02d5580c03586084241010f658005ca0301c00b00804d8481e281c07a00000c0d00801c0802070040300d002080840c19501d0102001a900000400b81c1c02d0142c10300307104507000300c100142683d000c0d000c442d000800c1300000505c1030403c1120400c980801000602c414030740300d400109990400c16903014100f04030f001200c890a0f1303d11100100782c1c00501141c014580703c04025044400c2601c511141925150700900400352611a041c5007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 856853282 1250 856852032 856852049
    0x30e010c0e01110a02100806012003092202030f19060f0509461a0405041a0412090608090a03050a02011e0e0c0a0605030412030f021b0610 61
    0x1030a40c1074004503000420080c4030301c0345201d08030b00703200960b542d108001200c507501c1d80c621501e444c1c042e000401e40c940791694082002d90004040000b01c0021007541c080701c0050309d00d00000d031600c410300c42c0040c049c8403160030311510010512100d50300d03420741c80d845074030f001c1801441411807517883e10440700244038a60030b41c0f100e10000c3c001890408165904602040f600032104003458000c10901c0403004264a2100e4186586c061070b9480c1050a41c110301c21820200480c890303c460b4549a090f00000e11407260f07941c0c40000d810099026800903c1148180a9074400c3c0340078a0005842c0c1c0e0001c100b44089280f85200182144c810150540705903500406082d824140b680c05803401d4201c40d51201c20341d501c640b04ca80d408020010703c9282d240f0040e001041081c0049490b41c141103a2400311402110020300030302031780b90004200da4010f540100d040f503400703500c13110440060000290680140f4000601088403410180c00301403059905005d98809072120410a010140d1502c5202038 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 856854532 1250 856853282 856853297
    0x31b0e06060a0e100c020a0603110904090201020738090d0308043908010c050315010201090f0807120801080c041d0f030403170f0d020309210a030e010c 67
    0x20182060700107032100301100d0801c0440c8402c1940018450314110001e44001081030000409524006017a500100010704040101101008031400d003886003012a42c0515221180c40d800c41e4400c12007103001b000300080b03040c03103114260842c000101c1403400303156003101c1185458050240c82000c542c444140140b281c1440c810558094035000c00042c010740302c1c3c0da42441640b4485640d5851505200182c0d0030141408905180081d4494481d4001c1809070385080e42c201122500442142d0b00700089071942d00000b07464600403405001200c0004007602101c00c00001004107590140100d58030904002d0528070450300100e07201e4509100d04200c0c0e80c0030f115002c1c0e660806500880e44145883c039468060318030700200034a400c80c01014404286e10000f02001070041a00c12500800a0f0700a007a00d003500204c1c00ba100c1e400707600414002036900001103180000c04010100043c411860b124050410078100002c0070340221902c100400d04042e800312040b58184111540c0d4a80b60700d80b6203 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 856855782 1250 856854532 856854541
    0x120507170f0601091a1b03070b0708040c090c3515060405060307020d120509030403062406030204050406050103180f02120109080702181006030e0a06020c07031b0e 72
    0x9181c401c040d00a07414400b0030180840c58200d1400d90982e400310b41e004c0e0b10350307031412280585218444100c40d00c811350028000000001c02da50002a00921070b0f00d03004903a0349490414001c81c400a60056011900d043c88440e8282d030080f030082c00c24108008089002c40e4000e00a081d6203141c045040c0500300f100d000280c070410701103e0111104405005282019180c001280e0180d00030f40b44000982e1102d140352500d194010080007042c203ca0b04140000c1c100035060954031f0055001c0108150780b244031700205007050300440c40720700d100d07207162612050303480e90050020340c01401035500441c14a2000b00c1c0e0755010b4040d12545503140303140d000004d0360940724815500c1c12032000f207030b101c050390036801303503040090050441603400b0786006036440040d0b10401c100c0f000c43e821030104250b0031104100809140c1103101c0102d590340d080200c4d0001c2d1038040750341003082d00c1f10020440781c800f25124845080010ba1102968810100c0380f80c209800301c0008401d06980c400c2c50720f281e02000008 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 856857032 1250 856855782 856855801
    0x32307020304030611121f03020f011e08090d02031c180503070c14010c0b0612011b09090c0e100e010903020d05010c080703151a0f0a12050717 63
    0x1951010491040d81d00340303074490790f450b810b44094008082036504c0209003554000080d60b612600b00c490314074680a04c041d02c01c4d20340c45005d294840a44202c402c0d401c0116241d0154100c851480d81100700410110a00c0d0333000b51201500fa56030300c0c0300d8800d2071141c444e803a000008840c07044400f0480b0102d0714601500000207049880740c00b020b0a00081412000208200064085280706905c030181c0c0c02c1c14040d03460301507a590100039040002c14803950012170700c0d003022a03401c0082503c00d40e0042d24104c0c6123601500c402c1e04021140802c9802c07034100107500c00840000d032645d2038418841e07089923081c100c1e00c80d1800086640c0c03082e40e4070070303c42e40c250203030003072a5031090b041c100001c01940c3da40004d0314284401d00140c4d1143d44601656400f1a841380e1001c1e0b02c0a490304007008044040811501400005e00031900d0401407181c00620010750a000e6501b0071280441441c0e4940c103c0200401c0030036074035260032800d800e00c40410492030044484881d42130044800303c0c0d00340d8034208030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 856858282 1250 856857032 856857101
    0x11203031b0c02060f0d0c02030703120c05070305090f150a0201060f0e010e090f0d12152709021c0c060e03120325050910030902060703050729010e060103 68
    0x1a03000b140c02c1040704c03a1b03108009005243d0000400d40145032200c21500300070b0301c2180d5102c510081c1c5441c1441d050304a90b044001e40300103513014940580c5841001c40442c5d03907130a940405a61218000c2d0300010010071100050483d008558000c3c044aaa40e106501c0003c800340550311184001000500070341204240702c1e070303000101c03904030f03108500c64540c00c07405c010300480350000003480c550708515004414051544c80549541060500610703280f00005200c140030b00451401d0000610884030702142d40003182e0690b002400c81d595180a05c0121242840c402021a00c7c0f003441140001c801c0c3c0030700001e907000c03207020b4080c040003040c0804004540c1d100a100215402555a96036920780109207058600225134840356602c0d0b10b042d0030000c5160311684c0d00c004150800d869840141c6401c01a01c2c03206500d814559250602890301415075000740f401c000080e009011b0249030070011062050403903150005d07995040e181c9000441c1a10700c001d80d0640d0a90502502e2a41451140310 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 856859532 1250 856858282 856858297
    0x7090f1a15041d0106030e060601021015050301050a02071406091b0a08060a060806090f07090f14090610060e0102030304020d0201111b090106020102071e0317011203031b0c0206 78
    0x240c1c0d280c02d840d82e507034401006200c00302c051660f0384100103200650f014403c5446001c0080014800e502e07203480000e40d5614071882c007044440c1c49204000c2080320f1402440040e003002030003440709107030030040301c4025001140107840044814062465840011070030600490003080074003202d0046403081c00c00344450840c140c0d0044082030300020010401e200850060541d45da000c03c03101d00e446038680c5800d1003d00004801c3d008000e950a0401d000a50030f400c45000d81c0010a09220700d2400100808400c040e0440407280c040c10000c155070702043c128480c803079241d00c01ca08151039203000c0f100984100c0c8054096441000400d025103007210081912500c14580030f0f001d0055414807034101280c07800c05240203d2040140e480518000d04802e002d071003e440210b08110311601d96010401c0d115903610144c080410000c02814400d885019100c2c1e072060b282880b65a603003650642800c40b45200360000f0349407030034451003d0310401c0003031038aa009070340d9204000c1080d000c10072141c0c01340300b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 856860782 1250 856859532 856859569
    0xd020c0a020d030206090c040606051e04050604030c06021c0c0b04051f0b01020c060f19030b04410a111b0604020a06050f0d0509100e07090f1a 63
    0x1682880140d42d2030b20074000c4148283d010300260b00300300e03032100d1614010315402c510031760030700348213101e0f00b070340982902c105096810118a2881c41c2c0c0c40010814400e40e0040c0d90072100001e401701c180442e460104040382c105070b085071038000c00e4140c03d004001400d6818400181000b21030004100e001031711640107809901070b00d01c8402465541081c0c8948136400078038154940d005590b81e582c050000360001e0b10162140c1d498405000b00d110464442c282200165030700c3e60005254140c4207a00944030018090000c20294164192072920118040405880c61081c0440d4111184c100701103500e01c05140c00d1064901c0e1642e40c102c4014042c01403962003600c9003848200c510440500c0b501c030030b002103203010f07281c01d09107401401005071040d0030070004d10004004064040790340c14200c50b070509a1b0300c000207440d1100400309081c44440319110b144d00307052a44020400d94045200010ac407103000d07080000549110402064600d40c0501c02e02c80341516184070b00b50305010200d003000c1014030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 856862032 1250 856860782 856860793
    0x7050714011e0b0f030c0916020f0d0504090513170c010902060412020f0d2105040503010e0105060306130228030f32061f0902040602030310051002030d020c 69
    0xc1c4560b0b01c103a03040300540c448a510388119422904000e0151400c00d002034001d03000c1d45140300085072024002400348407031410456603481c250f5100344008402c4d0000d0006540303000d21030902c0246240c06c0360085000042c580340200d400c81c603488071088821076100d6184140c601074440c1c00c2c49980c01c086c01c83e55041d5254002c21340182d40e107900074409400b0482e0000b030200414014400401c0c1c00e844010b001c1c450b10041c0c000422007602d003001c1601c203540c840181491003c4030459040c041d5600054066080002c0d1f40e03000360064011038890141a01101c0040d0750311002c805101a4503e4040d4100d1824841e21140070001d1000f00c0b000c40e4440b06101c50b080e40c2e0f55030341c02c000900540c15603101086d568504040b0004180900d403040896a10019001c0e0035000c007515004064000354020b98005204040426035020800003801006002c548603640c070f00001c1d440b030340112403042c0c01d40184180400e061500e080119060325042d0700460030309000540d414020741c03082003144014403d5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 856863282 1250 856862032 856862051
    0x1403060708040c2106050a0504031b0507051c061b050d151502030307140702062b060f060905061e07051c0f031a100302071b1413050705071401 63
    0x2421071346a041d010010702c141c03c00c20303003080300890307201500c0116003609100902001c00e90003511002001000b900201100e10240b41c42072a1030200e5000c0f80d00080050307030ac4415440c02140b01c400c4140607040621100000403100094040c0c240030000125206010461642030268045040300700542d0003180415165010301800c3c07420344c61048016840002080740040d48003c0b4502c80685448200e0f041203078540c001070560183d2403a00c104001b00061450001404c03000d800310400c1d0940081140340c1d198081080965540d01441021414040000440d0708000040b240000047c2003004402c29807030b24015031907403100d10161600c0c0b240140c201e404142d103046804148102d51503150207404010000b4050b00c2803001341c100b02c5a8070303a050610544465264484081c15440c005a0320011813908507064400d40450015800d405c0201183d020760069001d10254800c481c600d01340700030100f411055a5040741c02900060042c042d880020b18546a0080000c41c04400403403e59035 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 856864532 1250 856863282 856863299
    0xa0e010905100609060c171e0904240603090201020f03190306091406010e0109032001030b06041a03180f0607030e010e0705090a110f0a08011403060708040c 69
    0x4280c0100030555a644107102290304000325000c001c207a98200303503948900e03169015120240c1070030040c020500d030f20440402c40d10b00340100d910001e40540c44500d543c0354604c0c0c44441c0d4000810340c134002c6103414012000c0c100c650414484248800c04440201c07802c044040b006828001000c0781036101305d000e500010582840900f10811541000c2d440200480314010140c2e0394603840f9406541c0b81c03000000900300480007840e0b01c07000a00703010a00e003510800480361240241c2c0050540c801c0c40c00b0500c140389003030803034901c00b40d001d0742c090000c480d0f0b01e01000010b06c00c600c58065078410780c1050407440c004d0341010315803026800441441c52030031440c5c41d42c280702890440e240b03160440030030803200c03940510403112110b44400c000c07c0f941e404509400c0d55442c1900506118141c024000f8090914540003400d440040c50783c1e95441d00302403110303d10560083c8915034045410764001289151120410072558200100101950b458095060b074030644041d0003621154290000480c4884 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 856865782 1250 856864532 856864559
    0xb040b030307110405010605071a090304080304140f0a0e1306090b0f04141b01050f090d032105070e09070c021908062217070c1805090c10030b0a 64
    0x90040f850950102c20720401c202c200e8030160001424001c0620039100455680040c2c0491070003c0383c640385160701c51400480ca9170040754007050311403200080100e01c9160b406400b0301184015558032102c00d049808200d40324419000f0016628005170015a01c1c8142d00505041d003400703950002200f14030380d00c0c1d00e01050022074a29441030f00340002d11080126104290010020301d00217412065042007000124100341940c00f410170102040c40020f0804e08800c13034522210051407445805100d140141070080485400c400402c20080d2250b5028154001c0c1482100307255540520f2000b042c04200d000365015103410b0811954004140c0180c413143c001b01d0720182e542d0707510350001c0c1c0782c040e0041c58403100408040300740d103580e10300c0d244080003464030000103548044810030580c010b03801c03030040d8000c001020b410008420f038001441460340780010001e9000c070b44140099654406102ea6809501a4482c0c10501d039980d001e40b0309109034021003c0c06030003001c110038655645400f0300b085 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 856867032 1250 856865782 856865797
    0x30c0711370e01030f0521160c1d0117010b1003021b01050c030a0c1106070f020f0111030414011b080a0207050f0c091012080d06180e07270b040b0303 66
    0xc40b003203814800d00c04200310710020841c95034018441160281070088444c0219521207105401c091710b45802c008030710300326002412002c2b90810380c4098261185000d82001e20034182c1c0c844548410700c101c66010701501c1690000902100c0d08101c10140c00c400950080e50401c0d5402d80700aa00c92101700203000d058041c458040042c1c1d1a410180848021520f07000044d4040c0120f84175241245900410115400681c90a207201200c0314140240c0c1481110f40784203015501e0070360f05a81000d030100c0a54019030181008001c001d00310166942241c40440c0d00c0f07a505018aa02460701c9403041100f261305c140401400360804080d9501d8500d80080d03000442010f400000080f02941001081da40d40134109415000e4132624101c207080c846410f0389400f030195000010408440346281d000040104000042c4038040d40e02c0110400c010071041c05d030300c2058060900c0c002002007940601041c185007445000440c403007000320010003010400c1d100c1350000e44a0307031805520f95090019142c036 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 856868282 1250 856867032 856867043
    0x204031e05010b04061805071103030f0702060f22140a050a060f0c05040b0f0405101107090c1b171215100c08090a0506030c0711370e0103 61
    0x800d2545400d41c20f44002141e81d40c021880c2a404101d0400e00c0032101d4170340b5004150000b0a501d80790f2003100c8121b0b80301c4403c200c0384400410f0181e0307840b5081c486441000036500740c6500c0c0d11507103281d80e040d03603040d01c0502d440782c1c0e001c0501c920b1310400c0010010091160b40c4051500390012002414403140c80070a4405800c4555140c00303221369409100d0303144840c508100800c0001d5034016009024078018030042c80ea000c40c4c4405080d490204480140078010075028134008600300041000400b080e040003540a100c0c800a40300741c01740a2600d0420312030300d030340203ca490070319000307009624020f082e10305030a07402940c142d00003c0f00051020103e00801100c440c41c103411b05400794208e40c0141070040001e41c00000c0c075558441f245490302584681402d035600300e0000002c0600d4084d40025501c281d001042c04031004601c001414502d1140c1c00001e120042c010820204050320782107444500213190305c800300b480c0060400400d246240d00c81c500941d8030341844805625090300203c46 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 856869532 1250 856868282 856868333
    0xa2114070504060801090209130312020412060e0601050f1014040602010516110706120e06010608090f06010f15050c0a0c061101090312020307050d05040515060102060705030c030604020403 83
    0x1440c00c2c14000e42d005405004000c0c05015a40d41c00300d100c50500810142c141d040b01006c2c00c2c10140300742c1030004218441c250940d115a00c60300700415082d1101030840e00c15181c00c0e60f6002058020400c02e0490700020001000004110107110365125000c4a403000c10040d6130303056407900c16500c050302c0a40b01c0e81c1d0000505103000403540340d124440320a40300034006c0c40e20381034160741000030740081503072030030301c1c02e0900e920310a0b44501c0940404040f11145000d0600045005640540d40502c07640601c000c44606001624065440e00000c2c010b0107410b06105506214004180c2006c6062240c280790051a020307800340700d070341000c80d44001141d821030390040800c807550340b11014403101d841c101c2c000c01480c0c4141e40d000d840709062500c5400724640100024108901601c1603501c100c0c2d1a2405005d90318203882c089854102c45042d00070b441000d200403800a51000890a01c242001e4850510316143c1d04004441c0303403c020080784d4440c0c0c08010110008214052819004403012880310 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 856870782 1250 856869532 856869539
    0x31104090912080f010612060801140f010b090922020a1d0c0f07110a0810021e0a020d080a0b060d0e010606021603020411090901120b070503060a211407 67
    0x828050380c0d4500c5004000111084c8020440700e0039400e41199040d0400680d145002e0080b10040c1010ba841200c1315441c01034100d1400283c034074220700c0354a54180c0c150300c3d84c1c0ca40007005032500840d01c1103034003c9245400100c01900c0c80119154002081d6104000c00d913003640026041302c4241c1000080e0300f032512611124554400510b9040100040100d0420700c0074508000d46c1e0040e100050034007181c0d001d82307800940398440954081c2c424401600c03172452407212428080d40c041c4442c0b002084065503e000c0c10f40800c8183d6443c03ca407079014000b51007104038210f4189601805400005907210707071151065680c0801040c0920304500302003901003c8040e45821036800303603c00019900040f14140410200e1a808001e5a034100d81c00140d0300c3c050740d40c2c0300d0f942c0603501c0780c0e903000060b100002c10003500f00c0c41d40d400418810940c2d01c60075601e0102c111110300054440b1f40d0894000482484400c440c42c0c031051011b40b1054000784402001c3e2111000c071101d45c515a211034100100c00d1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 856872032 1250 856870782 856870793
    0x81314070815070e01181a09280e25200715110f01063201090e09030909070305100e10060e031204080d09060323070311040909 56
    0x3005151020200107050780303803d0401070204800584000e040040400005442c581c6c1048004050300001d0340d1213048070f030179000c00c1406600650741181316240d102d5114240c0d00e035480d1900b078440d24201008032450f01d0044088400c1710060070300c4040b519684508400050403e845501026599032080020030150302044100e0004801d80340c81c0c4e8100c21b00038080e070f80d4041921246000c2510b0449450449020703180d0501c5001517202c8200e5007840400120800701072071071042502502c11912141c7d465038103221101042d200e465000c41e014007820806417401c00f03941d0b80d0210510003501e03e008003010004224040845218001c06da4500071b001464044560020190070200c640c1545070903c10761140300d2603c1403150f0001c11a08500e54a100e072014031450200340c3c0300007442c075103907510b40b6482c1c0d44500d12901004002044440300142d824460302030854104101240c040c50241c01a140d100c00720700c020000d100f455103d0b081c0300a14502100113100516802c140052500d8403450f05 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 856873282 1250 856872032 856872043
    0xc050d020313052d0301181202060106050a1e030b21010b0102010207050a0b0603010608030324060703450f08030f041205160803091f0f0813140708 65
    0xf60240114901a03000341c820180040f5110801441044a5034450030020b805400d004003099103000508016030100b102d401807454400c031858081e00d000f60f88500301101c0a000c1d207a404800100885200c1608900940c0700e0b003c10541403402160718208031000c00d24a801c0c610b5002c0c180d01400c4040c19480c07000f84a6007082d510244000d619110740b540b0b60580c1d42c5050580034107242d000c40045030b1141c0d001d50220000740b00c45416207440c2d141511140020850141110340070304414010b802440c07814004036031005526464446034140781e03402d0920386101081310b00c40c1138140c0454060301984c841088843e40c00040c0c448500c0070f410000441c103058442d521032085035005020300003540c5d0181c01554180c5141c607460345102d0140d81840d910f4802c2000c40300c40d00b2280300001080031200400108036144040d0745004d448900ca80c42000904500b8020600248200004800c2c0d0b41c810120300790804180c802c2a10301c810325464001407002030940d10f02060f8440142004294024042d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 856874532 1250 856873282 856873289
    0x212010b1e120604150b04090b0f04050403020d0f18122d02030c0a0308030402240711040c39080a0203030f0c0408060f0403021e0601171204150c050d020313 69
    0x1061720140e14040000305580035900500710724039150328207c0000c0c0c6880c09040710f03040300140140f10074109400c02944402c0d104120000140d0341a4900560f58050310002c02c0c40c5c0350746d19680420500e000441400c401403414119007450820f4040011560b060510100322032109a61a81d10000c6104251030000c00345e00c0a0300421030319004101080d051015280d10a4042c1d442e41c81c6110381d6000400070780c2c1906404641118041505e0003445101000a12000d50980d4200603160b640c80c0107a8110814245140101c05e1b10782c241d0350440e560303580e041c1c108110444114811903160ba6030703031141c1c6c1010f92035400681c40031040041440604404030b03001080d003a40b041c80c00d400d0842881d11184000d000d0b1000703202c4140858100361081003003a140c1d403066000001140d2074102e020392500828400c0c0d0290514216580c01008000720301e5014243c2544805403402d85009a11030003641c14155001c1403007030518110340030500a2214880c0c600256018680d00c0c1144001070805984642 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 856875782 1250 856874532 856874561
    0x10801061b0606150908120906090109091401090b010206090d1b0b040f0302071710181a040201200c040b0604051002030c1209010503060d0c0504021803010f0212010b1e120604 77
    0x1031007e40c0500c06036084544c0e014085e546c0c10b9881c40c3c004016100044140e00c111078540ca0701c0f04810b0b40518078400181652174000091210342c1c5064012030340c804083d90344807144c0d00042c828448450207400d01103015505204120761101c4c1035182c514865000310b8069401001d29880042050741c14001403015003c3c40c2d186410250001e510300d0b0796a1031031000204515070719000c94140001c1c42d802c41055980c001d240c2c0320100010810500062019103040703001c900d40c002142e0892082d001069810803550008115100b02d400400014103608000660032010400010a141d00c40010768020300c0380710b400560340c0380c50141c0080c0c50035400101c100d0901c0301c20702c9210800d07070384802200c0c2c103c1d01c1113818443c02d00c024140900c00881542c80140c0c020310000f4440c1c240703e2004202d000391071048000300007010102c0e002c03400b40e1041c0600c03d080c1ca196400140801307001800a00256000c0b40001a40303903007014280c2426600c0107800306800d6400100300611464140203d2403000d140c80d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 856877032 1250 856875782 856875793
    0x60603060f040819020c060a120b03030a0c0b13021807020c1005030a020307030e01150e0c070c0b0a0311030a0b030f0f0607030c0201091a01060914010801061b0606150908 75
    0x25218241280508110304c4c8509002c1e5544c0050705208010142d10110010800390f550010310b10084d04000c900d60307248100a00b072400300c6046280100070f440c0144040d8070341d407040f5020b540d04c1c00c0c43c2c008000e08161042c106000f1450268480ea06c0c00b500c82040801c00785d615060851019290036004448984198581c0c0000a5240d138480140c1ea001138082c10003503200d03100e40b103040e005404030f01107080440d031034484041d491651030305501c41180c084500004264032000300d110b5a61289070400352041d045080308104e000c1522009106004c40c41c43d001820a40540ca00e04181e841540ca00b04c0d0b86444200c00d0341d01d8030f400d1114440d80c0c070f075020007000140800700c4016160000101800240b5a035607107001d01140c003e410290030142d00002d0041240c4812149090b522801c1c040c140c00980c19001c08516212120b521100c01c0c034051310f4a0340329038a0311008030f64294a0307642c00280c0001512149000030380601545000d08211202284600081c18000f020884541c1c050401359221 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 856878282 1250 856877032 856877041
    0x5060a1413080f0d09051c1202131208040905010b04051507050d110c03150106140c0312100503060f01033e010c1e2906040902040617060603060f 64
    0x2d0b1021030344140398905002d9240e48201e0301c00001030036094030141880c010004290078080b18040001c0c044c02058032200050302d1641201030032030090040002241c0103244d001d104080d4038007001002d947c03051400314078154642c4a0072055410a0740b082c010510046800e1000d03280c8090140d105040e01140503080c00d04030745820b0b903104160f014001c1401020081170040c40014803003401c92510140441d9000102c0d0003045e0302c880300902c1401c0c0001d4810117800d00040b4134004072a06050703010001c50506035400c4080800300070203001c01010b0402d42d007001803551028882a0700c10481e50700d24000541c0f65007808214844115650340f2103603611915549030440100c0da000a0000503d80446441103020050716600301e801c0300601285001c01440b03002400d05038505c20624415103118200651281008540c22005246001483d401c9070028010b414103038405450f0500050002c00c01554403503a400d050f90071801d00501c41d0304640c04000e950305040244e980c10505520104190707290 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 856879532 1250 856878282 856878293
    0x1f0b0d0b211014061504260105060303311d0a3602030309040203011502070902120a021c020301300b1914100e15010516050a05060a1413 60
    0x10001c000902c2120080300032084a04200c1c1946d0241c1021112056031055820011000a00940f0002100e41c280000140d2506001c010b58000ca2460340040305c690020300071b1405580c64030814140301a150031000121604604090031101644140440c4542405d140d4001074603030708000d0300c9552004001c1c00038403005500070300c110b01c0b040030500d82c204050740c80000d055101d4416103641c0280040004035110030000b00c000c0d1200c10a40072644260b689148403c168054a030704138010558130381c00500d80011a40081458100c1d80404100601c051100c1c9402c03600280c019000d034a802c0c000240e6440009081e4204d6248aa002d00007029070a6844c0c00d903841000308a812034841030320710038001903000d411541c0c0d4182c0c3c00c1300c0407a40e8900411010f880040502c502a071300900744003ca808401c41c0702000012420694480c0d10300071310250800200d601d02c00088441d0310888400e4004980248101801a0025080441d1a4109002c110340000340a0011018103400b814200002207 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 856880782 1250 856879532 856879571
    0x210021507121802030c100306261b1c02010203070209010303031a01020309100509061603030f0b04050601080726150a050109060f0305180a0b0406051f0b0d0b2110 72
    0x45040b50032203401400c87c0c03011809084c03164411100d800506980860596040340d1880100700c40030200c07a40f41c82c0500d8903c3c03610148183d0b10b81c000c0960038200c050080b03807900041c90240103004407403a140007903000c90074030700003644140e000a95a25135900504140440c0300070340d01007480198142000c440001f00310015816407201440400120b401d581e840b59400d6540101141c212542c1601c0daa00b8040c011f0300b8074842078000603160140c00013880c6400e02c5928000c400c107030b503901295078803123006481d01a282c40840c0310021140c051342d0246081030400c00e01c16150071306000b00100b5003070b082c01203991031038000d00e050020b005c4c01030068650003030b20f070307106a0760b075180100b4141c58402110254808842000c2d4280c06104030101c14401001d804c1809144144000c10899451404104a003081043c04800c05100801c0401c00b59000c90054401450100000503401c0008400501c1034456460158284c184180410a22090900803a422009644003e2001c00400307047d40200c02c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 856882032 1250 856880782 856880803
    0x190207032006180a0308041502150c430c09020301290403080301091a0405010f06080a0f06080d030f0b13180b0a140a18021002150712180203 62
    0x3d01c80075140190f0303541e041000c00055410500180e031392502c030407042c0000c00040319620054414201080492050049032501c9000d48498813410581800030780c2d650b41c0000d14840c284401910311040303154034943d10030140004500320a2500c1d0900e4034104000000540c060010284103000411107aa5881f00c03600710100100c5462009442264100c0a14052500301810341200400040742c06a0a94042d400381d03240c244030034000700d084104100548909001e81d4240c1c004004080040e20b00414103960403024042c00468035800036403d6004a9070b5942c031002c12617006400b800c001c0c1d501881540c9900c2e0000c681030081d480080040303040ca41044210f4907245a0394070f08401c0b00c4100c5008200515400480c4c6d00580c28030742220380140090340d1200c05410811004500c0e40107191045030840110810710f800250916000c005c60404544424001d50003081080b900758040f907468544074183c2625000c0342c07441031904140444680c1c200c6c2044181290034800003684c0d0004402000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 856883282 1250 856882032 856882057
    0x30204050f07021e0a05030a080f130809011d04091a07030911090601051c0c120207020a050405060a03140102030f18060c0c0f0a0809010f02240606190207032006 71
    0x25104c038100e03054076040300b00034040d1841c08041420800643c3c4415044e00643c1007611084481c0c41d03d1031140030354550030800400b00c01040004401c554003607c01d40d00c2801082545208542446002c2820742e241d001d0202d800d14410881c44610301c42c00c0c02c001c0c0d0062036a25081003012040d6460700c4081044015051003071203500002011a131141c0116488000d180400341c2441c080c401c0500e019002020150000c90301401d100c4a896815100341c03180300342c0060074000000c0c50407080c40028040601219005083e16070080081000031801e000702800c3c42e0300040e07491504100b603010300caa020300500d40c007200010100c601c440c00010341e190000d000120096032481041c5442e483d140f000d820042c060b004074102d12007031180c1d401c0540b54440302a00d42a54140b00710b042241c685000504d1a02c1d1005003c06d00311011a000d02d2056001c1c0001e81224a07040d00f030480c5041d40c7e90555080001a40000424820001d4910b94090f0040d1a41001c903000d20910000030a18050318940112 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 856884532 1250 856883282 856883323
    0x60e0c090f040807030318021810050d0c090b0f0909031c020c0c0906031905030408100209010207030807052e0605030606062203081c050f060109090b1302040f030204050f0702 77
    0xd4030447e0610a81180d005103850505403440c040b09005d92011034010020141c4280002441d08059803c048595403120300c400010b424120000018010031309a142c01ca0100320800d14030791114504207000304248001103840754580b00e014102c2c1e01882407541c8030b4034018003605041d0a000204071500483c229030b035400303603900c2c3c1004c02e162031600700007501c5181c3c03080c14040502c031020009106484180058507903106001d5888400d03445854038007801a8041c220400114010401920702c2600c030b541a030300009400200c4048200001c00d1544549040c1e0070003810740d05407445030b07000400b4154080d03c41c2c1d00e030020010340503010f00220f0416198a01c500c2803c40e14090744400065940840c41c141c80d060040105681c640404601907003a5182901180901284a041d688a680142e40d44403100c0e0901c40e00d1000740504855031500288400c0480501d042d840c00540068042c04200c0940607186004201c29038002a1902c2c0c944102d400501000d07503400308a00c501d4500c00d0702d0444 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 856885782 1250 856884532 856884551
    0x5030111030121021c110405131401021e030115110601051e030d020f070909020616061b1d240c03160c0905010501051612050403060e0c090f0408070303 67
    0x50b03644190b40f4000394050100e4212801d4400f0740c000664881e802501908400480401484110760050700c800c108501c0c5281001d000910b08444400c1e200422000941800f403601c1100c110305e003040340044c855102c04401480315030044140c080b40e140c21440c3c0210248081e80c1d001e41c41340c406000c4d2501528100600385c00d11100814800e194160150403142e8a0505000081d11044032f1000c0001500500c0e400040440b5a809004805078008060900d0301601070780e9a401c0d042800c60448903940c403030558450421191400c0511002182c441046001c0c0300b41102c03c8202d101c030b451610030004c040d1486d507030070b41a00511000700c040c01e50440c0e40d208001c3c401d0340b56008000c0c0e810303040c0e1454100181040140404c60f4103c17000d0b4502404541d888030010f5070700307006031140748008543c0d51079400049490001200b41c48000c605200d07213043e0700c03a20340c041aa14040201c0400d6800fa0303810560b1410300c0e1201d503902c25200b02044645042a03615019203100e5200e02800b0151030385100f0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 856887032 1250 856885782 856885829
    0x90c0f0607080c0f0604201e0411040b04030c09050c0310180e060702100608030414191e031511090904021c0525050105070305070204060b03090105070909020a0207090e0708010222050301110301 85
    0x300d0280000b545016103841daa4904607800c03c1d3fa41c05032a41440c10030001c1003030001c1107030550b802220507a00a91042d800d02c0080900640d4285070b900186440e8043c034212001c0078840280142002d0f400b0308040d011011140060320115440014640e004100800c094040011500310510301201d1014a0241110350b0002040203600305070545000e15004120514400b002c2600720791081d048600722142c1c201c50a41101c00489811111000420461504d4030f032111440350301520040c076502d149900852001002103101004403860750010b200748c203000e441c41c110032860071010b00f11850600d042000091043c014840010b06010011400904642d09ca40004003c0c0032020304c7d56840b031070007614550203024207898480c0032441400300441c030390006000329410300000d50000c200f00340c40e01c02d42ca0001d0510b1003504589020302800800c41c6842800104181d001c84040241100c03203114a40b20648540d90160f4070076858101c0b010700100030b907010b80341140c0da40d660307006e4000a10a400b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 856888282 1250 856887032 856887037
    0x3040503250c0e16030216050102220f0501050909090102040905070903140604170705010209031204060809160902030601020307020a0e090c0f0607080c0f0604201e0411 74
    0x90750454881c094100d5428060030000c0c2007201e01030112011465592021040103003816aa040007041403038604040c01e602130340040512481104074041e40340301d903407512800c92304149415002c9803041006c1d000c0c1110029406005403012aa0713407540c60b4034110010f060740c400c6010050056850200040741000207506480c0184a03407142071180d46080c800040203402c15000450b82454450807180680100160403032149502c45a03181c5028100061440785403c0381008a500c3e42d0204401621038401b8000001d51f0303d001a01d240c2c441d41401405882c2040007040c41d4815800321030b0300c41c1303000c8450f0000002c5515100c00140e81c3d44543d00100d08501c1748120203074100040110018501c1c801034000da2040c8140710070740d1401002d020801c40d600040c03002255001006200400200da0300500411604003654212088491501b00300c0b070904104a9095071207081c05101560303211700210401c908018121800070030000360a04006440c03921854542c0100d640e01d18a034000f20b0780c20304 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 856889532 1250 856888282 856888297
    0xc1d060d050718080703020a080f0c130e03390d08070c020d0515010602190210170c0304061b02100c050904020c06090f0109020a06080a060906030b1506190503040503 73
    0x56511344503030502d03640307a801e03200417030040401c0c650015010501040c0700b08400240c2006d0032200058504201d056204c58002411141e40c42c1c00d14084c414041000304200c045c640f5500b02c8600c82c01e011034011a09a41c800e034a0341d0340c01900701519500109140b2082b41043c24080d2a070f40b42d00720200c50f558034464000750000f280d00721040c207103d000141c0c6030102c40c4110301210640c0e00d8100890b01c80c14244c2e14048804400c1d000c10006251401c40c41412403101c1c03800074548030a00425101d012070541d24820000c5000040c001840024024104d241807004080740c4445d0b0203d40003075581d00030480c04400030b907540c0c85170341c0d149100b1001c03959800300081003035444e0994929041e490b04800d9070306251a103d0118070094036901801401262900144a28403542c60040f09407030a41c00205002a40742d175070800070552040a1040e0030103075001e060012040c0ca4110b00d0407505103d8420118840c0f0000c4c803100b0400c070260464103811404901d440390f140c1d100c40c5003080c950b005001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 856890782 1250 856889532 856889567
    0x150a180503120a0213030b06040606030c0507060509120403080c0d0903020a05060a0c060e15011e0612060803040608160c051209060720010813031209051905010c1d060d0507 76
    0x1000047c09503c012440c058201101c0030050181e44401c241d007103030100da000001240e0244402c2000c5202c0c0e40c04558070640e6001912032211507203803180715940c4550405c07680c01401182100318030604002d00c0390313803012a081c200d0b0420b0560300024201081481010711840c000100d2000c02445141e100101560094040c46004466460302e9114280f01d210740c019061544000925040da081d822908081503445886200c0c1c03d000d030880300b0fa90002c150752a095198080054a00401c1001784000c1100c0d54030740b400340c1002ca5100c03403c5807020001804012404050700040303000400e08862241c46140383c41e5665803d07d0120754103001e41e49004c1c00c03071194004041a071f0200c1c5807110603003203400d82c0d9050305550f600503079040c41c000014000d000a40904125200390515503c0304100600440844485040180c0b440303044000128080756540d440314076210403190403100d24128522084a8020301d90075407000b04201c2c2c0074001134281542d4403a030102c0c0d00c860094824452020349003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 856892032 1250 856890782 856890817
    0x30f071401110c0d03020304080f0c07170a03110309130c0c14070608010e07090e04021201150e0a06051e060c06070f0e2d0102030c150a180503120a02 66
    0x1007815040d64000f04240e0181d401032001c4504807900c284202e9125a91007104107003011306400d00c0e4883c0c0e03081000342c4803480c46a0440440e1004012495440c1100d1150041001104600d0000d0501c580b590b5000322642c818400c40886a440d2420180305511020b00020700001e900d208803120845d480d00904805216003801c200c0303010208040082e0340051b265044a0f90b44e038522038a04c4141122200001102c20344240000441d43c1525500305000a08008400da80408002d003160185070f2820400c2040040400060700c03400c83c0316030700900b018800c00c2140e28200100b00002c0c41c0c0e902020403000d07801804215962000d06558412900504560070781c913020130301a209198000651005c00c0692070a00070724503020901d0700007101c28100002c662a00d0301c605e078100f981c9200a03941540802d104800c0b182c00c0c2041119280300c1d00d0321a60025051020ba0402100e0b400c212480b0b0b40318554a81e1000704038000211012241c1d0348000150943c0da00034418000d029228460000700c3c0d80 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 856893282 1250 856892032 856892051
    0x2806050a020d180c050a032d0803071d01080928051504050105010e100b0a020a02060d06061209050d0c0317130318061b140a24020c030f071401 63
    0x4a03400103c3e4440d10035021032075210010016004868800180400d11101e400c1241c002c02c80002c02181031001c114001d11071f40c0c1c3d41c0c0c4500a0700100ea521002655540c1541c40d02d40258428a040d100282005000307414515502034481c0070f806000c02c14407980d0198650307882d010701032a041c0300380c0040565054141a45220b010000141c60982d2190b003050008620045c822607900e0240c0020baa81001192400340c1c2d06440f90030014000081d400384030750080c0580c4815000300b40070b0701a401d001030050304015010342100351501510106c50300d40b0140500040c40060300c450810b8132420810448003107407604813056001e14080fa4810b081240900c82c949552442408610340f080c1c44e00e14918000c0181c00c60030900c2480740c4030001c1c0ca100f03002101e030000c03204000300c9540510f0350781c03070740072902c150061410010034011140411010140c843c50324803400e032074605203000c082c25032402c5c0081c2c0c1101d580c0e0041c6070102d409464005030000400141d101c01e00300c40d901200080c0140c810 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 856894532 1250 856893282 856893311
    0x1e10090215210702120a0e010c1a0915040f0f1e0302010b0a12020d08031306020f07050105090a1a0a0f0f060f080a030c17090d0f052806050a020d 64
    0x711402c100c04200d004507610f64008100091038840c0761350301c80e040002580d4119419003000840906000d25150b040003c80c4401800040c80e1455000020150034291141c9207804089505e102c10751412100340000607600000b00302202d80c0204900740034121900300345a40c0007008002c452051141c0c0e14090402d42c042d0006000c02100b2074000443c50782c1c075220002c50900c0b425009500000c404c43d80c2001851b000086e540000a43e101144840702c05d59074103041f0382c0600300082c020031010820b41d0410009000301903225800b00068003145199035161030482c0c4011401c107008400704e03000035080020b9a40002e01c0c4401542041c40a070410003c0ca2004000ca4007854112038625480410400780c0020030841c41c0c0d03031542d074072903407401c0d00e03140c00b440d00300034148039030b8010b40800400e036413070f41c407580405e4019004000c1c0184030512460000c0c5840e54140d40c07614410910030054140b0600080b540041b2a0000400b05141d0b44450c0e140c0024440c0c05440380149143c039101740024203 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 856895782 1250 856894532 856894567
    0x50105070828020f0115050315070908010c1206052b0602071a04020a0b0a050406030b030c060301060f03050105031f090201120c0c0b0108060903030c0a0e030a03111e10090215 77
    0x4c0f240030003003200340181c01e44031400070400c1c010250107074400402141c43c0591845000d610000320300d03241c5031854a80e12102c1c2542e013803080210000315040d0110f112401207219170780007454121100c035030052049800c110800d520420410042407034105100601400f40c04070f80314190f0140c20f41030fa204c000c103100c0ca081c80c410380f41070340209031000001c148030300722404890f010417141d1100f505040c0360402c100c002c2c00f8103007103403505400385101108258440d240070350301902031a00ca00e0040e00081800a0490310140c0c0001c1c866070003c2c1c040c106c0440416190f182071240d0040120701010700c0c0c00140d81c03002040c90351701042498848030340c0c4034942c01800001114403810407400c03e40d980e04000b40d61741d10282c0d01c2903842d800401c049a01c0d4000d08000741078920140c14140180c0440000003801c04548000c10340102d2100341c0c5012501d8400d01540081c4940103284c20f094107004081c0c50342e40c4040a103080042e0b079a80c090503041d0350b00d010a810300c10300c0c4110140e9039401e20031007161490 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 856897032 1250 856895782 856895803
    0x10050a120516050c03040e1006081323030706111b07030c031e050f0106053613241b0f050d0e030c0c040c020d020613030306080f012405010507082802 66
    0x190b03100042015a0202503c500704140c004101111068500d00d04cc050582032445403642c0344010054240064010f0180700c0c5401640307042c40b034440c0d02200b005400b00c000e11036200102d0304010420300004850012103070030b490b04004148442800104001c10861221402924034810514072440221054110308140d45040d40c400003200340c40750008004080e80c03c43c1d280d050090f8036a10010354440302d80107600c07690480c07044100254948500001c4400410b200c600191900d2848100d40654001d80c00072410548085201c02200540149444003000014040000015050042000c140c001c043c04070000340035241ea40d00e031251015580c00c071001529009909002d800c003142400411242ca2100b5113402808140ea6100309984059403019401c03000e155441d0b801281d001000c010303170800507403000000951544c44d0300d1361402c00a50221804100703640100c09021990f402025561400d0b8400740306a02d400c180064940c80d49410f5540401c8902007034003403d0303c01c0e400145d19011 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 856898282 1250 856897032 856897037
    0x6080a060b01091d040807050a020a08070510050711010804060f0614090a050c0a0f050d05040305070303110c0706110c030d0c061808180d0210050a120516050c03040e1006 75
    0x1016542c44000188111225255814004003030005001c200004000c14107c1d114805407074100d41c059001030800500d503040340030320703600152050140341401da4107804011081d0608604101c01a95841d2144600c09005410481c0504c003150800503075030841c10541c00b02480901c60303a500d496a00141000103e138181c82003c0c0c80010030084417562150b41c0c0687d60042c90246440e00c92001682c103c0031643c4404100401046000d060321958070544d03020364070035079031680c1c0c5800506004055034a000c00c0c0507284081040200400e1800086083c1100c0490030801a0003003c03031042401c05030080d6646070580501c40701c914240358000603c0c190030744654800c010103840c1c80f584861080c03414400810310f000412200c000078582c0f45410800d404014401e035071419440d408142519641216000441e5000c6400300080d60024883d6128400e5490300b0402843e2032451058415a1a12450240600080c504171050018800c49014001c0e140700c035445800c0141000b00c1c11285440781800 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 856899532 1250 856898282 856898297
    0x9040f030e0a1d10030f020607030905060a120b0901060807140c03160515090604060e010f0e06070e01031b05130f0b2503200703050105101e0b031906080a060b01 71
    0x30490b40c1d0800000540b40c124407030304c0381206c1590a00c07100d640460700c01d805005180800048541d136080080c03013400d9076962500d41404081c1e00340030a82d194000580e00c0361501800510440d03034070010349940881d01e8504120702e0300c5030213001c440d5441003030298215070000160810403144a5518040c80e18424011181611721041140304004420b45000c1301503000342021601040340f41d000308190805a600010302604581000c40c2101e100220f0200300360800420004c803650042c0360803134825020300741400058520041c0a2580314800151000d0000c040750f8602011015207103c8081c1070095030120266403149414003450700404800204030039101283e444450204a0b114003982d070588442956a004010303007800c98100e010417840c6882030000020106809000d0715000b80200006141d103e030030725540e00729075040da14000d50441441001040509004c90440740d01440aa41c00203402c021f49031240090b0203250b108012510460400100780043c95100049400302600c0d020b1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 856900782 1250 856899532 856899541
    0x103020714010617030c1b0f09040303050601111603020d1a0903072102030d0e030c010603060506031005071b02010e060705030319050108070e040c0905010f06090803030609040f030e0a1d 82
    0x145d881c89000d05211351900148801e1500440c0e1050403d203800c0c1c021700c0006840d24050116061000072034080d00000e807107000348109940c00c03201c40c0e605d220ba282d0151210060042030301859004030b1200a000b080042250001d2007180c80c8054403050641d8030109242c00e000f030115a494008134019507003513440d05075610105a50000ca010032800d550003031810f00141d4504000203005103200700341103010400210500139400c1c41540e01540c803c00c4001600e00340002410f01e01000b00140403551483d00c828008401d0b0807010300302e070b810044d0b5952204203140340300495200e50000c0700702e501300401050060406c000031010b1803040b1400304070f45d550113489601c0c0c0c009440c001e10904441d50040a01400100c074071514856119015000800e500359442c8203941c00c0b20701c240c1c40b03290a4140100c040c810254844402c40003042c00340700850542c1800b50008a170f0500203407008148402412134841014003030b442c0c59104c184010141c2c1401991070182a010f5100045400c100041a03400134 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 856902032 1250 856900782 856900829
    0x301150612090c050123040902130e0606340b0f0a1e02070c08030a0302040305060f01140d020f2e020a12030c02100c181211060901030207140106 64
    0x890b9000c1c1c0110740c20418500d010b00544006080ca480d8200958100503181d20840080b4020320081c591100d0059403031a004100d00b8204055811680c41501003400380061592041d003610000c481032a41d441c1542c899885a600381c0140300c40c914244803490550900348155110028450903605224040d65681c000f10342e03088a10380012991041c0180c0075071462410a0780c090b00d031651080c00581172440d1180c0c4a6441c5030400784044d40003030707000201802041300c1405216000a8401d038510751550421602002c0c2801d040802030081c4240304050042d556004081c242030003015203042d00c0c0440408040e065146000a0803515a04022018030340c2403000615050094100c000340b0b40305500204201c018103031411080c01140b18451405995803941c0c03013600552100b58490f09400790215400c140c2d4810300b50301040c210350706020140e01140048449032160441203c4055468800000590003805000c5004c2c041c0b141c141042604000154805c130140d49080e10800364880700d45212 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 856903282 1250 856902032 856902041
    0x70f03060507090b090904080a171512120d0c03061d090f0a080d150e0c04150804020f0907051c0203011809051b03031e13050a0617060406050301150612 67
    0x150000b644d00009008142200050b00400000f8500b401c84100a0124020506415580a6910410840c00c5cbd1040c1c645041011400480e15028141c04504500c88030101c0c0107140416120a40340c4903203480040c86a405a4058110701c0403888110000c24001001100201c50300003861060f81d4441d590b000d0000b0f007800701c5035800301950786003030390000e8820040c0c603840d06031903c01c1c0300c1d0810210f402d2a0041c48135100b076401e0340309030340c032a450510924603d00d581c11201e42400044818440035031101d8041c100884d0b0203440150841e290407604031424860314040011951218400c08070711035058005604841ea9170030100d82040c003810100c401c40c4d6100b01c009106500030003810031450411400b05101c004000c060b03a0034000e208490307503d20700002400314801c05000801107000b0f01e80480c21401f5001c01e0700c03009200c0d81083c0c400380400b882148030308400351500000030340c0ba42e90354110401800000d00244007050148407510441c162751f004074070101c0c69000d20071503211060300c01d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 856904532 1250 856903282 856903297
    0x1140d02190e01120b06090f0a0305030f030a061a091e10050406172206060504020f0c010513230a080403110907110a110112090c0510090e0a0b03070f03060507090b 72
    0x101c0d47c0f4106c20b507010842e120140b00c0d091900004070380e1000010407410300c09800450301c40280f80f81c1e00d20b0026442411503166420076500341c500c510034000d0317400454041d2121140265440c07411910320101c2e42c01828420340703456601280e05800080455403100103401140c0d450f40f204c41040d0202030004424160445403200c0b440c01c1c142c6900d60b44030701c000440d03070018008c500019610380c4400c085030980c4d120104446850701b001402d0407050000748034403a07100d0fa0360b01c0203951443c0541d0302d0045200d070004d447c806018481441884103003080c480385913281d0b40848101c3d99196645012906285c7e00d5010a11840d00c5900180400c0d0081183c070310010802c9002d07140e03201c610b0344c4900001103070301a030504000452007030f1180c50510340700c2d014031680100e1801e4a06450007040000704070105a00d07000f0004038000c01c004a0740911041a044815a0070218a803034018003c02e1800d40f0a5000c401607140c3d1401c00002e10116034000c0e809040d80b980d80c0d14100707407500d01d42c800320702c214103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 856905782 1250 856904532 856904539
    0x30f0304080d09051003180b0c0909013309080304030f1106030903040603052e051e01081b0f03010308090108161e2003040503010b03060601140d02190e01120b 70
    0x840c5414941c403d074014040c147c00b151903515403160a440b8a0150368007258100d1110b600040c20464502d00341c3c2a00303004220002c3d40d101103c0b0300d038103c943d0402c101c44540b40003a0300f440c403100005000b2040300c00a07003140d80840c0c1d00c85980f070401103103001407101c064982c2542006501c0c00c5040ca070f0202e03441100000011482e00d07281c41c06c100d0007880010518001110003507450321304c103814000480c001c036045200125080e0304103400c1001310b580822940d001300342d000f0881003a45e60800c0e030b229408082407008d00072031070b20b150300380c00248904120000e600c40000300100810010750301030201e03201d003030362241210350f19a004200c03403c4000b1504408510180c1640780501024504508000d426140000c0481d05164503002d1200c5d41c00e030300455540000c581842181424414000f240b88120b0042400307050110001c0e005405410107004d404800241c1e03925400c2c0c040d011034116100c4030a820b0a40d0340c10000c000d0003000c2c10200c00340024020400d24000000c140910048180000c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 856907032 1250 856905782 856905799
    0xb0d03050f0f0906030108010b010305011e031104060b0a1e0e01080f06010e12010f1121090f0d0815030d08060d050a06090602041e0b0301090207050a02030f0304080d0905 75
    0xd00700d4216504449a0400c008070208038041a60701c6040103113000307000c04c000125000008400140076100160040700c001a000027800d602d41d2400b118440481e40c004650588100c44440881c0c040c0500c0d82003d1590350001850801c066442031034051a4482048a0354a00310140c10465070101091101c3d8002450344001c1459039811111050700102c050504920400b100030200d09514000e0000482e60b9564211001001409000e109201d03040d520f140e03032510380394002604581076070080209005501ca000600403400402c070704511281a81d0440d10451a60320004101c00000c86030341b500401e01807243c0d104e504001486040403121a00e44a00643c0c0395001d000c85503840c50b4056843d0704c11180c1d140045030041c0b04203020a0301600e00940d49a0070040c13080180c6000c0a0805081c40c0e90356010400a24400207580c1035528020340940c3d2248a0304110746401809440654180500007170524404400401401120b801c06e040d6040703040100415030300c80020f40300703454106030007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 856908282 1250 856907032 856907047
    0x110d09030824130b03250f0905190c02070b070f021017070305190908180a0305030304060906110a0e1302040501021b06120a020913050702100e0309040e100b0d0305 72
    0x103d070400e00240078044c0441e0001012015503146c16861118003c940c0544e994040c00304c100b040c1c0300c0e1800f40c444c950042c0428180400035101c0c0c00309504000940d966940100700c1064800e1010100901b030f201d484540b01c0c409420b03c02203845c65004202e02c504940c488148000d030040d1030250051400c81300b0340c0b0117503440381c1050340601002041d503003541c60706104440c460b00c50780c460120980d0080c0551600c0700052074480e80c28655000358035205a0306058200b000500000440c0e80c8168441008a1048401c0c5841c0028200b10100400b1034180030420110f50f03544040700c000b00c05000c503040c00d092081c040e130710803c074440c901034240160000703030f0039480104201c00509110800070300110316061681c800c0b4041d5140585820034a0794000810790a0b92a1030100c03046480c00c807180400c01410015400b0395626040c181c4080c000d40c80f0000200d61800074000d4038196400904103200da2152121001c1d1103500302d00d150302040740340a0900400d41031021191420583c19216245040c49 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 856909532 1250 856908282 856908319
    0x40606080a11091008041106040302030a1410020c011401061b030c08160f0507240f030e0304120c08031603051321050607020f0709110d09030824 64
    0x12041400c031262600f040180c1c0c0e41d85985525103038020166480203500d062030300d0079910344058107071384074030480050005202590b004a24164899070001d045880a650701c0a41401c0c03c4901c00107040151010600607500c11040d04140c40d041408201481140e1721000148c0d0741e440144200c2118500310456200083c1c05100511030b0170380100d80103814441001d485003410700050f5412a8a59851a41c0404002041240c44050500d0170700d0051603841c80c4080b00300ea810403408000800188031240e9008502030380c030500140a040c81601d603960340701e40ca000e40d0075820740b004503614001d01000140d088004819201c0064042d0550745c41c0c03034010b031401c403a25004041040342c4101c0740c035000103c10101c110b60281d00702c480d4045407414200c5003401070810b0700c011b04540035900423003004900d02c003011882c0015241412400124130105a0b0091964001d03500000c54141c40c0c02408030505030065a214402c00350070024103074851030004241500c15042d41004d03080100d00c106402c0022 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 856910782 1250 856909532 856909541
    0xa050304060315090632060703030b0f0910180b1c02120601080a062f0310030804080115120c1a09031c0e0d031e02190c0e0105040606080a 61
    0x29010288102d2058503500540100d840c280c2c82100003c450780804406d403031900705041d003c80082c00341200c5c0c03514441c001c14414898110001e042683e03070300850140c5e603514540384411203c040c0807162686085400646060f1440c024540040d00304c2542410805203270165a44141e0058140d07600814001050002c00032485c40486e84244030070b0140071007030410000c1e640206640070080c580c045460030041c4c200e03409801803250340311120614a04281010816517542d2409803c13960307803503940d0070014400d27160310303080100b00305000900026130760015002900989000200800700756500c40ba14401d01c5000321300101000d0b034200080102804103440308000020780180f26103003019000000e03040801e2102d116003814828141c0300319407580518452141e01007910780c0341402c0d00684001c0d08040c1c0031803108120940c2a0003001d40d2034070030320000100c211903012801a06806103030041c0507484901034101d00c504110000074182c030309801004101c90b100c0e150b80b542a200c444c1c1c40030141 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 856912032 1250 856910782 856910801
    0x20102070b360607080405010e0108280e071205161d040309030210020114090f12030408041a041d07050313020a0e01061709150601180f03060e06090a0503040603 71
    0x50389524040082ea8407400014a2058410140e40d030f0781d02e0620001400c2500498805410405840c04001600700340004c001c154206030407128a00e08d00d6441038101408841242064500480b0000100c41c0804200c2220781c5101304161060b802e41c00805068203240ca00c1000740c0c02032805201c000c0114860308580d00035000b8600310746040d4403078020421106030004140c0050795510141c0042c03520803280745030000c007110060220b00d81d030144c690380c3e150341421600b03a95010020110b801c100502c821280206a03102100004424580414400760000c2c0f041d07003c00c40744090381c400342d804000d00791441401c541d101c0724199201d50f01d241621058809040342c10154044001c07940f0303054115072034001c00d103695440082d60310000e034100d03130800040c0031035045500c1140b0781030b512502c0071506940030070b00786813480d12480c40c84000460051140c0c030000c040c4200c03460110034405c050308090403503443c40c4104c9a598a45030030455a07006405005000761700244401e005440c4240c02c1103600 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 856913282 1250 856912032 856912117
    0x604020d12020a0506010e1503010b060306010e180106050408060a150311010507050f03031503030310050103020c030f0a0f11160303050a090b04091d15060f0a09021204020102070b 79
    0x4001240d51380c4c40c0781c10020b80121603544284070800441b80b40c01c074800e10902000b41c00030f000303174542080850041e00015140c203040c000c01007010384164076154540b500a89000304a04800d5075245070180540e8040d010744545406101c00080c124946401841252030341d0785007107451a40f440d26141d01d00400d00226604000c400c104200104108100c0b6200c0e004c0e1000141d41d487c2040c40c40e903644260141a1180280c200f4010000403004001e00d490454800382000f60383d48040c0104181584240301103000f4040e004a40d210580f50b21030500340e030401c0c041d1103904401e1400e20035680d544a0410202100303031192401400024032480141c004481c00c0d08186114030380351981030040c2d400c1b60308103a255a60f0b80c5040c4080c0a00c0300400b41602003580080c00d940d5070049404940c4c1240108a0703070160f6a000e42e07800c05a25507440580080c031000e8801c640fa201900d01c000201d8000391003d80c0140b24600c00418a40c01c0003003115043c0780c1072524000b980c90100d0780c0320303500403600c001e2024 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 856914532 1250 856913282 856913293
    0xf060103181218140d1b0602060613020403110f0102010b18100e0f04030e0d0b0106031a040203010602030d091115030a0609060501050f03130215040f05030604020d1202 74
    0x4403160440342441c140b00340c200c02c180b00701094004006051080c4010b20440c040c180820000d00399110700d80e001541611403040501e4141048144c081202c1410880340199040028070aa03000c01d20f180100012075503840d091005a00d200264003450201410020030000820100e182c0507000c1c86c0716036810300011a034a101200059440c601e0b4203100c03101c902c82c135000c02c0000070501402001a00c051151384055050058000084110040c802400d04c104102c03242120340c1c0e071020585a40f5804003204003d503846100040c00b0f0400410f0545030708a00841140147c50507000b07403030513928590300450030092038aa1020280011907019203840850b2800401240c07280e060032590920f031004a9039980c100064024119110b40e8440b080461030300000340101c5ea480070884010741c06a20b92140c41ba00c0301c030100d58501c0f060300740095000100328541203410b070584010b0000c841040f284200d80603596424543c80d4501110000e500480d00395031140080d503035895002803410a4412110b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 856915782 1250 856914532 856914551
    0x3020a0906030f060b030123060c0726010f0e01140405060705220603091a04030f080c0d0f0608010b040204030809041e090609020906030c0109140f1903051e060f060103 74
    0x171440e030310a13086011078074020601480c09841c011a03030010490281e030031910b410900380c3c066803030707a03141e0180f021011601c01c88508501204411000307496080c0000700444814a0301d40e00c020102c100c1c01192035400c11900c04415504101050300c15130f002000381455030340b00030307040b20903501199884081034031200d048201c01d9040c0403210007602140e07d0014038000f03582411800c00c01e1030030b07801055201820400001940c080b940301030000503401c00c01001e4a07880307030401c1c10f4000d940c2003040e01890824030050403c510b070001c0c1c040b50038010081040c561507400380320a910842c040030740400e03810414078001e4285070784580365069020640b100700d07084480001059541500050320309030340341c410b148194500203200c0303500a80d00f107000b048840c2d40b1a001038003560040c4134404102c04242c41d15807898480a8550b410344100429800e0310303620080c4010b44500c010300090f1018440c90a811440719145a11036410800c614020f200954404a00c00c038514001000e160400d40c40c2d41d501d1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 856917032 1250 856915782 856915799
    0xd23040b0705030403021207150507031b0c15020d090308091906080f1501020a02240c0304090c020303100e070c0221012a0c0203070302031c080703020a0906030f06 72
    0x50001c035119201071030b900c52460041052140b03007240d44940d1504403000c100701c800780602c6803000190070f500f440d685400072420113035802d28408030b4424030020705071010001c000407440104243d0703105006a40034118111000caaa07800007006e4217000c10007146051004c120080098064400700404207071100d40441e44020300800d85510040100f9841000d0000a403012403205500849103c4028284001100001e541d034a213954041e00480496094882851009401e410701020b40d620b2146d0300d0b0f842540041d0340394011704c105040e180c98080c815150920100889010703500025000306200c0c1410454580b0b40009040070040c412008072020041e12140c0c030840c055030018038070103803502641e65241c0c25904d55403401303480140e00b080383c01c4400d6401a04040313101d0741494444002102407000c6444c282064101950510400414021421100103101050030b86c5943d401a1500d5201c0e042c3d003640500f541d846c0202d40810001d009e441d1003a407081540c00082240825220b6964103030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 856918282 1250 856917032 856917037
    0x605042312281d0d020f12010608030c0a0b09120f0309011b030f0b040b060d0902010509150a091a0f031f062a0c2705070816020d23040b 60
    0x302c4081101c180d02070046000c0d03805800c600001c02d9440e903c600c0c0c1903600040c0d04585041c00548102c54003140c90002e001d00354414400f07441c21500322560341904107031082d80c400c185681241c1500450001488124001c1403c4014030312001d074041c01c00c12101191605a04000c01d010b00c250f50b1001c00c1800c1c1141080140740e81d8095850010740504002051000e8411450015018500b895881d440c6503e540007180c240240c40900054401491300c0100c1e039500c140c5000d2580304440c0210703515a5840c0074002d11b07840455842d00300c00203036114400c02c0703c070748007450036000c1d03c0f0148484031200150100465101c1c600c01c2429580700b0424048800d2000540c000740002030580b13004038002d485450440100500070f881d4800140340031f81d2040040541030140f6082c400c2c5d620b504021810191384040c0014031918000d100da80780085000700006000c545188038070106003a0403c41c2e41c00481c0e51900c0d520250303a09400d405c0030810a91a119484420500c0382c0010003002a03150810400b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 856919532 1250 856918282 856918357
    0x16050a030e09070302030f010603020a030e1609050612190317070206010f05030c130e16031208011a16080405040905071707061205100f030605042312 66
    0x544103070101c900d500b4030882040003089102450701c10070a02c44800c6540794690704681e030500e000f5943e4441140c0480140032b5400c100107051050400281143c0740042c206410740e0600e000070840f5588500c00c001030b07c07410003500c14603900544901c0e10303410800080721442034001d060040981e2805c480d2141d60f80000c681c0340c40182c21590041c07080400300300407800288070440c01000c00380301e200001a643e41e202411500705c0360341c9445d8129012002d01000355021f00c001d501e16603540d501c1c1048107645048035000c08c005050580003007081d8000d0f00c0c440310b42e80c03440c1205900341040e07030b0005c01015800e100150340b06607051100103550341d0341d0300801d4001031080004d0149140307840d5140d011070300c99030000d14458100362428041c0c56448801070307806001d42003002c51103440e0f0314410711810340f59802c0901c051043e40f00103c03d108541d04958025441040c001e0080b001807500b4a883d079081100506a5801c0b960f8038844e02a020400303014101100800814506680030459800c91901034 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 856920782 1250 856919532 856919537
    0xb130c030f060e011b03021e07120e01090b07080901030b06160c0e09030a12110d060311010801051c150f05010f0e162d02070f0914040816050a03 64
    0x4491004010b001d019000040905600a1000c02c3c680c604400b00205a18040800c1580c08100c4a01000c6804101c1a0304540301c0e0041d03a480545003030440c00c402248140d4008070761403403c1010654418101642251030b540b0702a404c020455865281a0b4841d8107501d0401d61251003c190075540c1800401c0440c0500c0c400d01c004100d5440c0c80449135665030700c00400c0c0c4503064104044d140303000c0212130450106280c03002101e254500d03100c0041c1041c400c00007594801107903014a800c4250b00500a4034007858440c4080341072030004485081d401d005043d002244100206140810346480b25a49440742464083c85180100385504440b04003640c8203c00c0c4d00c1308010001c1d400305a00c20780240c284c1059a02d0207140002c0280146910031062008100e4480303039000011050070352600e900d0f1345004000000c0300000701e000399540154000e02003184007804000803541958855242c003025107609134502a500c1e43c444c084190484845010700c075298805110009100380410f1460324407a4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 856922032 1250 856920782 856920803
    0x50c0c04060b090f0105040e1302030703140a0303060b0703020d0e03152401020a26070803040303050109051503060a02070303060b0d020d051005031b031002040902030412050301120b130c03 83
    0x20f0401c4412128040c685050220803c403d1080f600c441540581c4225500b1728128200260710201c1e142c14072641c030140c5072490445264045c00300104200c0365150107a5000d101c03041c0c840400038100d100360362000300583d00c480354114490780225034203040504010159900c00c403010300043e403d1181111142d0103085250720aa0358130100607210301490b0020304c020000da129917a42d1a954001a80914001040102040780705a0600c021152066171100201d5220708040c600034028000a000d18002c0381d06201c0000c084800703128030b06904c408010b00814031912103401c1c81000358000c1c50b00380c0c201900d4404c0810644100402002c020704110700040c1c0c0c82045a02c40e204a030b1000e0a60410b1010040d402c11030b5550004000548081d100540020780d8a40400070385030480d03900c03084002d90700200d0000750038038650780518403540c0185001010700454850440c0c051009000d0002100d4081d000c03035010072140c40e41c55602c03090018140700b6002d03960b210130f965040540e204440c2481e05 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 856923282 1250 856922032 856922047
    0x1903030e1e060f07090314120a02010c17060a18060b0f030f0f0c070602030601030e07060306060801080d020607080a092f101b0602040312080610050f0a050c0c04060b 73
    0x410070703680d008403d2500314480341001d01c80241140c009110251480c0d24001c1242010b4005000b4244d40303004150b240c55031100381d4400a40a001001618400700780c10390b02e802000d40c005d901082c82444000c101070201410442031841303203030704080202002960385101050401985d801030410880c2014400d0302c9107000c1c0d401582c0107100400d07000b51001008117200d0300311400d400340c6441c0b5a02010150300d955072000100c00900c41040303816010300ca9540c0021307206416034842c001351240c1e0f0761000d140d81e032180c2c541590390b40c080074103600580c04200081c2c01c45100d43c0100707821520010011600d0011601c691000e801004140040d5131482c0c414541c8000e003890a1008540003030700d0b607070b909032240071001d001c0540c85900750309008102c6613040c08110360395045401440e403000424100089540004060042c00c136107070b600030700c0003500c40c3c907455024009590040c9400c1c014a803404260301802c85036500800303820003040c0b1404101c03601c6a962809110080e0216041c400d48407100c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 856924532 1250 856923282 856923343
    0xb1801060f051b060a0e06090f0705090601030b04060b0406020f0f0d11070f1e05240d0609090b1b0403050a02010c150516030606030603020102280f030e0f0a081903030e 74
    0x107441c000f4181d00544003c96a0791000c50b5803000c40d0030482da80d413020b540353701c016005000d015903d035601c945004030210361001140042c009440455084629651002c086a640c0704241d46100b01c40344e01c024101c14031103102d0703540d0300492001c1400307458560755265000c0010b20101d801030114544041e0f40d02000100310440c40c802400d080720f20120055600c0c101081005855080100708080020009200d84640d0051001018184020030076280b49040c82203401005640039001e42c1c000c10a241e05c03003203c080980e01230383e811402400a9407003a41c010b6509450244088a44804a98601c0d442140700d02c901440f403018901d41d20442400c540d0000c048590940001d01030500e002800e2015076800540f00384810b0340400b03040c00740c80203040700760300306a03100400400034400120104105640b041c2410280070042e08c0e02c0c0842507901040100b1a02d140c00343d05800d9100303030103001c41440140c000303401c554040c0c02d0020301041c4000e6030a081020385c020520b40100d24108101d120f20 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 856925782 1250 856924532 856924543
    0xa181403040305061006201e070510080c0406030509150106020c151806090a090510030c210615050415080709140c18060d0b1801060f051b060a0e 64
    0x9103245c28944a08101d00036141003041c4000d5180d9850700c800d01c001148040081c8000c0c03104402000394500b140c0813000d80e40382031038007415000b076840c440c80c21f0003d801440f401340284080004142018108401100144002490328080c1e1065a50031f1024060542005029100a0f0b0142100c0200c4c10b0500c070342c05142d10302001002e0020800e18860f1095138090301d522103030480314541da0304004d80006004028940144841d0ba20f02000e000303000390504400300c1100d1051070b40440c06503807018000c0b81c020501c5d0005140b2400a55140001512a44107500d20380c4600f507035003103980d141c001184c102c03600c0c010100e81010402e44103100c0e802c03041285030002c0c1b1a030030080c4a040e20006152050703c00c042e00c0200710705c0001c42c201d0710904400e6070502d00c49502a0840b902c440a401000d8041c0823400d03c124021040c04035900f82040c0039100440c1690020340703401ca0442c26600d4200c803d5030098000d0791800d1a12403000d140984140002c0b80152401000450b440d4001d004190030701 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 856927032 1250 856925782 856925791
    0x4050f041a040c09090317010807050102070b0c060c09120d030c1b0c0e040807060f05160c03360e0405010c0f14210a060806010b120a18140304030506 66
    0xd824040030000051295000001136074159000400c0d03c000f01d24080d15209032180b0100c071134043c5000085522400003d540701124002d03401c44000d03a0f9104070641071071180d47c4610380315800c8040020012010440140765910028080000c15284a000c05040c4180c000c40d00002a880b03100e54035105600090404690340000d20040c83c1c8080b5580b41c2e0100c02c068460f2030081c80c24034002400b4030008009840343c4076003048003806482c061130a21740040408407245001c0d91400742c0010442c2c0e02c034081041f665503240e180c015111981c3d2028840c08800340c140c24514490701c1400f50280000410254000e00d0981e071007514a082502d801420740e04850780b40c00400119a00c0100160b40c44150290f80d04184050a507880c00d007000302c84400480c4c20382e015072240004050108241130f50740014110743c400e0050301d01326626083c411035248542402005007402820100b4a4000a5485158511250000c11340d24005075900d41d04242c210f01032100e103c0c0c0010a040061000034044207901 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 856928282 1250 856927032 856927073
    0x1208060f030312162f150106020606031006180f18050c0a05120316030903211206050f06090a05030a08040f0b2803090b010b0703020c1c0f0305040504050f04 69
    0xc030603598940803051283c0d420302e1603e0170658013003800082070000f40304d02d4041b201404059a101c18001e5581e660a0f03844a0080c400d004040c40000c079144103a03c01e443c10880784145001c0f41010715006000084001c0c503100e9030700c0800850604a42405540e0981302c0d001410508003240c00b002070560455100b103024544200406082a001000f01e0f080c040f00f6864400030307444182011102c0303a400f80c1006111494030980d41c00501d0395440d81c2e50640c0c4041d81c0f0200444103004d568400d6401522485802c141d0070b9171034500525020010b04030b040d401510a04413140e403540000d02c0c00d602440c05a64810000800b84000115408205c0141c01010794640c6006800001510065404003516559a405003041d8440e14401d40100c0d121b070350880170308131707680d612144d400b456680b1540c4100d016100f0500d0844c1141000e0010b0b942003040700f400f5151800054a840001151645007201001410000410a40d5461040718018007a010810a5515243c94042c0f0f604083c1c6105409 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 856929532 1250 856928282 856928297
    0xa170c04050105070f0f0c24021b36071205010614030a0b130203060f0a120b07091208040e0601030b0d0818061204050d05071208060f03031216 63
    0x441d0360880100d0b00401d6005c24840018082810000b4045100e42d40044c40c2c21340c8000001030a184806000040c03480a40034140b01020247c0d0a913a585070701c0d205001c0d48400e40800d03280526040701c218104a43c0300c11840314a40c03200c509024041c49100f2030900c503050101c248000c0c1d50703218040e01441c4e603102c0b60804c120f50400744040d095618894505100050000010302d4404c525000901001d801800010300030b1291141800079400485486015614114500d21649401d035019422a1714101e4200307d812034980720303920032000007030000081c0601c110b40055843c4441807a10340c414082c02c071454503242000c0111810420152003241003504107149503102da5141041701321000d60100c0e01680c0d55441d80506440100c18a8009074060f801041c0403085450002e0300b02e10840c41001a91070301d100381c481c00e69a6010383c40024080302d5413024224039050103091126000100240880210101c6500003491507010000b1051425a4081408150410030742e4203050b0013414108040d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 856930782 1250 856929532 856929539
    0x705060a080f04020609120d032405100306031e0b0a020903190c050d0f051203130308060301060e01091b020d0e040f021b0304060206011d180c060a170c04 68
    0x10000d1002505510321030140d40c0105086540301806c4030029103025080b400544540e0343c0260311401ca40e0740c846c0c0860708182c42d59954100d00040000900d50415505410301d040c0400e01c42a154104900d40c241683c8050200101d00781504110144001c064000a4442545424401110094a040025401400480c030340d0364000ca8170b0300305901035a90741d40c03841f105814802c02440b101d60100d03030020507038880182400088000001481c2c0100119841c100c100010500c261000b202c0710004082520103550000f88110103042d0084001000402d000c0d4560700000216031080e401700302504d54801e45080c1440030054120802a0207001500800c07030b8031100500042041481d4903c2180d032410740107038071403080c3d042d242c0311001454000e100c029000310b425030300d0340180a904054400c000001508009581038024400a00d4012440548444e00440003c00840208003054041e00807950b079aa12140c0c068500c148140c0d44001d0310003100140d02d031b1003500c05000500c40410412003030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 856932032 1250 856930782 856930787
    0x9010e04290105010f021c030b03070e090d210c050a080730060f09061e060e040203150d030f14090d030e12100f05010b0309060c0a0e0619020705060a 66
    0x1c1e81182d0084c04c1c410007041100500720f007414111000c0880341000181c581d0082c6900d81d0060450354415000c55602a0f00e8400c009402c0314119640d40442e404904032480e02403003426030300340080094003026021710448611009442c0c8490400300001c0c0c0120f0322030101c0740d004801e10340101c03203410140e20b2400449050707612030411075908914455012400d004c0d658055100c44001c0c05030300240810795440c1c1c10350001030111807140f00e0303090030b1644a84109606d071200d80003c8840c03076103810347c20076500000c6c80042c3d04014405540707121540140700701500c0e02e4040c3c0041da44640c0d07030080d01030602c00010341203e20070016108200001c5c0680c68464940ea0070b15111540c05082401d00300d0f40b95000256002414400c0c002c40e401440c5407540d001d08190045c0200800c90710050040f60b8890684caa041d00040300c15003169032101c004241401c3c1c99000611001e08070b4070b0f1104c51404075102082c0e06910000e46462070790705900180c00c0050703041c4580c40151104840781450702034841c500 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 856933282 1250 856932032 856932113
    0x60f17040c06080601050705060f0f01081902010c031214090d0c0b2412030301031115070201180b1201082118030715110c0a080a06020d02040509010e04 67
    0x2d0030b0500503000c0100b00c1e03581c000d00a0f220380c2035100381101c08a01c0c1c007805040000c0070a8541c22041540c80c80086010040403880220400400c03a0215400c0107503001140c1400c2c9612042d03003480090a00541401c80b14001c501c4500290141d40342141071149040d840d101301859450200980d0350383d42030000f13490069558000da4003649400c0c60300c10310140c1040c48007400380c400c0d5020045520000c0c030b4a80101c06035048034010304208030182076480900c425410b046d45007038010701040124800541c080e1031100109a070305030010410913241d41c1c5040341030703003c1481d00b01019400c0c0010085080200142c0300ba410400c4000005050b428bc03100c1e205008105003000b03c000102e14440c060b4504102c09402411180341e524840c4070700c1e0300007420103085842001c2940c0190541d4401a042c0b400d020021500d13554002c010035180b42d1a400025084141c0246440f45c0030000061282d8400342a035020703001040ba40e01c0d0504151034a1212000f116145035804040d0f416148046604040c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 856934532 1250 856933282 856933289
    0x30b0a0b01142b0e1f0b030c0f130b100507050705060405090402060c0f1204080606090c1b33150a050f0f0330030c1905040f060f17040c 60
    0xc411486203d00ca8441019015a8200d900a40305458184804049544182503810709046013000026010028180c8611010b036080ea0400c6070740e804074807241071500120f101881414070000e468404240051048400410180c00042000c076505081c44401e0154000402044038a14580791402010901c0b01d100100041c0c45144046906041e1420a010b4059040d440340b0503100790402e00b40c40f82d02c41d5001401180340502c0740b000068083c2c1401400f003805401c1d2000003905000d010b01515160b400241180c0760b06d4007441740c140c20703d40f02c0d942060300c4409900c2d508010509514a5413551035500500603041c3d9040072031500013546442c007400d020380d18280c070303d1901080003a01060340150115075494252040b81200c0c041c20846031100c1003465251808481c004a42404000e0580001e03238100ba4080003c10840349900c807040c40310540801903003030250800d5aa0f000f020301d00410341d4051801b0907042e0340700e964000e0b8085068505042e40300504aa00d05041e203540d071a0380c0e02c1c0d00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 856935782 1250 856934532 856934587
    0x2030f0904090501140601300c020a0c030f0b0606120f0601030908120708160906050d2c010c02011104120c0503030714100603050c0420070c180b010f05090604030b0a0b0114 76
    0x10124427040784240321a1210f107030003849662006540e49005a80041e20130816a010105d0101060282c5024022248201045420b40c03c4030740b94901ca500807a50040c000d94189a038500c070342000101000007829910066440384c01007407501d444054540344c00202444085800d05a00076040c0341c109480c00103440d05403406a4554999030f86403401840d1108881450780350352441a082126030b007038500700c00d0741400020702c1400303803458090b4265402c01c03006001d1001c3c20703c4180105080014030302e2031503001d104210721250f03807600800c1c110791103c141941c03119041c4100d0b50709090308001d1603001821018003008020b155407a0103031a503103601c01c094130413925400e04904012400500460441c840302c0051317075600c0c3e0352511498201142c407814800c1a455640c815030002d0300e101e2982e1650301a100c0341c1f54070502c044111542d41c082c42e9400d5000c902440003101003a07440e81c1ea01e1046200700b00004154034541c001408003e003408181748445420444c0b00c1c0c1c9071ba4507040c0a4014007265 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 856937032 1250 856935782 856935791
    0x3070305030d0f020d1805012909060d0b090a1a010302010504140d02060c0c04050a1a0d050f0703030f02150103030909110909130c0801020a02030f090409050114060130 74
    0x703c0d4103034064403803040b20440d40d600340102060f84240d070000c01d141041c8290002c120141c082c3c40d0310fa60340f104000c1c9160912803032000400507418002042944014020300322006440e06a545100700101625550300a5100e002d91a041001c0f803001e0f84480d2144c40c680001d15891580000d10701d2107540104018070608056010182c1c84c0d1404510303800394010035458a0303602c14020950b46180d0704001300e11460802e40407d240c820b051041c140c46075900100e80c14012401424000340140c807141c100d03414403400804075161881401010051846541c802c0300404102c0d200924244245c4035400c1c03610030403401040017942100c07440084800b00e2001080c0c075049011204400d01500c007070300e90020554001c1001400d0b00002128105204040480b01551100011400c0380a000800000340e442040009000d01110740036149007a002400818010031550b2400c2c00c0d60144000743d030351004580184882c640e0040180b13840861240c044451503901401c2c0c01009a030940e07552840c1d556070f03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 856938282 1250 856937032 856937051
    0x913080d0c0e120102220b07060c0212030a0c09050316090b03030d0f1b05180d020f030f070e06060c0601030816050f07053618010f02030a0b03070305030d 68
    0x35280842c1110801031403010320075580c0d0710b214041d5012140200e40c1c20324102e0300902400c5000300310420f6a90f000b010f14100002c0d5a01c0c54010700e99120010154800d61002014058101005501c038504210001c20103407500040a069149541c000501c00e810860402c1030030b4082076441c100712420f408010990b400e175840420b08610405400d5840b072418080003030101d00d042d4001c10a01409172404516126000c801180c0c240070342018210070000d042580b403143e103030085901c10300c00d000902d0340e1401c20750000024501100b00074040419003010801b00081320b207850103940c0c08841558142c1c584000d20300c01ca41c86500c1400014411040402c0001c02d06032011031240781c56a1050454504c1840c070007041e41d4450444c810307503200d2015001383c0c0312003204c140a2820000c0d07814060100403081268918800d080041502e001c4251710900a15041c1c401d020f061000340c1c01c1d242c01039803410110901e10907907030720410150280e808044c1c10400940000102c80360b058002800080c00d164 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 856939532 1250 856938282 856938287
    0xc0816050d02270d030c030e010203132c010b0a08090f161a190507170d14090105040c052209030503090f07180f0f1107020913080d0c 59
    0xa884005000140b0204500c64400d42440d4001c44001200d54502d4480c1560410099150646807008000448400720000081c2c01616500c40961050040d81d0412255150400b4688100e51000206541c81d402036041c140000b24803440130b00011018043c20b60514110612038030800042004102c2c42c9400104000d5080c40f0541380301082c1c41c03d54009030111000ba80840c05140221000e11045911021451070040126524020303008400341100e1030f000c00c103880680201c0300617500c4400c186101240046076130018185d58a4000001030080301016403006405001031420060740e150505002c0030500c060941001c80d1400c4484410f81ca0081c2104031105803050303200c1e050641042c4090b010990040040e5200d00f489404803800544090211542e800301480750710165011403c45100c6a981d98001c0c0c412038000640106001044e500d00d901180e03124501040008404640ca00851604404281c2c101c7c2200301c00344c10168040e00c03240c85506c9642c0290000950794050280ea660 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 856940782 1250 856939532 856939537
    0x22020d02090c07200f1512072015310602030a0506030a200102010207080f0a02010b0603010e010e042d050115030302150c2206120c081605 61
    0x5034040e058000504001510300000d0300045401c03500d84030340c0075110340c5070002c00c0c40b951413080c070050007210350301800003c0c052000c0e0744500500c0b24030b504206185500240d000300a00814555640c200b10103c42d003000912a220007520000c0b940201c1040842c000300d0524164001c0c0c19006403402413106880d50000364039080c000508602c2e00f0b04404030074021664003443c407590301010207110700d6880034101074540580c0e800061071161402e03501180000700031104503e9505c180001403800d055a11041d005402c00320307420b1040328002500c4119254280900001d0710425a00642194140286180c507403205000c6e1840d18260320000a043c840b2247c0f080081454045002148552821030440d000c001c0384020f64143d800e01d144c8401c800b801c06004401c894159014040d4005213812841e000b02c4040d001801840040c0024007000c0300030041c0314120030011110400280c904140035000f0190003503881c102500d0141380c0ea1485400149180c0d0001140c0e1f20f000080411810650301d60 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 856942032 1250 856940782 856940809
    0x1b07020d08030411090606070f14250b0309061306020706050108011d07050d0f050703020306072303061f030f051504050a0605010512101e030b06092202 67
    0x511035480c24014425204000d40c000d82c02001e9000c2c0a0f0708480a200c00500141c0b09030340c001a04001000104581c3e00c0740480442c800c0481c01a0440c22040c4a49082c02d01c0e41c1155081c43c1c840d00341070490810300441e000406c1040030150861030120446521580010000781c40714448403000d2381004181d0f411115150717480b0700108105d50315414040c0c001c01181c1c3c4a02241c000c9100071040001c000180c1c01e0407a0001001100807007010b980300980351407401c804803a944030740f040100c0103070343c240840d500c150032550341e84040d0f1340e14003178001103850010f28800341454200240b0042d51a44071900148420074101030302f00569030742c0110010401a0081440f1034640030600c211081d00c420710784460402102c082c8100d859040309141290601d01c1003601041d010080118207480d82d200c841d6000c4001d84440061340e64503110300440c003040a502c091100010102801000072944015400100540341c81080f80342c89810880419001c030f002c4880b070000c810005046585040c10948070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 856943282 1250 856942032 856942039
    0x1d06040203062d190e0a120e06161218030f030c03050c0708060915060603041b030b01081005070806030c1201060807030501020a030b1503130c0503190c06020705091b0702 75
    0x150310f05000d10080321210451021904c900740700801c40000000900e6030034007078001078070310003041041c00c1c2070f41c0c40503072042e500740c0005040c480c20644c0030783d00303420381d04440c0078120fa25003640386000024000321702402d1a006841c13005109001048000704c40c580030950604010515060506041e07580c0d00803202ca0040798410040040744020707020600741c0c083c19801040320900c240740b01e0003c3d1395540848220b60080001c0c00090003180b40b036207040030040b10318020000e000b6100d84500145074401d1b00aa03040d0341c080d1850f004140d95a2240300c2e031000042c03070000324604000380080d490786d070012440b511800100030404140f54080d4818801400ca01040f949140c4d075928116003c0d41282e22198042450201c0f00741c01c3d800d29001c00489900e403007540d00c0c039640d50a0b0240340e181140078816101e50300442c4000c0303040e407000c0008010720100b0322001000c0740140c1ca000ca00d0100036420040864000d008108125140e4217113543d04041c06e0390700c192507241d40c10400300f401d0140c1c42000e0f50 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 856944532 1250 856943282 856943371
    0xe0907062f07031110021015030807030c11120a03080601020c03010e070306151512110a03090b0a0c0509211f060515040b0a0c14011d0604020306 64
    0x140d41d0020300081164031404a0450358010799041101024001c1c0005000da04580551407900246070700421003900305104500d9420345076140c0107916001080d0844c007284102000e00103001301560884c40c20041101d0313408003802503618182e00c402d4108002010702540e04081182607009100c05d200d6580013030b00030450708100d100c46a070b49031000d20080d96010301d00201c003c0142c010034001c9098074105c15295091030000c1d0000c41d0350300203041524110560701c85070105c0401d072007402480d0000b0f0541e80442c2c0030240c0d0030405070740d03800a03111007809881e00507111140c981180548810b158200e40405c80311b000076113640d104100c511280165070181c800b49850161480c2c58a48d004419040100000d85c0c4440a01203070720889a2129031303003441031004214810642c80200b00c1c1071401d1900b2844283d50340e07500d400e60941c1464108540e5152520790030306403c0c8444101c40084030710001d0400b41800e80103e600c0350405071569990010b040c1c0fa5982e910ba030203000c0300c2010340001d05c503034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 856945782 1250 856944532 856944617
    0xb0c0d0207270f06081204140f0102060f1905070804030e030114061507020a090c17010b0405040c02010212160f03140f0601091d010504060b0c06010b0d270b010e090706 74
    0x942c1b5910a000e85103204102c1c1d45d607140d071818201c05c085040a0183c009191680b60031300050106800200031114242c1e0401001d00e500809000d0a40a400c96407541500746c241850003900e01c000c40912076000740e2501e2540c0b41262035080c1c5442d00514140c1d01c1c22140704410362001d19501c02c0c0031012b500205400c10004203017103982d01118120846a035940140e03898029182d100d104284102681e50100744400c2c440741c40c0a9104e120300003400e0000501e8003c00401094503041c0c03c5540c15035565680c07600e20300300c64008010140410312407408001038051000703101c14884018060034170240c080780008900c1d03400b40c00c0039800340c1402004410709400100300320410307600901405005600304540020000d41c20015103101200480140032340340e080901c407100c01e410080c40c2001c02625940c12460210151481004485071007450030583d41090821030201c20b01a4807801ca8500c08104000242c90b000c104041500c005103406600d200c000084160300d4002604811200701403c414107 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 856947032 1250 856945782 856945813
    0x90a0308030a0b0a0308030109020f04150e03071e1e080a210305060f040e01110d060f050a03050706050c01060e0108062a070b09070b0c0d0207270f0608 67
    0x45215504860003400070103015001d000795908580302c0204802c20a10061048442700e4001e00043c0c1d00040000f4205541d80c0004442c502d501181c58000c01c0c003a044254413070400b8810000030b440c08505100d141303802e5540c05501c4280c10321464504590b5007003049000c0c100702640b00010300b6200212264130045017007508058003c81080c0d00a014141b80e01f4082a0003801413500c80c06004001c52130307442c810402e0001429214001080c00d560340c05060343c040307117004050140c0c040c1d1504000340322400d14074410043c0b0301a802851040481c17043c100009040020342500351006864003e071101c3c5e0560340075005d0510b0360045100041c1d40c400101b821140010f000c0d20644510018482428101c2c1684407075881e6a581050648810000c180100700d04818942d00810f448084072503881d611103840082d41c101c0d00340742c1d04540004a800c0002d5a0401c40d5202412000c0d2420050749030344a000b04d02ca001c01d03450002010389038480004507102d950700240c0142800c1040d10b000c4d1701b114080 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 856948282 1250 856947032 856947037
    0xd030c0c1a0a090f0b0403030302030405070506030115021e0604030c05120304060e060a050106091502031b07030308010b0c102408010608010f02030613090f1506031118011703090a0308 81
    0x40b84006611480d0000341030007102e6868084420301c6018034a4607003141c5046000e940020002d580901c80d014000a6039150315008500a19000364130050540070154004e050401c601965905031100501003201ca65000c240650005d0340750825004219041c81c00a0400016140e806040ea0001c8104400d204007900312240001081081d54000d565000341c01c41155030038014880000c003046020711415007811010b0646440c03500444e410900c6401400108441003c600c40e07003500800e100304105900250b4279070260164031045406c241c0001031460365402e050b1402c0700321907200c2a0306a0390a148402c01c000c6078592042201da22a15160501d01906d00d5100701c03001903113040348110040340c55200b6680038801c010030001c11414080030700b9015240804c0141d4141c2c42d211103203800106031400d44441700c0d0f898078001c2520703842c40c00e0602c00010b00205e801d0040c01d00d42070200440041704038440c191400110320030700003e4030390300e20340c50341c0580011f80d87c100119440110500020303001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 856949532 1250 856948282 856948297
    0x13060e06130c1e050c100b040605010203070b06040f0b2e030b010512040204020906030907060e010f441506041203120b18150f0d030c0c1a 61
    0x400e1848001d04000080842e140a5a5000042c0741c04180101008211403c4828550709180c20350801d00503904c0709080c40b9089030111071265442d61100c03440c2c00c09018150080c003090004c1c40c02c00e16a0707180c151805c81c004000d10b105554031048110003c2c1568003d1500385005012610341020b080e000314240003010780f82e54500700076001c0b0030782c010f80f1074004c172800c80d201a514035040003419201d940d603992000d4000c03039209800344a01c040a45075000170b544030380d18a10041072400e19002c030140019500c14409030400c07107184072100c00141c00140c200d8902d25402d1983c0441802c0c41400a200d040104142c800314180482e4030500071000c1e0409030045079100080301c40d40d0740d102e041200d203101d144620b101c030218503c1038070f000c01e010740c0c1c800440100d003074404201a2070f2000060842005801c02c4c4058802c050305014510302600250b02e034112058070440303264140040042d144046540d001010040450102420408802501001491003100b042803030301c00030740c0584081c0c10890 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 856950782 1250 856949532 856949539
    0x31e03040302061b04030b190e03070b0708040b060f0301291c0c06050a0201021e2106060306040f1506021507030203010308040b0f07140d1103120f0613060e06 70
    0x101113180300e0348040078520b210341e41604143ca041e2542c6ea41030942ca000501900c2450742c08515541c0001e168000c02002d0302008000c0c603030390321103440c181c0c00340c803c003a24510404c0300300802c101c00203001740100c507000007040712203c0a40c5400030010f40503150503180101001c510f108500b203130382c20080110400042c00c8410000c07480c24050315004507802480082c0c0f03004000315080000300e0003040100214440c2c0e100151502c003040030001c203940803000b01c03500034440008084502d040d240d2150321b00d01c503190629801a0500c1e1000600ca4000942103034482c9598003d01c42008100e80c0c054150b1000c50607120400f40d55032000a91031745006044d40810b1040c0d40006034070f4900c04c2c42201d041c0d95229000a050608141640103039400941050422100070002800481e050017441100701454400510885007100030040c80407200c1c1c00304280c146d0091046081c01c035131614800354018070500c0403500c0380c1c0e039036000203030400524100700051920342000481c031000c1c0b1a849900c10b24098 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 856952032 1250 856950782 856950793
    0xd0311010609050f0604020a0c052e020319020c03070c030b0402010e03060408070f021c0b070f18090f0209090c03010608070e180910020a050301051503010e0403050c031e03040302 79
    0x2c94502080d54803ca8806020140301400150f00d46410b50152507000034a14003403014484658410389800d41c40c2d60780f10040c0b14041110019040e20f03250200c0d07aa402000300f50f08606000900e14007455a014800d0000d98012418a600b070004005031100103030407052007004540d0303e007880344940405a8043e0300042510300825030a080010724103002d01d40c449007040c80c010158842400c11008101c0032a0b00c01166082e40c0000003402d912888481d0064212141034180b45602415030b070030340341d1984280b10360001040c0e59004281c284c1000c8400200d000b1038000f84c01681d00340207108014640307034402c0801e0140b00b040011074000e1170580c1c0d0035468580d21911064415580d42140d01040d036800000703c403007061114410109150860380010842e00e107480003111481c2607030046051080080d5002c001005145800001b5148807031207440d40c03d01c1e650401002c500e4a43c4000d03c081c0031302c58001034080d07070010100119909601010301c1800e5804140000308001d92044d6816401441036 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 856953282 1250 856952032 856952039
    0xb28060201050c07110a1a030a05010611100b0a03060e03031b030f24030d0e0a0e15100509030703060902040e0705130b030f070b0a090e01230f0d03110106 68
    0x5224243c00365075000720082c2804003565610782c41002909801d60028050340c80001c04503031000c0000050101401002c7d01c1e480e05201140031500168081c1041010000304554100008101802c000d26100408038825403094081941540300f903100a060514003070141c1144c0351b01002035405201380c000c003a0210011284c0d050b940f400159081e0000400c50004620441c1c4a1854a1012072503141109440b91118000a09203000750540780003203224044020350924005800c08040d04010585040c1030030003028803100c80808840450040b0034000709110002c6c01031081d54030418004044500f0b451f113030b1400ca0003500c401c42c401c0340940c0c100304001c1510000451401c0580d2400f42c8455a001001022003011340492110280c16016441084041c0941801900044c200d020b1041e40d0340d454040e0000d0100d144c5e9404810261021001800b50003030044d0104160305810090301c1245400c04001541ba0040c0203146500002449441041503040700114441c1100d010080140656 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 856954532 1250 856953282 856953287
    0x711120a05071203050a0509030c130b0301060504020712030504140a0515070e010c080306061c0b090702151902040b1b0f0708030405130216060207020415031e05010b2806 75
    0x280f50040100e081449a0304000340300c0c030003824441d68010112010f0f030725800040b84200c0c416040d07800f2644d44034031641d01a418240202001000240d03003c51802c00c142d03d4000041d8100f100e0750003050380782e0011905200303281229035100c131141000c3d9040c841c52407400560b954010455444c0d05100100000c03a02c50050344000750004040c0c41d0311650400d40c0e50b40c80c80641c4001c0810394440c00038404101482484001404900401c4900090300c2054004010a51078002c10300300440d84003081e100d282c0c035607155800d6000401940d0031450041e102c3c001704040c1c0165004002c801e8000305592410780031943e501c10710011148140c0c0e90851071140e2041d21140c5900a09606500070042001241060684888060700410006050503441004280080a68002a00e00c250045204001d501d40b9108201c0164204881540da075072075030b83e880405410a1290140d200e003403002020900100b034201c0e0106010050115920300030360408502c1d5030394030701e88030002d03405044c1011407813030b0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 856955782 1250 856954532 856954559
    0x10e010608010b190909020f0903190c090902010509130b01090f0f0b0d020702030307030801090f02070201080423011d0f01050c1b07092306180a020711120a0507 71
    0x40e40040040d161180080f2002400f0089901e880300700801400700043c0c424087c80606480007044001c50f94503540c0c04101031a014006018150301810241c2c801c5c0010b024606800c100d800102d0080364102d07031400180c03090f0003000700a0350400d14540c408910135026510242842c6401d0700c5401000741c8401e05180101090b025010790080025030030b0004020704405401005140304015240060350707408a401d6070041c0c44102c0119184800500c05d844090040c07060000ca980c00443c20f0400980000b454282c0160000d003900302d070542e0503400084056000b1518829520007030048015002c0c41082c1d00d5900c0885d071003540580d20b01c00c07200c0d003c107000700d6000c0d003500107000c1e043c01102d4000000394001941c0d50b243c14030034004000798603003150150010b0080074148000072540c81c41e084450040000308103a1182500501581c0c0300c00c65066940c0c1c00001000e80181c8480680c035110a0742d80410a4a5520028a000e4070301d840c0800291801198412019500015902c440849421 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 856957032 1250 856955782 856955789
    0xa09020303090d050304090606020f100c080105060a0c0b0106050306120a380906061c0302060118060305060112060c09030b04030c03030b040218240d09141203010e01060801 76
    0x181c20030001c1802e00e141080f0201d540b60b02800c1035a00d07080d95514008101c07000b80d417103800580c0101c2070903404403406100111504103400000e01c852003111130003c0c0300345814090380c0d10894000c45c01400c01c41c49101e0701c0c00c6199110080b500f155071146000703482c60f0011111144500444518480800804601c4500e517550148100700b1010102d94517441c1207040703c1014115988109503400ca041050f10164010820301000d00040c0c00c0100a21050095040c1e048011307106180f4840000b9900240e0541101c200c088002007103082c601500c4c0141c202944060081e100c3c0310008100440110f205682040c4036031800c0010500824080d035070321013244806014410710300e0006011034001c26150215500c41d00c1c0004090410a0004040f60480030200305880044081406c0381d091001c440c0c409040400421010403048803030101c2a441540d841030106500c6521003000c1000003448000035203e0ba0080e5082c0000380140e20980d43c10900ca68458010580b00000d00c0c41e0240722200e06a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 856958282 1250 856957032 856957039
    0xa110a11031b0f0906041803031509020301030b060118120501270b070c080d0e0c131a1212031f1a0d0513080412150509070e040503040e100801050a0902 67
    0x4504220104507070340400400040c0c2141d2a2000c0d03481c06130040c0e094802d40b51180e1000641c81c43c5040c550340008a052f0130804000d8410001480490025aa000c2d8801805d1805080c50300094030070942000c0c4a0b0700a007101c01d400303210801005419080300009909003006181403404021008180728407011018002050a034040303100a44603c03458510a802501400e00d80290702c4042d80c129520702c5018100c42c0c205481c400746c00d16004c1950058040c082c0d00071b01c1340303005850b1500d00e1403003040c001038451403a886030108604002c0c00344803c14048118a25102c0c9032448500c0e070500c007a035140b8183c0c0d038501c0402058040404c0312942036030031410151070801340c2140c1d80c080148800f4042c83d0480301d5220307031300e40000c0c00c410085c400741c2005420030300c808a0320b16200350007014245102a400d81402c08010600300c0000f000c0048540b6000c0ca028162076a040017402d51089421001c800700f030100820201c15620401d51b001c80e404e00b00204900e5442c1040c2004a425540000b5071 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 856959532 1250 856958282 856958299
    0x310b03010209010c020607210f021504120f020109050d0503041208040b04060b1c080c07050307080d0c080c06070c02011403150f0402090306041b0f1a0a110a11031b 72
    0x5814001c01402e4006e10484002c842e048c4d50000480500c41c4001d030700d50016500e1200d041e0710b135605010040010a1001401d4202d003420b680d0200020000b0074003008001040c0001c80c0b4981c0700b50840c0305100c1c0c00000f1381d1064a40b050b8000c140368001c85058903000112100986001c0c40f56425070311030768011801c0010703078549541c0c00e0082d004504c0e01552291080510040d6010034061624a02307104800b1580e42d85a00020b550401d0802d502c01d80c460b41080c1d108221088002c100703c5125480c1c0e1502e44603440091414985600629422100c10300c00c54081180720350300100f004440c00c2c001d032100c201341c6503183c030040d00741c1c88202c0da84001e0307200c21a0100700300d00b04000d404107031400052015041c5803003000480d1605200311003d0300c03c0c0214400c0e101c1000000880314018048407860050528145501d8800305424008401101d090004101f0030191050001c1107425104030291102c0d00243d042c5503d074a00414486031007400b808250180361007440c0111040f03004050110319 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 856960782 1250 856959532 856959557
    0x10809060615040e0a0b040612051c090f0611011a010e0d0c080102070327031a06150409020703020c030627071d07032007020d02310b0301020901 64
    0x1084500c0d0b2a42c0c035000d05201c04207604075104440c1d849507066100c006802c00581c01000190307209039121070400c0b52904d00c020b01044c1e0114650140d16041501c03103c03078101c041002c4a01000981c01880c01400d0344d0320106150740d020821081c0c40312101d0003800313504141d20900c41e22402000c1042c0c0440c152600c8503120f07042c04d41c00d07000014081c9010361035260b52186c00d40e0130b981c00700200700c3c000780e41c0c100d5000545400242c0701d459840b8400070034450b18250b50320762092500c089410994545800000758540d65054100c0d4249410940360f161100e55681c0f540002c0e411018085004d030150154180582c02c000826600c2480c644030036aa00766022424807420150603980301800d4000d4000c00f050b8441c003400d0854030749040e1240301e40645043d14000301210f1126207661481051945080c0c0203546440550b040c4580441e600b581803104d62000400c0e089a6400146403082c420050707600c5090128842122003003181000e015200d03080081600300c0c0700b0a940280031070344400b000c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 856962032 1250 856960782 856960789
    0x6170405010e060c13080703030e0904080d0609090209060306160311090409052b05040b16050d02010f11040e0a020309100204241b08030901021201030b0403020c0108090606 76
    0x4580050003000000742c540c02071110325003440e000700c0d6034010100300080c0c0140c8882400044000a00d94070000e800e6490a5030b0340240803c1c84500c44c4d900c5242003a010809001a8008a60000d2903070a0700704407255032810041d02501e1544002c4e889001654000303100c50801040d150312500d001c192130040d80c0043c2d90150028150348092020f0031400344015181c0707031200d22440c0724a90080300103080c5501c8000b064552a0485d00024810051061145600e20380103411b64081da03042c410701ca91a552199000301200c2c508003000340c203522850890200e5560194407885503411310080c2400f91a465511002d00c81c81684520781003040c426000440c0181d540d40610381100340349080d60085440a80c041c0c051782c220750807441c0c4085000801c20554400ca281b00c00700070b5800d0401d1078400c44900d4800c0c0e20a04203034000b030701d8044000002000340e00d00b90304031000d060740000000c1041d42c480c201103000080c2128100c0241c42f45400130074556018081d014805e4441d0b6004180c10754548061 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 856963282 1250 856962032 856962077
    0x708070e010b03090a0b07030b0306150a060f0903060902010c1514060303040803090f150c0714010c20060d240b0c071a090a08010c030501050118050913060507051b01020406 76
    0x10b2008c04d0344c4c900e80d0103036035036050149901401c9100500c5400000c41c00c1007100411955001009102c4440003514042e0b40007880300080b2034200c1c9000984500c24001138464090401c00140b00c2408130038405c20b039081a5100300c1c08080710004040d0103903660818180d99106a01542c0242c0e441841250014544141070038400c0708060070303904e28844500c03188401174000c0c1c0310076220340c0c014502c00c3c03092100c9400b40070b1550500746000b0345102d42c0e40d02ca040c030101c03104883c01801029035a040d09540c90b00310841d8281039180381c04101d240c00d40e801406646c00300034038071429001760740f00c0014140642d1040d10b0741c406025028000261401d00481020707840c4800c14041004240144d00c0e059407041035000040007081d001088410fa400c000504449058100314181f2a4450014a0148242b800c0c4000d540055a900002c0e03142e242040d2801400f000004240c45e081c0030405c5026980302014100a9103461090038440c011010050300742d000300d000b6080058a91005026a185410303003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 856964532 1250 856963282 856963291
    0x3030427060806040308041109010315021e03091005010509040b0f19020f0c01200f090409060905010b0a0609050603060f062107091a120405030c0708070e010b03090a0b 74
    0x5001603481c1c0d45120180c10003c007180c007a00422482c83c200424040c2d2481c8251803490200e50006440d0304695504400000b1a5032421000781c0c003051080340400c00c1b0614424507603100700301d01e031245083c0400542e00d000303c051200101c0d0400000107940e0a211000c0c038082c650040c0c0c0c2d01c080795101103100404080080c889050003201070a81e1151041030303c0105040d62240b03160941e10703d800d0280c41d095992510b0f4100361801d58001d8110542d84840544160b80c502c002c02a07958503076079001502508003805d0203850280b5040d03c80c070030400150301803451900141d900d800000d9941d00c0035155018640304458208d2010000034103185002c2c41135101d17100340200b41c0e6040c000c8c0300e54524514925400c040c00c120503503c5c10f0004841d0041d4404000304000d540880015512403100080d40c0100d500d1314141e481800045000c116091050f5040b10085004444041d07a4803555203540300341501c20500801c51031400450300d002c981c01141c0c0300e800a04c0003041110100d40c0c4000e5035100062 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 856965782 1250 856964532 856964609
    0x1203091b081b130e0a08040306020d050c16140f070e01060801060207080a080d02071a0a18110409080f0a08010626060910090608030702090a1b0c15020c0105090c030304 74
    0x3200700001501106c06400694041c4100586640c103003405901124009440103c2115090201c226840e0600c842000700f20740c044511403010390b0101009141031801581506140a144408100706003c4101c6904031003503031b51050f440f0f036a500c20036615220309006106141e00142211404103034100e0042c24200303040c01e401451300d925910342d42e405860381c1c2d009506442d0002c080c042007220901501030500030202d10341030080a035603108811050754508203030242e80c035040d00005001200b42522022000d05c0f03c1b650b070392034240c107004244030000d008a901042e00a4509284944480428a0210032050304040f0076140c0c00100040542d0007000c5008031010040041003600807400f8003801090000010b50b1103074003601c100b01c80030300300910003c203080c54400703c5850980548001c5401c8445420000c60101d41d9050003e41d100c450580105401e00000e020810281c05600947c0300315090026030f10b181a82c6070406132648164451100d84c1360b044001c6041c4000c4e58a00102c80c11141c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 856967032 1250 856965782 856965793
    0xe0307060c05100903050c060a02040b16050102090303071b080303160e1201060902131d0708040302010207061803111203060f0609030d171605071203091b081b130e 72
    0x500b4080c050701d244d03510840c0024404542020803000410560390405000c41007581824204400301100d80211210562003007d00300303031076090060070740c11141c83c1d01029050320390ba00210708102d000c2d0841d402c07543d1001c00412500141200010040c0d82c0540c0042c0201809401440c80407038250450b001c0c03440d07010030b840e000382c03440304401d11440000380302060740076840b4481c80700c00e094003d119900001c108004550a41100708a0405156010509045c0025140c4590608034024041c1040042075607150803402c00182e44101d04009801d8403a035a0640c4003d03810300b0003a100d0200c44081c4030714501c02e0011450510f0220035000440c10090940c0b400c08000c82e00291038080402d0304100444c04003201844c1d000440c01015521001e074658941007400d0040f401006803252100c0940711501d05414071402c944240c1140f40a02d0b0840444000c00014070b200001c00407681c811600141b10741c080c0e4081c6000940104000c4010044c40c4007446840800010007900040b9030b45842c50245 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 856968282 1250 856967032 856967053
    0x120a05061c140706020c031e2814011e0b01140304060510120803070f09090203040b06120c0108160207080d02060a0b010e130f0e03041202100e0307060c05 68
    0x145061032a45400781c0e20403900340109661141c28259207401c600115002600d1406d52601e00080400d00d5200d202d41e944440070f21f49440d40d05054958041d241980b0551002416032451040c1150f4968010420381d640740490012003800c0f2040c803e6030380030300d08002140b41018081c59001e00030420b410b05100040640760041c0394480d602c111000c03264103503580d0601544181c100303011805801400c030030a801d80031588a0509038080105824100813107401c115200620800c4080700401d0340c45070035903c4c0d050074507246462107811649240640c41c450811612030000188075661007030f041c2c49000031031715001485158410801024400c0d4030541c1d40000e40c48404000070618030034258040e00340c5003815414001600d00c0b1002c1c440c1000000b803074100d44d40c1d5030402c03641410708010000142110f44c42007040003800504000001030b0001040c00603060140c140d020300050710880e040f290138100450f00f03031582401c40d0b01c0c568046d801440140b00c4180540c9980c8181c9015100b2101904c6a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 856969532 1250 856968282 856968319
    0x60f010c0f1e06060317070203071505090a0608061513290c070e101a0705151005042301030210050904111903110d0209011701141302120a0506 63
    0x1c1500c0b045030815a5040204280180010f02030006044d0b496191b14011a6800003541c8403003601a07440c01c10382d00d030890307d2603074051000c8909600e0007a1445040039551400070f0308828040350506c1c05400640d40550080700d6600c11a01207904044c103960016007005686244103118840c245543c0c1003e140c0158103108075006803018140110040815600b0540203103c0c00c607025040b11503021040c042480544900034810000f2040300350426125161424514030700071481c90084685400305c8240121180140c241d00c0942e070042e101403015400b114400b20325048403aa64510003603c2c10018001840e021096540b41c881c1440c00a0805050100140072140c1c0317024843d6040c48001041c034240d0800d2041c2c00c0110315070341801c0214041c0404492420303c036104540e03100301d60004107140a41c1c041d8440c2c18410320462030042840da1142c02940b2030b64034400b84e0380e1080c405801c01c13030300c50703c3c050003100c4403220413607011607040d01c80c41c1a2402030304018240725400014441140303c0c614 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 856970782 1250 856969532 856969583
    0xb03040501150602010e37030905040606090e060f0a0b0409020304030806011805060c150108030705120a0522050d1109090a053706020909060f010c0f 66
    0x34051000080d25640c108101c01c1154815404041903904000280b5031003140411440200914200300c2d160703408226003494031494a000d0454184c6220407810b00a060b03008803107405445050b241000300c0c0e500d400098400044520905404110b404005151820140a26090100060704071100c082d25030000d11065009504902d140382c0d0701000300828564040e5416410040c00c0c20464860800c10554422081550142c54018400014041c2d2031482c10008a459000f4500440c2c4103541c54403040f54a0368403e0400b83c44a10403e41070210690040048a000c0030660300c0740d52905003041d282c41400c0e1401d041e0030040c00c03552540011a5100c03980901100c502c183e50003002c119403801044250074000c1d100021a41c090072440c0001100040d0300b0f001e0146074a2205a882549440401100b0072410300100355540c480a24040040c15005440030000c101c50f0389043d5030350f80c010701c5400d2150044650008130075201030004503c40c5c2c030038030404c00d001c0c866034000d00300005600c90024 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 856972032 1250 856970782 856970791
    0x140d0203042d0f03060515010912020f03102d02042301031b022a0d0b101703120a020307140705100c05090a09060e07110705100c03120e030d0b0402040b03 68
    0x4540310000c010721f88401010480c00d111003420a9445181070003200030881c2c070354078002800388004061216181d40e0800000d607443c1070780740f020b01402c400e068040a80c0340320302da290040200c0e10114200d41d09400e000b40d4003902c07030f140401000100c04040c0c0301c0d00d995034001c0c424103059441c84014010300c2d015400c040d81d4100d07500100760030351502c41603080e200f031108401d0840c100c41c028200e100c0d0f51500d1520b00e0403030f00024401c5030380e203c200140703011042e03582c401413409100c0b0ba01320320000c1c03000c03020341241002e0000e08443c65940d40303600347c00d0f031004070750480004017a1114109482c55810203000940c4c0508121040320120160080c00c40740904171030700105070040382c005050310300102102e000e04420201404954a01008000000b0f0040c00322000d01820802c0340620075004c0003d940240001804070403c001860800342012001c880240c00007074205c074541d0b48640c09400b850802801c5180254900251594a140201803075030802d0b90040c1c00300400035000000780c010f075004 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 856973282 1250 856972032 856972043
    0x618151603031a0f09070c0201140406080103031d030d302007080f071703150f0f0f090c0904052d0129040909140d0203042d0f03 57
    0x203090400c1c541d40b900015000941c2c400c020511000c0099105d140e04940c0043d02410500b010070701610050f078100d0721031007905010300c601003800a40540e002044a0403207002c2e46818903030b00c45004500c1340c186030340c251031a05a4042081347c181a0720511400140100031030000f4000101210004060003652001c02996034442c10901600e06119041d801c1c40c02855802501e07012440d6241e513154054400e0302030000384007250340c40500c42071100081103844a050410f079645049050300d0884400780309500c0c061081814021060f0a090b00d00da4907030140106a02385960101e000c020b04010002c0040e040d4038428032000801d0384442c000c1c01d00514000c500003404540d0100500b00001019040e502c0544802e00100311804144440302410030040881700c400280c00002c0c10350522a940c05115014540f8010006101015828000d07406100c02510300d0700810380c500f2a581e008034002c03105291801180d000c4091220080451a031100e82141600307681c2d00d0503c0c40150440307030b109651 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 856974532 1250 856973282 856973291
    0x403030f020c15100e06040f020906131a0406051204320f01050f07050a230304021201050912090d0203031b0706091202040b041e06060e061815160303 66
    0x200d04440c0071684042c5500400008038507003c5c01d94141400603140d607005568034200c2d05007070001a0100c500101000d80030607501c2082c1a05901186207610030440c210004c104200e241d880c410080b02d0032900300303590341820000750325043d244944020348102c0d070600f040e950640d504152100c0751007a8000540045841c1c0b69030361403090504080348000320351079140000b080309a5005808035908401c0500e00306440e1011210292891983c0c03103403803980c0e10064070a0f4a1038507070705c0e0000d6220310b2094980c00c16015102d08010b0076914151068055600001500c004054a10740034020814004165846030345040e00071900310380c41007a0f22000040c100c03429521030741c1c007004043c00809c42880c1902050b8a001c000042000e90442d000b84140c0d11503040402c04e41d1103400a106540030100000c504040d00214600140f9592080d03001080600b87c14812901d0b05809584902103500c8031091032280391410002e0130b810070310316000740042c140007012034195001c00700c21b1120b01c00d032030015 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 856975782 1250 856974532 856974553
    0x1c06180b0a150c3c0311070e0103020316081e030904020403080a080115080105010503190c030c11070302090c030417070308040b010e06010903080a0912060f050c030907030b0403030f020c 82
    0x3040c42c090450444206201581d285181100c0350382840004509003031130314100301030307203812160052004240d0b4018804c100012401001241400f41260310881c101c80583c007014803201d8034024940b14980d0180c2019086c001c007121081c241d80250246c2d101500d2818070780c2d900190483c0c0040d0401c0c0c80d218404030301d02542c540c00128580c090018061140140c0019100c002c0401005024490400c20f02102042040c051344004210504003104140034280c10294024010417281c000d003400503001c410340a40128001c80d03a14166900034000460079501c41801004a0f0710241044502a203480440b282616840e40a8919075110303948000c40c60406061007000050182c0100c000050903106001031a0f0304031190303d04482e40446159154140c4140c1034902e0700c4a070b445940410b00a602c12000c010175540004410185100c0820440d140d039020500c1d6400121030000b0789600c00317038003880894000b888030741d44248280b80c0424010825801d00050343c00072003e20b01c0310b502419950 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 856977032 1250 856975782 856975793
    0x60503030c010b0f150d180b070f031b020714060c030a0c050106090c211104030309081509030a0e060d020d050f09030a020a020f030f0f031c06180b0a150c 68
    0x1c844220111001800842d900780760400502c0f03040741d100c2c00c80b40e60300c0c1c0b6001c800301068007c0d11844d8200ca0b0220551610403c040e156020300200e4000080c6000b0f00019180c0a0030042c05003411950b00416030142400000c4403001c010704502684014107000c9884221800c10042984c0c01271a80d81410203442442d100d401d6800540041250b5400c0803140e802c02940112114050385180300160034114030440300100a04100340219149040040c000c410300da0007070301420840b20420103c0d000311000990302105c01006642d1220260020005900c46c20f00c54100c0c80192031000384828981400381400d41c1c203da21070543c6803034958035001049046800c4441d0194040b40c80d0000e0f41c0307028002030000751183c00d00c0d5002407107903002e0341c41129192404c12100d6101001a000c40303001074805003c65551b508560505410b403140d119004a400b00c06001d13490885030300e82001d200003110741ca94840548850006260049a07424001501c0c10002e9034441007040f05858100c120300c4d0a0820 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 856978282 1250 856977032 856977049
    0x31b1502010204050114071b080109030e091e041403041401020f01150512011d070e0702150a181b051c0209070c05120c07061716080703060503030c010b 67
    0x894080d64414070040009076005a02c00f460035041c071405940d00c0489260401245008800c466080031003000007144044056208140042c0030b902c1c2c98420306118410030205450455801c40ca591805841c00080c960035280340d40c0051003021284c0d41c051900c0080392070350700b00c0c1d0320460750303200c0c0f8442c0002c4550701406401c0d0f105659030000d1111b0b1010200c41107040030b00303104040c0209505002a210007500b0b40c0500c14901c000c6d08545500c1240096041d5109140d029500d84d00381100c010955041c00040c07911046904903580b06003c0c0d030b80814100c02040c1001c0b0708507417000c0200305d800014060f451000c0080e01800b55142190342400e05100440c1d40d2001c041c69a0004001d0103030140c0e60304d06d08142d05c00e81a01d0001e0051509240c5070341003001e5a010214031400100d40480c01c08000302c0c1d82410354150340d580454100f41e18424801c0b1000a49680d02004c0720342d802038900e07902c0383c01c0d480e50018440c02c4c082546030380c900c0440d10319880f2a940c100c00e0303591441c841e0180e00e0206803 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 856979532 1250 856978282 856978319
    0x70303060b03070e1522140102030a0e0118031a15031216051608010506090c120403030c18030b090c10053001060507050607080727031b 60
    0x2041d0840c034000d4030151002082d150503500c40da00d02e0105410201c05c0c201101d99050342c46040c1501c0d12413800e0030400f100c0c214000d00341e04520300c080c3c00703016510000907507440070226900d600008410500640b54243d18203d48203160001813004000705d550031019001c0407a07003120002e82e600e84104000752080c00002e00c0c61183e0008185044400105010340d03070416150a5030641d180c00525120b0300d00720642c40014142001094001511034042d4040d900c40c0f2000d540d506207642e91004110f10354070403030a80d0159500c1c4000841c0100748a540690380341c0803c0c6c1015103030040d01c002c2040d00703a1074a40c8102d13108072080081220750301e81802440340d480d005a48003d4061108407001c0c082c0d0003180c000c045003904526999090320982d80880c1801c1540ca25289400e50711004018020b5002c800c003a02c251040781c3c00310780d0491065401610400c182c3d130318241c1991001c2e400c40c03084010405101c1e2032074455a004004100c120400e411f103250075803084c3d103503030385001c0b03010510039842c82 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 856980782 1250 856979532 856979549
    0x3030415200f0c011206051c0506150a030b0603120d200405030715020703020d0c0806150a05040207030c06021801090801050106050d0c1106070203031f120201050a170c07030306 78
    0x2c0c5448040440018240100502400c004c0c15100c81e800c0c003c801040d02e0703800180d2003854015030003440034601900f54611405070040e80c140b82d9900c003050701103081e1000d20300e030001d031880c0c010004500f961484a410140003801c0d901c010440401c40000c503003050404500b076980d50010705401000b00380d8005c24824008400a09080c50880000d495418034071468441b52010703054441c2c070320300c01e08c0810302440c1e005121070b6040e002070500c1039890407079003d1b0f8089407080c0e20101e441d01c1d0402061410700440100ad002074a4241030034040603410a5604405000f40c0c40c203060006445400039140c0c17007081c0d40e800c910300403d02d400100700e11a03591200c00c143c0d00d08001400b60f00e520900701c40304510588004100c521404200321000c3c81030000d50001805050b061204055021000358000e808090514030340d000350078082d1006041603c25001c5200c0c1e03100354140194000d00103407081600320f00f0814800c00c20480780c800b00510407516050904000204442003540500c030700302c00b40c800c00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 856982032 1250 856980782 856980793
    0x60602030a200727060b12180a03170705071106180411070210050307020712081207080105041a060405191d0601120207020d020118080f061e06010503040f020303041520 74
    0x1003c106c0d41c0340b00e48010500706214036800180c40b00040881d80811b001d009084604000450800400d1041030600c02c000200f21400450a428404c00555803501d401080800602030740000300401c0d41c3c03003150754045011584445200550380c1d480703032210700c07421000c0590341c0d00c40d1031040003d034028043e50340003804000c1c024801881c0d40004c01109803504002c030220219018200f04845001e000516404014201c040248003a80310100324100e0305c0c03d48051000340032207140c280c80d14041d03a0406412602c140010485840c1c00111100e07041c0c2d00311038140e01152100304280e8614504e03504800c3c0d824400c1e00f40f03c41540e0006243d0170040519038114281a410743c000342500d84002c90280c100441c03110020302c2c40043c684000b0040a0070740860301681079a03011591203a600700c48000b147d00201c00c0003501d2001c0780205520400c016558686160b58950b600700c0322010145041c0d0f02341c030040c00080742c1c9107030b0690380701205c18194881d00f00000c000901543d10f484640d0101d85a40c000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 856983282 1250 856982032 856982039
    0x40503060723090411030a0902010e03030f220801020f0c101b030b0310062c041115070c030804180902010f050d090f0b010513060602030a20072706 65
    0x402103060102c1c800011126903514401000502601e0700d00072004800b00000180f0001103913651100b00902d1003a03c865130742118802c10142c0b20300980c18014080c031010030040d031040800c101d01c0e03013400040c58a4401c402c0d0301c811140f0b089800540c5426030b0350300001100348a030b540c100000c0250119140040c0404440140b5100e20075851511185c00e26032289960400f82d0303000e100103035000725201c00030001140c0e940018607150b820400180003000f034800c00d0320391042c0501302903031003181c0100c944180c0c04104018417641d40b16075800200460414400107000601895404000394010500340780c0751828103044c0c1c6650680305210b514a03d16080441c001030740c002500f00c903a040a401c0098030340c10040145005070001c81c00040510f200510448200230020249034182e0310180c0b030303602d10485d00404420444100b80031700c00141c0e00c00c2c030003000072a100740f0114040d05c0d044210100e0a003003811a035072408400f904402c0006528030f403103540380c40b43d612581c1001e41d81d050342841058034 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 856984532 1250 856983282 856983317
    0x108010b030a1403070b1018020c030301030b0c040b0316261906080f0a111c080a1e2114010e090708120702040f091a2a0405030607 58
    0x42d070480050410082d03076811481c0b0641401a00c04841e04903162805900d07000d000c038600d0100c02d010314590903605081c0f100000310188280c88140c02028001c500d140d00f15151408854030007850b03404040c204010100b82000c0c15070240d40200080c01c40514a1140d04034003410080b1190b002000d05050210f2030940419484111038100100c442c3c5441c5042004c1031040140c401030308107101a00c203901c2400101000018840c00d064000c0640308504122041000350060410401078442c8051000010119468000404284241d400c01600c000c208000030110400c6041225010440001c0c00750304842c100340c1c40060100003003004000103203428032056200107040c000d074079408010000040c5048400c000c0000980116400c440c91a00c200b030513000180c1c8140012030165041540141d10f04001d802007282d16907002042340e000c3c588950310180001d6006000101c420810610880b840b0004681c00c0360325400010f14903a1103051005240c600400545220200074403c0c8100e0a00d28 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 856985782 1250 856984532 856984543
    0x50915030a1b050d031110050907150210061428171908131e0e0709090e03040602011506140a0203040504020a110f0f1e0106080a05070e0108010b03 65
    0x240e100701040703940d80042c1c0040c1a49405a00481e41040000030700c2810302d608400e20105c0c0360444011100c00a580c00e60040583d01305680c0440b0503071054200340302901d894000403850405510460700b5035000c0824074410f64802c6c0d03100e0a44110880c0c1401d040f0b0034a50011500080020f00274280d5015000f0070043c0c0300418400d402c08502408070f00c01c0210028002d4017244041c6d01c2c1d1416801340103051040407540605803002070a0030f0b0071400101203001000750b401c1684070b00010b090007884c0c006041944d8000400c1d80c3c0400540c1c03c80452407004510907908031107e01c80046032280c0c20428007074215138041c140c407084800d91000803c5260340c0408800201400e00e20120b0711005100401d134a9402590020f1390301034004107a0703d11042e0300189200c022483d080c12901c954118510030360303c8040c3c981d000b0b6800e8021a440401403c10030929029204001c00009101540c0d00181420130403000740454040c5c0020504010161a42c40c1c210b0251038414020000900c0140010b075440 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 856987032 1250 856985782 856985803
    0x20c061e0903070305030c0618120d020c060c03060f0d1e0305190f12150501051b06010e04050f1606030f02090d12030e0c130b0301020705100605091503 67
    0xc0039410216003554400105407114070001900325058582c403440e03c561a600680c2c031103070f0103108000010320915040c00034409800a0345d0080e1400b1003060140180f503038040000030740b40ca6000c0140000119040090714402c5020900c0aa01c0c4c2c20b1120400c40308034804120244070f4180301c101c840114800c55414800c1c0284403200d049100c1d6140b0b01a20b090044200d610307201c078602d80090111a420026200d0031208590b20042e1030104180c3c1001103850a034031102c01202e10b40c9003070001e1750107000141204208490300c01c280e5507207443d80c1880d1a00982002c0c0880c1031801c1403004206c8104016200c140100011300700030604480690120b01092007031308101074803249113500800c0558110b40703c4407809400c1181c00401810542160442d01000d017000074034000a2252251022806000202000307220541d5101c181c01c0b1807018001601255a05550812030100001c07410008003900c54400c1102003261441c00007040422800184444110550210f00d400d0581d400b08500070f0f41c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 856988282 1250 856987032 856987057
    0xb0901200d05070c02060c011b0c080d0c030b0a080a0c08190b102105300912010c120c030605150705010b0307091e020702030c100c0b042001020c06 65
    0xb20303520800e048503d4a0040030107508140002000000c1c41010f400003d90041078600c0118203030030001040703801c8501410050072080041c0000703200c40c00942c000e803800002c945004109007506200040e12451340781e200044c143d005241040400c540140510020542c607806410b20300c03d00c10384a0381d103003941c480050410050600240e1040590a06403000d0300f640203400040012814a0f04200720003080240c4452055141480e040c1c0c6078008070600c2086441010412140c074030341045559040f0042c0d050b03025002007403159a90318244112401c0c8003443d6a416903031540c1e04059030407200e8002c07804042606044041c401625023080310702c80f200d59052500d076030780300d1703810107d0040010140e80c03a814081c50100244244441e0000f1480e0014442c075002c0005125011500328420244003d400da04040e0000d031a0380740c120345200322400c4508041e101000251358035904803408640445402d1415a0440504020b111005650725020f00041558005600000300039014141d03e1040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 856989532 1250 856988282 856988291
    0x503031c020f0a031a2b030201061e03020a060302030f06280603020c0d03060e0408031f0308120a14060f0103020705010f02030a0b0306250c050a0b0901200d 69
    0x1180105541240c0d0b4401481603001c0d12101c550000402401642c0044203001101d1015141145820100c581e0056074581004503626480d0207880822a0385407000da0940d50781e100c0c001582c5003000840d43d0a81440e0032240c1c0b6443c00c0d441040084c24040e0030140405205200700800070902204075508100c0071940d00d0b5a500580a06020a04022010500c04d40f071280c4009001e5400d6000707404d420800390b0681d01e03028489002281200c055201e00944001401c0c040741c04285040001c0d070b0000c0781c52201c107100448100001c107004446034801c59800200240416803141a20030490300007401d0041400b00c4801803441e2144010054051403141d500b465a41c40b542e8042d038100c40c13450354000000c1c030000c1c440c034209000a400440740700c0a4581451401a01450086405407281483c0944078a001210401e482800700000b080c03007040c850071481c0341c40410030411031841030313511807559a40781e45400c449690079618008000d07a03004107140c12201250301070609030746118030080b60001c1c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 856990782 1250 856989532 856989577
    0xe0f0a30021036020a050f060702040234050105010b04061d13111308030a0503160912080a030e06070e1c0204050915151c1b14010e0604050303 63
    0xc0e0070300e542c0e543c00810040d40590700000100310344401c4202c43c0c02242e00c144416030350800d100c810728103180310341d5101008115070700061419501410300180007003d4500c00100d41d400c1460022404081141000c441400c001c040040034003626000d8110040100e040c0381c0b400b007010303080000b03014101844880198000c20140c0b1400014040d0b06a4043e0602c0b0420b00e00700e10a1036944541c1e0103020381483d0301d4010440400020490384181441e5680501c4c60ba22401401d01041070b4042001c00c221550780300080c0300c07140b905440011070050490340d9a503130308150050100e030381e4548060081d81080081000058020003c0c1c808000199943c0c071307150442d024a00c03001007080500a52042c40c180620210542c000740340d0303000031001140c44c0f420345c507940c0701080d040c480e00e54841c2d88000581c40f00c0110700601507001c415140f090208410b1a09a500303c402445281d0300008111143c0007218021581d1021600c500e102080d10700a02e400d06080120b42c9074030078598007840c00c100400104 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 856992032 1250 856990782 856990811
    0xe0705071704060f030b0a121509060f1a0a030b060607080f0c0a0302070e010f1a0d0c020607030c0c020d0803070219080d050a1e0e0f0a300210 63
    0x103000e0a400700c00301c5035141d84480f00a080500072510701400249800401841c03400c0080d250801e0f150b042c0c0c1c1103841601c0c1903680d140a45520103841c06243d0300e03080c07440c00103a041d0040c290b03030034a00203021030240210301700c1d080c4407210942c0e07641c4101107154040011518952409030001e106070b40103a0b98900a040200b61841140d04800c41502d000800081d20304012561504040c030980c01c5c0c9080c540d460418021628081c0a0030050350000441004000341005426401d40341e50100e280c141603050207050101c0e0b540849440143e040a0100418aa0302d480f50041a41407420240e032404625004a0241080ea003030040256038004041641c842c000c00c5080181d14601c0039440e620030203842c05200941140f8052280c1c0c3e410000411107070700d400d00a40c0751284024290600c0b0041c1402c40d034000d81840e602e0700141e4041c40804030074001c1c00380030301007103140140c042c13a450b540362309090306501080900d0104e00640c08600c5000d0b07642d01140c100e83d54506014003044001943c40c84 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 856993282 1250 856992032 856992053
    0x10b10081e010f090e1f02280c1202120306060313080c0f0d11030a080408270312030709140f090406051902090a0302240a0c05160e070507 61
    0x65500c20030007900004000344070140d8002a56201601480080c070f0710980c0d2a954281d00142150041c4004100c48441909501400c00c6010300592424042e40c0d14203016081320f0652800390004801210b03200c1407000d801c090310040543d6200030007503160350320080b6081b4000a049039101d01000808100f20101004ca142062908142c00d980e82d0380000c00c0c001d60b6401152903200186c0240381e1405010303405980c60a0724402d40d031001c1c61a01080b1501103410400c01001110b100b1001e1145414080310080302d1140b500d0080e01d00402907074070790f04040c50980e4810135041c2c051010010044c0d0720740c0c403200700000c0324501140146929502c00000301030302d42c00c1406c107801a403403100f00402d01c09290001401400548018425141c00d1040c89059124000e5040d40000241c041040142051041204040c8503601e030800310039124402080346621071481c1d440000c0b2594000b80c28845e040c420501c0380d21424082c4102a13207460000c3e82040030013880c400600c42d0124007402404a035022 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 856994532 1250 856993282 856993321
    0x70e0a060510020a030801060305061f2a0203060105030304050105040e0a1b0e0907020a0308160e0310060617280f09060c020c01170f09190303090311010b1008 70
    0x448200002c005000a555100c030b22000d0700003a41e56800025024040c0c49004d01454015180b11210000908400b00a00c5403212101c104000c0605c81341c14004007280114514940018881d19085103004040ca003080c182c1111b88a41c204000401203a170700403044904482a1401900d099a100d4407940020042114003d4880c2103290b24182104d5202006100340201141c4c440702a8580b110126520169035600070040f5840401140224501281d400303c81c180c10b1800c5c030302e108402d502080c14944003c95450782540c0310502480390399080702e43c010300b8101c00c0007044000c0c034000091042418482105003001060034195201405864006200c450131a000511240c511803401e5401481083d0340e1200500550040c00d41c20762003142c284040d22158071b1101d0950700c80380d900c80743c0480081c001c0850391140d41c0c41e003071488111041d64000305002e07460018482d03082e03080c0a0a02581c400039984182d1415654515913a03885d0082090000d040c40c00204071350310401100d111070031070070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 856995782 1250 856994532 856994539
    0xd0b0d05030d05160c0302100f0e031c0c05030c0d020702040f09050607030501090b1e031606080a050c0403121d06120a180f3c060c0f02070e0a0605 65
    0x30765180d4034907040c0c10503070141000081e010400d0444c4082110342c0f0070130312801001a001601e04008861480c1c20080e6145c0100303d00060880d0000211071560740521070700d00f42c91007440341d0000d042c04030380f14518807010389007030503843c618203501c100c4694465084000c800356070118810303066484680c0043d5520b107100400700240e85040c2030059a4041c100d030f02c0000a4201000172554001900540c042c0d40302c050840404004903004103800e02900f40c0c000e0350180b1034552003010030740d80141c0050080a02d034466103060f08120034408103484000f410911001c0c2c042101b00b00091181c1c80d003411980082c527251800121b034030598100420382c0d0002c5684440c006c20410594039030240703414010110258204038030101c001d2400d11500030500701920001da020304500110740409030700c0700d420a18020080c4010464a01c010032180b090210102950300b8813645d50400030148180035105420381401b82000c0300e0210002d55a00f414020800d0142c1280045880455950404070140030001c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 856997032 1250 856995782 856995787
    0xa12031817010209030c0a05061b03070f0f05010b0d0b010b0a180b0c060105041a27011706100e01050f03070305030f03070815010207050f03151503070603110d0b0d0503 74
    0x100c00142c080e42018154600c01d0040000030a490b1910034442400c132070300642428105000f00c0c2e820240320b000502400718070f01040180701c00140f042d02076000218400c5255014003440d07420000d0031a0652200c0902410150100304082a8542d11030f40c1124100903609650714030300e01045900c0c52210200704003a00f200840031414840980c040d004003a807440483c2c90070303079a41042009030791501061010b412200011210306d802c0c05240994140018605910b01046840c0b00d4100401c00b43e2041c3d00780d100c9500661413170034080c0141504a88030701040e407103550070120010300060061003540c3c8641c42c4000020043e031000d01980c0e0045030003005403070b1204905000c003241580120b42d000000f6841200041f4801035251915a102e42c06074020a505401c0506000200b45810b240c554188201009030003507a0101441d1840750a441103150628500c0109052070070b651078200748240f50918031445014603628041e220314040b80c03200403c094818102040b01c01d64010406400c0b030000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 856998282 1250 856997032 856997069
    0x1a0f090414090f0c0a0f060807021e0105060f101d01020705041a010e0109082d0d020f0f07050d1514010e060a0b091309060605100c0c050a120318 64
    0x2c90401030680300e00c426100c103d510340c3c0030000d00500600800307070b115007440c0e0244007091060703d043e94000127900403648910b002c00194540240007007441c007007580d1101d0400c02d8070f0070716048100d0904020354081e024403400c02405071900840a03020351070152400b4114289030b200304004001000054804c21005881c094800040388052032036501003003200101034a95440b82c060360048462140103010224001281c414580341042d03094808000c0c8509408410001444519030700074243c0c0040024060039040c450921480d0441030b40107802056042000d0b442c0c070014080308039441222120305224083c400741c01001c00d049240042c1602da000442c2000000d9482401260122401000301b0b50f100120341c954171500650a411401501c088490440c440d00f020509500c00c17140071a000f510388010030b180303000f00071180001548030b409110900c00c0042c00800a000c05030380100b881410814108240126030100404001c0ca0a26184146569844240c054500d200d00790b03644005 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 856999532 1250 856998282 856998301
    0x21030204380c0604110603010302130b04060312020d02010b0a1a031902121b07080d020319110a080603060402012028032601091119030203101a0f090414 67
    0x6007144c01303d8056076000f00c9001c0074908241941d040781c0d4002c000780d15110b492901c03607028081c0d00c1e001542180e1180d2012001070004540070901610650041949140000000342901c0700024254091121030f6801e0010480c01c040d403c442e28410031400d030792070b00c1c2e032654891239000c402e0081141078404602450358501241e103c0d4010341c40c0700410f00700310294030100366241c411004002c00c092020008280c80b40c0d0790760050f5510140b4004074a41d004130700202c02d130545240007500f030408200050448840e982080c1c0080c0c00100c15401000300e40b0b4281c0c0043c100454024134125052504441512a040b04200c81040c1d00300d20681e1a480c035240c10041282d01c110b011003240030490840881030700001c00c07040d400154010803545140c903441c2054010042c8242406c403040c00904000c81400d8414210000e503120406a4006a9914000d0031000002c0c285402c40c1024a0740049034ec910900c0301019160190707500950144d03625a400002802040c03030320f01d4480154440e0303041101c03422 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 857000782 1250 856999532 856999543
    0x60a03020f0d170c07180c020c0f0d1a190204080307030302030c07060c080a05090c03060117030c030c060106020f0d050403032a050a060c09051c1e21030204380c 71
    0x80743c06190340c050703d100c0075910040e1f078600b00600380180e02420500c0710500c1c0012000b080100301070407123a448880c90721540c070503ca015129900042440c414405140b4030380c42c280d188641511400c60920b41840582510fa11400601404040d00803001ca8010844901100e916651140707041242d5018007030b026100d52802c944408401e8544400912031185c08514501501001000740c01e81d40e082440100007401c0c0c60701d14203101e00c0141702d00c0340481e808000401105034400014045581b401c0402880c02200b101070600d5504842007018641da00310061306c00b45d90740342c10703c0c1000809440644050054801c6c03190068035070148581d06115000c100014050b014040c107000f18442d4110907502140d062103055000341320f84252000d01035070700e10940c484034402d484c0c4804608950548040280d485c620a440700c0b00210646000c03425202c0000300b40c445c541c02e09508103803a0a8042c0540b01da2000007503070221100440b004890704040d5030101c1d00058480541c0c071422041300c200c4e90754 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 857002032 1250 857000782 857000789
    0xa1d060a0608040b0a0504031119120302042907121205090f03040603180c0e01060801060f0f050c07151101060b0711120a1a070305060a03020f0d170c07 67
    0x800c22020042840c901c00c40e00b09100b550040702d6203165443d62141c800007801e00400a400300030030000340003404401880090690300c007444400441803900c0c02c1c07107543d50399101d81b0407007894810032040200000001c1e50340c02d20075800710143c0d008400d0609994030742c0704141c0c0050130444048264100e0941040d1440c03805040c4810401c6580d03600503a803076840f6034440303803104103600038041001000c0c4203800c20b001546549004c220565590380e10b600310702ca00ca4006400060204006100155011001d5401408245090803515814070070117005105a0501036040000001d0110081c1c1801c1003110b009100f04440c49222820089005004441141400006500341030780011212100000c1d6114140c0040411640e42c010b135080242c0c1c445d80101942c22805402c440e0b9002c200150494051502050f818101d40d15141c4001812948000d00e9188102d071041814400b68460280c400950b02c0181c1e030350f0440444900b0302d400c01c12190f0399600000313100003640414010011402c40d086 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 857003282 1250 857002032 857002039
    0xc030608010e0a05060105130609140f09160b071a010e010f0b0906030c07140102120601080a331230050306060a050c0105130b06061c0b0a1d06 63
    0x40040780480b00d803078400040015000b9481240103210a2604446101450030581c400082c05c81d60364008405840c441258110400459170402551140366a2116407002c134100280045001c9003070502c0c1c4051170fa004880c014080400c021040001c4000141703131a48210750304440541c0d440c503084080c01c500340a100c5541c2c40300c220004100c006903089c1d82d805800101101c0c00c0d56604501c61805e6000906c00340c0d1140340024100319103801c03c2c070017000311307021400fa0030205152980024001c08400ba10800350070345402e541501c5c12607441c0c40d00c050781280c0c5420b0301601c134510b092020800c03019004070509444400d403030b000b084481840a8503a40b5201c40c0d0004c4014441f03100344904030821440c0000c09d004200203902031030501c00410181e503050900b5401c0c44d515010450842c4d0302107402440d140327115805007003444425054164807207801c50300c2d01c4c60540140010340310481c0c400301c100426030311103036000c2040c1d59100c402070251405490405000311100d07015000841c082c0d0f2030502 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 857004532 1250 857003282 857003291
    0x8161b050409030e04020d090c0603061d0c031f0906081005090c030703061503080a0c050106051203070201180e091614100e15030108071d0f13050c040c03060801 71
    0x4041c100750041c1c480b040d400d03407586250200b0500600004c0e602c003e52620b00607649001c041c0010b003680c104d03003000d440f041da00090f059003032441d2082c01035040c1c1a01d07280c4103404402c2040141c6010200d030380c0002150f994104a8100748030f0031011060b1034010955050030864003240400000231402c2224481942c14031403512843c2d402034680c1c0e250306140c1d400d600082d10038008180982c0004c014068140c1103040f00365904d0300e0380031064000b01d100c600000d10b10f6800d081032207000d004c2c0c100078000032522191405800c050161f5a442091002418006518003144084074280c40e514000d01902507045024580595071545440042c002c082c50158001c8010030712248000c61540540e10140c04181d41296441b410340b50303c941c00e050301d603021010b5182465881e040d040238500802c20302c0020100641407800700c0040368101040c9558207c032007010483c4109030908826000005407140041402641c00c5c218202412100440c0e042403c00e2203049009074554403010488110360001c00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 857005782 1250 857004532 857004539
    0xa05031c080f0603150c191e090f05010e0409020301050c07031d0109173408160e040206040b030c0d0501330201150f2d030b0408161b 59
    0x1400d08401c1c3c0f410303a016408100c481c0c0070111000221508000c1c840492801d045512011032180700d031407041040021105030480e41898914138001c4613040490038043d01144c18081104c8607856a8130800b810030000d48402c01c1a0344466000c040042e130017500030310032441d081c554200f46500c48401180052072080e00c1e1b8022400300d68988861800507076481102916009003c0941c400c0701601103841c3c010022070f80001882c0c3e04100000308964569031302d0450140703da02145540541c8503800b203400042040302c01e0114510701074166800d04801c048039840350300215006000c0d6404c01a0000c10000c05c1c0800d26540c00040c1a0104104e032050290340c4c0c036007151800914044003181c9079044000d4540b03030070410003036030300109400c940300014912845000041d5907a50703e500c141c0d40091502424402650507140004000342c0c2c04440b890720101e0720038495030b00001c1d444050203441556012400f0084030404440d4406440e1344070090a4606080400c0c4a52050038248072a000d901c5002 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 857007032 1250 857005782 857005801
    0x906071d043b1504020109080a030909051005010509120c090a0e0712050312070e0310020301180203012d0f140f0457030e07050a05040207020a05031c08 67
    0x1501c2e018800006800304040350081c1d22038120307001e00100d042c0720341071602165024081100400c20ba01170342d6090003480c6000e0302c030f00803100040e02c00f1412204e506010700450740c0007400c0324040401901e4404021304544c9941e410107a03445122035100003c9024030078160010740080806106880a50700b405655210001541c03615000090194009101c541d603124101c0c034459030300a9290034001c0c41c420407a070000c1e02300010340305010400e684c08801848008400f004100080748104002c51455040c280da0800748100d1103100c80740048042c03081c04070790501c048408020441d0218a2116544482d00c0c43c2c0c2a0300707407440b000e0243c14406070581c1075140c14056601b5600b82c19180350f41d44001c1410304c0342c51a07015030348504c00c1c410205001c4000304c0402d1601c080034004c5981d140b0b40c00d02d5406c0007410345542c546007000c10345c40154240020340d5501032007030494000b21001039681010b440800c43c00203070b69100b80c0c0c2c14000c5880d554020f0540a21848004280c0c0d07941694540d9641000d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 857008282 1250 857007032 857007131
    0x80f030a1704060e010204080307061404020105070f21030912021204050402091c050705090f01050303030f0603010f0c080601030612171c020a09050a06080906071d04 73
    0x409000901c4840d904040080d640007460b0400d00038030000c681030b080480c54500fa64000d44c1304150a0f8400030788a020701400d4802c14031107909520001510341000c0d00000d0060058070300181600900080c0700f010083c04603580d409a16101d25a44104140e144002c2d000b08622351095881407030046501000c14804685126026248039a0342d05050416041c40008d4015000f06600042d078280b03080240384424003515070a0748514000d05095003010103000125201501703500d1070f91008070050145a0700801074035480010388040e00600e54504c00028090104012040201072034501100c1655a0101c4058881c160a803024030403290742e49058100c0c2d100000000d001c0380344040803289049500310041c50000b1141c010341d00a550800c1105080307900164541d000b003540000d041085040001100009107800e007000c0d161803508000c4a52a42030080c840c00400110507001c4000d211403440c600300920300034204100e08806100036250055520050f450f4a00d400d070310541500224014 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 857009532 1250 857008282 857008297
    0x111031b1624110c0411040906120809100917010e010c0e0d02100c02060301140109050f092e030b09060105031908030402011407080315010504050a0e0c041e080f03 72
    0x40501c494810000115089243e203040303001c05000d4034450000907600d030700071241455100140716603114a00450340044405030340c45a99000c015100c50310110340c40f881651440308050300e0500c03038512280c00803940e8603440c0d040000400c00b4140040a10401503110f400e807815114000c106000d0207120a4444000d140c40040c1d002c5001e030800d10040c1841c0b180c110031500c0d20300b40540c0740e10072580021403a0f0001d8214600307581355036500e1079141da844025440105410b0301c1401200c0303064800b2880a40780280140c00c5410007588040d80c8a4032070202001f80c0151540ca08211500d82c82c00c0c034401401583e5000e01e81c4205400494986404182c0c0d907040c0b03007219141c0c0554070351641c1d000c00a81008106034103010010b606c0e0031001080300000e190300352103104559641d01d0440348502e5411141709200d810044148814800703500c4404030311041c2e81500e450250155140340030923105200fa0341003c1003401071100b0342468419074111000039501180159009015141c40b6203560313000f0000c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 857010782 1250 857009532 857009579
    0x120c2003031611030f030d0605040c090302060901090302090a021209030c0d12060b040905070f030e030306060d09050d03050612010203160f170f010626060111031b16 73
    0x84480c12644003918142c42091091400440300d000c01070009060428031501424181c00000b140c42d01254036110303030406080c04440402c41d0010055000b0074041d02c0380070090007034400095642607a8065101c100045038024a005101e190640690000c0d410261300019035a1071400400d2100310080107440401c0310000040011360300c803034070460b0300c1000410b81411156840601050844c1028010005003075001030115940c14080e10092007080040c05800425142009040145d48007100f180d03040b4108640b141c1c0c50ba0300b030b030504000514a961000b0010710130740102d0042c45406402c141d102c1c45003110841c070684c4d01c8140c21400c3c2d2004071105004154150000e0352050f000310301d034410341c080900d0072000064042d281808130030002da456100800f000d00041103d0b5512000106003e5018010700c060040311010b085a80b050160405040c0040c104c00358030301c0081001641d080e00018103418101d10580c008454845a0503600c00380d4204800501040500c040310a0014004a84c0c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 857012032 1250 857010782 857010787
    0x26040b070204092102010603110306070f030b011407060e0105010b0a0507030f09031b0816081504020607020307171002071101230d020c0d140301170307120c200303 72
    0x1070307080100809060f0812994841c03d8650420510144072141402403080e400000b04181142454035050310003000c4107100394450f02c02c0140040d40178a02104950720350401062141c20900162180e00004182d030580c1800803840400b84031031034110070712100321400200166600ca4218100510644102d1404580104040c8002900c1510b5040d403d155a02d07240140380e490b030b911080e41030040c4195100c2c3c00d496500500800600380021510760000540c03a140880c6004002500c1704000322400280007035403400a000d54403440112905e0b16401001d40f208280c41d079070384021441c89004001c1b031704c0c031800d49400e10311886072003105c4c0c040c2d4010f070030000ca00c445800112810f212070b40604c4101c11004821440404c04180a480341144050003d07880311285103000f481e2020014400081040d440700c5110300008080440e41580c0e00c900f54107400850b400000351039842400300007171402820781490755840c6e6022804e4407d240c400e1400c10350b80c2c06060b10740b044070300c042140168103030002c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 857013282 1250 857012032 857012047
    0x70e010806040b18031b0309010314090703030302090301060b041d060409112218050f07140909010e0d0306050933040923060f0f04140102070f26040b 66
    0x4141c80050800c1c8843c21281b80454116005202c6a4010001096a803011424500c150303018060b1b03012022803811070f84654030f0510380c8c0980d074468521018042c9580081c0d200f5290300c1c29009480540b1742c2e02d403420b035125580d944825003022080c004041603c6c018010481a2900c0d0046214082c0c0002c0880d4580000c1c904220440e01c103c0040c40350b4007001d03a10038100d00c00034090301c504180546040401c888507414510b040140e43c9000361019081110b083c4003100180c82c0362403141c5802d072611449540c440400c540100100007040025104607002340e044e682d40364002c002541c0c01a1030415950b22908107002c00c0140704c0120f0f500c12905c107684c41506640c0424014440840203001065059030340d110148000b07003401d518460007009007146140c07004204005600000240000703d0300d45000e041c0b034a695107029200801a50480704218201c0000750180c0b40308a4014a10301da2240d620324086040340c0d0ba00407504502000140d05100203248030041d1021104107070380d82840c0041 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 857014388 1106 857013282 857013301
    0x2130305010c0219120315080111042103080f060a030b04060b040c0203040608060d020d0519110d0302030d020d021b0c1c1220010c02070e010806040b 66
    0x102d103050013000440e500300b90200441e451400040844141c4030382c10034940158000702c1150700300078240d42098082d100400c1101e121040301240c0c2c0482c008102e03050801c1040250200e8441000a40c8a1142c80901a8480c0c40103003520b140945a54600d50004410744c0e041e6203265480210402c982428424034040c02e041d400150308040c0b92880c01040c3c510020600c50240100104003011519a9201c0c007046661003c20f9409059404840031300500041ca026a1410b10600c4400110f0600390b014003041a01940038520f0a20000c0c0504041d41c041c401c7c89401660070081584078000b0040c210758514103280141006882013420010b80185c10380680150b41d08440040c0700044030311100b607242118604001000c1d00f040040e0351110f042ea58a00c000950070005d04109099021070914240e56441c00300d80102c1c1d88920009036110b0b8201c6006009650b0840400c48124 = true := by decide +kernel

theorem cover : BRFrame.Cov 856834532 857014388 := by
  have h0 := BRFrame.cov_init 856834532
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856834532 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 856834532 ≤ n) (h2 : n < 857014388) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
