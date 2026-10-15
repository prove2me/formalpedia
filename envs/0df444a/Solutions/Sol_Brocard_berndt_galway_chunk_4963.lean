-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4963
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:18:17.666479+00:00
-- url     : https://prove2.me/submissions/e6593cac-0d73-4ca4-b16d-eb3dc3437219

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 892446043 ≤ n < 892625899 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 892447293 1250 892446043 892446091
    0x191b0b0117060423030d1103040204270308150603070e041d150c04080d0206042d11012106050f04020307120203060d0602190306170d0c050705030105 66
    0x11520740c2508203500040c24440000d1a60480e04040c0c1001042c07081c41c9060142960f04500c03c1d4213000f00001c5c1020605415025404011805030340708076810031803000185040404441c2a000c05c1e41401c103645140d10100f0f0103190744942c09100b95401c640380d00103420000c1c0d0f05400c10f681c1500021110340f004180b0341440e2144c02e0401c00c0b0060b0302c0c1290210500705030303541c00c901c001c01c00400c182540030138a150039100940d80a40b00410688210102e01e0310000c3d510a41240c050345e000b0026248000a0446810420406a10a0481071140f01944c43c0c0f1140310410301040384c100000c80092402c1e040720550450746148240c1400f1500515110800600300d00c44078910303104620400501c2096500403101020300f42da0781201680325130310900007811075045040c0140c003007400042c00740c06280443c1c80b11b405280041d2402c001c07460719240c1ca908004040c030320202e5075078400801c80d1052030091f001c25050a1044040303d99050b00c400100342940d03419103c008000c6017010700321003440 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 892448543 1250 892447293 892447319
    0x6120405010c0e011e050c03090d0302030d0c080609013609050f0d0206131703010608011707060f12063803070c12111506120c06191b0b01 61
    0x743c0240307451201070080310101d00c01100381c180c00c1814003100003800c2d182e024090040d203d040b00006c107401c600059a04010b9269400301050304032145c0380c0800d144201e405000f007240a54005006011240c3c203060021081806511024440442e0111240140c110302e01d07a6048005c101e0b40c0c00f0591030306505d0b00900c0c14020103290b100a4004440c444038071580080c066030310040300b03020310840c104a414030115012560f070700401481d4000002054050300300d0301060488822640e0307040945c04e0548019100d10840c0680340c0000c0c0c9c1d0303440b8908801d01c00d440c2c062005645420000720b096503219030742400c21480b103e0480c400b960341003110035140c2200c56114400c030510310581c65032900c0c1d00010000740340c9010040c03540b0505027105407154440c03503085955000d541e0440d40c1c0702c8000a00b08101c44001ca0b00980b0401d91109200d5020002003902c820410f4064401410924102c0ca45403e52a080c1c131820100440000c451b41c01015551980210b64014800705815506007158083c0030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 892449793 1250 892448543 892448567
    0xc07060c05150709090204031121070311061c1a01050703080601260732030a0b0607080304060221040f0609140f031b060103020117040206120405010c 66
    0x21000004048000c18008034007050340c1a54802c1001c0c035551075a20640b40081150043d48001d440414003004000380c2003030041d000d14084628000c03169222040050b410462400d408550300280020030005160940c1c03000c640400803c4541483c5a0308410150782d094004500326068880c4a00251190f02000ca4024583c00b80b034441c0c500742c000c0e00e002e024240050f25686c100a45018000e00f12101030814504103902d44d03040741c00c01e0820350310040c144d00c450225034000c0700f22428459803130304c080101c1c00b0640116540721425035540c0c44034030000300b490059803508804100198800503110100a43c49a03102c2c01c001a01da084004048100980d01c001c1914544911b809200100740c0b08171115010070f80c020400320319128185018116407a446440710540d10802e400600140070100280944042002040d181c07040c1010700540d0b6020280301c003038045070f900e096401002e80aa81560b03031150001d40454500319a501120b09a010300300c0781925aa5942c107041c100299000c0c48819107 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 892451043 1250 892449793 892449797
    0x111c03081e010e070e150c1b060a120509190807030e04020310030b0a1506020d03050a06050d0201200a080c060603060402060d09020120010905073023030c0706 70
    0x70a40c184245080d00c40c0c0f01600c0b0005011058040c1d44541e690b2051080c1c4e651448260143c071118905503043daa82c07a0107148100c3e400c1140c440c03082e01d0604000740d84180c409aa540c0c101e42d0f0040e100c1d80e000304005400d200d114010040071f2500700803c001c8200d05c6622803403003165078254900340100820304206529105600400601c0381c80c123190400032041e2a044a0011540d80310700301d07404010200a54101c6010403040000204190040782004210504d5141803005a482d103480e03c0c21106075004080e40100d104400b040594441c840000440e85101014946c011840074541c1c0740c410340d80011128810000364541004000740320036904410140e00070001c5041660004009000d11000d00c0c4034a680c17401c038981076a2251a00c44106400d001c118010b40118408890107040308020a6484e032050350030000d200305200305009000d40054024141c40c4540c24100075a80034240c10a5400b402e05118013440d9011400da01d0640420003002150307640c400003000b0382440c0013a488801 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 892452293 1250 892451043 892451101
    0x6020102280e09090c1e030d0f05040b0c030a03240608060411030f040606060819023901150b040e06180c0301080c060a020a111c0308 59
    0x1400d0074030714060710340920781c8034400008015194111082c0c0d4045480d1a80b200785082409140a408102d04000032420f68155449406401580d1491242c07030141c0303509036128040385e40f2018403c22146101300c3c200e01d02030745819981d54100c041038100c030880191030341000806204040e0584650301e070142101b0450395080c089400780304500703085c80c450541805203400000d501540d07690312400100800300c00305500c90814418035040c6100840d0120b07002c03840c200380894403a000394041c900c150b54111207200f8081c04051003101a410541c1e41c03410f0540603025030664011011960765480780c808140041440c10954010b007901c60f4021800309295800034180000d8065104840503a0540c800c40405038540e4804601e80740140d09548115006003000d11000c4000e5900543c1281c04200c12200c2101e42103003045218421009080d0160340402007540000b05401400550701d500108104182818801c0f149401000d038a0201c001405d54420840c0e0a41076000080c0b0b0190030b200c80711 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 892453543 1250 892452293 892452307
    0x6080709230402010e0a0f1815060f2303090d030b13091a13050f010209090708090a0203030c030c1006121e0213020306010305090a0b01120f0b09060108060106020102 73
    0xca400d00c1d911080103540203800c0001e0669015400e4004400c0b000303080c2c0c4100ea55100300e201d020001030302a900070020344480d202010319003070142d014803012010034400c0c01850880f041c1d60b00320080c0b2117601070080ca50b1840900d05c41246d054820038013081e410b980e503450300f42e00843c10325143c403131380c0803c1c075203030010000d0740d602c0b0f042c0c00000d280c0000b2000201c02c19581040444103007110030501d9061030100030001031040101584407414810412a1f52540c941250582030303001d81c500c585c0d0003807454000030b1101e03032003640d4060300a003c0c042540d0321050241c01080c03c41d40f05a030603103a554000103442c4640301c0108005600c60310701e800c04018541c2408603100ca03100151101422901d220344400729800f1611040d07100f5240d005000071454450540070ba0041e400450b00d2601107441d1100043d0894070119441105a42c8490902056070810340c050881d1010918142c86605e1205500c8002844480880b80282c2c9440c1c003d11503585040e901510f4007005130801d204690041c07001d4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 892454793 1250 892453543 892453571
    0x180106080f0f01060f020f030a0f020708070501120207110406261501030303110d290301090b01030b09030f0706021e0406050f0d020c01020d0c0f0309020310090f0804080106080709 79
    0xd2410b444e150b2a00300102d03800b14008a00d0520000e000c10900d000000303070210a180c0211200d907480d0901d40076140c1150340c4441013138076100144123035070110701c200f0160b62201c0a42d42c01010300c6485044006003004507600414200c5d0015001042c0300328028141018107160003442c503529114410040480342c4924030030204200c0113200c001d090640300c0b0084c076410350008007914401c0c0d0780c100d4204150348900c2802014000c180f070b107100000200500c0340000d410103014a114598021103503034416481d580d606510030700001e1460581c4d001c1440790740310094180c001042c007180140005600c0307100003580c1c090b01101d000885141e10504100420a4030b03040019140030881c0c079098036490310243c005501c00b034030400c0055842c0b07510000d0866500700c0c2070741c8030b10034110701962417a00d040024281a030803580c21139000f03507044d4002075103501ca11783c20350400c101a9104481403580d512080c0c1d01d41740d55400c5500300783d155944403842032008410410045004020561080c04416959090 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 892456043 1250 892454793 892454821
    0xf01080703030c1401020403210306170c12010605100302211e1b0703021c020102040b04030f02190e04050d020a03050703030c02210c1002041401050d0b180106080f 72
    0x2000b4107a8204c152a02c0480e4420b506a50045070001c0008004001e100c0000515030100e40c62000403038501400810114100d0742601c174201101d1000346410760448040045990341500d00e040300d50f49510020a05031150203610409003c0c41e10702503121800440c000c07000c05042003160300020308090810120b02c92041401865000c0f202da128000d03100c0c000045141c46d15406e49401d07110001501c80101503000070207980c110242007441d1415200548206c1c241d10461140c04032901050009201240e0740e4070086280d14401060000b031551000f0000343c482170382e40d101c0010300d0700c001e0400040c03120602c26000c2c01c1c10745102401070110241e4020b8003034000d81c0d4016003019621154080c0c29402003024152a00300c107440140c22030707442d44001c04141d01c21784440301c0038000d03014101d908042500035030307090b01c050070791400c1c1c88543d9000448168000801c203c0c0020f4840c6200d00c41340c0c448528201c10760b0450040b048940d0f0410170060a404006001e00740001c00c9402000b441c0792503450 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 892457293 1250 892456043 892456067
    0x50409080f07060f18210f050c0c1504210c03200411180d0f0b061f03051e04170c03070203060108160f03050303070e01090306020c01050f0108070303 66
    0x40054440ca11401c1c503c00070705441c8a80c5003624541502c51980e11540041510039601c6484003c2500b50161104141c0c180342c040e408000ca68136008000d8803500a402410307d0080c01021640c020108500050a000031500c3c586032000000805115054504507403018070f80e05524510305010b6a6a10460200c074148809400a140c40b008107405008240c904000d07154000c0042c418100000081c024940c45541e80c004c00f26086c1e082c42c1000c2c200840441420342c1c0104034201d648d070458483c89403c600042005a2241c51801031100403e4460382001d20f101055071300041c03500d0040c0e1142c10700c1110790910000784001c0c500b0032001440007031000075040495030069840e002c1d5402054a0341c01a214001e40c1405000000710b0340b118000f5402140c0a8580d2581d4582c59030796010110b0304000c0d002c0074009410400005a030785009d21008044000c0601d08482460b5072610703280d040343c1040c900030380d0703994480042c009400546048503000d049800080c0c0791552135554040c0074400411 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 892458543 1250 892457293 892457317
    0xf0106080702030f0a0918061401020f1903030b030313030302100920011b081810020d030e07050d050c01112a041413030824060310090e010603050705040908 69
    0x101c20305c1d0688654034850080038822200342081c0442c10341040900b40d14056032036440c4019060259540c170001d9080804d102c0400985201082415044c440c0340c1200029014561100003c480c1134408100504c400c050035510402c0c10f60071464000c3c14124500d080345495410101c940012500301412041c4403442d40e00d1076a8030b02080343c01a2070404a031080e2040d00d134480440503040c410350350300030a42d214013003034480c030381c2906101004140c031413803881c0340010fa11400c05110818003c1e44049002c40d0200b08480c40b20b0f94410000b01c480c010303c8000c54031900030454142c6296001082c41d1501800c074400380600410000c43c11201c0926201c015656404c808980c43e42a00e4542c0401a4000203031a030302d14900e01809008189081618100c00150240000881901d0200202d1038210f80d90001e946905c3d0050f002c000d0030740c0019240c1c140c441441c0ca03000402d0819413040d880322001c044000310300145181000c0c2e04044c490f03400203020b581005a10030004203480d00b100c002c20285 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 892459793 1250 892458543 892458547
    0x120b0f0406060503030c070306051f0302060a030605060a11010506010929040503030c03191404170f1b0a050111190302070e0906010e0606120c0f0c150f0106080702030f 74
    0x1c0c10044040d15055100c5501400700040861b40c0840104050042d84e016540a02003912200e031030f000754043e494105220002100e4050005250140040501e290140f40106e40a074850f40080e605a102031200f2010a58023140544003031400e001e4203a0295007428a002d5061922080a00d204414007080e02d50030030b225406615190744e1026a0050040581129140c5048043c00c0b0368950150315141d041c240012050b1645500c1480c60400c0511030040711400d040c588084584001c00b50103082c45503008582e4118541c500402c42003501440d610b4035000140407020a000150040c5d4021074100300701030f81c1000d81510b00141d0048400b400f40c04e211450045801c08900300075070360300580180000300c41842010040001c8140c1600c10307035900c0e15615282e602c100507070f52180f240305020341c8000c0c2c000660300c0c5e00000701030000030f90303070680d85458580c4543c805400e01c030310190014a4140a8002d00c025130f107400003882d014040a040260490070040c4c80130356240188040c0102c41040 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 892461043 1250 892459793 892459801
    0xa06060e25080402100207350d02070317070803040615090b06030402091f030c05010807050c0d0c060b2101050a02040e19060306320c1209011d060907120b0f 69
    0x20030005000140407044a652000c488202420395014810000b4181d000c1f240103000500d01c00172440c104427036080d4005003070603407075903407080c0300c00700c540070314408145d02401210007003078a50004512407803040e08001103c400f010044441950660032651566192100c106c429464202c00c40f030304039404030340500096070340c0c1c20707980c1414682c0403050307019911101300002080845c40390038040d0360b070989500c80da035035903800c04031030a004490224074280d02c0702051450041c0078040c0189440e008807030110341a0042c502007414800c013643c2c000700d06461000303600100b000030300c185c40d080301c2a01000d5280601e05603031420358480240426010300c0e1074042d0410382203950341c8401e0041d503004070140001a28011707542d010359184403502134101c44403d0520349071500814280e1141c05081d01c0c15091824490803440c0700c100061400160359a20340003100c07604a045600091514124010181403910b0b0610707034203159065110040d00e01051001c00001038005854550220184c00240d44030381d6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 892462293 1250 892461043 892461047
    0x13060504080f0703090312021f0507090803040f08120c0a030f1206060e010e03011103071409151e070f12020c0904050309101707110a06060e2508040210 67
    0xc500c4001c9070b45402c0c001925003c05400910b0102100d000700080040300c2410700c2c1c00c4c0c1e03c030700d689481d85046400c0d41e4003130300000d5001e6022130b030466494a4120781c0b09488565403865a48681c0048035001d0002404200d080000c00c00c0c805d900308058861400c002240300ca42d0741e5110094130040500c42f801212104081c458140c1881c91211400c0c2030192035030341c0074050500c0d4201c921041c005401d203c1c80b00d800c0d04050191031445c2c1c0280309450b2855403912000c41d001c80000d43c01c400040c03010024441c5641d1481194403440c00b401000d40e03031b40e0304c1011f40c810740303560348494910501c5014801c21001c81d2011802c51203064118200d038441d80d0242c402203040000340069950321201c0541407105002c00040500a40c4d4000e85041c07100240818064900c08007070004020013960319070006100e00e208003246444004800200c2e00340600d00e94030350003610310a41000c03103030000610400c81d40c642c030380d0310b02d0081c0042010010001c0c20f1050700141540c800602c00f9028500d440d000c402c10714 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 892463543 1250 892462293 892462297
    0x30c040e16031208073605040510060809070f061202041e1401092102030a140a050c0103050c03182107140f190809121e061306050408 59
    0x701c41c03507041200e054482c80d1001030140b0030b030582400110094009194240294131000d0b41c0d91084c2140082c0c1511b4896881505d2512414140514030f002070000da01e48580c0980d50190780903001c1d0409240c14500c0040c22032000414904a5901000c0c0130040a4491054002640c2d0300d407401d200110404950130700a4031a5034401c0065540d12080100141d504040171401c1e5909075560303e070106c50b000d00440b00a821400703803080c901c4078110045c81c0c03e6185000c13412028405070030f45000070350341e40ba041c08d0502592007003013041d0400540d1b2810408144600d03002850242000c01c09401c04c0e41205419000090844a2a802d20805c2d5085501e04101e9004184404d80e58040b41000d070014002e82074010b4041140c1e46400317904104039400340410000008940c40000f820f11041a039410b241d49a230001058510b22010481820070b81c5030784026000071200352004011445410f451300050f21040c0400311600d401141c103201d40031a0b11400320b404c2c260080710100c1e01ba1258189458a8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 892464793 1250 892463543 892463563
    0x903160f03110a030c090e01060603060b090f0d0602131805070806090a2702130207050d0f0c0506070918050606090112110a0e1f08061318230a02030c040e 68
    0x804103000001b400c2401d034101e8100d41e40104000c1c0314151b51003005405407202809040120842400359101e00d081c00c04020b00d00c002d00400141d0303001610b480f8442264018105840c0980044009004600c7c40c1143c0442540c054842001140f418000003000c100014000501c6219054042400782005800c414003821016014a28203110791818198100d54154100e01807000c942c1510b021011610070341e403000307401c2000307405160340c40c413021944030348540592400e00c5480c06840000c10420004180328100a4880d03101e90341c03c000005d00080ca844030b0010f610390404003002403d4480f0400d030788048000b801c000600503d0100e803140905400403a00d604900d000c00e14540c840e80c8250800041107080d20302d0000f8080c1090703d22a00440d16002001042c454004100e060034004441c00c0440c6846400142100f0311401c5080b5420707100346d01303461007000c0003a00400703c1040302c20141d1058580000f440302c00100e46c0482d8480682a0185200f196a0400321350300120602c06000c403 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 892466043 1250 892464793 892464803
    0x20303090316140409050c10050c010203040c06080f090c091902030c07020414040c0e1504050f0702010e010b15070606170f1204060e1009051002030903160f03110a03 73
    0x2c82c2c846200e401c0d40c822203520802c2040340d5054005440d9003400d1140b00071503904000980745440000083c040151000c0071041c0c03c00c00108100f0114042c280301650055100301c1141d0090b91401e08014803442020b03108002c0400c2c0da03070a104004070001030b106a00d900607a10502c03e80d8543c141e00b10151000206c604031540004200701604c018440184181c2c2c0c422a0100040070803580c4d0700ca104002201c00a05240d0032400038800d40340142e100076030100d448000c4003642501040850295141940c41003d0650860244850a038080c090308540341c138050300810034100e072840000c007140541640e400c41400c00060600030300409401c10006811201c0d106400c04003c175a00f569070310341c0100150010700582240c4071502c0c0440040f5000c481860b030b03a804055800c1001c00c45046080d04d0907100b4000c0c80000002d568a0b01d809154102c0301c1a0042d68658615000b0b05d820302c3d40e0704c07100c6580406110750500181c20001c0a16050340d400c550800845913040001c1080d5401d03540000d00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 892467293 1250 892466043 892466053
    0xe1c060f020a020a05240c0304050c04020a021e1f0506030109050a12030c0302040b0307050a0c0b010b07050601080304050d120c020303271f03020f091e011d060706090203030903 78
    0x400583c0014900a01a210701c1c11501c204135103185180c851385004070900000c48a40000c034039180c1c0a0720285070820701401c03e54003210900400074040340c0c880200c50f005604000046030060003807062485c45207000402401c03010352500143c22041c04408841c40d1001d0383d03640818142c5d2803d50180f9105a031040c01c803400c451041c2000c000091150016800280c1884c5903001264417a000703507000c640c0580485400c2d5128030100b07071507580140881c030b0100a5806c03a1040031400e0072040d20b00034022140101e680f0241400d086003001816006081d00e503008020810007511521071070811950082080d007904406040126141d885080c00a03500d8840410303240e0b0904d800703010b02144a40300348113040250560354223000540c00e00340341c03845002d0b50044080c038a00340250004c083c2061404402407804401e01d0005007003160400e0903803000d0844280c00780c1e0750758000021940c41541c85d815203c000781161b0029800348990030005086a032505046811900d080040d2002c072107005003611 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 892468543 1250 892467293 892467307
    0x30a1b0b0f061905090106121b050306120109020a1712031518070c140114010b070218010e1b0702031b10090b2505030a020c01030c0e1c060f02 63
    0x20740c1004161500c81c4291081221450100000c003942021a41d02400c200b1450386072003415200210682039032100b6540b10707842d81001707110008030310007102031980f141c0762242490780600a0301d940071482c20300161f24191580015903100340700102100d00043d500e20700504070708402810040c66000c102044400881402185050f01c8000c0c9410f54050b21400d03802502c600c00c0008500040c0c5500000c54102021903000c9080703a44003e5000c03070a0030000c907110090000070103898070242c3c0101e001c2c100200d0f4481c114a000c04820990000c9240002034035410080a2400c80601406280c0448004801984295207a03030603104143d0f001000c3e0384540c1a03490071402a40c0c03980c0080343c407030030080e141d01103200d00400e035540607180300c1d42c0b649041034a04001d1030940302020520b0100c80c64070203085000244104000d01e0a000da6a000d800c02042080c001340035940c0d45c0410000f1b00000f24110566034656040744407001452107000302400c120750070320704020602240d070b4401d000e000203502c0b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 892469793 1250 892468543 892468561
    0x515220e0901060306050f0601051602040b031f0f020307050d0f0908030a050a06050105043f08250f060b1305090307030905090411150405060711030c010c05030a1b0b 73
    0x40c2048a005e0070b000d02403075546150f00d86030070800701c1f03540c0d0205105000d0107080b200600c481c0301310140301420004610850600007031405904071807110602048003200c05d0341821502800700c801c00300070000e60071400c00c510040c016005610340e2202c950f95600e51211072800d65080780c010140c0066800384e40b410300251610103400b04840e03d10485040800c00610344d4410750440302103c01d03000c1e9a500c41606000b410b0b540481c188802c20000111000030410b550400382039015180c4607411700342d650f22051038150414219003081052509608640b5000f0030b116421507901642e0056001456030745210000f518210b038a00a09166440c090400440010001c024002c4a0080c0c803503400c2c175541c400410056000840b0004c25148103202d0034405820513000c842810203d070031003075007042d0702c40000c10916042200141d4611a05000e00c03030990409011027850100280b803e81500c41540d03c51686e40e1080034000020002c954a100380380300c403203280625445078480c0122066080c80c4501c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 892471043 1250 892469793 892469801
    0x9090a08040e1807180b0a051005030405190b0f190c111203060d0b040f17030a0b0603090a03110102040504150f12050a112b0c0515220e0901 62
    0x729045038801c9100a10f0480e00148440883d504c8080300c0d0402946154031324050031507250510b0704007601d9100840d090780c812a04901c10b0b0402d9946036103d2078681885840c000384004011810b03003e00d210200890300030840164805840145241c040c1c4800d01200103140000912107540c80c980000c0101040c0d000e506512600420b4003150048000001350460f548019240a94080d0112002100040071007405d141d0040c0030b800c06d010008205c4d281d081e00340640c04180041c0403c00010820380c66440d2290100910058810605516244d0000c9a881550f0003002e000d01003015040c1210740000d4045030081c9c03a000d00140311807000100340300c00a11036402242c0b0091120040850520840f0108111107900100203100c007030b06544800c0c80c08844444400e800c04600768211868020040d401c0c0c8201c0d9152140309a001e080d8286103010102e560071682c4035184951b11003131310b960042d0a4030b07030450003220f1780256003036080e004403408802540441d07140700004080104000381940 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 892472293 1250 892471043 892471051
    0xf02280813211b051609020c07050f010e21011401060e04050a061805010305010b030f15090703061a09060909071a2119020a050313141c020124030209090a08040e 71
    0x10241c0005440719256003c3c8d00551001200c2607000d0b4030204442c2c5403031906e01034002d0303041c18205030400f004000318000089150780340b07074181c40000c0c0da000c65010034032891721050392015000c0c007036505103480100450f0b07600039030328072039038030b80012640018003640210000c3c01490000007108201c102c0107400b0f4902403009550551030b00785400100c1c20040785003100400498041c05025030030864000e441c00c000703403004480b407041450120000d40140f251404d0000101880b80b4140503c030204100040c0c01002c10340204802305c01d1001c1c2500018000c400d44100c10210140c80019000a130000d0190681322900d40e031890031000000325440007082e008032400e030542d860300c0f900c0000413400ea1051100001c00a2001c0000414881c1580300ba50b0546224051300d41000f03010b403015524245400b0b188901805602c510461801d809208408100810311058a003241c1020b4034010382140e00d110190050708924009502c03040c0501c480150940d100c82010b0f200c5850b80e284e00703043d40c4102c07 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 892473543 1250 892472293 892472323
    0x6090c08240f0103020603070807090902070c080c010201110f0c0a051c09080303071e18060306050a1211040504050f010c031409031c0f02280813211b05 67
    0x11030044542e50300464180c0e5005414a071454035400021244888010041d008106404038081502205070000348145409102c00000d12402e00140320304100381194611705581c500044111172030420000d8881c1e4100703601d11203480d0845d04828a0510b948814010214010300d89150341e0f6520300792248886014603a200740e2041d0321007600ba66284001e540c5d07070f804225550540c0b44000c2d144164842103025600d86507010581c501500b002c1c01c91180c221801080d1110424407180c1410400725009261384103080c2d0704494280c0f58982181d00310790003a8001c40e11400000e0a03c00100310721111410340c0c0c0003c0202001c01c1030000d0040000c0360244820001d140b01198050703400005986000b039014640c5481c140c4042c1c8004003d008080140245070740a0040043c02601c05001a1129210801c9406003d089400060404200800c900300d001c81040c000400f042c400110f1011002e52400d400d1400c5a0170380c41500c407035a12181da00101c207441001d4a08101c008506400445554 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 892474793 1250 892473543 892473613
    0x30304080310120503070b04020a031a070f03060b04052803051605060a121a04110d050108030c120306060d1109010806040e0c153105150706090c08 65
    0x81d082070842c0295043d80030b44a83d0080c04404089820b50b0035a90701710b803000780000300303261341c907610711b614207100724880d00c0c0709400002000407490304008000011602c51404010090500584011901503801880d02440c6480e02040e4000040401d420f0a692141840c0b100259245803007503451444e518910240300c2e0201c000540303402d003081070b40d142c07205940b1410825800c0803103500051583d5407404203104035104070344090307480d288910314420458000d41135482075146140d070103980c0103030722107480c99104210030040e80342d001c40c05141c0c588410410658a0b1580b10000b03250f4000d500031700c060945001c6c001d080e11190f05000300b0310b20b402030300c8524241d6030b0728081004441402c1e000302225004081e40013070314035000d6025103d40c91111134990401c00c00c1c00d8150843d81c0c500707030ba4000098040625213012103200c0d01100040108468070301001f194000b45403983d00403800c0c001c081c2a01c4209007001c201002e000100541040c42c226005010101a840705521031313003031410380300448 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 892476043 1250 892474793 892474799
    0x1506032706010605091905330a0801150203130905041a0402030309240d060e0a29060d050403020d0e0a0f0b0306010504080601081606050a080a0f0608030304080310 72
    0x100d0031078103c8035640c540d00d09020021040c40107280929090145c0b0f08103440010916680e54142d40506c2c01d01030103c00000c5000c0580500d03021840720811003401d606100c80001254400850350549420070010000380c1620002a45107008965401e100c0307000000340401c04c0e42c42540210b1003075006000d040020848a00200e40075041510080d4042c0c10402c2250018200109542d5558a02111001c80c081038024003d0243c0c024508120006851700400c202d04555000b54a0700010b03000d104021080303007107948140e03080c126001c0e50811208060480f00b9a80e82030162560792140800138012481c0a10f07000b51191021010707100454940070142c4c003d41000700048054410802441c2ca42c58245446444150402440b59040100030000811a80c0e401e200d40340c000c1c56440002d00d400c080c0e039407030103044034502d41100342044020301214192aa00000417508071912002c001402d459501e0808050f10b40e542000e42d4a100000520041203e904010751041c41d941040c001a552 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 892477293 1250 892476043 892476121
    0x8100f0c030b130e0316210212070f110607110306010b090306040605040c170106050907260601031b08041709240415050c07060206130803150603 64
    0xa40002c1c0d50750040c100e250084401881a4010407410411030204c038188484021081082d01d2600011100314107000e03052020003104d181940d0010f40075002030302d803900107090718900300d00801e00c001d0454000400ca01e001d000c0d1000e00440f14407405481ca80d6a4140c0d42842c1d190f0b00b40f41500c0a0191150340c0000880103000403d0395150880103000d0001c503240c90300c50b100a410302a0040d0707000c0745051000141141c0d07400c60400224000400400c00034a8182001014840100f810052002e55400003d18841c1c1c0507a110320081c414005600c00c1e207c5c02c0049004010850144820280d20000c0c401d100d90844c11041c4968810011098035640382072a00205000b10703100310344c00044103a0b2401e0a2081e0351003030740e00d803200c3d4910380d4142950b92800c1c0d420408405441e00200348002100e44c44c03400c0a101c2c410161403140001d02aa0411403400391800f40405800b800241c4c0200c081760329940d44a0304941901f90091019881e030401105451a030384a04240d203125050020800e81011 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 892478543 1250 892477293 892477301
    0x1a09060f01051c1805060712060e040b0a09051b130213120f08040608041a04080f0a020c0904210e092e0308090a0f05090a0902030708100f0c03 63
    0x1a9100340c14100703c00340c0d0310010302a070f0140303640d02500d640f0107010320741c0081440400140582e00400c80c2e4100400301914401603071524441d10f50a00d882440208641c0005a80081d841146060a5903030070302c00000500d2040d070010b02c0d500925680841c0003090b060107600180e421210412182c443c61140c00482c40f859400c48010943e0300820400038030840031941000d030058200045201c12603540d1006540190803040118001d2000d000c2070004000000c0d13006201c64a45c540d141c1026280c11596009440c1e200c1400b1400040d01c0c0511807003805240ca0182c03000d01601c00504003441d2540600c00240fa0032603268905003080341255215007400001018040e080055079101c00f05103502043c01a6445103000c00880c0780310941040300d0b4101402940107411441d2140c02900801c141c83c42c1590050841321203048003071000d80d40d03500f000c60b0061881384000601310860b201080c02c2a4080d0300400160080700e071454004181d940013046005182c031020824000e4081c8246c0842d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 892479793 1250 892478543 892478569
    0x307021203160807110303010f090b030c010e06090103090f1a10060906050a090305100e0d0507110d0609020a0311042d0c110a08120a0b1302030709091a0906 69
    0x86401c45110103050b80c040c1c09201c0e00140549402540303100b444401c6813031a80203034014002740152503c100002e600a1140e20b40701c4104402401c01c00709c0c500d0008044c0728100c445544980000202a0356680c000e9000c0301803d9409170b200c0f080a8171078140550880c01e4448603800d6000042c000402d03c2c40d6516469050341d00a447d081d02d1a401c0c85070403a05c540085600c2c1c01804150940480800d5042181c03440c9400400340110381c1c19904090039003041c96076000c48080c0a07080c8119000694050210b1440f1201510881c202210a06003040900002c10b4080d420009100d004024404120a01f03491228151001d00c41d000c004181e280b8881226210000c601c83e2600b000001c590fa035411105180710b01d0720301807481c04844020b10b030a114800c1400c031851031001a21120f40700300102c826900c03410a07001080340c441d1450101d01d17039018005000d00d8499000000803000760060040741c0c00382c008075204000600390207420b054002d00c400c6101e1700c41c085da2000603580d071610039900014 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 892481043 1250 892479793 892479811
    0x50702100302090102030f0d050411121b030c0d0c031a040206310b09010801141014071b03021309051f270311060103021c08130b0307021203 62
    0x1004120310040300250000c00c070307090440c00100080c0c95440c00601c06041d120b64285800502c5e8105481d01c0c0748405403100c0b1080c081c49458070cc085500e60081940f40002c200001541c10220705000004d041202007034100d548404120000803d01200b1642e40040d648110301e00303110226204506440d19604884c02981f0640030040c4d407185444030296821a5038129402648030300c03801c008000e8013201608078400c000c02c04a00f04825603840b030a114014248403070784d0840700b600c00300401e1510306103001110a01c0340812086201c00b81c200111001c03141c00076081c41d102d10680c1d07030300b8031480c80d58030040c4d20074030085600c081040c7c1039120724852550b1283c0182030b16400c1c0003c890710100e080001c1040c0a1361b8801803403071040e0030102302c501c82e00d0808011302003801c2e600d0007030070a07602e540b100819580204c0c01030005846000040d003081468010f400d80000380381c584551184161581048031000c982c00006010b5190380182d80180c1840d005c0d100308200c258420446800100c43e032a030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 892482293 1250 892481043 892481059
    0x9060316141507030e130b1c020d0203070b0904150e04080906041e091b090512010f050f0720030301050d2a090e0115090c030b12030703020601050a030209070807030e0f0616050702 79
    0x1c08101194052300884e48090024940c1c42c070560002428000c0c1940b1528a90b000021000035519080c4594001c4208141d14000312038204120a041d02c07500805c0244020f500240d404030725610482a18000c08070400c0051410000b41c1003440d04c3d56051203000703007260a145044604c0c44a110400900802541d40c5000302480c10082220300c07104010b0002e419540c4d00210040141a8000d85210710340843e061182c4d070030301410007410644250b4204890030400c00e0246603005010049904580c0100c80f800300c004011700f407201e111003408140f510120b0302c8060110861140d4140001111440303030042000080c41c400c8107007a2001050160b1903c40e1020341400800591b600902242c0c569140000b103c03a49140490000301e401d00d810707c1203905c0400d411080503410041640036150588801d03201d185140d020070401c0d100039184900307100d2520b00241e071140c403a600c9041030308181d40441d05a80d0300703407402d0f6803500016034440400d80201100f40341007031301480c03c54070003542c0600040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 892483543 1250 892482293 892482319
    0x1204060b13021c0b04020405060a0e0922060b0f0a061107080c010c03110a05010903080103050c011407021c05060a020706050a020901141c02071109060316141507030e130b 75
    0x2c1e00801c03c030180c450f400f660900c000301c2c050b149d120281500410a4482002000d5074804010800d0780040c107031a181d0302c6030511625030302c60140d8402101c2ea4858000b00320790740e50900150f041205e43d04020b80217603c03800001003483d4002104041c2d6140d81c0142e4482644441c1c20503210b1710b1098080340031441c20300100001034459002015030756a400e0036034009007800d03521242902d41440341540010100c1005105210302485240c0c0000002d0800107001500c603406a486030242100c06445440b00706001c3c0c0c0c10f541d408010302d0000b079010055500b40d2502070351020003500b18003400da0303c141c5808001401e40c185407080710107540058441c90980b441180c80c98955610468944400100e400c00c050b80c1036407503001424105101344008076604036207000744060848014a00d1b4860b078840b42000b000e40c0c0e4000c03440000d80d01d4001210b0207007001c00001c114440c0c000b0007014040c680004503881455030080141121860031130b100100750300700c919032030191350440c800968041d0001d5080 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 892484793 1250 892483543 892483597
    0x1b060e060d0e0118031b0f060f0f06080619050408030f09070e0a06031403130e06011106090a0209010e01060f0503060f1807031805120a051204060b1302 67
    0x81c2209580c81070340802d00441d040038950956142a142990200b0b1541002d010160080c00e80000d0184142c1107181202954540c2c1200520345a0080c290030354400c0000b1350340810f9040b03a074100f51000f80500c4255030718100300f81c0c3d40c14201c0300340d8210400101e04c038014012074066203020340d800040b503504503280e590083c440307840050314a21180c45038510020320051048544c5100d04203150001a40360724505180221601d0b28045030402d402c104100003000e06d40218050030360700f03d62014807003076880380d0040c0e0f281030440380001d10300e21510082021030100040c450824920070b0f144c980245e6a1625040011078080c026040868454140030559501c80c8010715800500200b09903407848600010410040b05941e912410703241b81c40030021000d4250080300b0b4102609101f0340c03003031280d40e2a910345030351004804503200400000d00c0c2038206e22820580381202422a4001124205854001d0050410a84090082c8002030b01045021124420385050310240f0390304200240064802d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 892486043 1250 892484793 892484797
    0x100503061807080a03020705011d030a030e04230a0c0516060506010318050f011407020c010e031509030304050c030c06040905040f05010507030c1d0f010f0c0209131b060e06 76
    0x4040c0107126402c800105900c0404c100743c0203a020360080c000850a2800040000c82a0300d501d001d11411000d40302a19100012681081601032400803100d00c0c0801c0014007500c165101c24006070343c081c4003001c40ca01020a018040d146c845000c0020700f031120b000f5503150281e541c14840d82c0360001e182c04081421a041650700c808140f500280800c84810300052010b14200c0c1582d4560020400510109003440f03071100c5a24100b4001c0154070785104001d40e01ca42010016040201c91903404207640c03410805120b81401941202d0890310742030380c0d330507625003040302c0a4a06e840b0780190810f8608000c10818208100500303418075042c1014082c0d000340c5405041100c8810a00c2485404610f0a00c250785c01030420350b6002c40c0060490500030700b220622440c0114a1b03400c0120303903c041c6c0e0384000b0142e412303c080c241a07100154400058035180486035004c0d4002100b04100010b514040c0d285010f09441500d00c0000c41441e403c000381107a41c1070085801040b00c40781d0083e268a0702d0341c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 892487293 1250 892486043 892486081
    0xf0f0c100c03261312020a052d010f0207021503060f2b050d03110f030103120c0813051302120103020609030a1506051503040308060402071104090b010501030510050306 74
    0x1030350284840e60042884a0f40d600301d03903000100301081203240800020f103052040c2c80c804c51008103651821782c4c84540e01ca4000c03006054a09680d910b00c03c00b80d0001d100e22103021161000200a451142001b1801950141004920030030741c601d000d04510a00340140c81c0211805003c03214001102c0080c4000d116840c400b42c580e000d4101c44c0401c0581c00d01c980f8101c991300c44c0c0080c0c80d51109241014043c3c44443c2160b88d08001c0520021140758030400c00d680c11603422020054140c01c210905884845034010003800313000002842201d140d101d100100300b2a0301c107480f0f10103040b0f100c15807401240120030b0321031085402c840040000d031030004040c02c0304c2c0c44002d06581d0303c0e801c40d6445400f4060000300e071604c96a141c041c100b18924104020120202c40915003031b24506e407a5030010102c02c0024100c40c880d940c00300e0b00c4810301914014000051902030410410381c01c04d4104004004400d200742030000e03080c40e000603091600120300c941150000b8004100310385502c002501507420800e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 892488543 1250 892487293 892487327
    0x507031a01080c101e0903060b0d0f0b04031808061012020f040b04060f08010501030b060d080a03050712050408030a0605032a120105070c050111160803070c050f0f0c100c03 76
    0x20741c1d001190b40c4c039403620b0545c03402641c60301c4041c6851450004165940740702130034824100c40014801107451314080e08604c0d0f50281341d11403260386034a015600c51011075031050507042c0050300801c40407000178200f4000c05010441144281d602c520080390070351a100025080000420700c100c160405400c684c0c45c0c0f000080c0045940c03a101d05401c408080d05501010305030b074480c00100207009161314034580049007507a0340c9511603002e4503078081301c0c45460424800c050351040000c1c40507204403448041d07400300100c1445207080a080018042d041a42c5107610f080c5081c500040750301c0c0003c0d1070250801d40203052110700d000100ca09041c0c1400c050700c6a000440c2840c21203040c5c1e03080c41041c3c440d1140f512901c0e600403031420308508542c080640c00c80a4041004440c4444030700c4940041c14035800203000e42e4a40c1c510380111201c2900f50030007007041c0b203003645504074024080341304410750320303110300302c44101d645041000314030142c0d52806004200b038000c0ba1404a4401d40000182504030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 892489793 1250 892488543 892488557
    0x1d0a11040b1305120705150906043f0b07020a0302120a05090303070501020426030405040504050c030a03260408090f150c0610151d0406120507031a01080c10 69
    0x280f8049403003a5810703803074036410b908040c205000d6460700e0b50110345121141403480d401d10b9806404624140b10380c3c001c1640b44941c60514840401c06180c0c512450001e596000480d26200c00c01e88016244281d012203070900032100062405200142d5012200c2c3c2541c01800d06c001031000031801079101805440420800b00100401c90310108010b00ea014824000180d03030703e00c2d0070b00c080a0402c10800e8601240c002c20700c10503e00900100351000e41c1c60072640011a510b80b440c085141840314080c142d0103000c0e01215505054000880d400000304495407075158244040c5214043c55048800410182c01801003031128141914502c0b10b81e1000b8001181080c3c01d01070600031a00800e0340b00005a01c0081048446100c580d2043c00034200207a0045111506100c0908002085d15402083d4007003108240100c0c0c0c0c0d2500094000d04905080145a10f403170304003140c0700c074668002540d108501c071050303088a210448a41381298007220141099200440401c001310742981d8001041100c9 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 892491043 1250 892489793 892489799
    0x5010206061815030609060109060b0a020d03050703180b1009020f16020105161506121505040201050d020c240402010c080d09080a030f0c0503010b070b041b1d0a11040b13 75
    0x40140d170780078031884002080c281d0b1401e402304060b1011604001c01210f0280b102e1003d980d00015515082e01c814140440d1607920000d0840c01003107000351110441248a41c02c0c42400b070b91a9009005811845920003010f407101d901c00c003a40b0440f0b02c0b003a91403e041011621074600744600056407441450302e146841442840c2c2000d8404904040e600e0503515684540741d60740340d21902c0000d007101d010170b1140011b00e03140c5040c044a40801a41ca69494500281c03c6a00c50000c941e041c1c942540f085442c0d542d041841c503620108840c20a152610b84031088501480007107085c2d128a80c140c0d1521203030300c0d0360b5070f96070001c0d00100c400c207108030b031078007007076000188a003001e80345c2c0c000340c1d60340020148504041681900c08101c210f1041c01020001030010710491800c907491682c01501c40c81007a15146040c50701d1113040c260110070f1890703000c40812a03e1125418507464900400388880700d40700c01200c3d8040f40c10b0f11080380348082041108010b800004009485001e021a081044a50b6 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 892492293 1250 892491043 892491049
    0x12705062211030405160602070e07051b0d02030403020901090501150507030c0204020301151b0804051e090a0501030c0803031303030b040906050708012306040909050a0f1a0105010206061815 84
    0x2c2c0e4080b140d1386c1154114040d820703440c3c503541009064910040502d0b51400041000303e0902174040d02c10044000380800e00c0721000281042c100c8107140c100c3d40800c4440c2c40080d00c035082404124495039091000084140050299078140c800d080d102214185003000e05844990100900303c040c005000300d1a00582d0f9244040e60003451004031000c0810a0b210006106c01080c500080110814626030350101f00040241c506441c8152512a40301202540462201c4000c412081d841903a800800a984009401080c1201d215544070484a038641c12165120300080f074240e100c00303c1d901550b40100303110303420401c0a03541c040d00c0080c4400441d2a1340c41a100704945c000042423070000104640c0d0b44880028110656030104005081c240d0800034015104611032000200c4d203c0842d5014400d0074019507a0391503000c40020300802c114034020103010300040040d0440030324100001819400407846511a00c8024020303c02c1040c09080b2000091000d80b1450182c3c100c4d03041c15043d92 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 892493543 1250 892492293 892492297
    0x6011205040c0e0a02120615070606180501080d0203030c09060c010c02060f151c03051b070f0501080c0901030f06090906020927040f1109012705062211 67
    0x207000c0d1031003490607410940080250310f405407501c02a584100084440200e42c1580345402010031580e01d401840d600e0034400325405801000341a05283c00b81c00030343d98100c007000e441030510904090109a990320720507525405100e5403e800760304100005002c16640170b000707210462009041505080420594600311038040600c0c01c05a4403040621003812400d00030f0591081c03904818044d248110000700d08a03150b010414500002c0c400f24140070580114203035071980d034902000030548241501442c2c0d9401c51842640031640000c0d1b130100d00340d4400d03c00c80b4411a80760b0400c0d440c2400303d40046004050070800040e07901c0da00e01d80410441854000d00741c03400c0c003070300c00541c981c1a12020403000c24191404080020508088070310b04401542196500a070071000d10318100d82c40c1c2c1000c10345024134142070b41c4d2150710003001040001d00104035100304010030426030002c0e1074828500007200c3c400d403401980700440c0142d2402d504c034041d802e0f0401045900007c107021802540c5c004c60b035 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 892494793 1250 892493543 892493551
    0x7051f030b030703080d2f120a11160c0602061b03040c0f0605040608010b030412140405030a08210106120b01051e0912010203190b0102250614070c050906011205 71
    0x240351184070220b840f0b000c1030400d2806203400c4030002042000c103121903003039114001345100c03418250701c00100800e41d96400080c0e003500c155405a924102010055150412f00d41c0332201e92111000c042001440001c10900c0b40c0714003170344400d844040615440070758100510840302c804a400c00807034a056944038200080100c0e454054072281010340140c04080140c1105106820038030811010909400402203c4c039610306041c0b0050b404801407952034401d940250b40c01d4440c0c0c40010b420002e8010041c4401030645107480318040175030103004d42116080c0300da200020700711803c10b03401d04040c1e8422141000305041562074090194540441003424494450350850045081c2e0b6050800e0a00c1d40c8542c1c2d1000000c40c95844c000c20b00380c10752034040c600c40a0302c0d41c0e5030000300d00c264020803110504212504001102054900518908800714024500000d003140080c10303a034814031003918041d13a072022440f016030341010f051142034500144424104802c0c0102d800810185105060003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 892496043 1250 892494793 892494817
    0x160e190e0a0b01020a05210f0f04061101020307080708090f0105090a020301180f0b150d050d0f0c0503030c0c2113120201050d05040201120e010b0307051f030b03070308 74
    0x20358903114092804031000b0031200360554120501c600b00054010444190200344168030b1004400301034042c400a000c3c94200c5802d81000185090100303c094000e00100c17001e641d56400ca90800c4403505083c1c0c0810b55075800400da46a01003507805000b1080c1c0e941c03000c0f034802101c1b58658035915240c295202924034080326004004020250f04080c0031300c009003403007446144c07142103c0b55651711520b0100380000e41101e02680200703c9904250980c800b2400000f01f1858120041d410001d4542850303000b91030200f2215011210303540e0094045e0040190408007071410341c0d8070840c06003c0d90b8441b442000da6402106801d09500308200201c101c0d488032500344a45908242414007201c1d1515000100c2c801d003089240700050380d20408960b00b8000030311010640d5111840141e83c03034065219264500b504081e402e1028038015400850406402c408031189a540c03507040c8055100d81c02c0110084180b001000100c940c042c0d08450890900a0b0481c0c032125581c0d10766000035004490302c400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 892497293 1250 892496043 892496069
    0x6121211161e0506070b0c03040201120c030b19050d0605130b090303010f0807050904152909060901150f020f030d091b0602070501140909040c061205160e19 69
    0x3207441c002000c2c1d04041d02041e40d155181c03080c9910b0b03110714150300418641c000d100000010b02103900c51922920711000d6201c00b4018400c410f030019002e0302c521070a10b4010345564100250f0180e690007904201c03103020304811494483d540341e52010380f07030082c00700310001a025404030003c1d0300d4140c3c00384141240800745403070354141800c004c40070791294010130b1581d21110080c007885d600d12440d16000382d8080529010150701c6d01502c00900800d40700d070350a07254520040c0210300240d40c1210300300c000c01c84840860b55124000c2080781d440078001e8045d888000c420900c0f46030300510103048a02c0b454011901c043c000e20314136a203164031041c0300c0b19400352205ea002c0200003000c0190041e12a070b041c810760030541041802950741d9031a1048078100704886201c10515001c01045444511002d46800d10714a003070f0801e1201071906105e400c0001d055142126110021486018065080c80303c2c1c1030303520740020004642070401c200d8240c0c0d012082c50301d02d00d802030503019400700500c04450014 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 892498543 1250 892497293 892497329
    0xe0609070602120405220e011b020c01051903020f1c0b0f01170a020a11010f0209010e101407060b090f040b0106050703021c300612121116 61
    0x2810f092140c4a262540d14042c00148520394070840c031504041c14008801c510074418003218409030400da00040402e51804410000c0c02c03400c0c411102c1008110780803903144060200045030380b481054281080030720300c40c107041c8a43d842a001440050200f030111402c0c400e0001d04104440e0300031851411082c0d540d24061a1810001888250a00c0908040748921100b280b135001305440107003041480c83d4000782e5541c005006845807141c088a900082044071200941c0c0700007503001c5941c00e03011a0803001e6201d2289000c51071090600d1071580c40d4405803203120302c1030729107030046c4034215100ca0725040380e41055110448024401c0c100c1c20a8146142418208605d0307a0806800c444100300c010030003200481d400080544000c0d044c2e5400050b01d021641d0100c50019400c02d00d080c2101c0800e040c1c1d007803054020300d04d80269010860400000303948080d81d100302e081c02c0d8030090000103150a140002d40c012300251950020942c00d50b001101440c50700141a0055081401e22070726026107a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 892499793 1250 892498543 892498547
    0xf1305040f0504120e03070807030b061e13180807061e0204050f06220b070309050303040501170703093f0824150a0815060301180e06090706 62
    0x12201d5441c41e000c10440c03400e182e03c41c0ea103400007501044061081002c142503441d1030401104c1c004000010503a41c1c9240c4034503201216400c256820741c410901c1509481c001030708424060300185000700305000701d170b01c0d0b201034202400d4105462a40700715070076803520215111170000d003038280c801c010000b43d40400f01241803c2881500126007000d00c144401e00458030340d00c0c10007040300d81c102d58494545a040f414800042c2140c403031f0148401400c00005024814900a0204544070b500c810000f01e03118001d142e600d015510035580002d9803203640e001030640c4804120b81040042c035000c12560400e481e13190401c00c3e0440195580c5040041d5940c3c610711071007800c10143c2640b10401d03000e450080004001041c081c203261896240110800d110b0f803041d1a850201550250011418031103e4049005540005900030007184d0701000041424400c09015000c410700180b0303039802d603420214068bd40d001c4200d01040306642d1120f0340000500d040009520840e11000103243c2c0605000c00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 892501043 1250 892499793 892499801
    0x21e01090506010923190b0402040302100f0f0f020d1409030615040b0d1a091e01020904061502071a07051c02150405120306010c062405121c050f130504 67
    0x80c1403140c545c07020500041e0304070320389000710f041d5210300c02164030100440024001e125503070009622080c2420390900a541001c0300c9401c142c95501c07155140085441c007554042c9002d03038400010382021106040c035a020b0504000d182144c1403065040010341800b280c0340040a076480111030701c0700303100940070b4500380c00307040d2010005031075040c1394008a951300f0500f081003518640d40c0301d14910001f5038404040200c607034101000c00c00b20f044071031140d0f100c6000398002d0320468056800d211010800f4000c0070041c0d06840b40b203a00400b215031601241000c000c240403c0c03034010034010018800802e03020041e484030300300441600900440c2135100a4680030b028000d5403107403008841048080751020030300d411214140c0441c42d81e280d440b400100d982034501d1100504031881c20603065120110007c5100c0d20143d2002c15040090300c0c2d10401c4548a040c4920a200d41c1c42400207030614080000f05081c0c100080c1071145c03c091144d0162280761300010003c0298a41c420030070440e500c0c150003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 892502293 1250 892501043 892501091
    0x1080f030909160e0607140c06040803220b22091104030f050111030a090203010b0411041202060c011e1a0604030204020a110615091501021e010905060109 68
    0x2004629184140c4049414000010001800d002c80b071580c4480c4507014070020701d03080000803c0c10b170340d407142881c24440ba006001c001c0c1c0e55911078040c0e00105c0c0e007000011142900e5147c4000c504280e01004030369048211461510318000c0c01c00c5001440c2254003001c0c1c05155106000c13440d007800e01c03003940203c40043d0350040c03440307034100b801e510407080560003102e0949411400800d000015400c140d40541410407a20510340340000c00c0010559071a4024440705100b00e00901a008a5804200070398000e90010046070310b0400003001a85139800c52072002a1003e0b144d076040041081d000b03421502441000162440720090b16600740840d44680c4807070010b145251290001c6420100f22180a00d000084c0902d90019010303080ca03000c2c07641c84d2400c458680880b0030919114208822210341524000c2c000d00405000c9643c004403039480305900078040e4003c11395400851007125100031920700040042d50380d02201c0000c01c0d402e000d1203001e007603118004a2201100b22a000c140d1a07114 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 892503543 1250 892502293 892502323
    0x2040605090f310b060304030e010f030504321014010f0602030d05150d050c010e0a0b0f03040f0f0c060f08090d0f1713061401180207030908150108 65
    0x103500e0f0050240b110741e00e004800c405090312180800c0000307000008001c44a00c00f0340c000408000c102c05c140c3e01a1640e884240d080e03840c80c801120075442074007550802e842c01000c66072030000134036004800c1c0d10a540400000800d05403031281380380b4103a003091100b0340c031000051b0f00c0c6c03228188010182a1918010b041c0240b0390042c0a16006000b0344078016806500881c5071610003196054403042d8924040e040010310a11200d04249003055a66088c200c00c1c0c2e01054030201e0090051929075440011550f107600102e02e002c2601e4900304041d400100704684004800300354802148801d4a40840c0d9889112034034201410100050081c034500c20000040003121400c01010500110b41110b40c40c03c1401c1000758103245940030ba80081480c0c4503208508041c0c1c3c10001c582c0c3c000840850740c64040c000412080000400d0a01c81080900941d1501d0211105464408120f60700400400e03000b07190411205442d00301c1c003400c292201202140030318403000103102c0302c0014400094048061 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 892504793 1250 892503543 892503559
    0x40207060207140316083708011e03060b1c060b0a0504110909040c080d03140a060b031f050a0b0a0206180a080c03130e0108100c140313020402040605090f 68
    0x880d00e10036403200890004012180110303400d0341d1709132a840c10804181c07580d6100d51548942035402c0f4403629421f5420070008603600c0001074901000340404841c1c61480403038500300c50450f110035003d02541c0d40b42c40c1d0007140f8801d414000c402d903984030684843c450407011540440d16001c1110700c034403507041a03114520340481001031001e40f10440b8041d1100365184d9803160384e14181800c40d03a5050f80311904500440701d400c4041a031507130068203035400d03000d9800a180c8508182500301c640c98061003004003410408201740c001c0c4144440204115009210072103500c0341c0104854641c20303449000901400f003103000646070140306035584165002c1103003403420b9035003082d5982c0300c0304008090580000014454895142482201c40c0740c100240e0040c2c40d581e588811400b0a01700f486800c65070b008008410340501841e014103d1041813681d03840203070100300402050f0b03661014100e9014501c0001c0f200c401601e40b400508010046e5444003501d42281500707111140b640703004024460040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 892506043 1250 892504793 892504807
    0x92904110403110a080303071701080c0d171e04060f0e0f01030f0b120a0b0f07021e0109050601033f030504020307030c0b07170a1e0e0402070602071403 67
    0x4060307604494010a12081050400012580e82c940d590480c2413140000010000e006030041840d100c46040305503454880c1c1e0b6603030302c5241c66414048000e9400003030055050040b904141c8103104100000281502c0c00c145001d59040c00184842e207411807010100e420000503030003096080310345880d414044036444401c0d0000d04141103ca103405e040c1582c0e080701c01200400e0f41d01100c600d20002d00542080c007000048141c0d03903a080c2208440c2c0c00704510009801d5000d0071740c07542c044e08894005002d40400f19500380c400a034400c0c0c01c05110365860f2004404108100a440c0c001d60003040034040180010792898034a10502070061115029031088299007840c01d642254880340718900015281c440c0d1000905146043d440606800d500c0c00010544401f900020400a4814071140c3d09400300602c1c46886806511034460124030700a4001301c50b1040b0961410ba0311465140c91441d21030754100040032a0400441940c0b0164003051000030003602940700d000d039041c804015410014 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 892507293 1250 892506043 892506071
    0xb1e160e041517100906020c06010501050f071101050f1b010f0b0105040b0d1b0509040f230402060f0a090906050a1a0706060321020606010807020c0613092904 70
    0x74483c4612951051109106100c02c1c3d41485030318070540c0d2408041c008207501d400c00402941080481040d58003941000080c90f42c010001c0340d1040e9000080113081280d55200e00317034008601c1a1890510500304000b68007089902d0007000704841801040f050285003403811070840d405d440c449041c030b41c5803003540b15940c0c0c0c0103419102120071003114070f40d580700740603101c01c0940600041d003240d0032101507180a24a400101604402009840400c5a10f445c080d110050f100080c902c4100899040200f5501e13084440b811075002d40003414051511081c0224200d4581c001c003500000910202018132802501d0b0296800501d012250a00ba542c02d2503040c0c202d42d40c4c1d11100c10280725000a200781001040c2d00000010368001d160081840c0306000b034903011800c2c290681005019050000f044c2d9800b42c20503e02850040e4000c14001034200c5c24407a45900020841034016502c9100145240e81e44c00b4180d00821070070801001914183c002090b201e820114041c8524102442101401 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 892508543 1250 892507293 892507331
    0x619270807090b0f04020c06150d0b0601050d150801060515041d07110d03020703111f0902030a060606051c0c140d020715021c060b070b1e160e04 64
    0x120b500d0b000207544403a40c1c0029443c2c58080c09541e40050020031412004600401c07090f104001e000021035071945450204003201070030040003881c9440c86d501003040d6511800c0504080102c039200041c560070a1403043c944101c0740d6000c1c81e07040e0b443d80c1c410b0107e03082c50800345c404180340c41c910509143c00c040400c08480c080308140f001d50100d520004020f1441a0144404c640910041d111142100207008010394041c24007640807500c1c40c500d10540780c2c1d00242501c045600348400000240ca8030704400003a090700c3e0300981c0c2c9885100d100130082070b19441001c00034030564071402e075103603004080443c011101e0034400100d1458011000405600000d049034140322031004170f0b030b58040c1d5204100090041b00310240c40d000b0001480c211091040d40188074003e6288401400b48011003070b142d09a542d1401602d000030000e015041c006a0354084032074020304016407410300d90403c0581003401c600101c0707207083c0b0710b200001c2e1281e00302c2e0802c1c0c4007051804140c405215524000311000408 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 892509793 1250 892508543 892508549
    0x516140321040816020a09050a050f090d08010302012102030c0705150403020a151e0e100b1e120a050102090f092503060b1b071e12020619270807 64
    0x1308981405100c01c6544400310000908174180b070030045420032000003001050125204201d4070440000f1a09680c2c0008004088603600d55500700f6503801c0d9401150340050407601c1380f80c0008100c805145046c51070010718403411500000c01c0c4c80300e40780c0c107047c2d00d020740b6080f80e14007171360b482d50500001c01e9000c5111260300380c00030003086451074403000060050034007450188081c1140d20000300d95805a8008100041f1400304a80c01a102c180800c01100d00d08010b250f840b00a4108101224084107a8140d40000003091007035103c641241603801c103080a2400c96231340e58002881041c0c1d00d0100d081d83c1c01002c083e500d104440c5855141100c0f4140706085e102000101c440100360324a101c1d82140001e07210382851251550080340301c480c440022005101d21a00a4000101e4140e00040441500b440300307203442d80c0c0035454040051a81c5648101c00d80e007008080101c4110b40e01d05802840e60501107540b0964140151200c1044050848040121450820350104901c6000040440a17 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 892511043 1250 892509793 892509817
    0x7260f03150609100305060612040f0210090b0a0c05010b0d05210306091512010e071a0309071e050402041410032022090204030c08070303050a05161403210408 70
    0x140d48507040000e1090040690241270140500200002c0000f44429202c42c1c500c00d503141d4049414130700c8266040c60050081c3d5580721400d0225801c1984200c1203032510354040e50000640c08461008101814202d103400d070f40980c0b1040c21040307580c0305c42c3c01c20611f4884015006042d800c0c28800502c0c0d04d60b010b4000c40080111b80380325402c07959981300f01100f91a407031000304600c031590741082e603d402d803d105400d80d1241c18141702c8103e005910440340b0442190015020207070400982c2141080d51064174040d040f41510301098a4483d0301c02000605800c0413003603800c5807048100202940011400800c2504100c00b01d0001d002180c1100c0340444c42201850300c58581a00c0d0a000004501040b0101700302d980e8000352403005030f8000d1050380e00604c2101d64464407012255520700c1248030050005d1030800100c00000e01c554041d001580c22500340300161001900da112071802610041c025a8100103801c070b001d00d100d5100003104a03814015282c0c0741c80d00e600d4130b07003103401120241c10b1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 892512293 1250 892511043 892511051
    0x602030f030a0c18090e010b0d050c0d050f120702040c020a03140306040209041406030601051503043002010f0b010309030509091e0a050108011104030807260f031506091003 76
    0x442601440c40f02d504007010301340b010340c20f0356100c08920241036500c0201d00c0710752030b012910102d401c040ca140800541c10800805200b9454001d005d0003105a070b0307054030107000b0003208465240c0706124100038014010241e03a124842801008210b4000c0100271040d542305403000c1000035000345038810340340030320703645940c690751210082400380c03003000c040d954801d02d404422000c01902e841590700402e003c0c0d040390708aa880344240700498111200e0202101c00500015001a201d020800f20100b15140b0744054100e08440415501201c001c0440150b5100d031012240040c261181ca4001c13502460280456981c0740c60242c142c0c42103001c924001d280002c0041c044006941d04c0d509030050088002d21549040340c2c0b004005c1c4400c1c0200d600c0341d400d00c00410161650103041d142a031b80c000d00302c81d1500050707649544041194002e40c0c3d4503c4402c0c030f00300013011402006803050500980c1110380d203152081040c0e01a160341040e0a12800060000890030f07128049a03903415046820b0000d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 892513543 1250 892512293 892512311
    0x6110d03050c0c0a0305030406060905190506030a0f23030a05250b071d06040302010512040203011e0c020f0f07030803040807200f01080c030a0914060915010602030f030a 75
    0x31019103c1c44200201c9031182c060f1884c00c04d40c3c854021407256004410400c4070544400d00c040030b80c0d10075510600600e04005100650010940c486a00002d0080441e10700e103409a0ba00c00d11900548016121085481c602c9040c00c0c0c0201118814455004050f41c60000c111502910714041c5260003004400001c0d21f4111b007803440085c0448403604107907405844c0c684020018646040201e4007001140129204510390500c501550203403030f8140c44843c02c10058030300f8043d00d504010400e80e81513485040080082d00016054410f4403162240072070010111b10029240c250511145003244c0d00510000b82c4902d03020908006030383e030005103d44e90740c449061407015809540e4000d4020300644240204002a00124a240c03000981d2030340d201034400b1006580384002150003c420307001c1000080c185007120381c404100184966500d000e203101020b501c0c0d1601d04100d99009107544a2440175180002c048031190050500707100a51900c5280300544045010280a48000a4035601c5c04 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 892514793 1250 892513543 892513561
    0x5190e1e03070e0f0417070c0603020306030a060603142a0d03021c051809061f03090503120a14040812130204020c0a0c0b070506191103040309030c06110d0305 70
    0x2500034070300000f00e844281032180b50854880c1c2c054a0441d03248081202d02d400b1001d1050035900c0084d000054103291500e002d2003940a5030004008a03414010125920000f07507045c40b900e8041c60003403d01158075102e03031031014584081062908182241203203800100d80c0d0b91a00c4070089882030b900070460007841d1400b43e02d031030910f00d0b5565a0440882c0310040710342d881790240c03443c00c1e070328408140c22508100501c1f030041d100780d07103480d0000c1114060382950001c039203840414880700d180000b0303154015101d0a09580005280340483c541150601000380c010307009000d212501950216514205036943e0740fa030380701e00032414600e201c08200260554500c1c00368511304c41d402901c01d40d0788070859052203403104100742c0300329224288241c01059441c1000c2c10745a41c20b90120090070591129502c40c006080d651140d81d24650b280c1400e000c01e42d81010107107004500c6034680500d010700703601d0510228291500008200020f002c03132907c03800000078132070b00d00f5060327070800040e961030720320314 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 892516043 1250 892514793 892514803
    0x509180705030601180615120c180e0105090106020102211f0909050f19031d041509050603010207080307180b0f2d250b0705190e1e03 59
    0x4150b40c10300841c0b000044c040e410340110f070000000300d101006080c2d285c502106181104d00c8043d40000c1701085009514101680189400f1a450620380310050160b03000c4240744c0700580000d41514443c1e00104024109a25514050113040c0002d5080a440065140c0c0311210005403541c03030800680800c2040314150942c101240243c400510880d0f2110060710151000d404115001d20070140b084842c0c1c1401b007001019071900881403c40e165498030308854800c0040706030302403500d886001c02c00c59940c1d482600d010000110000c0e980b5840c1c000b507841120001041c05020340d0040058600050300e100403694890708905260001c102d002c11011429800d5070401d02c03003000001003510b00980c00c14060880041c03040c1c03e101040030451075030070602082a040411040d828015141c03480c03d5040315111544500400703006055907601d81070100380b4180c0d03a01000c100001074402c113074401100d044d03a448045041003a00c8e40e4a40022508100e00d04111740d400162142201c10b4540c1e007400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 892517293 1250 892516043 892516049
    0x6090c07021c150e030904110405030d0c03111504080304050a15020417121b030c0304090603152315030a060b0f01081e070912030905090c0405091807 66
    0x9054812400000c606403525800000f500d00c0700d007020102195031200e000700548107000c1005075040916040a10000c0c0400ca445d45026580a01c030208d02e40c0c42c20007a6200d150401c0d40d5094040e013490501404c2e1a03024000050190008a0020741c1141e80f0900150003d501c00102652030b83d403400c2840c10301c840c2c101d006050340d0300310501d001c1011064000c0c0007511485900c080c180d031010350700079541707141803c81059114000d00032007801c100c2c030002d000141ca03006001ea928003026120001e04552240d0402031940f59209814814080305420f07000d80400340c49030400c40020034603901c441d250700c00c90f0340c9804451100c000903c0e000c1c292001c0c0d0300190010702102e154503080c0c90564058504041203d010308242144005550710400d001c60082400d014900010880c1003505c202002d401040d040500514810000b008031030301d450707904404e0190b515100103a04240401100c6030028000c246603600500c0309010699404072010b40242958441c119030415442c1d40c1030606040b0741c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 892518543 1250 892517293 892517299
    0x140604030e040f09241b020607020d0c050c1002120f070b07030c0813080412050f010501140a09021305040507050318060f040213090606120c090b010806090c0702 71
    0x5000816400c140c01c00741e4020304840500041d64040540800c032240400c01500c00007089049448404201c20210744113440300c8800701d29400102c0035100307010890300d0030340d0051780007038100003007a41d05000d42c10b80034040d0b181060700303012142c41701995400d0348010f1314422221301e00d040b05898020450001c0183c0c00c04003160301c601ca000a0707000c5540040f00e00b0340c0c0c0c0711500000100d041d0700c6032242d1212138002c1c0d03c9403625500d800a021030300440b904411110140300f004007144221600c02d181c2d0926101e00000c103012108412202e00791031043e1300a5100002c0085c00d00b425649018040003580d01c0070000580780c0c880d0840d45411f0180d19485141c22918003818042c440c0c1e40400207500c980e0281e00400e14951003c4181680d5042c100c690040584110b404a0700602e03018170100341c0580c4907513000c95039034415150704080b6015a44034203406000e501480d03040013442e489000041102c82d4040011503000c1e400a0400440100164400c201d03201c00103031007080e41402c0e40c0000d5000707 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 892519793 1250 892518543 892518553
    0x602150a02130f080a020102010f050106171e0406050103021e03032515050103030206100503101d0d031d070305150601050c0601060206010906230405070e031906050c0c07030201050714 81
    0x91151680744c805441c011b038019420002c45407c8031001b801001d0488400790341d0107840b0200c9107540240810003600b003d1005200c2c0c42480f0000032000200350280b40540b1001820f549144100310040c0f1444000792070800e00030b2445072142d41d020064035031031041c00c3c020343c05608984454480900520350028021803941ca5000c582c43c41560209060ba0320035000c8541a03103500014a040c90741c54410b0503417561007003c0100442c111a00240242054060401034003951106d1603418401040342c0c00d030010b0b9407041c0109105400e604e00c8004840000d018059841c11502c0307443d01c540201100201c3d2504010209110383d100d141151a0700700038000b81c804a50b180e5100a48505003071041c520300c2410440c01041160544c000842070101100d00344050442e484140405000d004003c00107000341e0704040322a6840500c004c104036640042d409404103540e00e8120110380c409800401c12617010710102c13000800c0041c10100b030720380900781103468030803074a040c426070800001e07010818010 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 892521043 1250 892519793 892519799
    0x40e0f1b01230a0305010501230a1205040609020f060c030928031a0a0b0f13150803041a0c07170109081c0c0201050907030213020714030a090602150a02130f 69
    0x2c0034014000c0024555010701513640d8502c0110f9018008001c0a40074a40c004800707942d1204400080800c0416418100f480c0b4035000658800c81c0c00443c1c0556241d80c41d2000300046140c1103000c1d5007200d0b0101c899a05046071116210360301d002d00c2000d180200391035100300110000c040340f80c821220300081e045602c2c81d2686044898540350f604001c41d12440304010030403214560141c4c0980c1c4d540588440d034110b400e0783c00c0000d04003200c0500c05401342c0d603900c002c41400d4441c035200c0c05000400c00850342c8626106171100100c0030b00d03861380480c400601c0a241e80316000b041c80c00032640d0790056003601c00021485c041c010071120b00d0040c80004c0014541c0d48182c7d0481c00c40095000c020800c1001150a00c0240d007600d00031501c0c80c241750048801400186410550482e020403000030050900ba620303910884003815651615546600110354001426409880341003d8a0b491019103010803103041c000b01c5503a0080c000200064011844040e04201d45150000411a00303410300034851f6 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 892522293 1250 892521043 892521107
    0x40f0c0203130b070b150d02040606090311060c19052b02160b09010f050d0612020a1d070c020612011e06050f070f08040803040e0105040e0f1b01 64
    0x44026803002e0480a8104005000d496032400d550309a038006403441040d81e103949203000384101c0c140c0b0865000c07070b0001c4804c02586941c8111406030a154803402142420b5003441d2480300748480b0450301c9920104a101e56065021a085070310079800050a41c3c250444d24182d0f0070b00988075111501100b6141038446030501d01b00d40b4060348a00c0e81c0a50702076044c0c10034401144846805100d082030800c10003141c0d5544a035084c10b03103012883c40c04508261011481c01c003a101039a0086944400001e03449041d40380134030b1170f80000e0501d460101e80802c141d1469400c03e0300014500024441e01c40e828506645405044071503280b00c0c150003000c59038643d0101e61842042070300003807255440f5080814904c6c0034404540c2c150700e03858141d50603c038040d034a45190350307112070040307440c51824400080c1c0d4a00030000b61015101c40012401990706040c1408119901c3c9003407032226501283c0c0c0046911004160130118000c40c545c2c40600c00d41c03a000680304c11492840c40c0f01510b01084030911288 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 892523543 1250 892522293 892522297
    0x80702090c250c1202031e070b0414090603150703150b0c010501060f1d060c150c1c0203010b0d0504020319080306090708100e04060f0608031c060f09020306040f0c0203 74
    0x54443e01420991a444064030301314107006020003505035010f4483c8400000301c00c003a06105804c00d0341214030b07058135481441746541299004440a00004410205c00e19081200d194403550a030001e00f0800c0302c07155a00f03280c2d85c001c0c0c481420705a4800410224510380368100015283c01400759580300264030080d40203100034403c850025092444a00900d403041100e0b842000107032040e548e000b0b8910081003500d5204401e5504248261070b0048030403011004414428100303540140d4962100038551030014404000146000b0310406c018000c00c4655404d4030882200d011000519564902c00b203868410030004480118150030305036401c11004a000350700c58882a60303200c640d502c80fa0016200000141e0341c41079404c201c818140f0007031a2030f030301c1107611a019140200700b1441c4000800100c075481d4200b01219000020346c01640900e0005000221015074020801d0515000301e103180e490341d034000d0482c0640c000000c100381d40e031a9040b0f40c0112115a034100110004424065075a07 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 892524793 1250 892523543 892523617
    0xa06031a071202041a0318071e080703151a040618060914060105070c030c1502010515030c010e010201060503011505100804030c1101031e02030a0e0703080702090c 72
    0x2c075082015000400786000f9242101d01d00244104101d40ca60390802c8142c000400300450803c0c0710b607e00c00000d0b0308110f044020b00218850400311001480c54500c4402d00350810381496021160400004208401a0788401c1300b280b400201c80306181e800042c6c0b04901c11520b540181001808180741601407450f042d028071000c6c04000c11035441f8000401d661001015091640d511000a0660750244008004481c031030011010f06603225070301d111100742140c1000841504080d40d07010001d40910441d038108050840e200c4d112044500001d130b0b03401c0e0821640b810028a840c042c0c1c40742e4001d41055014100c014001e1040305a0803041081c03c05107403003198400c030303411080c00a0309402104540d00803905561480040b0350f49886126507014480310060406035550303c2e012648003c2da0741c007100f4600101c00540d0300e00f0822206401c0e80c5901f95501ca81c1e4011000800c00508070f902100c9e022941a510001d20341e40c1c0300c404000320b020b4100d200c16a051070084880300464014599199 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 892526043 1250 892524793 892524797
    0x1b04060906050a03110109080f060106140309060106320c010c140f07020a150f02070f05030309100513121506031104050a020423091e07080a06031a07 66
    0x50558031500390058510521455400129440090003c52015040003249034010304080603031503604c800c481d14000c8052004901d5030044001030102503405010400b0400d01ca990550840c101171078602d464160620980060108000c460070a20103010aa00503004d50642c00c01200600413140c00202da01003d240041e951804085c008070a008410403c1944a0400344a040100e6108294196488441e041e13a1015070b4440015000040f000100060200da07507401d10b0103290300c1c0d000fa1501d60740c1d800440c80c003c4c1860f03013406103072000401d907000700f0b03000c46400c0c815000221003600c81c1e04c03072a0041c2042c20345503240402c503020804031144800d8131484a60f544900500502d408945180c00010240d002d400000107980c5000e0300500d4100540850061500c3d0744c403075088603020748200346603021041203c60066240b505240e85940218043c0c14170801600410982c2c2410310000d201c502841211740201d40c083c580d544c400401386a001051a40004031a68403007a1140100e503c040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 892527293 1250 892526043 892526051
    0x3160e011806020106031b030503180103181506050a14010315090921020102310503030a18090b01020c0d03031b080a051506190203130905090f0307030e10111b04 71
    0x15900700502c01f86011640c10601950a0013466012801c000c14100000c03410507458403240d0b91012001061544401d00c00c0b818070600ac1d030345113010029102540e0200d4406c8100d200304024118417080300b100e00c0c03c02403800052182da10000d0810300300d81a08400a0300340350002404c20408000d0b000c20501049403450054000446800c1303090f80301f4503040386a8030202e140c01c3d0113200c80c90680150204c1080941c1e40c00c032619140468516001401c1850010340b4045552540b010149914009410184001e002781840c0300000307581c070040d0350801c5004070064510002450310951224490202140302c0b4212034070b0070b00d40201001d40a88505c245c00380b4110218504c21200c040059045201420140c00c040b0080a115040c0c0400007e40341540800c011144c101100940f04802070180080d0025690904021651078000d03071100300c4106a10801c1000082a01700003102c0c0060000c40315441c4641c0c40c980100ca82c0e81d2020a400054414040b0f0b90701a0704484001401041c800c0d0740c200 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 892528543 1250 892527293 892527323
    0x60903051209010f0c14010f05060a061806050c070b040305011409010509150a0605040203090703060b151c02070b04050f06060114190c150f0b0603160e01180602010603 74
    0xc80e02c0740320306280c0400d80c50072103024204c0c01207112444c8140200d003407681c0c400701740040500351400f849105600c540e4400c100001845c019501ca00604028907000b80c000a40602210811203540500010b114000c01c041191000400908001c0d20417078402c90740f039903580c0ca4898040c004100c20007900e40520400031340109414400c0c180300d18011030042c00302c10380a172150510414080c0511882e6501c452007c100d41e115400250700490000780240320710791450034203200325085045201d206294030000c0911081e50013094512070003080981110103012a40c61000911841d00001e09181c81c00c2c1c200704c03d110011561400c09059001a02d8065586200450751900d900700100502d15040c0480142c01444180350f407003458160800c0c5420403040d440d107508500c3c2401c8820026500c44271811000e00f200d00440070554401e440d42801d500b0411206001c0b65000d50142c81000003080d603e0a690703200703643e9050318003641440401e103a9169200240a04003502042e22044070b40b10700d032 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 892529793 1250 892528543 892528573
    0x30d0f031b08040210440f28090f020a2103030905070f030503040314070b0d0f200c07120b07080c21060111070501020c010507021906090305 62
    0x1a80c52482d54892a140e55180e00300501a1100c201000800c40f510a501084003034000048078168411806407803040300f03151801c0d105c000c82042c4002a079054100380000d10302c2010029802810401c10071603112070b9070980b0301d1000758001c28a21810700700480c52003030001ea01c160070740503402659182d901e151120a07400413103a41c440c0c00d551540300e01200d400424801e0b401403655a200c0c07401d48417003507035510840d030003107000790426030b03c5800002d0200200180c01e0001d407403c0f00c0c043c000d4240300c1d01e010308014181c00340b001c0d068041750b1204040903030528590300c000c020a5020070983c00f50140020011041d802c0101c00c2125442071081c0410423a0456440c0e84149134403441030350361a0f9031003004841c003401c02740c03981c058114144540341c49083c01800c1850902e64039003a0002d5840c00000040ca01417980314003542035009000180b1569a020407040c80c05a420300388a80c0d1a4101e10108201c01c214032030b621a10146100042045075000042e070040b80d003e48100c80707802d0054080 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 892531043 1250 892529793 892529831
    0x30c0301031208010302091807050315070906030b060403030804140d0509100e061801020a0605090312010b09010923030304090f051f0311060903030315130c02071e05030d0f03 77
    0x6c1d50290000c000102d0000421800319840807086c419145081c2ea1040401d1511411822600c1c1c030940c01010050150317800070543c002050180350a100c6010003402080883c4105c0c00082c080101c40e400040611a0b01100c0d40805000a0111501d2804140d0020610f4118007002031081c0c10041031205964810100b10180d548014803032031034079542d030f405100d000041c440b2941c190700a003508440441c0c0d00e445001c1c400da00356000385903141c007010b00410510301c050300300c00811641071000328407a0b640038114030240c40840c05000b002c00c0e0000c1c1d905d245204402e058981c94400018089581130098210b241000d0a4650034025500c0c1e0740806104110810720300e610300c1c041c40c40100007003410182c18020480d400340483d03283c9600c043c0401d08540c000c8444d00211120380514440f5810301e80500c20315208541010040d18401c0c01000791541c03003034400c5110f561111450307640c89102d07604291006020060444150303410150300604203d0781a52071074003080c9845245410000d4041c2c0c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 892532293 1250 892531043 892531049
    0x70810060e03060105060d230411040204080a0308040201200f060f040206070803070c02180402010807140702090c1902070f06020c150a091e09270323030c030103120801 74
    0x3d070003103a080400344900c54009501b60302c0010b031503400c022103003103001d12145802016034402d04214034080c00c021a80e00d100f6003c49009502c10001044003010100340c58074196414944030031a07407034038001201d0320550f050881d1441030030b21940c3d901d0002d00007145000c01d21444296401c070f54440070f030840f041c00d040710081e400c503404100c1c85d000200f0850045070b103c41c240c105120b03071003055000318151900e01c1e022603400f009040c0074441550380082034142c0c40051031618001e050300c003001c1e2003107500907120f00a008000d000e01155803803034003900355a43d00b184144076140007606100c00075552011807161502d11500e03104081017407880400c10940c24040a08020510090480d25140700e900034040e1034100025060007040344103401300001c0268180764141400a0b00781116081150b0081441200d003500d41003012005020615510a6458140c1002008140007004d210090b0b213400f911140a12000004c200d508406500030394162400b4005a6100806442c02034481003802c2c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 892533543 1250 892532293 892532299
    0x112107140f1908161a130c26150612030702060a0e060702030d0305060a121104242714010e0603010902120703140a0804061412070810060e 61
    0x2040403031084100340c40100009129551161402c1c0413201040140300d240e180c1220700b030030300f400c001c850300000c0c0e1419501300c0702c046a00c804103403841c4c0c1c51040c6d40c080c52160700321505840c1d030007148004011010460607003000c000e50340440f511000510050004654151003103a2143e07106200442c00000c0c0c90035140c0c0034054610f400c228040c1a0742c0000f1485031160300c0740c010850303080180c600f07212643c80c00c0305584000c59141000703000c1220891480d04407010921354100c2170000b09075109208406114159400100c0c04411002014000001031006244d422071034400241d040e45040b42664109001c6428528a91266601010b0390700c4c401808080c003a9180040c406070800c2c008117500880024000a41c000d46035000c5890b102c01030a500d82c2c141c02c5400100180f0500213803151124100e04d0252041c1c1c06030b6039030400d19000d00e01820381000013015a02c04803005100c103d41c032101420181050301d1070102401041c101013110004070000c40d00e0000a0003078018000040000001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 892534793 1250 892533543 892533553
    0x90c020d0c080711270105011817160e07090b18121f0501172a04020702090a0e120a1704081216020f060412112107140f 53
    0x20388541a843d0402c4100b13a900051240c103002d955950b110309105100c4a85413180601c110301d0700130a2240310164000741c180900e1207580315a05000c0c0c00420141c40340120001306000842515a2504440c1484041181501407001c680c00c43c10f124010b10030b00039036513460000394a030f10068200d8007400d40c0c05144500010302035100361a003103000d00c010700182e0049401c074007040f4202152000100903080e4900b9610f80060001c1d6481e4856007806601d480300920300d15001c01c1c4407009034400c0e00c1d420030030601e075160804019501c075011560000e8004107804001e05000034100014228000d140031313284210100b0016a405120503030b0121300d040c0d00c4420f065220510030040e6014001c1003151041400c00851003881a1881c3e8580620651048002c100c401c0010103450400c20233030101c0d655110341d0030000003078a45d02c0148041c04040c60a00d9220062003482880d0030400b1a00001ca06170500034000e580070b179440074100490050500e18051030700c80000588619882ca8004d50399000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 892536043 1250 892534793 892534817
    0xf031821070b07020f01020d062907140712030815040e030a0f12090623010f15020a0c03060c0e15090d0f05010e0607171614120c04090c020d 62
    0x740290342076010a550040d03601907031740301c01160308aa0080c500070040320341e0340c8402e000d82e140d09a01e403540b4000c0c3c0400382003031401891411030f06000304580186400150885825103000c2480002d0080803c1d0200c001204201c0c90098081a021191000e8443d02e1001014441c9410300403140600031403030181d480c100d0b1552084600e0b580030b902c031505000a00f200d42c00c10443d544107841006004800000300d1203501c1c42c8070030301441d0b02d001082d010940c40c00144141110400380c1c0045900302080d9451840014005908010b15214050511204204000240b2040390026046a1910342c1c48900c0c074520340c1c00700700d502c4459543c09240b204041c80000b4550514144551200d03004210181190303186585690950b148008003002503006038003032210b80d54002c2c0c1c20780c1400a042d03400e44100c0c80c18604840c85200300344407041c100f000141a03002c413103620350115600c8400034443c00f81c81c0d05d80141803007480d6009100b0150342c1890310001a540740e20100b20781800d002541e5903000c910030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 892537293 1250 892536043 892536053
    0xa0c030803060f09010306090b011a1206010e0306070e0405010621020706090c0602010902090c0918100819050f030a020a0303090809040906090201030509060601091a0f03182107 78
    0xc0245441e42040d40e5818038200c42e43d45440141c0254416480402da80b9102d02c0c002746404d02c1030b48460141038200030700744c078071003915000d0f5010080441e0540d50f4580c3c800300101c410200680625405000b83c40c00c0c001000d92040910605981c240c0b81844140d9036014200c41140c96540040312107800300180c081c10340c9071500140900790142d40c000c9140109900d0710801000380781d00000260b07544490791002c40c1412001d0301c2e131040400003154185081403000c20600d0b41c0360742290891905100014011380b440c1c4502d600988417038412100c0c2c081520800281c0c602c10074034241c4191051018403042d11000100b140c00c03c1d009580501404011554260302a03c2401c1041310211400d00c8400038640340c902c00d101d8510701800012500f864140001341c101c80c2c000c1c0041031960001810401d607031741c100b6503079400c5403258401c240b440114240514107601500c0340ca42c0c4a84000403d100e9049085180001c2040c412001c0c2c8602d2540004660f029881c65551003148140034070006010907 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 892538543 1250 892537293 892537297
    0x31b04181812020609060703020f09120f2d0106080706111f02030711010905071203020a020414010303080903090f04090203011e150503120f03130804030c0e07020a0c0308 75
    0x40d01d0880850441811961503911500300b04805100583c007a10402400c410200011a00f01c0c0711420210701c0e102c47c904183d02540b1880400c10301525148018182480d000c003c94040f4003550819203902014144031401c0c19070400e0060400140c988444000c0da02040c0710f00401c8640f080000c11025240c00000d4640040405494441e4024940c00395a05440d440c51600013500b40c0c40d00594910700700c60003a100c11070541003068560701d004c0d034140c0007440c00202c11082d25100480e40850310810b2074224030f0310b230307181c1c1009400078102035800031180c2003400250b041c0e038460303200c4074415038646048640e40c0c0030301c1d016540c0c8443c4005042105003028ad1060018500240001c40c19070f848606480d00d44404424402032160380e15a09507100c0503039440ca00c0030b85021405042015400000c0769098000c1c00180307400414000041510301c005078407107030301d5264040b10319500c0e00d079642000100d41030b1700d12070b581c0c4050341d000000e01300a20100c1c2c624400f07a4440113048050f420341d210041c1d50303 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 892539793 1250 892538543 892538561
    0x132060a0c0f060603050105010f06050c120d020c0a050303060f24090a0e0708011a0c0c0f03010204050d050313151e1808100614090c160204020f031b0418 68
    0x10380410410400483d0b070600411014501907400401e1070752400d50b114030b8024141d0300c4541041418402c8000c810000300307020302070581040690b5121100741d8813880091240c0ca001c11030b1440f81111903010407002202a40c03244804035030000c2c0e12400c500038805000c485078900d43c41c1d0042042500c0001107004080d00142802030b049002d020344507030510010000940c0e400c404102c05400401411103100c1d5001c01418011800e80d0030446c0c0d10850640c0e404d041d002140c42442d2001c0c1c5030107a51800d605940044c84010803010920240f41007242d201d904c020907840000000c1280410380c4a0010b140c003820134a156613146043d814418031000035410914080108504c0c42e600032140414896410040c0c2819005001019814101e4204a40c03055100340c0c0b00c200c00340c0801c0ca81e50b9078003003666404054140d0b0f0541c0d03402c1120001c0101c061b84c060095020f8804035401f0b0700f1140c2e40024601c1424001d401c0c5510511151030030b0074130300440c03140b10406500e8940405015480e44c10100304 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 892541043 1250 892539793 892539803
    0xc04080d0c051e0f120a0e011d06040b040608010905010308040329090d020105090606010207060f030f180b060a031106071b06030e0d03060b0405010503070e090132060a0c 75
    0x368030f00d0300780c00c440c0201403500700b80703034640c08640302d503020752020302001d082d5400001009260018040e800b900401d980a90f5a051110110381c103031700c00c6190001c07401942c40042071035a5030b544038a04000389401500520740040c09403000840c4032a45449024180ca800401c0a0b042074a9603403a00360040e000b4440784810180013010344060318803405203e0240001070007030011141c02d004001d003100c00044c0f01c3c1810b9440003051001c60398000c0b03541c60964009181c80004c103103050307405070050105019011170103854080000d24100301c810355403108900c12000900252540801c00c50003a40c903000142400c22016510105803a0400003000078601c5804940c4007950004103211080300c0c95170140c1c1c042911b900b11260300c00070500c034440103c22141010881c49050903031544846c002c0703029040c14064008045071031a406003510340015640140078a03182e60312008000016648103a940c0c0e008101a80700102d100ca040d0480c041449020b044241020038000040762038031400d5034191b42d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 892542293 1250 892541043 892541053
    0xb1f24051902030a0e0916050309070e0705130503030702151305060f030601090509043f030c020d02010902011209020a081510060504030b04120201020d0f0b03060c04080d0c05 77
    0x1401c2241e4200000100d40e03000f55441e681c0100d4050074203982d45844030f109104050400c408245440303800304401000d40b82007900c80c1d03a034140c00c916107613040e001200c100007010200585940d02500038010040140f0748414400e5075003003890381e41d01418000961200d40001d8031348854407041d014040c031520750b01f000101c1b941e13244c1c0031658560100c1e43d000c0f150400081000107958200605074011321040e6140742c81032070705440d80c400311207064800601100c080788602491000e600400480d10215450050156101d41000740c01800469000c0004d4090b421424802500604c40c00c6409501a180d104080c00d07100c9841e801004603140480c2e2001880d040420711000070400316007065024181c00486090803e03c036010007040b68070110410408102c18400141035501141d003040c0c0c402c1185034002d074030340700590290054040701706549181004101c9050881d4018400884082d800e0700c03110384074245032044074881c5005e2107403aa40100118215907104a90310300e00d180c02441030350 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 892543543 1250 892542293 892542307
    0x1314010f081e061f030207060e030301030206040b221214010b150c010905030a17010e040f080d0905060702100f0c090618050910050112092d0b040b1f2405 68
    0x41c44c40501c2075005030010398046000c40801680744201d0321104074031001107085614503070000701d2a00c51401841600c07200460340c1c1c9881c0301103d21500c804a4010690b8012035150509140a40c0f111441030f20754185c0b0040c0d01440c50418801c2940d80200a41110034510104500d0100c0d584900f48540d5259607441801d03010070401d101810601140b0394480b90008103181c0110361411060700a1540f4000440a210006680c0c2180b4000c29a019130400c0e1100c070300300c100310020485104068402c3c0107010812020301e5021807000b41c0403e4078803040001c20004080b000c02c480c584140030010581000301405000d002c1d20303500811240c5070b0700764030b00552141702107541c80c58269455210089108420310980d0b0b00101e103035210080300b81c0c04000b452079a031035034079420200890341100c0740310810341d400b40c0800703203041484101c1d006454546035003000d01d84004582c1080b03907000d10000b40b05000b00707040c0e14120080c2c1c04840048100280e640c062126090100728203840070070a00008020308 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 892544793 1250 892543543 892543579
    0x6030c0515070605090102040f140a030f0f0b01080d17040b070c14010606030b04180201120c050f03180705091006050906071a040308060d0b0a020f1314010f081e06 72
    0x14600c05c01640e000983c445180580a4054107003a4210390b09000d011040070005803038001c0b041c811250082441d41340a002428040b00f161902b040c0501846449130007c41e0300c41e00094441442c8829a0301e05a0340e1101c007600a03c2c001c42038400800c03442072200441d021510821904503020301601c6242900040710312a00e00310340141c0d100d1404070340c4a03d40b821542c58684544a040301c03035150b40c00c070001d01c540c2c0020308078940c6c4100080b07101c0c1d54100c0302518501c200c0588142d051018002582ca04001054840104103940000c10310710941030041517508204416034060110321090003e01405c20710f0590711074110018440e049041800000041740603200e10b15004800315244082604144c200185111f1009141501680102800800044030240b01c56840036820340c00684824101003005168414601a6034000c035080318082102c5401c40d03503d40b905c81090b03c451203029204001641e00e543c048030f81085000e5080c0d06400d480b882d4829441d803041c0006d0803070582103c02d4a071 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 892546043 1250 892544793 892544801
    0x7050c100c0302010f060501050d0c09050d0c17012d1103010308030a0b0306130618020613150e0d030c05120c07080c06180d0c05030114070e0406030c05150706 70
    0x2048000030401c610755802d01d40c0a114184900300300710028040542000000380092141d01d04d41c02469588000b4482c107184104050340207404000d104a400035160b04101c0301c1c0000e0340c040c0c14444032916007444d02c032280502c9814400507034403e00c0540740c0382c1140c9004200d20b5180e425180f841e10303800e80c6800306030840020340c080c604c105141030310f80c1050310103081100c203511100303070090344603c003402110f40c00800b06072000303540b081e00400c0c40c4070040f0345012425488040290400e801244110707581e0344020210040d28a051140151404a42c0c004c43d8902c0da40d041c8280c001c1c02d19000c41020a11460412403254010000c940301e0b00701c0402b448a156000348411035094000c408103012112042c01001c0d0309a03c1154010708040b60001520809000c1c25400b9100308a000251810803490501e01d100415000700200425900000c409980803001c5450000041504614420a1505101c0c070010380340c2110b1100c50762810300081c48010302d5444001c00c2d00010070b01842c000545039000e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 892547293 1250 892546043 892546069
    0x301020d050a1808161b0b07170a080a092f01020d140a1107030f03020c0a1d0a0f0906060f050a0b0f09040c0905030312060a0902070c0b07050c 63
    0x10001031a18000d5003003003c5901030000a11840350124452000c1804001901c0341745001900920760403400b440c14030703815440c00748051034030185107078002003620110000e0140140124031404810300c0380150202d4a10030640240041246c0b42c01061124040e680a1680c0354400d0060140035038401b420410700e0b141c4600c0f4100c0040766052003201c556414418149040070a003841e0343c07510b807040d0146440340110a02c0200700507854580400b444820000c040c000d680102510850b0051418000d46540d07082d00b03e203010f55000307500010390120024031942050004440d408854982a44070b1010701051030b0a2042c00c3d480c1c49065002c00c0f014440c080081c1900a038000300c0515180901000341c1e8682d0200d800ca200c20300280070714491210440d0302c00300044500140100000b10183c0e030360074581d0440342e098031005c070b112a68a40c1e401d1b2503c1c0108411a0000d060300d948080d0041a0f10910314010582c01032560b040212103d0100036144884c4980305903000415204003207541101410 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 892548543 1250 892547293 892547317
    0x21c050a03180602070f0c0b09130b0d0b0115080c040b0a0309050c1206090105010803030906150604090c0e041d1b040612150b090f0609060d08040f080c30030702030102 74
    0x520580e080007000d604007c001c041c00e0300c7c2c05080c00b5000c000200c00c4108080d48140d119110801071013030f40d450704144216941e00241c800c0031561154000e004143c9280700d00808101c01001080000b541c800035076003140c1421072002d1801412600850190004a804403018484e0380a12003803940d0744608480c01e03550780402020f4501d0203403591070035a40d06034402c1031250010028400b4103080880d01c2ca9000c0201401038240c05610350110307405110b90340c0b1541515140060725111164490f000c0c500b01c540403079080c070031907040440180b903129000c00540002c0d8003c0d400c141c030710444038040928418004100107420781d41d035110100c03840d50401048520010048041012410600c100f04480a05031041b07481c42c0360140c0c0310380a45030054107542c42800b4000005400c0d542c0c0d0f03001a9a40c80c0d0200999840b5035460030301c50203041650241074414050305035014142e00f058000c0b6200f46000201c20307880000c40c0d8203500c2030361a18849105041c00204000c40241c0c400340000c0410ba2004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 892549793 1250 892548543 892548563
    0x30210060902210606041e15030c0305090609030d150302100201021c090b010902071e12120e030d0509100603050c0111010203070e0112061a0406021c050a0318060207 73
    0x40e90514020507005001104140c43e5105100301a11040251025150000701d254010000c107187c0e03042d0b40b205940710980300c0704909003122220307516410000d5000400d407414000c0d6260440a40e8849a04450a0035a9070042c80340c40501c0036182c21206890320740c0c50310250481e8070380d000304060b081503000d40e80160303400003005603400704818062a07540088e400300f0400b0351031a039510a814041840b81d058440d80220340c0300d0a100310b603003030401005c81300309800700d07080c0c0c00386841c1c11030400c02c2d403803800881d80b8104a2119400a4040c22080919a601840c9000d00c11114080101006400700d5541c0c03280c82404074940000b4802e01010b503000303200808207501c2140004210440c0010740082a034010b0044c04017a60700100d10309041d1400342021240c01d0300102c8550028141e990101c01085403141000c1200d01c0824024000d54030194240c640041000b0301022400b20580f0310038000070300400c145100d591080e44140751407924084040300c0001c4a495100a070382007044203880c160f004c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 892551043 1250 892549793 892549807
    0x20d18050721030e06030a0f020c01050103050f0111040e090a0b0702030c1b010203030a112a01050601020a17090d0c15020c030607090509041b1701050604090b040807030210060902 79
    0x110b886401c0034140c40580152100c000e642d0000c101c4406000c0a50041c00003002041000015802071010074039006411900d030940203078114007804003807000f9500d9001d5000041c00c1000e040c02200011801d10040707a18240c500360640c603117180005c100301014015808803a00050f070b50650103020b1489070b4021a102d8210522a0781811200b000b501c0c0e6045201214111030f036000320030359901840400d07000035203070502190340070580f0542c844c83c0c00d001d030300c03c40901c02484a83c0789220b1901b9108020046645c0e102c00680c0e540c3c0041501600404c0441108201d1400380001070040000c0a0441c0c90390035502d50320090100307059041184007000c0c14840341c0b021681048100b41d40c1e0000c070018490340c18200c0e40035001c803a19000311030040002000090500006102420380ca480c5031b00110502903584003a0a050b071080c3d00180c0495091001244c8140b50901030b545106800118060303140c0c5070f80e6a004400e0b07200c3c05048042d1300800e000b4503001c0c0c80c10700c1104010140050b007d0f82d2003207 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 892552293 1250 892551043 892551059
    0x409050d0f1701050d061a100c030e060906030f040515070905030c100807030903050715052e1517040311070801110403080c030c100f0b22020d180507 66
    0x1554022100c080b0003000e00401541d17903000400180035822400c0003079503c08107401e42d91072601e81070010b40c05c8020340250800c401c0e8000c20009803503000303a846d0714240c0010703070801845126580d010f9030702c40c1003840458038041c0c021840a8006100e00200c50100c43c141130200c0c0440401c0b0b84030004120440810480741c1000e00c43c41000d060200d0302d003c481100c0403000340c56050040c02075000c055841d1889800c141c024011200a02e1b08036440e24404001c90311018050310b002c0f034a1002200c3d03580070510a940b0542a4030441c3c2c255400c6141d04542000011420303000c0c1c0d0191101000500c1c0a07141041d903a00d241c05000320301903568070030780075507900c4003904d401d460350b020132003581c507009009039141110720a660640b94081001c9551b0385a10407130a1035801600076640d07060050100e041003103e040d0388240320023041c54000744080001e903001c101220302c901c01240403003000800d0002081e98160700802045910080016031615031495000c64004941301c103c42c141e02c40c41003808500 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 892553543 1250 892552293 892552307
    0x310090c0302150304021305060a08011d010e0307050a030c17210601020a021f110d050a020d030209090718090e1b0901030201020a060e03091302070605100f03110409050d0f 76
    0x180321200703407134070350700701540420b0f83e0b000e5090100c0b2480e41d9071310100e4196912910800004d24840002b8004202205d02140f0b203041d103050f40e000190700e0000040908580403094a2245822401410414816480544502c41004011141d040a041c00e012040c2c84c044080d0036641c034040c01d90b0700c1c00d00e101503c151440c034014040e5415075000e0312540c401a030b94040e00c080500d800c0540c40402c0300d0f2021060b10341c001044050440303801082c400d440302d1032f88080900740320284d51f4220b6481c408810000c3c2c040b84581070185400c0b507019400150042d020b078541d900503159810310416810760b0b80c60400100e03420f04d01071030328a4101107a0010721001d02d490001c8402800c5640b0ba0080d4990360011303681d852054402042180c071800c10180454050007a01c1e54035030041c2c81d45020404000f141c40013136020483c1118864035160101e585503000c1d41010096a0403018418011030668955000c28241d843c0355a9100342c940d032010340058000e01604030351800702c2c2c0b1440340000104402903c18 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 892554793 1250 892553543 892553569
    0x1806041802211323010203070f021903081f150c0b2410121d01050915181212011814151801060503010611060108030702040b0310090c0302 61
    0x848810180a0b2025140214108059200341c03843d80284c03544041e02c03100600c1c007241300b1039035101104008002d90800b0a001030b00b0300940c00d442d1443d1300c8010100743d003481c281c00940001e51034400180c1c0040400c0d0b1074000120030518498a441da600700050701c0355448210840000d42c810b035a001001102c641e42500640c0001d00d043c6e4006859028418103006810b0b2144914014081c541c3d01a005014280000e10b1443c0b052040c442152001c2180c62050100d080c810b40c40e0000090886c00c02041c0e081e4064104403488e04241c840425241200402841141640c003c4034000e9821486a1008041548148012406540c0350a9400e404603059040f0280401d08048a2015546122010b5580000d90700000c010310300064011600300c0100702a045004a80340c00007180d41038200010b9030486080f035940c1e42d2800d0340642850344440007881071503603540c402d00c19070380145481d801011800d0009011900c0c81091480c0000585000241c140d0700c0c0c03001d81380b0a00039405c0c0031100d499a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 892556043 1250 892554793 892554847
    0x70209250507021c03090305070608040b06040b1e03031b1c02160b030a020c0303150a0f2403270204050a020a170405010b060d151403031806041802 65
    0x28030802c1e4021884020b4104e189111560300888800f00305401500d2000245800c0360844917125210100509003c10a40d019209035006800081c1c4620301809070808400f400303000000001103502c001c0c2145080c00b03130455890b01061000300f5022804072a19035400c0100c50083c40b10481c4d405040310440c801131840c83c1150840981c4072200030307070b0010300b008403118020243c0d0307290b6600741941c009006000c040d03401e17400b0001c141310050b00c2d00e0701500403405080b01c00581185e514003600b500c640d410310404d5095101d546c214a401071203107004140b0b030740090802182c1050003507002808403407405803903008524241030326030540c20644030701070340100300c01c40440c54448990342c050700c824250208004c8104840d8006170400078290406041d201300500402d4403112401c42042c050050b0785050012548400d0f40020b21642c0d641f5100c6070200094042c42c6400c40301862411409a0900c00b0b5410042c100400107500300d0078bc016940c501c40d4804010780300c0391007285402c40c0600e00301c10102 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 892557293 1250 892556043 892556047
    0x103150c0914031504060b040f0b011b0515090d0914150c12030c0c0c03241312120b0109061e0e04090b0709080d051207050702092505 59
    0x11038021080304180d80084401035240b15600c00001e1070603584159280b5600b900e00f09000030803640d5080012189421101885925007040703d4000f01e4041081050005402086190020070862101e03013000b4081c1083c1c0e462041c4102c00101034140540b40b94646a1211008980c0b05034000010303030241c2210060300125042503400103400c491901040c1d0f0801e1000640c00102d120100685845607500c500410344a00e800b076031800d800c2d001943ca01c0401d0103083d596502070700e808500d181c50081c0c0c203891550b101e0308147c5c5103440800000d1250222500d080928404110005c079450a070b0b031400c2d40c5102e149007201840c07105940c02a200c150500030320580c00c1c8210768000f200304100c0302c40c010400303c110740c0300c240445648aa10a0b526045480e01e60507006001c0311900e824411000f948420280340e64403020103a669009140c100c0004106204141c158442688a82d4100200b45013280c104041d80d00061000c0f6029074141e0010791000940c4041810340120000c002d102d5802c20754 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 892558543 1250 892557293 892557311
    0x6090c0408150601110105090c03011505090a0506150403122a0b0a060f180e0610030f031709070602011802090c0906040b0a0e2b0314160b010315 64
    0x5a4442829200d1610a0030350b1002450356403250403c01001a40340009110700d00b00700b42500c0e1500c0800722024001d50900b9580306034420442451412038502411200113076407030a880d5802050064003241e845000f2082034100490b02a0242c0055401079200d05007800c65003030043c11070308284910842c000b489400740b40a05040e402d51101146e00074851096503a24444403000400c8550040b03859060041c1d40440e01511007110f0398100405070b00204070302d42c2c580c4800381d40c40108880c0007040c90050441400007e0070141d69010f500e22034104162101300840c01190114411100070741c03140d01403407040201c2942402058080099416940e042c4080764010410810006042c2207020b20001500d43e09500c0301030840b8001c015203030009031901913841c030040c4600d10388240603101e4823207800344050fa00350044280143e00c50050f2040c0e82c50308659820364076070341480c071800c2c04120144499041402c030316800580c03091189025505c2c0f58198500030381c460380f654162101c0700e0702e006211 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 892559793 1250 892558543 892558559
    0x905010f15030504060f11030402190b0a0c0c03020a1706070f020d1107080d0914030303010510030c02010f0609061d06010c1e02130e1b0604050d0f1a06090c04 70
    0x4a80103000c0d514000c11a0740d5135040441c090300800004503011807a01a02d0011a0000e40296009601c22240110101341d282140900d4580a005207800c04a0400c80c408142c0d00500702d0090051064401c650031b25030340d8000500703809840d4045002c0d10000b0743c0705640c406040c09207035030101c0107003069200415007840007275842007510070680900803150078500c601481004404014100e8400f240e0240150700780080c480c02e4140318000f001d40c000c8a01c20079600d8003201752816901d020305071b003402d00c1110100710058061840c0c247c040d17558540c2400d11960ba14003500d03010b84914080400d84902d0544040b07030390740505400302054410801445443d03a40580c9144074140c1040030401215568400350055100341d410080d48040c184605492100b01a0401600d4442031401d440d8401c00310000044050703002c040c100d520a00810084c01b2600e0070941c40003140c0d015071640d0701e5200013a1758000000c0a042481103450a01d00b0030040c003880d2518046070303c43d0854584078109440c25181d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 892561043 1250 892559793 892559819
    0xc0e04031803080d150306050a1508150402151e0405030c0913080714060712390c0c1206200f2b1b17060d08090315010905010f 56
    0x130240c4203070300c919a07102407442e0744015401841e0840c80800c003500b40b50025000912044005102c003000b4041c0014080001203000a154041c10340e01050f147d8803075003003010943c698a80079210110a020582429041d06c201d40d0f10000170440e5240c0e12030400303042610b01406080340d00d1150312440300b00007400c0003034804062100c0c0e0000b1100d072100c80a1400140181d072303100380301945124030b004100c1c0c2d8550010314805c108280907400c0001d000382d00141c400841050504161102118112500c00000300e007680196480b1031805101741d581d241e880b00042d4402d03501c4181c0c18100701c40020180f06a6209903041640460b0a0901d0308030a401d280070f00c1d000e000c1c108600084007142007480409441e46280a001c500c016203003001c0780d80f90814000300080c103171180c0b424100d000c4030a4041c0c080c4d04c68500e0250492020a101c4c0d40b0b210400002c044038003c121400e0343c00307004445c0a904c04005400d030602e110001c0781043d40c14504d00d00304a8605900506060704450810414540c0101c9 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 892562293 1250 892561043 892561057
    0x30c02240f070201050405030a0602041e0617060a0b04030b0103060e0609120c030f0c030706050c0a2c040204180f11070b06010c0c0b0702090924040f0c0e0403180308 73
    0x141d85034a4018900042e034643c0a41d60003940c06009110310301040101c40d034010000d980b4003111004019400710140820000d45000d080c011a8540c0242140e52070245140c95004034020b101c140619100e907541e42c4660040d40c0102c03a0071310701e2001401009910700456039919902c800410b05403034800d840d282d030b4003550000c108414800164003840e800050003122010074100803d0b56580e10090846560b95002080607681c0380d20740740102d400782c50b50f4422198119025500d543c4020340d91609004880021420000c1102c110401c211140c0c58070b0014200401c0440440c168000000801c24203803140ca070744004a103441d10181c90280c0810310150f90311160082101d1b086543c4100040e00d80c075490000140c031401c40c0340000103490102000078280240b0075184085030340c50301540b49590705e55240000c5080308550040800c41c1c203107c900a58418060346001e43c1c40f81c030a8941601080d110381041840d07458400405c4103140d0407405c11450a019202e440842c6880e64840e00041d0040030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 892563543 1250 892562293 892562317
    0x210d02070905100e0903040b1303060f110915040819030807090609060f0201022b06060918110d0203040302010c0e0303031504020d0b130f20040905040618030c0224 72
    0x113400b003680c0e111304100b9200680320a10b915956001600c091000c040294031044030101d0a1107602890301c4050b008040f59001411519418901841c0030010820025004d540d0141c5041c4800100f25100f0000441030000d85000100022071a0074024422103004101006000703405404000301c0350b104400d070085401c1440c1c491040781595600300d001e840b5020540c226110b0408181d8011040c0340e552128030000000d080101c244c0d5134000703031060340b118822032002507030203040000c00b091142c0040d01d0412a52403524a0100c180e60313f6030890700705890540042c2c0d55140c420b0642074100d141580c490104500030340c01d601e010110940c0701407070405158022078001c01c5021082145400000302002c4c002c18450400400034800b0b8001c107010000c48804d030381005050021804644480c104d0030b01181070b19440d01c2c5c103001050000d0240503004480317195885466004452450040307200f0785219950300d4038041541e00402c110016441d0a0459912801d60105960781c410301c1102c40c549044 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 892564793 1250 892563543 892563569
    0x304170d060512010e0d0201150924090b03070608090616021e0c040b1f03090f0b041103150112020904020a1d09010f0b0112050402210d0207090510 65
    0x400d91a4000e03250642c031203600f14000b119000201c00041d009040c00c5188141101d4500d00e420004038240c481c2c1d20020700000700100018803005409800098040c043c0e11141840c00100402c0e1550f41842e550003040300079541c2d00c03e01502e1405119490045c40546003104450410510072030711218064404400d0041010f00310341000d000380013020318864228148006010b10f03980290321121507640b160720481c60840481e44070315090070510203907a107842c900c6400c07103041c4c3e0701074000b0711801c10191141c5101c41c0847c0700252803e180c0138031580c81b4014602c4455204002e05250104202c2c2c3c0c0205115540d0050180d087c3c20140d13003a400390110351280d0070351150300100d000e0b071920b40c00002c0285980024400d0b805180e0402900410191000b0401400c5c52685c04c1f048a42d406d0915001a04540107040151200e421150300035000420101e96542c001480340300c0c80120004c4c14000350048403142d00610340500a032402406080010720182c030740130000122580041c01205805510 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 892566043 1250 892564793 892564807
    0x1d010b1c05070306052808030a051213050a20221a03030c0a0b010b0c060703020904020903060f07110105150d08070507030b040c1d061e09040f021203030417 69
    0x21a0b04001c4c000d040150a00311020703900c1c9070100d84500001260400300c0542c105c00201082e0020848000c41802d588040c00c0c103543c07600d000c0d405480640030b002080805c8035828042007090002609180c810001c036035401c80312480c00801c800c0c100300240d01c40e8044450014003120312540d40002c9030401e04000421000030800c0c503442c2e00d6a166203d0b014840401d603160081000a010030b4054014440c0d01880d0380d980c500b65400f03126034032101e0595000303000400d82c1240203802a01000700010005400d29030110040307071070500121045040c9424581c1070101054020354100d00c1c00d10008002c0c8001c2c508008070780100709038110b98502500341070340500c043c41079100648040945c84030654060a42e41d040c04205001c007550141c9900740600b600148010007204203144401114600c04400d80d01e0108100e0b500300003130300c2000c040c480d02001155983d03502d001d0a11407849544120b080c20001d0040c0400750300160801c1c803460744100248000300c0c03030700c103007100c0c058060503605d544d80c0f65 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 892567293 1250 892566043 892566047
    0x726060310021e040e0117120909040809030607090e1e130c050904061b05030603060424020a051801030c05030a0e010603081603020c03010b0a050918071d010b1c0507 73
    0x104040d071843c070b5001041c04944640e40e40710b030318121480150121000561210303429203a40100b1408043c1540800c0007801c60309041c002164402d00074032003142040c030040007003803c10b0300407107455000179114203041c4400c40f840744455070001c0d00c3c1044a41044407020115400c040060000312444082c2c0c034001040011441c0b02e1000b800014050400c81d00785454800702402c05000c81c4c4c040c0252540c0614400b5100e40c05907071055600900a2071942c685d80c80302442c50103602c00e0b101103546035100328824a107150000b050302d00101d81e07035256540e20505003e803549032404161030406052200c0d0170150740d80700043d80c1d0050300301c0744001020540c0c0c07543d10b030060800d039000528400c004134203402e0078000450310114030342c02070b000e03650462140010035080300d402e000c2c60741d840200e0350418000c034101f040c50399a0011440d8121102c400410110790701d0516560301003c0f240351790f8042d510000c02c840078001e0040120300c4036030342041d40d000c150805403040d154074105100e950307400180c0700364 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 892568543 1250 892567293 892567327
    0x120f08100f2d06021b060910030513121701050a0f0512010207050706030207020f090108071203200a051e03070201030f0f050703020d060608160c051203072606031002 73
    0xa000b0072059000580c0d200d601075143c000e01c0300070300814034940f000400c44e41441c4080f0745a10600a1119046c017600840a800625001d081828036002030020b02c0c0c001a040c401021864026071241c0483d5040014442c1014105800c498050400c0e008100100c441c4441a941650000c6440c1940000900e40c034070b00a0240e4440900b1901c240d050000708160941e00401009000b61043d1244001540070302145020038806c00c1c405521103601040b400d0790000360901800d21034078101000c03003880c16810103000c40100003003005030014265841045820000351240f2000121003a0320000402521500e13805440300c00b0303040c9504c90407240001d50700c650102e148800213030310030001401d240034024000d4001114002e062803801ca80420800e010f4240d5601c68a00d40441d141c5000d1101030840710409404400c80300e51180d06a12101c40b01100b000d0b40c0f02e03000540c0e400d100700264420505540202826424551112209102042d1030104802d20300221112707015940c0c00000260068031 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 892569793 1250 892568543 892568609
    0xb0d050604060212090f120a09080a060b040e1c1b06020a23040f12020301110c06040b012709081b03120903090a14010c120f08100f 58
    0x140198000c100400c1015805020209429025482581d91300540250342d01986c0315681815071103c4601c481001080300203240c081c00b0f83c82d04141c843d9942c00b81a10f40100380301c00b10f80641d00c444101046040501c908dc01c100034110081c28081c1103e84d802d84014104000002044010940e480b804040091549450755026200310355403440034500600c200003071a081c03418a04501020300c1c0011006003520155400120305016680c5001c8411903054049203049801d03540310250b01071b13280a40400b40904480d524040c0c1421301c0d042c603102000c250b05804c03420700381c40b800e250b501030824252902120220903500003c0c92029604282c1a18060308c0144407140c10312806403104118040f001e045003d5928817400c1c0103840e0303030522580300d0046028481d041621440b04000340001d142e80c4417503011060406401c00f07207071a26440c023014003008186002c81c44580032440d42d25405100e855000800c0301045910a060010481c1031181c58815008200e1032125200c1040c40700c68410480 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 892571043 1250 892569793 892569803
    0x206090d1403370c080601210906090b01120c0803040f050409030905120d170106080c0a050c161401020705031207060b031501060f0c11010c15090813050f0a0303030b0d 74
    0x1841c3c5109020026104103a058000203035080e0104072194003c0408104480300348449200349911b1140e400c0042581220540301d0b00c0d00c44240c400880c92070150075000c0d2002c0b00102a2580c00c80c00e00d042c24001a5001044c940d004000800c0601e021401050075650201c4002c00c241445040c110340c4414107401c820340c005030b10300741c40302191f00000b0b0105480b1050740f10f008000504400100c0e02c00801d100d440040b58001c03000075034000384540240700e80401070a1071414090300301c090f14034011500c00640740d0040107040c244542a000c02c450801d0a209100500b90700b8104008261505034001003190360502c003166100401440b80c018941e4031001408403800c501c8191402d6101950030b00c02c600c04150100800240d26101d5991400255040b004420441e0808001101c0c3c1c01661482984c3d82009880c14102d100c2490242808841c00741ba265031b1941c208407401014130348280d1007284155160900c0301c1580c2c41e0710700c0395030440f501410b000405041620108200481800b40201 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 892572293 1250 892571043 892571131
    0xe01080a090213020d0c050301031205071b06020705040b1207090b040b1302070c15170705040e0405070501080a181106090d03272909100206090d1403 66
    0x60104251340c094034104101c400c09008411020106445522080c00b0141984641b007481c00085801940244100391052a01d140701003a6651764021406181d00003000582010700c0402c5030385441d0003403141c10002143c840c02840850300c0b109565072042d2149240c00358549412031074036950303070f4403c111901e4080d217601c0780505005101c000941c04448110b075aa51002c10209200c0b446460204008070143c85184030300c00c0c01c440d84900c00c03100401c00780170004200f00c00b142d100c01005509001c0c5120390010070481e07040070005000000c1c01020300170304c0c1c1d140c05644500d01d0b200d60707074100546400080c955520800c80c0301003000d41c8110352465030002c000c4e03502102056401200c29811450703010791808418900007890300b0002c481c0c0315130850005059044c0125031150000070002c1c0c04100b120500c0d1200e02d80200300c0302c2c5005250a00942c2043d020002c0b811002e00c600300086080c6e28202c80701c903040c0044171005003c00341155039010000d00c3c110b11140e03450381c211039404100c0a5001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 892573543 1250 892572293 892572319
    0x10209030f03120a0e06071209061d0607030b1003150f0f08010c0e010e01030b010e03120c07050a0f06080901180f1e0209012304020f0a090b09010e01080a0902 70
    0xc1d940c0e44020324854043c006400000c0040c0c82520600319007040c154041c026030345038058221a80701416030030020482d07840001000040c4544035802e0b88907420f2115038584242080c4c03903030500c0e9000740510281420040b003c0d40700d540303013405403131601140d082c0014680b4841005651981041d08102040d060314031000c07400c10100c0040030100c03000e040080c004002d4013401200c1c07803c0f400040b980801da40701d1581740b485d8001c0c0c009a1007488185007007501017204074002032400f0f060001c2400802800500c41210000911004000d41801c3d1000c19089103805d0303802002c2d000f14403641041005010104000580c290044900d40b075141ca00240c0b410018102103607000000c00e81290790704210034102c02c010031808240e2000d140c00a00b14641d0741c0c0380c419881100048030b07808c1d4489513500441c44a05550b6880942001c0c0b941540d0b0340c1d15500c0d01800034000341c2d965002100340510900c0a15503070381e400590f100105900303180281064950152510281c000c2500007580448000544 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 892574793 1250 892573543 892573573
    0xc05130515010e22060f1e08120301050f030f06190b15030103081c02030103080a0e01210c020a050f0304050a06110a030e0f0d0f02041107020d0609030e1206040b0105040c080601030e01020903 84
    0x6184900842994a60b029501c5a00d15989d1101a02c4d80340000f109000410080c680045071003070603d805001d4818540701040220308110040b9042060000328000c9844410010711a000c07503034000341c540d41185801340c585c0c030b202400b0501c001000340c0400110380741c180c109865941030b10000c80c082503459503100e1034a10801c1d00441840800241115005a095841165001d52540a541864454101c0f0071181e070003401070520445c055105400144c000544204400f4074400c040b64055910740b800e01c0100100c00c0351f070340e01c550300300701200b19000744030f072000301c2c0000c078075a4541810001090594007050021251100c03d590000080c002d00c1305005c400481841c440d0304c01c440400c01d41614404c1d00145000b030341d030041e411a00c0d414224000a080354080c03c0c1041c002e040460040807030500041c109140c1e45c0b100e0505070406014002005a281c005070301409040350240202540400300601908004103101e04041c5c4824103804142000c1d4111810100301074190f8807446000445 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 892576043 1250 892574793 892574819
    0x513020a080f100204120f06020405060a110d020a03021c0926010f11070b06060405090907080c0114090121020a02011d0a120c0c05130515010e22060f 66
    0x10700521406607003402c101100d0544200c60036a4150200f0072880c0c5115210402490b0f601f04d421110b5503400c00011519984200c090700700d0481c942d556195803000b07080000c0c02c110780070040b0350942d0300031842600040d402160680b000c0d02c070161650b14190302e0000444031041140d01c45e203c004801500401101c91500c000ca0240c0001c000078826920040d440c0e0040711400000c4103403800c81400728100044018800603005803005207854142078030b03000050180c1c40b041e6200600e661000b442000103603818820088003030ba00342046040c501102d07410402602c642c0f01014104070007901075103d40701c3c4039141d8210a80148100b10344801002002034020221414896003928414400c00254900014984500c42d844201c2a0000b00045e0b41034800072001c0d5011221000c529001191a4640c08c40e05c00310f036070001d54003161a0402d40650303540d40004039a02d5040000761403100e03070240c644a46003c2c1c010342c1e01d03e104c0c084981c60b07010039001700465001000d0192403104001201d901ca041c1e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 892577293 1250 892576043 892576063
    0xc1318020d0c0206160c060e061501090f051c03170702030c0c190303055d06090901020d02161a10050d110414040308060307050f040513020a08 63
    0x107040120b00c44280d400d0b661034801304c45c1024110310043c00e545400c1d22070130011790010f00c540340100c1e6050348400920704100c812210400448030707409480c9102c1d82d00900c01001802c00164407000c050802000c9243c00c00c100c006240c2c203031919091082054400c0c100300041009119001d1458100054004c0d104c1d4803010b6211000c0c4601040e2032254907207100f80180c072000c2d1411013804245541c2c1e050303605030009840200301c00705000c0c030021101c3d204042e448450886600d141425601e03641c1100c0c0031580100201c00e4a1411000b0300c070303c2207440381d201e038100d90f08540520310fa940f404803c5003e44226108100c00500110300315480c0e1900441e4448454425041d150b0a80c0083c01d24480301042203e0f440040304a05800700998281001001d400900800400c0d491201c02400728060795079901030003c81c0e6140c40100000c1c964840c4920350840c0045000e400782d80d18040010707408085038180c01f84035540c0c2d5404121641d0700710710440003056001d0320624250340e40d500995107070170f0110 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 892578543 1250 892577293 892577317
    0xf110102030a05150a23190608010f0902090f0d1104020c010b0a0b250305070204020415091a0f03190905030403051615120f020408030a090803070302060c131802 71
    0x34980c0764072031424401e03d0707065500e4688031190f0f1000c0c5800039403405806d01000741c1c22204d103030741c4418003a482d580d5100240400762209000c0b5490b02e1540c1e0700000103948503410142c0306110322404ca41c4c1d001842c180c009811185040e400505080c031140e82d1303503400390840e880b03840003841c02c05003001074021424041c800c803214072075996108983c1d0901d100e010050b035000040b040a4448043c2c8030301020980343c0c000d140c45404d181407a400700d001c0303034001d40150b0b41542e41d443c1c105003016400308804014141c4000c54075070548c0e01c40022409d60081c0b00e0034a8144401000041800d101025130742c00490065100384445592402d103a500c942c07044c00250307010301031081d58404810200848400321069403844100c26010020100e0300c00c1948241000c03419102c3c400d2055001c0c0e0b5001501c0501922009155100d20b400000740c902c07aa41c0d8445401504140512030129802181e0640e1000202111701c0d0b88800d02c5609828000c910780010500e034000ca503004942ca40b8a0380500003106030340c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 892579793 1250 892578543 892578571
    0x5070e01030e190209040501091704030b2514070204060b09031509030f0306030a0c080c120a17070f0602070812090307020a090b010318050d1806020309010f110102030a05 75
    0x41d42e6040e8640c1c80104550b101180f004032581e0050034000800380d4020300520000400d887c082d5a0010f9000d66280c02102280b408102071080c4a500b040a0b600500c486040c079108005818a81c0070612211141d2410312041d04035400c8100b94003004c6801e03a66006100304059610764005109a4200d00b0901d4003d00ca88032281000303040036101180994400c0d8004d50a200703002c801041d640c0d00c000c01d0b041c0c2600407125654006007114078000045c3c4288000340020a82180500c81413541481380200c070f5600c1b9444075404100c4502c03080410a0b0b02c181325550300e043d581002003910091900040030948002160418404424090082c031100030749081203034bc071208000c0399680a03807400030b0340c0800c00907820404180b260384140c1800c041070501094040e46507001c001c40d030b442e030b803415120307904400e010100107940400039090448045181500c0141818802581c034003074040110b0602480040c01802d4a0141c10180c9910542900a540d02d10b05402682c0103060113030b540910401c98 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 892581043 1250 892579793 892579811
    0xa030b070908030703020705040207020103061d090d0e130b0a0308070602030f060d08030703092d020301140f1b0f04140109060305090312042607030f0305040206040b070c0905070e0103 81
    0x1c080f0483e1603454050b40280504c50506003080000c1d0702c0304408a040c150b541400048039544402002201140c4d1071815841d81750181515080404900902c3c0030011041100301e040c1e0b503290302d01010480201d50002d80744508101103140c3d100160400b4107a080007040500030006d941d00210b110b40090703207940b80903440b60028040c2c6481c40582c010010802440050700740c2e4820f9110040b0320740120800004a0340300c00043c0034100303c106501c505000c01c0c0031210b065017024061800079174904401c013490352500f40204050142e02600d0394046140103001d80e4150140c0c00151074255403d6010103650300c0d51000343c032104031b660740c402d5070114580c2c2d000082c0142c000e108042c403511070f04014501c3d1506000c1c108101c410008c0c41151000d09200319010040040e02d0741003000c0c20403c44a5689201a00300601182c0e21200044101400d0004020041c4c13501415102112401ea0540e5103c1c65686410381a446045d0045110145800b04005c1c0341544003448815258083e2410400419 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 892582293 1250 892581043 892581059
    0x90807050d0e2803021306090b0619050307030207060c030605090f04080a0c170c0a0213050606090d141501091119050708070c0f050a090216080c07050a030b0709 71
    0x82d880c400e0390307400380000703004a0540b10714158015403804860514090b0544030b03400a888080311851503a015661107005125a0340c2c18841c2070400f80f002c880031401c0040b210741c130359071045801180d18100034020010600c81303402901038601050f80030030144000c01284100034004c0c0900e1040c58460007074140400e074500c031580441406260007843c001c1c5400c803900c0c0d05540d80680000d01700c1e181500340b940000c800d2a0701024103401c91031100540244203560042040c003028420300c0b8030b4090700e440c0c01d100540d81c0b034034120389801e002540c980f100000b241c1041028403025100c640c150b40101340034200c0280004030154141c2e000004204046161607100c04928052550301c1d02e888403104026101c058003520190035502c1c4544402890404141c1c0c0f460380f10311190380118180c0680754028492882d00c1c20b124800760064210440c10030041058890b0701c032340545000780499100040c5039030b000d5030a200d082e0103404064100071303503580e607880e00c201203820440b80c200016615000c0031600c05 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 892583543 1250 892582293 892582307
    0x2150f07121806140408070e0a050903130501030515130c020f15060603060d140105041101080c0306012d0806120f0d030e0c0909030904050a0b060403170706090807050d 74
    0x924254002d08074242080f00c1aa000c0b03601511404a070303078080c00005400303a000c00048000c2c1840303040e02051030404c16590019036101400d464880d400601c800321040c109041503008072002440c0115660302c0d541450398285001d01a955084003030049009281e14094103c02e4070744902d503003120800c0340d8410f00c0315142c00c2100001c904914801e40810001c0c0341a0025640010000341030400ca40b82580d83d091000b480d403010440e40d81d444000b000180400141e40c070003100000c0c00d1901c05d624200c24803c2c600d2100030031040c1403002c147c7e55611405140d000400c3d040003405841c1003945a041c402421547c000c50b150b42c844e20030074003840502e1101103403041c40c02c8440b00003440780c8250494241d01511042d01115a54851109001825a903100200b030103007400c54082c5955a40034818042510402080400d8690800074405451384480c02100d04032a08400e22003d03039024503881c19a180f00d44003014154a080c61101801c1c402e0f144018402c2c81c1c8103604031541914401003c5e2001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 892584793 1250 892583543 892583567
    0x3060a0902041d0901020904061d01050a0303121a03010204060306030c050a06020a02010f02032b15050604210c0f1509050904080307111c09120809060702150f0712 72
    0x60803c00983c3c48a1440c140c1c111504214040000750030400c001c400705045503500d074003102c030350121040310203601d000c030440b1039015000680c1c1903541c250841c0c8015241540210700c18540e25907810042d80c04841003507210480100007002507595a5607502c0080143c0000d00041c1d8214811103000074035460046a514112051070300a0141c8088507001550038140ea60411400d50004102c803030861140605502e544464145a101103400100c0420b412100819910b12490005403428002c9a842006990895210400c0944005640194071010345110400240034051064020a168420303103264001e031078018840d503400e0845501c013100c02c0d81051107502c0d0041d620001040c046801400119444641420300f680e8401c50f54424501e4608140c0142c0c092050b18817516402c030394000c12420003407108051001c0448945c0e240d0001520a00920900c603900c001961400c43d11a200c101d200001c03a160141d03200e007221482007c42e07501294044078000c007803065280c0802d00030710b104201 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 892586043 1250 892584793 892584809
    0x1401020309030c0402091f0309030f0c0507031704030803010e0a11030c04120206040518091e03032a031810050c0d1e020c030d15180513060c0503060a090204 69
    0x4540303c41040c031000b940600311580c1c00c0385061205036444c5c1c40111259540803199a000100d1040034103006022030940001c5008010348214550085030001503408282e9030032034583c5102901c4800e51041603c0340e54001004184003100000c0c19a20000c0c2d001e202e0182c120042c040f00280d0034562010b88011541041280070912060015881ea51113800840d03101510071441e00342c0f0b0b940001d10388500d40c07540e4050241c0e0601000343c2e0140610001c89002c2018104160200c81848800e48030702004141c9206411a26155156a0b40700c2075000200c00300c01103019602e090800032002007881850203104a80710700e0640341200c08072840303454440c000f810032080c100100c403450f00d809000c000003c02d00000c200b1050582c5801544002d20310703609018000c55a820755001001d0a80d002d0008603034104071950402c001072620301680048001254500142075500c41889844140704e500010380780500d004046141d941e04000110300501d0100c1d045414150360318408030030b0348214056402 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 892587293 1250 892586043 892586053
    0x70503191205130b0d0b010e04020a09090902030102090d08221a1c05190b0603010b03060108092415191203121103061002030c0712050a02040603030306140102030903 73
    0x329441c4554082c0c006010010300f41e030506503481000320700da40c11400305010041c0e690a450001c075030708400b514110308d10640e02513042200a14015000140c80d20841e00410307110200b02085503401e40c1206c10a000c001c4c541d915441c0641004420368003e074452468036140d66050340c0041140a0518045409400c0b44d402640740e1b0040001307450700407800f0781ca18100800622008194140211071040c000c250400110346c1001d070329070050794059400d0387d0180804000502203154a04200ca038401d4003803e10602c540c80f880459854021503a081061860700000c1e620410101d000c85d29000d098654817034103400b0f40605c10031134580d2100840b804403076812002040352040803c04806000c0c0282420b40ca01251840c0d050242c818042400c100084000308004003440c1440f000b00c1c4c6502944000c500380f1055444142c2d0398400d50186608000d401c2e03000904010007000017500a82d0b010704144001580d81c034024001c2e080074041c3c801c02505c2003504200551002054070328411005008003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 892588543 1250 892587293 892587323
    0xd0f050301050a1a073e100806180a020304020a05030c01020a060c2d0f0536060c0c270c0a0c0206131d013f0507050319 53
    0x450381c4d0306141c00484410006000b1440420038801d0340c0d054000011259805407904242c001c00b0501804100e03c07908000505108621340700c00e040c580b03024040341029880c54a85000048406010316034114641c614042040090a42074000d0f500951094070103003010364413282015184d10070090f1042c01a030001c400107000c6040780c0c000140c16000b0381001d9407008601103816001c44145a440801d800380c982c600c0c0a001d60004d400c114030002072802c542041d07060210408980001016407501c40c00015548041d400d038a40f038803011540047c10b40740d8610603818400d46400307004450394410600c4852080c14a9078072451030402d1f00c103d480d10a925030740c02403a840c080d0070541c0c03500200000c1c0041d0000684135540201600c0a50b50810b0120760714000320385202d2509240c61b002032908460041080c10310408000d00e01c040214801045400c2e0b80d00c03003542d518a000c6444a038040c2d1144c45030103002c800300300700b015224142d065400781074141803000140c02400100408082c4900d02d44 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 892589793 1250 892588543 892588559
    0xb041104030b2410090807140102030a050a18030303154b030312060f031707050a150212090a03080106081018050603010c0306030309090c03020c06090d0f050301050a 73
    0x180c1010f01e02c1c41d10007034035280500b0100340500500c0b000c400125840a0050020762000c2180d0303802800e070002c0030b6005040d00d6000035240d0040103000b000307000c0041040741015000e400c4803941c0c06410742c090b00740203540f801c0090142503110010704021020f480d0200d0300c824813444200030b412050801ca11045170748044403140a488030300c001642d4024204d594202c801c5a5070420055000390360741610603050446003c200d0310603a02c400349402d18910b081000a800840300d4055a600c0b04e9400c1d111601801c1c41810007101c0b0500500320036903145511480c82040e07001d0b1014444001804489a0300c81e4501952000320714000f130042452040100100e0348174100c03a9501001c03a41000400c569107169500920301440d80c41c3d841c0c0e035181c2d0100076003030400b40b042003905002d902c1c4c14444180f81da18042c1c80840180221006a0344070310801040c18000e80444600030f0f50314040b940f542c900361003881d4486003041554400502c00d0701d2403010403485042624180c442c01441011028074007031078 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 892591043 1250 892589793 892589821
    0x109080d0e0a050901080625080a0203250f02010b0108060604090b1309150b010f0c1401110408030405032a04050a1b0206070906020114160504050a03060b041104030b 73
    0x14041e8406026040482d20f511803101541c02070686d50001c014a091240322101d0f800c0b2000342800540c0c09140600034120b600c040fa29401c44640380c0010390340e0710303041704050302d400c0d100e60502d490b00c1014942e40c0300c896001c0000010b45206500800c0407160300401120f0225060b1161030703201c0000d000034001b0ba82c1d2603010200d02c1e4401440c000300d40301c3c011450020384800000a540f011601d0764003103251009401181e100300300034a03040740e080d00f241c4000703480e51561540240c41c10381010705280490000354458410a50441151030325036949035020b0303a9a600078081c40f07000c0d01629000f136812070043e01c2a100c0000b0001c009103041c900c100d0901005200082c12064803a07220400301c0380700003550120003002409a40a0003003440c01e00c40283c82c0940b81d6101208680c503090621a1004038510794a41104946500c003200c001d541c2c1045455010b5074120f81d9005061843c00010060035500410500c04190f6013406402c4403a154070b5034074000c521018110064841c0010100c041000d2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 892592293 1250 892591043 892591067
    0x111003020f1e071502030a0c0804030f0c0c0506041211040e031204020301110c0a020f0f240702041d0d05040b030610030f02031503190507032915010e0109080d 70
    0x1400700d00345641e54503210680000313010340c0316481e94000280110a1098020a004801c260030242d0544c00c041e80c0c0180506c1c94002400c0410404401680c104103a03200030030001c20340200000d44694032840b511200ba28050b5007111284044a0118403600701806501c1d03804d80d680c40a14245a50381880011684004104a2340b655a816060700d440e00000041c19107284048020802c680951040c851640c80704e24000303102d00c504003400913255441840940d90f4000c803054010385840700001038015405a8840258490b0801e02d40548007400220f56510046178882140c0c4140d0b0b08403800ea0302c40c801c0b4021000341200030030000d0314130b0900030082c0080d0415842c00082580340c004441040703820555a0708105503994200a110b45030802c000311784408600d01c4202c481c1101d545e41c9a540c440d074840101002c2014481c2d0000c20201c50309050341c0701610060f50001c0c9498100007803103100c00ea90075404204440c3c9131100381d522031101801580c0b00c0300028401d0469900c03040e035a13103466803 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 892593543 1250 892592293 892592347
    0xf0807050c0d06020d050702060c0f07080f030705070c0f06080103030e130e010c0e0a0f0e0601050d06120c09091a060f0303040b2809030206031e04111003020f 70
    0x4003000d10769150111401541c034043c00005172281051140d000c10385002401200c215440202400048480c0b44201d500401d40c6a048030313901c1000746000d484901441c0c0004201c120302100f0800300c150494001c02a251140118080094441d07586040081c002d001d003000261500e0010320020380104c0003034100742001404004a80160036248c0709617020109880b03010703512480b95a982c9600401315888041d070444500c04101d081070464045802188156185078903d180854001c0c0d001c3e000311562001c0c1e0f101c043c440c86482e41c1b501100003080342c17400c031103400500d000054000d5180c461040c40e158001c1c150545032054400400003050080d00c1d03e6407290044014143c140e400300020b10003440e0f81c0b4045511780c10b80c0008545054a040402040da64240c0101d904807507100104805607581181c0c0f0760303103d46840030340410061688075081c01010080080c07201f031120011814500300803ca80d1070485a000241c214241d010b418017084008009010405520488051441c00007c0c24 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 892594793 1250 892593543 892593553
    0xf1302010c021c030201060906140d0b04020d0b151008070203090918010c210c020307151b03020306030105090319212c010204030b0408090a03061e0b0d0f080705 71
    0x1600c0c540803c02c0c10720085000d41e55803442002100f8003406a40c0081481c1f0301a1003007a0083d00119034691464040140682c6d07003c800101199100780c694068207400a0742d040c994908610402e18403506285045d100c1d100f85604480b25a11800c10144207070090350146052815040c184103800e940070f0103080007a0a54101050704050074800c011000f003640d5201e510001240d8030a0310200d4011603c030762044d05104070088116000411203007500ea000f45040d1544150610b444000d10005082032840d49451118100440c0c0c160013450080c1c0e0110000c02140c0c840140701c0d5900d100b0030002d44408200f22004580b014000c1c41c0d00781010401d0200042a140b14003945c9044907944600c06081c50200340003014610700601010001e407484100171450141540c0700e00b407480da0000d10050041c000020411030503140d0201c1d400065a00c00300500c0791014103946450a0003040b405043c02c0703850130040101c10b140500c41034a00c507030403820035001118661100c40c840d9000b108203a07050300c16 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 892596043 1250 892594793 892594819
    0x6120a060509090115171218040f0b0319050d0c05031b060403080907230d0c08010f0e03090a0501050f0c190b0703020a0915030f020d020301030b0f1302010c02 70
    0x20100060b110340c400000000328443d024092066120151b08032141c0e8290b50b0701c00c001c1c04500018499040d840141c1e206849408002003203080408008003190403030300b403000f0030342024a5500311031a20141181604c0c2e41031282000002c0030441e41c01d0142c01d50307100d40040d154a90045142000d103500544c1a02d00d0248000e259009081c04040c0c05c10055111008000c185540564078580107034004000c6e0124a19162900c80281c41c141070030402a2001000310a03581d4a42104031030955100f00c401607115070b25240a8004d01404110328481030914100145510010040b201306000050600c40d14034148001111190804240c04105800410400c40c3c4404200710992003040c8240c16000080c19614100081d128050010000c0c5030050008018041d0020018419035450a2054002c0c02e243c01c4100c01130545100e942003458800110804041c1503500158142c9007d4011483c083c1c5a00c0a14800398400721641c40718140c11807552001907220b0b031215801980005d00c0c002104403 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 892597293 1250 892596043 892596049
    0x10513030e24040e130b06011d09100501021002040305102705010519060e06010f090f061e020607080406020c01021314040f0e03090904080c070303050a080906010506120a0605 77
    0x6148802c602c5441020504000300c900c0d800c2410340c0a94510139810000156580d10444080301800040c148405c240c2c040400c00001d111030060990014603107001828442c800e04118021401110f006020ba000c40c250f6003643c1e030003250110b940c4040106841c0090786140d4000305080050f4045281c408100e03502d40c94140c1e80d110760440c0c00f9400000e03803810181c0c10329a0320002d280b8a00714480c240038040028501603041d00b42d0020080c00c0c03228080710000400c44060085400c00803007030080748000308000e6401540a0590507044101011441c007941c01641c0d6158210b0f0450009220340c0700041c0002e10580151500150b800000350400101c01140d42214040d504003089a021000303804281340f4003401000c01c640301407401042a405141c84040c2c07203102c3c0050070f41c01a03080d4000700c0c04000c83c06003260305e482c601a041e10101d5071245402400c81d84003201d1103000450090104044a00c0840c1d01c6040f0f5100411241c03900c038100c101052880030081000510741c0d5507640015642d2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 892598543 1250 892597293 892597339
    0x11073c0812040801050f061e03281a0c161106070303140f04050d050f091c0308071b0609050f01050415060f0302090a2a030c11010513030e 61
    0x380100c1c49142c407581001a82400c44500030304450f2509600c00921803181c40b405804200c0f03480601209565120501c0403c1c03a20304401d4404c0082a04400c10304155515828030406462042254108a5440364a4554260b80549062440d42000c0061141d044195401e51100c9407191380035818107100000026600e4000c0c000c1030f001300351550341c1c0421840c500032202d0303400b180c40c540d0b0500381d041a46446950b4020106650306001d00010301c4c00f140c05000c1e0a90b02568401002444050307008842c05020022052040740414000c0f40422480c0f4010022007500303141c04864540d42018030307184d2a02400d0558000c0d1480d000384514070076510020300440c4e110b00d0145110080f05101c0004030300454403280c0c003029400394201420301c0142d4800320443c1d00400700d00c44c041034900d0030017805405a0140c5500c9850501000201c0d0503143c0c05400038405207220380c03a03006a080125400e6420303103038221045402c400d14200c142001a00030400010401800341114404445041041c2030034 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 892599793 1250 892598543 892598563
    0x61c0c09140703180b070e0a050a0308070b0f220312140907050301060602031e0c0a03020a060c030b0108070f09090f060e06060405011202090d060c11073c08 69
    0x1011201003082120340d00742c05400102e4400766a04d004140440d1140d03c00000040c0c0208100540300f002030303207141e4403d50307813401070000104040e1500ba0343c2e2900c01600e60098004803080d2a5500001c0c280d068214140d0b44920071441589010b032603c0400d401c00c12012450441c00d026040400982c400418401e070360685040344a114510305110002d1440c00d0242e5204610a81c1416010b221455020040c1c1d80305503150440200814030580408002e4040c60221a00c0341c8540c401c00d1042c035500107041c140103801858100309503104004110183c8507030944140c0410a58070200f8030492040801c0c200c107031050b02d01039000e076864189140c1a035440e00a040360003a16141c0c1844031502030250980c01513000c65a091500c0e18140001c0d20b50b0490510b9400d900340d01045080480c1c0340d41d440c044480390304c003d04000d8040e06803405052034440448000d8a840b51a0000c0751224290340640d00c1c00c00a901d1039840900b01d039102c45030072103501490584002141800085001c01001446c9070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 892601043 1250 892599793 892599821
    0x80408010c02100606200307140d030e03030705090609120105090705010206150d170904050408040315060501120b011107080303070f0c120f0512040803011409061c0c09 74
    0x5801c00400300a10740701c2510400010700389440000c00910340c0201048040700c07400a2500e480c00b0f4040c4110b070460080403409030203c04c45901010521801282d480e80d04104d03034500300100070074232100c02e5607400212090350104070104401c40ca9131034290050101d02c0802800c0d01600e216a004031429200c042e500f03040e4a030302441050105680501c00320364410118414114503000c8880082e5601d0048140a81f4030340d101c82e1481000c4420307204494000740054420301150078540782140c1254060f1105964251211a00720144020350041804a6078169600c00356008039507140f0005211380c030b003454148500c1c400c00c0c9200d900c09000350001482140003658884c5040c8001404080c1d01c0e001c80005c00ca02846220000b40007251601070f030203814507060f0684801000151105d00c40c02c80d42e0810140724004001c200024000218140d92207001100e40f028194000d010303040c482038680030b9008480b900121101a940780516506078040e48000d0703100c683d030702503131012034011f15082c0341 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 892602293 1250 892601043 892601051
    0x30e190e070f0503040b1f27060605030f010e09030903120a03140f0a02030711030c0c13090f06090501060506071b05091e1812090a0f0e04060504030c08040801 70
    0x819075030064205030021550b41441440d528142d641c03e075820ba4014418150b600c140b00000c0741c500402400387d0050800c601500542c0201070440380b480403514149000081e0404001240b100e228500b034a00901655010b4040d50742001c0003083c9142c03008246000c1403000384402d10090743e0400440660360235a212003555441c0c0120000d0650b90400b000d2040403080c0010301554000c5c010805e03522510754440180c0301d4440020403142940000f04a2429100c003062190507650302090290814a080310028500c501201c100801d441d5007800c05070101812003250001b007441030b0012200148124000aa60f40e01e440024070340703421003d42500c098408400d10004010351b001c40c00c2c00360900b10303074407200c6207810064043e698001c58440b0703500384d80e88008103402c02103200403440c40d0195071041d25030071000010304c94240d80120030024451880c20b60001503002000b02240103840a1001810140e940d645600c1c000e440d000d8402c4040000c00e1041030042010038025001500b2028000300d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 892603543 1250 892602293 892602301
    0x10031e03021218090105120604030c030c06060815010e100b13082b08011202040c030e030408011a0f0105190507061409010e06060105030a0c020c04020c03030712090f030e190e 77
    0x705079010140c00c407e005400040001d000b62000180d12548540c0c103150200740200d403413500b200c02034201600101358600300038002c954250b003c2034583ca640070701d03440c400c46680c0e10b101107900c00005581c29002896030000c18842240040700a10003c01520101c60441d996410441d10f40003016501403180310141e6035201e2000d40030002c855201c17407a460080065410228400200e103607080703000b442140d031405126001c81c065040096400d100c0025a500c99580c5e014890103800c41c4102005a15480c0d2800544c61030b01807014200d40e501030751390f5420050704001c150124001914443c00788030040c005c0e0000a00240580144582032403441b000c0c6080920109007550340c203241011282d04840100708959900005403580101700900c041444072021000740c1c01c050002d001745400600004542d03103a40000001180604248d81e00c040d8040070b2051030000b01d0360000c100030014102d0350b0703612000c039126080d40515984020110710f190112403000300c0c000042d692121030540203801c200 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 892604793 1250 892603543 892603549
    0xe010c0201021507110f070f0504052a131e0504050c0d02070501090204050c18041112091c0206010303081b0405120a0314070f080d09080c0f0610031e03021218 70
    0x5a46c0d8070840f10003480e02e241000ca180c0f10305080c500a19004075a1600010300c43d84d500601d055020310046200541c803000400b01251962183d1200c85050551000010709915403040710080e10790700300e414030750381410501040040c107005400101c0a01c010f00001006400b24030080c540c6a00c5200000f405e60100d20601c0140c070002032515014040501007040a0780034610a908050310440b40050404e41c514041201070149407001020030400408010040400081d0766003103240c95494800040c0c44990200d0b42d80c9024000140003424060214540c1e20b0440c8040c0c4041e00340c03910503400d0039251404122170303680c145800499039002c808624189500030000cbc040c1130620030161883c007401130725003030700c1c4c1085130390300410080000442505140041c1c1c040b6250507031181c0c80035030302d8040a0b0165035460b83c00d54905a1801100089140540e080b00900304484e0300c119034280600390303524400e070b1100303c424059003580141c524005801c16850700070700d1040d5500132141454001035080c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 892606043 1250 892604793 892604803
    0x1b09060902190c0602040f06030608061005061b070302060a021f020309070512010b041d0606011701061b0507270903021f060509040804030201020606100e010c020102150711 76
    0x856a841c81000a5500070407100403110004205050490002202d494104000c0c442d5a0204400baa941c00010540039450381203003086078404012241e00303455904011404491038810a9800541082a20109080e41120080c0320039031200380c0e490aa62600031461a5202025120041c2c11044200d02c00844400044c0144440384804505520340468041d98400041c01003612450900c801d200c4a020709402100f4450000350050240d5a02442500c0c41041c5100b940d003414002c3e90001403041d4883e8981c16008501d42c0b84481050b441c010301942c901030200c00300f00d101700da0309240780d010039030400c403110062078401c01c43e601c04511105409000280c1d8520b00707210508041031440031a600090b211100c0c404d9500d1108c02130350169400000300780662056401607142c000700f005101e001c40c054800c882c001e801b981d4255039104100002600700042d2a00806c00704002d0100a52059596030015841801110405248480140e10000b000c84406e00002c080020301c2c21181d100f488 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 892607293 1250 892606043 892606049
    0x609081210060f1d03100902130c080a0507171f080c060304080901091d04060c0e0a090c031806060303140c06130c0b030907060809030c030702060d02071b0906 70
    0x801d500141d0400d40c0050860080c51103c9003006010403140921a800c0d00d02513031402401011283c0b00302c05054410040e01d410300d02682710f10f40c00f45000340040d00714080d034002e47c9001d960705050303070760b943c0309442c01014081c210408226166100b500c2443c5480041c0340104c00ba4044800c9006003000320091481c0950031164403900810b42003202c0741c4036402917a80241e0700c0402961541a8280129800030050307208082d9644c450b0706074507101305044d8089000341d0287c0e00078007040c03c1d20341041e0b13444200d00d0707445a04040c06130b000300b0425045500109945109140100d0080c01038810b41c1c000f404002e00650780559141d40400405800541a0750440a10980355044c6284800005e44540c0024084520444c0c107109038001c00c0a0100d110020304440f254280e164104907602c0d1755114851b015080126002401243c8500d80000c29980a44a101d000394540902c550a01002e900004120702d450b940910800d0000f5406c1800e0b0101c82081c0d4000000c800d2402503510143c8645074 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 892608543 1250 892607293 892607311
    0x807080402101e03061e030f0b04021203160b24240f2503050a03090302071205060a050c0f0d020f2b0f060e04030809120c01020406030b06040b1c0906090812 69
    0x1c031b0200f00140e210319130344240c60f4000001c50410764aa0002c03600c0c00c01c0103030070254540400a00407500c2e0b1714104c0340303502040c042c00c1c2005080d558a5400e00c0700c00d660048015130300408002e05c18840c50440c0c51402c1030403009110045125100700585400d4001d4500080f042c030740403072500000454080c080d116506c0d031f074410300803040345070b08e0280491084030501001c241d222403000081c1740c001c00041d03008042074480000d0b030001a0500369103820055030859200c1e4184004181d10360968401c1d2450300c0c083c814007a28141650308503100035400440c003030f01203030350910440400004a03403c0c100c15242c12500074107c1d600c004600e408440e0300c1c07000c0e803102514008003400600c2e101d0440c903511582c941080c41058a400041d98580211007140c903180c840009281c1c01c3c410819000362080350300c1c0f42c80911200321a0810040940294041c10034410801c2c04800c0c0704101c2c04552104440001100045c00c121741d488180943e82c8a0006a5060a000941c05200c56002e041d240c0d0100e040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 892609793 1250 892608543 892608599
    0x130501080f0705031308040b0d0606031406150c1c020303010609170c09191a010f050705030909100807031b08030c060a050c04050307030f02010207060807080402101e0306 75
    0x1056000c2c2041c0005059a03c1d001c0a581c9104100701c006c904480c050800e0140e00f545410700700400b2000750403e0b008840000c1d08284a00402c0c035040149680a100002c0548180d4140407001d2016508040c0f15514548640a440c030251a500c2c001400300e1509075028507600d42c101304000e4054070159000c0e0660380704d000e10740341cbc64810100780c1c100208812500304000d600d580294444070056050210403440c900601203820f0312401c102103118503402e072180311107048a040280d0325401000700140282c3c200f040b1111a9141c03105445d640041c44500c0800365a845810562500d080754100b101c00012506086101c0319400070042c00402d6020015072800800c0a900d540f1014054080c00c1566100c0001c02c0c15814510180d80c05818054200c1d0b9003143e907800c15011900a40d07506a026006038000451010b11a0f041c15118011075101d4488644480c0e007400001c044c0c11070030000300681680040703084030078a06e01002005069801042d20344c1481c0044802c0b58003064089000c00321 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 892611043 1250 892609793 892609801
    0xe090f0a0303180813080f0d080f0702031603230c0a02010c060b0607051f0203060307062304150e0f010c020603060a0308040b031504060e0f0a11130501080f 69
    0x26100912941450040307100c5281520320b41c60090302c11001484240e0200d081c43d02401c40203c5c0608994200c400c480034480b9407503441d6111100c0201d89000140c1c0c010019551103001400541c02656034412a841c11040000440416803200011000955401d407201280ba080e084203900c0b40140c0b415003403411507001c0c142513481040c544001e05201045040e001844141d502032891040c3c050540c0f56210072030700e00305032215002e290308403007651400001c12a5100b00c0c03003a00d11407070b0301900809140d41820302c00e0f10700c0301c041254020001c6200c080e103071240c404000504010009854007444042201c000a08004030011490b8002c0c2800303c0480308a07030340206883d042c903405581450740c2c6e0300c40202080030101950400740010400180028407040e03000029441102904c01000c805004d100c104070036a190340c030404840305400c074049040c4200f0306c4545600803850010005803846820b8001e50150490b02c000b00e01c04419080c20403055030400803043d4050001030801b100c501e8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 892612293 1250 892611043 892611073
    0x240e0910031101020a021507061d0d050309011118100c0b150d0b101d061f051b06060a0e01080304140a08070e04060b0402090d140a0f06060e09 63
    0x320911028041c009525409600c0341d009011416440703402a01c03100381c1c5102808942150b60200400300c40c2c581c40d022181c030085400790300500c0e00c49034540107059035070152001100c035a0009880200c89560361001908440120002050701e80545c500d400e21a00b1702c5c4042041c84280c0b4251a1300b4081007481c04000580c02a01043d44610300e00d00300141803c40c08080358265001140040c0200b1400d401d010241158080307100448204510304003440c0641c6004468125007560030540000307401a080e802c030001040550001e10103494500e0400f28524142c00c04041c1c0e1008041c401d03001481482034a00303203c00c0c0034000e030906a02d440e0055140c50103ca640f88283d204400c207200140c0c00c7c1d54440da48004003800281036140813104910781310500d00351415805c1d41c040ba5024542003885010b41801d00999105000080010612070916103500c500030b49219420140741c001c002c2008009018581c0c4170500300c0c000d40000444605256000d80862405448a0665880b036903200d074610b4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 892613543 1250 892612293 892612321
    0x1502040f21051e07090204030c0e161706010c0203011802040c05040e060d0807170a090504140f0405031605010509060a09152309031201051c0803040507240e09 70
    0x3c45a04803160201021800300e0b003400080d400615145000090000a0104103160b0714152240e214064040392180a12403082003a07540c0c036280441c9428001c0454200030301200c6500c1401810170700462081940068212800c40d407403281e000c84514040310a40c01c082c80340c1c824a0310780703042081c502810040540c1c81ea03070000300154803403101e221505042040000a4952081d4800c1d80000030b54444c0300005901d40113404c90100203452000001202d103014020031400d86030040e046615510341064030300d80d45800a1058070684010000c0008800360305032409100f50050340001954242401107905240010b010126402d0415082c000810b048032051240507a03543d2000071905010503191003010700101c0c18104440301d00041060882020008003041804000043c0ba00c0e078840c4104030722501d403581c6645000300c8921444000a000364003c41d0030601520403038074455641c5000356010101c441e103415108020741088250702e90042c44040c0c46010480e1607000342d05d010380800410f0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 892614793 1250 892613543 892613563
    0x60a0b0111100509010b0a0602061801060b0a0e0a03050d03020405130501030803010b0a090306060f030b0a06080c0f0103060f06031506020f0a020607020415150e2b1502040f2105 78
    0x42d42c0d407100490306404003540038075610840a04208082a56040c002e92203c200300c61031201030001401072420120184035440540b4400c250030750400200f0745003210700c00101200719820002c00d00c0b001c80490000c000b07900b85c0d158550b0300540d0366418841481070843c480c90344251030300e08050062001402800035241900d60040601da202e002911045418400560001c0c00080ca0484007044010030398400d041600e000e41d04109180e00d0721464a001c0b0f40d01440785041310b8210201d08026840c242420051a002c14034002c0340c525200d04220100180c16445000860307550046c0506001c0b2400000380104458005082c1c6c1100c1c0f40c00c8580c036141c03100e01c024424a40001c00b0030842d070b03c580c4a01c01a0303204144078101a9250503040b140070004884030004030b0007400b559502440c00c845190b0a04000001c01507202c10f04829200c400c8010080c1111040300f80304031150055013600c050300091100e1140e540c640b07881c0c515081401c0003191200c08480d800030402c803021450000301202c00c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 892616043 1250 892614793 892614823
    0x1020a3009170a0903060c021b01052212020a06020a2004140412271211061c14010308190504050d03020a060c0507030815061b060a0b0111 61
    0x80700c2458508641c1840e100780c4007400c81c44003c162294040d6008410506992240804201c1400341c12402e83c0e1780d5a90040d44690304812a0681d12154401e0000d0b180032409400701101c000c0c1341c124078002d00d00703560300b18070f0405c404801e549080d4034010004200911a5002a044560190302c850074030500341483e03511841110004900c0b503480c0c650244001d5034209443c4059400c00d4500103003404000070704240002c1c032010320503140450001600501120300000740703000c40d142800846022100c0030041e47c07994807186140d2010345130301c40280680440c6039810101204211070110444080c81c0c100100800c00d800180001800601114030141c01e64180c640e051414a508840b2845a0f80259421444590052080540015410801e603100300e5051260504c4000c08552a018004025001a2204c2c0100c3c07025040801d1010043e030f006021a40b0301104d030200003244401455440510f90b000c60200f1044003118131590760308500034030700045100000858144d6a80364540c20501c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 892617293 1250 892616043 892616051
    0xc070c0911090a060503061203191103041d09100c083907021201050c190905030717060604050106120e0c0d080a0f0c050307061109090901020a30 64
    0x1c900c0140300680d40b1845000b4882da60702074031588000c01a410607180603000d02c0b41c0c0c41600040400100946419401c80a00c110400070180700c116055040e0950741280750208103c0442c50080d6039440840c1d46440401c000010304164020030700c2c00c400e00d008000f449181080c2d083c0d80302d5000010540004030142c0010206142400c01d8142044e200900105044084000d00590410b8400b420315207000300d44c40082149910300403402d071642112828038030b032b00801c41624850341c0101c035411070110b10b2a20b14150380c5c8400c00329180c0794003034000c1481690b60403600840c558040041941c070030300035a401c1c011755242c04006861048020228145145c440e070500b592418104110140403c0042080d440807c180c00c100f20258017604d56103002502d42a15103810a004d018489513880c0d0010055240009944440006203c94070001003111800c2180c41c505a8030400707640e0142c0011000180e0b0f50065403406081d11640c400700c00030724051440e1400d40b1207c3c4040181d820011040046 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 892618543 1250 892617293 892617311
    0x80106051b0114060319120309170c0c040c030903020705282303060411091005040f0e0622060e1e0f01060b041203120f090f0203060c070c09 62
    0x9100c03140c548001003490b42c41c1c2000f07804081c410029140c01500d0030b40550f0f4035120104158a4003110039000170b40540fa101400d030980c14030940c000d0030304500400590441a509581c2c114595001c010500096404807520f1440e610746031184001070043c034241000101042e540c040d44840c014440d0511420103d110840a07420032446404000c0003c6000d003052501c0d80c0784120740040c0030503c1401c41c84a8000031030181800074020b0b0281e03811203101051003030214204038104070300920483d00080100740005503078603030f40a4407400c0451480e01290b459620101c2519000004001a400203400c140030201d0802c060118589544c020700080b864501d00e04615182c20448840d014a80d00345400385070700b294020420503401e240070b10085c005180e83d48900800340c0581d0060600c142a42d02c041d2001a00440d4035a40340034401c107020404100b542503510458000d04000d40341c3c0781042c0d0740b8400310700d01445002d601600b0b00c2079290074440c40b516001100702c0d2034000c01c0d80310303aa901c1d001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 892619793 1250 892618543 892618567
    0x31409031509160803040906060e03060a15180504120305070c08091215040506010b040303050a110c0402030a090b0f040b06010f0e131a031c050a030e0d03021e0a08010605 75
    0x10f6086220114610790f00e40e1081c0c0c590b0b80790b00500c5088142d51400324003296580c0700e848008404c510090080007a6242c46a19000402d01d20032007041c2d0b80c0c1074000c00a4a071031016840140c2900d4290b0004940c0380c0b42c180b05201c2a0001c00782c00805103020304100206400c95400c200a981103c0c400e51910305c8040403603000100450710404170f00c0791048111100c0380880c0c12500c02e61181068466076640c0b0004071546d40a240402130106405111641080e8861046983c0c407895542c2260465501c81c00031404130b03070056910001b840c1d00c130702000c0140001e280342030341c12414001803c202854191542004041c02400c03449c1042090f00034131022902c203a02001d0360540040c030354403100b4191000e283c0200810038440340b0700111518042e031940390104000070b420388070300030a40c2c4555240c80b0444032944003c6081c01030580d030b0a040c07620103804010030742c01590146c0340142d0300d031090403016a00c0c26000e030704546949020440310000c554020308480c111070107402c1007601c4503005801c0c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 892621043 1250 892619793 892619803
    0x12030106120603050303090109021f3f0c0e0f060412080d0e0610150c0308090a050307050a030315150e04020d050703060e1003050c1c1202010504031409031509 70
    0x80e10611000c001d07c80b0303089041d4003941c0103501c04c4403000c1c7d4028040401d94a01c03940702002c400804d402811245010343e110b4259041648407400755014404010101070010f00c0c0f03a041441c0d2141d84e11030141e60581c22200440c01740c0c100700c415211816900c1c0004042d8031990060200d10031083c0030705010000450140c41c60800c0c040c0f014450b1a41141e555070383da040841c0c0d02050000e8815000030a001d04028a41e500e00721940e4004001c3c43c20303181514031450261002c1541d209540100c00461740600260845030b211b100900880100f03401c0050540d0f206100380750069041d20310800c540c22448411000b20051403c00e07924585180000400030300030744881c0211907040c0400c04c10415450344c0200280e400082040009494154100e032901086010060440c0d2241c034144000c0d103400040c540c4126261458402c03013100340d80c0c80046254a4000c4040542e440340140300030540c03c500201c00741d880142e00c2d0341c01d29410f080040d903201003403001541d41e011110045501c4800c20b003c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 892622293 1250 892621043 892621049
    0x71a090f0301060b040b12060a0608270a03050c1002090a1e0504060e040b18030714030c0109240c0c022403280510030201140c010507080702010e120301061206 70
    0xa00341c03903695031100041b055016035801480501030400050652405901c00c0d0300b40c0d2103d07a01c01c0700e1961010608d900c04804090901294040c201344110441002c1201080036840b0b559001e03144e0242c03800031494030300c003041f06c060507600501c11000d00c0c1d107985002c5000c440c0707011240d50190031455201e41800800350003481e08541000d401285149000d441140114401d20340310320382c0c0d034401c0759030a110211412044560741040007543d0104484c8800d60710640400e00a980c40e103100174442501b104c89112003104d4104d044254108480d0069200c0341c1e20030740b154010310000d611040000c015584c0c400000f846080e1403082580f412440d8041c1c20b52151409105c2d5580e420490460246600c0780c070354024010034610310000c4074450300e01401380100740307401400710140d04580c010f541c4130417248041501d6808c1405143c0704000c3c00d005803030107606661925809414244c900a003516004140fa0900741c0c808800c030b07070030489454100c07411201c06203401c2c007445500000c2c01024002641c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 892623543 1250 892622293 892622309
    0xd0c110607030c0302060601020109170703021c02071706070903120e0a090b1302070209060904050f03131a0a02101508030c0d18060f03020901111509071a090f030106 73
    0x41070000c100b541041d60181140d0081c1c0032500c0b0707030356054012400e0740c00102c0010320300303014007071021013a00e603a00150604d9803003401640c80310302c44c51150740d644460399403600300103a000703540030000082d48112001031440c038280582200c3c60044405018240c1c0380c80010f00d8004441c03a10742d003052051f00c4074a480707600104450b51030742c2c1c5c410442024000d202d00c610702c00c200c2c045001038800c81c1c1c0d1085403a05070b4007906900042e43c411080128003a801001a82c80d07014024040035814820310080c40511315207500c07902036038103002036121241580080e03810852020420360040302d0700050074400c1ca500c4081c001c070b0741032030b0700ca0382d0984400c0c540c0c00441c1510002c070b14041944000f2801e404c0d501c8240d554030f0401c21822415030204800c61161001003166042804190b5100c0d0b0000c0c5203a8506060181884401d04011454510640c0c1807001001c460070600c0b0145030240301c0480101204045610643e000610f1084140f168180080c0b14601e4001d182041d51401c0d00504000c011003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 892624793 1250 892623543 892623547
    0x503160309120809010f2a0c2102060c0c031602131a030c0103060f2c01080c0907110d1107030c0b0a0f03060b091e1005180307080d0c1106 61
    0x82c5801818250f4151415502542040009171500110f80704415130108102a081e804542084c0c0030101d036030011145208000c50600240046002c403401c01c2c010140d0080200e4142a03606002030420b0406000b01c0b101d000c040059040341c04c2d0002c00e41e22800411030380301d800c81d10103200248948801e0300305401743c3d6041c817110b002890b150b090680b0340030400390f00380d0340c0c48031420700118103d0b001400f520140c2c4068170000e200e00400042040480500d42994803550140d036129014191000d13840740019900c5134030110303401e0034030b84202a0803d00e81d04003031404402880d215500d800a04d2003910802c0004003023800e0091080003540001c3d600084400f00441d1107a5440c141984925000300125105601444546100c0d2144500b02c2e504026600c0c10860180108054041d0251140341c80d0840e0a210705032540e104060084022642c4d11065990301c9c11456091600c0d64903803041b07110383c06c001e07401c200304080840c00e084400860703c1c00c150013444a1401180d1190b40c0e80d400340d084000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 892625899 1106 892624793 892624823
    0x81509010b030709180504031b0804090b031006030620250213060807060306080f10020f1204050703021201050601021b031510030b070f0503160309 65
    0x1151402c0700e0099902e8801c0c1541d194030207000300940360341b64140310415820101c40540000300481d01c41411000b511a100c1300d000c4c0e41f0030741c02955152004070b0140c1d501445000381030020f0004c04c005d540d8032030400328000c0c03850480707420000301e0a101400789101400d003035428060b0706940c080c05080a0314070a10404038a5001240c012000c9924203c104249004107800752403107030010301c0f150303107080310090580369680c5c007a0390981c004080a0030300d501d0101c1c2c13499058020132070150b40e84140c003095405078030a6807001c0f01d08004080500c8100000032810404a9008580b030741040002c4151031401c0703800582e010b07030142c1e0100501100050b1240315012554000a050b02c0650707442101c0d40e03081000c226855400ca8411000078002c01c9900006540c020000d45000d800001035003002403c00e10001e0580d043c1c089040001c060340e607210340c100409140e40200d4103061400 = true := by decide +kernel

theorem cover : BRFrame.Cov 892446043 892625899 := by
  have h0 := BRFrame.cov_init 892446043
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892446043 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 892446043 ≤ n) (h2 : n < 892625899) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
