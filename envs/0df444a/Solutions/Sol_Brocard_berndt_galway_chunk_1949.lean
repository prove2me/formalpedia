-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1949
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:16:12.747306+00:00
-- url     : https://prove2.me/submissions/095a17a9-061a-4003-ad32-edb71de007c8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 350359712 ≤ n < 350539568 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 350360962 1250 350359712 350359721
    0x9011710090501110f120c2106030c03010e06071e0c0303020c07080d12141e19060609031203060608071206030503070f0c0f0308090f03010b03010c080603010f140109 73
    0x5840b00c1d540c8014014800700c00c00c00404c1d01490305031005035554401940d807a108107014000d01c40c501014030840754001c1003102900c0c601c800909403841a644c0b5200028034003400c0d19204e0f9099404c2c501080c0c440c00c0002441d502400283e210070a003035000b828054003402c0340c0340c401c0380001c0101d58040c010a00960040c81d030184079000740c0711860780302e803c040d04e0800c07541c8844d03000604210314100c098101c0c0c17040301c62407004251001c000c0c0c1014420f006032100303504049041750840c0808200c0c0e10030000841000c52035040c00c00e04c03a50f60b907100050b08000c0144030545043c0705540c1201d0401c0d1292040c0c0040d55881d489070089601c4038031046500392040c0300c81a40c0a0f9032894080041803040001d0800c280c82248c500d21100300f24a420303841000140c2c0040074040d01304400b072000881040503100c0380366054070001d5a50003044c1c0000d0140c14203199554040d460018402a0180d000700c2140c407880096000780b00c8811109030709022668012485803845080c80014030913030314150007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 350362212 1250 350360962 350360981
    0x1023901090528140609120306030c1c0f050105160c020a031704030f11040b010513060f170a140601050909040b06060f03010608060a050108061c15021809011710 71
    0xd21190200d02944d800b07a0740039186030300c0e0710207900000170456440002c21104040200d0640000d00703604003100070070781e01d1961203001403040704c2c0194102e0000040c1218460a131760810219030184805007000303030003094280d42d8100680a4680c00050f940e021b1003904455980c0030f030078030400600d507448850540a414503d02e031000420030001000c1072241d061100c0070ba009022140f40403042d5403c00049900005040e81400403d010348107402e240482610301300c45160070122244c0c05607040440350200c0404d080304201c001c807020700c107812100c0d81c0412000408240c840e0015100d050042d81c4a00500e000c0e10341c0030b126000082c0000707030495022070700928050481d6050110b4071300e001c040d40d00240c003c0c40c00150404100191494081c01000c0100001e082c001c049080c0140410781542e01c041ca04001089030b22080c504000e40c00c0d0f002d000032080341400310b40f903105104200301c0c40211521224400c9600030008510a11988084115a01020300030800c441c5002212400740580e007a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 350363462 1250 350362212 350362273
    0x2a0d020a0b07060608061b031b1603050a03110f040302120c0a080a050c010315090507120c030b0f0f030303130809191509080c0105070203010239010905 67
    0x194000340200e20207028150152003028040380c86410804070707500d0f10384024800c16035000002004905842000103d80d0001030030480113210320f020070b601d144d040c4140700d03141c00f021314051200d070107140e4480003400e0159030070750b82882914400300c0780b002c841c003e000f40c850000200b008200014502403030180d91b68124482925070256440c070015100c0002030b44208034940141394807108010041c403000a0310482400c040082690402401000c10014001d00c0e01890f92180401d500a014801c0c42215240b10102440f96261420300140038100540e5890701414400e4940031031440d100b50b000301036040190045003107039a80981035540c500119020740310b03501c08001002485e101d500d000c10301c2410020410510724649807060003ca01c12901300010060314580c00d00403550041001d0340484001d00c0e0094881601e800060300a215a00440c52942c61a421074107000910000c0d40c8080310552600440c2c00c490b4070039440c282d400c0501c0060040e0410342c1c1c0101040c0b6405400d014806521 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 350364712 1250 350363462 350363479
    0x20706030c1b080301030309120308041719020c011209110d020d08042c132306010e07230406031e050f0a051006090e09031204080405032a0d02 63
    0x80710030306408102c820060310256400801401490f421054400050000300f407104050b0030343c0e4a00800504014000900390313145500150f4080d6081c6003603480c02d03003003800081c005012180c0040c0d500c40b0403040c094085080c0c0a035030813040509110b0400b440b40c001c1903c4041101040400955214440c0100da021100248000210341280c02410140907144013900322107020700380ca4015000c01c2c240384c880c00260030301048602e1409d00004a852a40803418440901c1d500004541d20a1800400c14091047c8000018106d62038035607903000300242c0d00c840d451400d8040d032190023482090340da072031a49400c100030403200344039502076561100c0d4a1203452070b1422120983d002e03140e00ba65000d07114000d02042c06140d035a03a10400e600456400e0002c4e141d14035180d00a032402d0203078841c03e80149000c2000540e2080288121102c8a10245041d5114a00f601c2c151507550480e0068600034841c40c3c008140e141e071140585e03002928501924030448201800704400792000b80c0d0120b0300440700c0d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 350365962 1250 350364712 350364737
    0xf030709081002123105120d090c090e06070c03020c060706020d1a0a05010302070206070c08160f0609120212030a11060609040210080702010b0a0f0602010509070501020706030c 78
    0x6001070624a050b060015a6680805150241e5040b002e4140d10710318192026001640441542c02005038840004405a8083c00c1c18054146407600029400e040c0300040c0440b005115a408420344c5413040311001d00300e42d10f914414044641550007198154480b0010800b41c5000744185201caa2080c41200c21210941740454040c1d0049d810031502240c01080c51051145180200e100728002c207a090210940f03440005400e04585c2d10a00381490340c0000c0c1c0f030080d0744a000071100d01a070001c110380143d40d074407035840340d46070b104c4d03c45180e50541c0c0140201d41c4110000b411411030314940c1c3c914505c542803610401c2a0680448220b9004c2803004090b440c655082c80500520f0312592544030720098217070409402c0041c0140483d205403004010000142d80300c42e039106850b00341d8544003402e55182e41c426030041c41e030140701c0b0760305c800c180c600050424020800304003619910360080c051615018021a6602441c4c000e040c0540c2000b0300c14429141309503c1201c2c444018508641400c08 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 350367212 1250 350365962 350365979
    0x20a0c0b090316031e030b0108010504230906160302041202060a02010e1209010314010e0c03061c051605030607020606060a05040b04090902040e03181905091501030c0c03050f030709 80
    0x4201d001100450460705c0541541590002000c0c449551814140040116280000c1042405024140c840c642e624064070f5504060080712414944003200d001a608141100b5030743c814048801c0d09902101c1400759103001c4c8a0300030b490455100b01c61448403543c1c0c590812a481e040341d640c030407c541d40c0b1143c0201d11142003000003070030710050155036603540542000405403540244c446689407446c0004011902c1e0040c0010b90082e0040789040e26030300d807000014050fa126203080c43c581140d001c9440709004012813050750f8002121181842950f558090ad40c4910b01142c4a10250b04010005280c40c14007800400124925251151a00f519a200e40c90b05070401e401441103265520709801c1107081a01c1402452008080107504000311076455105545013000d1250051941d2851101c20000820840300601001841c07e001807408400b064020410044103900090034401e120071800e0180a804070707440d0301540e69a14003290704031007468503480a00781c0020840300d01d070001085074 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 350368462 1250 350367212 350367247
    0x1d0c0d021215012d090209010905060304060606031b020c0d050c0a0b1c020405090c070305042304050c0415030513020901030302070305060702011125020901150210020a0c0b0903 78
    0x1101105082400c1d414181258420144045910792554148000d0303041104107282603002c440b0202c1025a0301c40000004a41205d540e500ac01d40141c004024441003145d150409015551650307010030881c50000300340c0b00314190f01e417090b201607040309104d050795042c07041400c440709022f50100c81c00700c4c0415020880d1800c0940c01f0828058001c1144105840302c00c20180c00c0300c116000641c00c160400c000115840400341c00d4042c1035070001606410103018005070b500824034111840890fa1010700e400601800014115120340e00d040c0004480c4d110341c1080c2d8042c2c5940020a00d101030b0b8821090700101006840c10701e6502c1c4007500724005030b80300b0691a000e548a94080c21010745035180003894803002400300810359040440042100a0703440543e08034110f0480303655280c200282204c2d484458504c0d0181d0000ca204001140c1043d4140305541040d0180c0c3c2201c846100d10750f0034000301d00400e51520006120709010501051280b404150000703640c0b816a490407070144100c0030b010 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 350369712 1250 350368462 350368483
    0x12f060907080c04020918040312020d0615090e01090e01091218080606090a1a0409050304150503011a0702060d051e160c061a190302041d0c0d0212 65
    0x281d00140c002c0c066450140042519000240c0741542040400400078160544200403100806444c5001609241c440d03039010a0308001c080701150307644141080fa9000c3c12490183c1801096030040c3d129203140314502901c12561407004124560742401c1c03401c03025103624070810302c0c1036484449078004108800210100c22402ea03d400d401c011400c06000041c0080e03501c40006504140c04218803501c60581c100e901500701e941c00076040c4c6416400441040c03104514035046403030040054200300c0d000004000740c850000700c01c03d1070358200804031258402406160788090300c44c402d96a091a525010b059801e00c000d00079414025071102c0d020440341c0031104062150801b007200a08110006c14407600310b8060b083c0e040c00321040181c0135026001711030b00180303070696500380e44100c0d020910394400981700040c406058500301080200d100a601d01043e849249000303007505c07a40440d4504480d90b483d047e80034100302c488140c10019200d65030301341a41c111345054180540010140640010b1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 350370962 1250 350369712 350369731
    0x4030f08090111030114041508071401050705011517010b03190606030807060b090a0501060c0b100b0a0201050109050a050405120c07053102030601050d09020d050601080f0c030c012f06 81
    0x80c0345006c20001039492115030611000071210b024050b00001243c614141d4080402098103d405440100c9a9210780c140c0034216500e002c038007c500035a0300300d00340c0c11286079080b03070003003c038041107200d08840103c0701c3d45034180c0c007034030345500700004000e01c0701521401403c0c00280641d8a40f05c000c0e05511842c8100c81a6980300807942e840c1c640381c030440e41c0126071004104143c0d17040c03110107040303c0182c181c05481052110009242205910084c1014104109190703480701c60700e0301c001c0e01170b110a028040d040c0d42401e00182c150f41c403a104142c49640c1280060214650251000500c0d910080150215014210021071141c6800300300500114078803808241548804440085840031880200221401041071200d01d0ba03008040d21400300031224001000c40d01d900c002030300d50304d03003010080180c00f0f140e000003107440012805081c2c02017041d0561b40788008001c01c140d1a013485803a203030701040304484411512078405500384905014400b9110070300110043c440c2c076041044404110 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 350372212 1250 350370962 350370989
    0x1030e0105100e1e191b1209020307030203031803010b0321030c040911121f18020903011503030219151815020901030605011706011b06050405060106110604030f080901110301 77
    0x60503170040c491001001c0100780140e01851007214000c010000c01c01501134510344840d8450107540c1c0600c48500116401030880e5034600c5240d4081c1e03020162548a18480c1d4a00740c1d41c66054100412480c900c0b440740169101107000c2070058000a07000500760600700032041c040410a00001c0c400c1c2000705103001c2071182c85200104503180c52100c0204000099490329106481150302044c40d0400c1e100010300c0e121010b100e19440c14024021700f0105903056080c00c0c80c441e0907074200200542580c0c040c1c0e00717962440031100708610200b080140d0061041c031100100f010060410b0b441460f1080300a0a110035040c090b8480b03600416100700d140310350320350004140d07109680521541004240a00309504885010b078503181e040740b00100024140441413900c40300080404245c0f1245981c8504200064100781c201550f40c0c6809018201c082154160340801c0250002101d0748036650540e201114a03061002c01c55603000040e0130a80341e9901c92070740c41e9200403180061800b0300140d800000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 350373462 1250 350372212 350372251
    0x90e090303060a171002160606030807020405240439090503011e02070203071805010305011d0a0f080c1005240306070302130f1401030e0105100e1e 65
    0x3074480705584103030482102ca90f45030300307922004501000d076017030000e00040c1c8800513654840038103d418503005003524a45040803080100c500c000c4c18842d40241c500708072950341ca0541141084448030300d140301d25030703180e921510352615411020070000c12000200320a01c161140d000000310300d85d00e151844010182c408100c5074002074000c001d00d8101c0003803041e00070a101a0082101c5181d480210310f80010719407007076441c2004060700030211301c1d002c000c1c07020a000c5400011b16083c0812981c550a001c3d001c00748002e450f1400c078181d0400710262022070395036030343c9003481c0d07205880841e82400e0900c07802504007024040e8000c0606941d60120385450032440d080076503d81342e03400c8669000302c042110190f4a0004103554080d081b42001607540d070200742821000310580c0e0040301210003541011070010000c0c88200860340c42a00c0600848070000103031401d0f02d50803540f40e090042640c00810400a954815a8001c0e42ca0000d200804102c0c800c0800403050031203101b000d00c1081d00c1580d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 350374712 1250 350373462 350373469
    0xe0a0209040b090c090112020405060f040e070203040308030c1e1303022806120204050a1409070305061f03150f0f06091a0c1501060f1103030c04030b07090e09030306 73
    0xc00012400701c2d4291a04d1400c0c403d80d500c2e074003a6403103550401120703505021162416a044502604e4028200c2d6219203030000702007400d600c40d00882969102f41001329200c54000802d44068075802000c4c0382c00c5941e40c0d01200600d0304840b101c00c241141050b50b01102d0414080200511030300c40b58903510690440c0141318007503d0510b900011f200c4402000e9074440c444041000540e00d140c0340005107078162031449006801a030b0005c992052041d440000d8001050b0340c00902428280c44c0103c0560740c0e603000f80d04442e01207540541000e4088106010074160880c0102c8180c81d0342000604c1d06040301a4402421041c2c104079030290401406008590320421042c000300642d141903521613080c40712290001030401210704051601184050344460144620a4180301c1200840015a5540c2004080702e10b01124031000c43c0e007600701c078066810040110381c03048084600075850946143c0e50790b1031100d4000d00f6801000180e81000c00e0f84404034016a01644400c0000d6450303082002c02c1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 350375962 1250 350374712 350374721
    0x1b0310060b190203310305071e150f0e01120207080301030506061e09100b0304030207060801150813061104140429010f090807080304090c03090f0b060a0e0a020904 72
    0x1482c09650040c02980301042401800b000003001c02655070305c405101130082039a9061a800c014220700400201045003900862044414408100b904110310b0b52180500c0e110070300d09114400017070602c642a04d03064002c9600c0b92840d2010b141074240d06001d940d14070101c0e040301c4000c50b69544c00100410a00c10308208031504102c0481c0c522034010310904e80c043c130344602c105815025103100b40c0041c580c001c05142610080104090366641d0340b4041c80c000791100310a00414010401e101c0010503100a012a04805801192207581c81d13030b1200b80026000a160400071511140c807040d41c54501c0403003602404c01441003601c01f4128000580c1080300342c80503070b00507412145212038003640c14003410290844281d000e080441d9071030b000d17410407280e681694000805600c150400003582c040c00000900484964070000c03c2103503145141141510801c8601170601404003124102085c0001d02c0103400100040602010710350b81c45411941e090201e4006100c00c0c1c0c045690f8189050a008 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 350377212 1250 350375962 350376007
    0x50a02040f12022d010306060206270304090212040302071202060d051504020412170c03220e070c0605061f030903030f05090304030302120c1b0310060b 67
    0x41503040a0400070149021080c0d80324100c03030490b5108144096450340303050b01d007181824464004400c1815a0000c510f441040c0c03420740000e18080380041d00790300c041100c80c000c449000451401c03410070700d1042c584000301d0340400090b0204220006005038035200030b110000070340c40140e03c6443d05080190038200c1d1580714100941e203040c070400c0103039684401c48450003c0c0400008054a84041040c074074403500209640061002401080650280c0c022901c50717403181c200400740c580e10501c1c82000e80a144504400c40d8800d01404081c040c10a000384822014142000f2007580c0e50b100f0190031510984400c404144c0600f00d4809112960090320f900060540b404e80212000b02c003031012105180596508044d56880c0d10000c040c8a80c100641311036085000b0700603410b1402102e0b07141c3e481440200c002d803140c10751182e14604200181d58020841201402540320081d461002020250105540c103004500c000490101d41e80700e00c0024120800d4400e45411030320000c070003012804203 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 350378462 1250 350377212 350377231
    0x15040609080d0f14030915091e0307020a211a01090b0301090c0e060117010e0f0915010e0403030e010c020f012007020d020f09040303140a0605100c141f05 68
    0x5403c014540c01c5400c042c514000202460342da5943c2003001c6007800303110900315080c00d0884040c03000c0e660000510100346410034031310034030200d401c480d070995034401c00d14000e4000c1e440c07400400c880342d414240700712140300d503901007442220903942d0941013040c000c0700a920501001d0060100202d10b100340780207003400350000c00180c1180d480d4100058414454071100d420507500144943c0d10a40c00007514543d1500d0451040d40c5072400000c5100701141d10b502909401d0300000c40f1218005041c1019084462000b24241d0034840d03240030001c0300801c1507041c13585070070f01c8003080542442000700741d0180c1c1e406404640d001c280110f01355008914400394440c500c140610813a00c83c0011905480e504542c0004c0e0f101d401d2010403a0000d035101415030112500c01000f0615405402001404207686010b83ca107607607040c40e40703080b40c0a034003445421020700c3d610240841d02803c074000520f809521001800981060300c80c1c40c140d00d0118104001441c3c404140a03880c045c01402e40120101 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 350379712 1250 350378462 350378477
    0xc030f1506141f09090603030e031002031303080a020f0d0923070504050a0912180e070c08070323090109080c0906060a0e0a0605030105030f0c010e06070215040609080d 74
    0x43c030480b03070001d0390050000a042c101d101d014080d21605000b0706454a042c0070305660780c10060103444c00b00c1e000d05e000740601c1d607040e040c0764203034421248140000161080c2844042d141112040070081060392481d03400c01401417110454005000c0c160042c4801040c1d02c0450324000c2e107a11007a03181d0010300d01d040b00d85014402720124400007034490503500040e035652180c220b00013600c85d002c0c002d81103900402d002c0e10301a03440385a8203007202c510105005181e40e41e004c030800040d0101c80b10ac00044004007040d002801080041c007000b806464542da40c143c00c800c20511242426612003822800044c078242d4070350300908008000c090b180080d140e00801480817070540d03200140350320300c0303450005a1082c3d00e0b8010600c0400e00540a0240350400e6151a0060700c503a05c00c2c01202d10034802c050383c015175500002400590a4010307074440d140e2002403801e000b41c94104000490748120058048981c10281e074000e400101181e94443c030015103007070005403c101e20b12035044c1c20030110 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 350380962 1250 350379712 350379749
    0x13050601080727090203060a08030c0304030828050c010f0902030d11031b06070e0906030a15140405030318070324020d180308100e0a090c030f1506 65
    0x450096014007541092500d000d8a1142d40c040c15010108503005603803d03160110f4248582da020b148108000e540e504013041e03d80419554a0081006409540d4010801400002e412030b0141c8000007140390000603000ca002c01010b407180788510302c07000080001c2501019248240580420900501000c01400c01c440e00804d442d412801c10250030b100c14a421710a8040301042110038080075483d0b10005d0850b51006a5210201560440c0000e41c0c0b0454000b0b861421a1041e8011400200107040d070311040c0d03076400100540c407002201c0542d076400302c0840020b010340c102807049104002440c0d0340c5c0303003200301c110203440001001001d550006000707100003001b9a0700f140c80b00c01304509201440d5400850b1001030311412030902c807000c0c10401d41c0300710512071884180c84280b194070303021181d81d10b0002c46a0340d01054468800481d88000203d8000052a400440b0385400350b200b0608023512512107014000414008458080c00c140a0301d65a504510801c0040c12142c00b0044070b0440 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 350382212 1250 350380962 350380967
    0xc0b0c0702060d110f0a0305060312180409020102100f0f14010605070609080712121109010207031103190c0e0a05010501080604020c07080d111b03070308030a02090a0308030613050601 81
    0xf401e1820584a42d8030100b88006103100020f0312255507401111135130b16040e41074001d010700415500d140c02032243c10026120172004400740e071041110aa0fa02800a00c444200405823050080aa0550013054401101c00307440b8081c1070b801102420010031031007888805a01101c0c1d00d81650740e460030740b45005000c019404400c44a8054008402203011405400c003101c0c0e070f100e0b00100510502401c0b000c01880c07500b0402c00100444048001c00a40c030341b50040c07080c80c1c8900c50555006811040092000810054035621404000b50032194841c0101d00c100801140d032650941e50b01c4805d500821502c41c110500592000f0a06000d01581d454900046e007a90b0002c0c061521840c0c02040c51179031500c04100d46401000c1940480300601d0078407402030000180e8049848090085061091980024840310a014803007e0001c11010b81345840d1181590000703084240255020000c5006030380e5031a540d20091405010400e41e42c2c05d125003000200d44d2107100541e0310314285400c00c4a6680c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 350383462 1250 350382212 350382217
    0x3130c08070f210b042618040b0a050a06110a0606060324080307031103070b0f06030f0f0d0f020f06070f03050a0b180a0b04050c0306010801050105040f0b18030a030c0b0c070206 78
    0x2d80c00020b8141c0b100301d018880d2400c540c0703150406000c48002c11f040c07043d0408032407256441082628104028500c040901480d002240691034100701164804c1180c5d6100d254607101c045034060130380c1d028000da6521641601c10303942c0030000107a1036a19038000c80e12981c1203044440d0301c0059171310a291500f1a450307244d00a000d0041c00b4001225141c0015000170301c11030712055413150350100c0600d44035000d1084864103540041c024803404440d10b450302e00000c0c041d904001c03020000d01c104200754800321016100000820118010f0421004001c90704001c454001d00040c2c42e64030b00c00c800041c00030202c501c001d103010320080c1011024003564943c0358a102c45484041300050041d43c0c0c1c03610580142078104107890b0031500c1e2504115010201c2405180200c100741e9910b80d940c0d0781c500044031280101c3c01072007112440b0340c80802894075504020040d0091001c002c040b10260f0400013030415104180c1075000c00c0c1440c07900420000e1024440d03520a8809400d103040c035145030085081130 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 350384712 1250 350383462 350383471
    0xf0e070302090f03010c03060e010803070804140406050a1205150606090f06190e040c0207031e050120030f0a020f0d090203010209121005070804030503130c08070f210b 74
    0x3540c0007400d50155110780031802d0070a500980244940180454020018465845008040d244160000c141017001104440341143c21811007418141001d42d240000d03405414030641c0711f5510007001a8a4036041d41e42d00c0107040300f2407064141400c80c180181015413804503000b00c5404403040044035034851042d00d03001c0c0b40c192081c0384845040e0002c1009c51103003000034003c0200c18110380c0e4080e5400002c107140044140e0302800640840d58041e039803400d46000003414403401982c5846940b40f1088038684041c0220000b04003841c000e48007410445008010038412000002044010107480300b080d80c2060414500f180380c060011003049540c000c5100343c0007403c0d01c038480c40b82950f6094060340d00500c40100746207206046081f00c0703503407005801c14580d1181d05110005071034600845060780b045030161181d40c515034807100b50301c030f404040072002c071002010582d0110b19414100541809003640d6404040c40f141071420300752038060018036001503410600000d100045000902179000f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 350385962 1250 350384712 350384717
    0x412020606101b1416080c03061b030903210a0c0f1215051c120503010e01030b040519110a1e170307050a05070501081f0612020d0501090501030c0f0e07 67
    0x502a140c00012840e150054aa00e48100041c0581030138507901170004441484e0101e9032440c26400516460f01c204594a42005900385080341e800050390004560060021003034a143c0001c20180116429010034800aa50768000c200000710036144110801078034030b42809131100d500038000070300340001c905150070316540344c900c541c0000c0c8408440c4d9000e00b400500303c1c5458025458403054001c40c40c101a900c1418626800250300c4c01002100e040e203403448000700e11a070031621030713690304080503200b21413511499420381040000512600e00c0544907201e03400d031224400c8100030841e00c164011060078290182c20441e0011186454021642080c0784424000c80410381e460a5000d1a50094680e00070007010500b005004030f03204043c0c480982716030b94141c848124404201c442c500e900d14100341c403070318107201c1d030b83c000c440c070210451055802514006003803c850065038000c2e403040880d0340d00d4000500c20002d13503012000242450a489080c26890901c0c1480c9070345025014405 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 350387212 1250 350385962 350386007
    0x3060603021e240c060903030709060f0c0210050403081204020a1703090f030c120a1b05060a11120d090605090a0521070606240302040f0b130e041202060610 69
    0x20500c0c03040c3c064a0b03444c0200030644000b450b08000791503c0e54070440d120710000c3d0303a000c80850410b0140701c68800c00c0140d642c03a843c001c0c5455080c450f82c4d296407803160342448000d06c40040014203000040c40c010480350703201e20060408d0b00c188844100d5541080f0030707030342c41d9000a246520001080e12010401103c011300942a4200801e0520440100240d000406010105e29690780040c001c550a4440c0350000081c9285107042c00c1c8031451402081d41c400000c000208e030f5184a15000d0091201c5982504d001c803910503c07106043c1d00241d18104515101d9a0301004c2c4a5640b140c56800039800010b400c8820160365003584504540204044c2050a14030a18041c0c1d00350040c0c402d815400081001840e840b01000c603040500c2c60300c41200c0380b48115400305064030034000e4508541400c94540604c0c2d041030b508500541041100c120079104407480000e4441c4241d03d0140201d002e8200700c00710031100d900082c1400c07001410340740110503082d030360306c80580d010516400000001c4980308 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 350388462 1250 350387212 350387269
    0x6210e2a15070c0509041428030815060c100f020405010507080c010b030102030406140915160c0c0b070312021206060f07060603030809071a09090405030d0603060603021e 75
    0x5200b1107003504520b8010785c1c1003040004010ba09108580044000001c4441c4c25100801800711680365a111924206041c0394a0340024040c8014641050020321405036114698000c43d11580020840145650006c1c002c101780c0c55981c4914000d4140d41181035103810704140018140b88568080200f085c0c3c2c001402c6040507200394000e884000c40200207540da8205428000054540507d121502180784004554280300019110300c03508015604201d50b80d80b0720110181c913000548400050250352a800400900c5004003000a0034140c1c80755500d8500d0b90034001c00c107100c40300b200d40e0400d204014600000c40001c60403540403508070703451580e0f507008203c02c0c842030254640040c410b070705040d40802091740000360759210f40000402c9501440c0c1c2c820400701c60401800001401c5103040050520328200f0503c129130141c040c00c1203a2034100d040340104202c40a0342d0054400c9a80c4150900442c508110840c583c1440e002da2042010344070720004181855601d071642050381d4070002c40 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 350389712 1250 350388462 350388473
    0x30309120313090203100e0601020a06020a0c0203030304050601030c0e010b04120c0b2b11070f030504150206060310020403030e0f04060f06030905010507050403030906210e2a1507 79
    0x100d0704642c021040450090b501c4035814040d400c140c82012180c0014407011800d000b16000301441244140d005003411540c0b501ca8030025441080840e0030000d1011440016880400c001d5010b039102d200203180715895801d21840314081c50300714090345603050004001c103200e5003090b10240c2d0314050524029862503d007441c071b105100c0c2c1c400390304c1417030100d2030000402c1d000c1d450120b407489015001682d200304044220840741907150710841500c091220f90045000c83e06071900492003801e140f40707040c1c2c9480f5284201c100038111600103910500401c03c00341818001000e210010302415801c0c0390955030090640d080040e1013034000c900c044120800f030303521900f10000078012075002025aa40f10341d0010040d02c2000010b0f00c02d9801c05000c03038459031088040780d003101e4142d84c850303030424182181100d1141c05c210201118030346042000441c4007007807050a0758005100010404d01ca510746440d40c00c1020b0780f51070304d441c0c0284070b40560182c03074903a0188180c9401709007c3e0b0780c0d0180380c07400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 350390962 1250 350389712 350389717
    0x51003020d151202121f0b030a020411070507050109120b090c1c1e05071203020102090604060e100212040b0a05130603061a0a050403020402090f040c1e0801050303091203 75
    0x6004002c03109000140c020003825030880c9040c000e42c0c1c0c401004c1a101c00389a42c43d030041c0d080c00b00d080340c910407200501c01e15070b1080b101c00c00700500344c2d81d4804250300020180ca08400f0700c0704900ea40090090100720341048000001c150a080c4959500c0c985840b0044140b20b0208c040d05843d1918000b650103e002d201844001e000245541e080e03100d8011140702170200000d0031281c5002c00c046d20200c1031850b40d2031141d007950010040c0041402c1c001e080901800d541c008600f0b543d003c0c0003480a035540c003c040d10107406556100c5007180051820007c480301c81c0120345040d5007019940014880144e4111000d4410503040b25945846801040340c0b94401c1104030042c200c2c0e00343d40811b1a50341600020201e403002d5402070390080d40607115040c40d1245581e082c0100c0d000700410001410f0a40180601500050402c00b01c2000040404c05940300d00100c880011151074148035282803c2c000191840d00c1c03854180490760400c030100f990380c800e4030001d078806e5844041060424404004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 350392212 1250 350390962 350390981
    0x20306010c12050c1009050a060213030c09090605130b180c03070902190203041508130501020a080f0901060f0e06060f0409150902070b0708152205010609051003020d 73
    0x18892464040000d00800542100802600502170324034102e4001060f03000e850324554005003d840481c180c1d69504000358421890000c01815140d4000041080150040d0090842240100382044986054412103030700a2868441c1a280f4071003602007031400c00f01c81e50280b541402c403200c0c80401010207141443c002c05c0d0075414403501c040450b4500c0a600274007201c40e1a181030402440168501f640c880c002c034050902c1c1944440074480102d4801c016054014849200690550515440b500e0036030340412000d0300881c8801c0c0c14050308603d17905649900072030342d100812505040561300d002180d1207209140741040e83c0c00110300c03039a99040c22600c02410245c003460b95a5a01d200d504090120034a0f80546080000c4000030101403c2c02100c80c4150301c01c0203003000340d035903a0003a29001000307043c4202c0c2002a401505c0c107130b02d544c008400c2d82561141d141840d00c802980460a03500b0503082101080740c1c041c2e080045866280721009407040a003001768952104900c0034004001c10003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 350393462 1250 350392212 350392223
    0x20f030a030c06050711210d060b0a0801050a050f0603090313060917011a04050a15140a05030d0801060507030203160c0303080f0708060609060405130e06090d080a020306010c 77
    0xc022000c00d070700499030071240c030b110741d1003440b8035070300c4001c10343d2600340541c88100241c1013a41c04d001c4800b482010704110f00100521141000c0c24080018112030b40e94100200d100c10015194040a82100b43c4c1801040211350b03200c41c0a0408001c640090000f0b250395000e40c40c0030010848800050040e1004114100e4880e440941e039414024040c01e100c0c8100c666090a4641c003008024040c010303002090540041e401829031008107100c020400108007914140d030b01c2c1802202c2490600403080101229542c0b24050a28001041412105075000900c00e6015100300507104d03070810050b030b044800c41e04240e45c40d40450309050f815403144040c542e01c81e000403100c41080103035408001040ea4041d0b91a42e1031542c50180c41030646905480c1c902c0429500c0c000074156150802c010100e0b0400501610b080c50ba40320080380e020846288002c2c2004c0e160601459211002c0094aa000b683c000040022910141011300154000340280350390303d40000004040d64000d0030f0800d21994440c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 350394712 1250 350393462 350393473
    0x4061a0c0120040617060906010c0807020414150117040809060c070603020706180203070311030102070501180201180f060c08040b071b05010f020316061b0c0c060f120504020f03 78
    0x40a140da510743c001d000e60000f05216000e1000d001e070f2401c02da5485698060070004440e11044010b64400f2140c0208031901b031420001003005807074600401086032464807280c8814104074018000d1185402c001504212058505003564682c41809580190f00b040e0a00e60f10b648400c04550584100640000188101200001c00951507070040071524000c80b02080b07004107176a40620100344440c0040c0d41507112010500c007203020580c4078002020002c00040c609105e83d914607095034a040b81c8204100120100c280a65822062104140741010081030055040c491940c0312090395010707010412810b140c8580c2080440402c4070003402800d1001ca071100b20741e1804d40c0f21000031a0b0740500301c240659000510794021000c440605143d60003450410750b0701401c0664000307100c00700b0b0703074880d480701304090845844e10110514681183e90f0709500340100c0c1402041151142d020504004040304007425003507001c0c001800304035030180702242c65141e500000d090f010030482c03501c0c3c1c1400303003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 350395962 1250 350394712 350394761
    0xe011104030f05010c1d04050901020c010608061e010b0412020a09141f06020d05091c031206080c1e0102010f0f150b0f091003150e0702010b04061a0c01 67
    0x700381c454108240301c0c3d8003d100c031050301c03482142d81801c3c150402d5001094885c0780768003841c0c01d070007040e48010b104000600348440701d500242921071560041d0704580050080c0940c407110505134208a4210700002600b0303525000c00c4890364402c902c19581e00308010050401150b4404507480d001300050101444416100d65541c01042025070b40c7d045072603229201d80c0d01d1440da0300080740071600b05401409445c028600242c3c0c0c0c40c1d209918260740000842000585c4003141084803030118080c2e640c82c2d44401c0c089034900211100c039000020725502c0140c000500ba600c152400c0508401c441c0040c01d1640b0741c40c0103074050452804581d000604090300180758400c00d81c000c2c90010010f905c16403038240e0343c84002180c2c2c0704101424070000c00420070768140781011a40e1035821342182c0390000d280303400e4103000c1c0130201d8030703030050051010100b00f440401682402a5021035204580400c48145403030146100604841001c00700301700b0200c2e0300784c0031702002e502c00395150760400c0c0112540321a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 350397212 1250 350395962 350395973
    0x6091014071a01150c02010e040906060503011d1005040512070510060e0603120918091c02010203240a05011119060e061b041202131404061808030a0e01110403 70
    0x500b40031340d0200200e40041821401d104922650b00980c041e1903440c1c1c10605041800003a00941c602a15015198440003500751024880c1d262100003408007482c3d8115006040c41c1403070708030b094041100b0b00305002c2c0300100390b0110340c1c0111070303032055621030382c90480e4a801421f000300c40c448046950318011000619000300c20342240b094408038103440c085c469508011030203016021603203801280201300c0810520319401040d410400100032201e5545660408408210a0306c08040040c2d40100c00c0c000b5410a0200d00412241c005807541080f00c0600c020480a11462050504011940500045d081024040200400500c1c0441104940b45041c24001703000480103032403051082c14002484421681100e206996583c41e826217001e140481d00700c02514290016640070b20a804400c0300b228491081100e4448201d05a10755460282405811100c030b0b140380200484a8100d140c0026061204136035001120100008100c0d200700ea00c00d004080c90180c1c080e00c5c03000014003005221 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 350398462 1250 350397212 350397263
    0x60f0504050705130c0912050c060304050c0f0d1101030b0103150e04170406050d0b0103020f03180615180a06030206070b040606090b0d02010c0203101b020601050609101407 76
    0x40041d04c0042e80e0a900581000c126070f000c1803000c001610040040c06810014034851411900035030440d00f07030b00070700030018034543c0c015101240c02d03038420965030041d07083c050508003031400222028007802c0c3c255201d0624003016000254101a990004091140c3c02903000c4075546a00c031040401d050346620441030905c10940d4181d40300350103800c4254115542e03a0454095600681e00c4a06090140c00c3c5140680b0640601d42c0c18180c00b80718250501c1c509102651051018400c1d08400d0303008400c0c4a424908080c104038118906104c0810743d6072900541c84690030054000021165a80e1510718010309894000941c4030b40c0000345a400e1118020b144c03800385010703100400002c1d41d40c3c1642da04592a00c0103c641040c45211040003660041034042d4034240050280d0b540c0004058004d004c540702d2002d03640030900904920f06510768104030050160500742e409034a007100d4400001ca000700303080d04d100200204503081c1e14030708002c3c09c2540e0f60140d12002ca0750700b0b0114200f802d00b820 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 350399712 1250 350398462 350398469
    0x4020d0c060e031b101412070302030403110a03020c130905070803130905070e040c020c030d0210060605040524070807050c182e050a17010c2a060f05040507 69
    0x9109100c00d00c540020001902d0329140d2001301100c116a0b010201650950030326076480d44144418003c03006141007d007200d40c8200e00710b60380143d07245007516010342245001c2001c40d155901c69610940000d4000950011169084606034201e02403018141c3c0a0400040000d0541c018100c00003141d000000150818800c00d441c1217020743d0300d5078034410803903004540d04000100035000307000c3c142c103003980800300c904c0d80d0f881955000f0106201003445d181101c9004801a4845901849174081300d114640241201c0c1c5801c516182c94003000665444059043e0080c02103180170b04240d0b24141800c8520301c075407240c021500e80c0e2040c200381e9254002249061300850f034103032000b800001b031040e403036200703c216100c0309001484c5010000c00c8130615400b10f42e00101c40410204030703913480c254a03034020080780c0f82c04403a648115840c01e003076130003640b07468007444581100c2d00824854061021941c642c00075002000059038205840948a89400c50fa1140d203000240020b110000c245281075 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 350400962 1250 350399712 350399719
    0x1f0207050a1b0e1003080a17070903060f1509020c0a20130225020316030501020d06060509101d04061203020f03030c0d091b0b03011a0a1704020d0c060e 67
    0x50036640ca50407100002d0071600c5403103a070381e59581171001800d80e0014014000241c078081d052290b4920402050700025524640811030f40401001000300a0040580602c1164001e00c00444a04009012501c80d40220510284c011603000d10101080019000454001d910420360750000c40070407941a51035000c843c081d0345440b045400078441c50003100c030400f0078680140220000141440c00801248204a0f0f05002d00f0a1a401501c0c080b0b00c1c010185000300d0005035603c1004a00008542d425030141c000d02009002d203090a5940003110b0311304103450304080c0c040c0114000850030340c0d8000d410059115190403008100d079410b0f0750764013500600c40d400310b8880c02d0b84442030760b95030700040380c14501c0d102e0200b05880400300c0e1900a0901c081c891100485503c3c80c3c0c2c0c54840c3c030700580790051002e0280100042190044601c0e92010385051004d0091030f0121210006040c403105103101c07608001c444002c2000c546035586500620394104555a1035541c03640c100038440400950028071 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 350402212 1250 350400962 350401013
    0x30406080406240b090d080a021b09150118050405130308100b030c0a0e0607080901170126100c02161d040b090f061302010906050c1f0207050a 63
    0x101943c200c55015001461000410950301c0e2075500c4880b507010840007074200c1444081400041c1e20300c00541035000054024001c1e4411001061007941c49085100d882019030b20103004170b841c10001865031801e020300e00050039200002055000204681c0076a40040c9441c0800c40c8008001030032080840c403aa582410700d45507190882d00d074140900501078038080c10004a107450394107000030180301c0103504080803100d2194000411300d82000b80181e4200038002804a841c4d0f80c002107490340b41040201e103031342c1541041e00041da07452744803004041240c40c00f0458074100300c1c20401c031103200e13503e00810300c250280c0a40080d1180707519010050310030b01d03000010810341007040030b10314820405d0710f003a0159034aa03181c1c0c0c052904040c01c20b0015028400d07503402d0380701e41400410702c5500185000400500c59100040490745158000d000b084414048031142c040c020541d04111900440c401400501011600d0000c2c41010402045441910700d6241003141e031614100c22034142541e43c85 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 350403462 1250 350402212 350402231
    0xa05150a05070e12071a190f02030a030f110c01060303030e0c0f1014120601200303040605061513050301060f031a100f1410050a1d030a05030406080406 67
    0x8080e58000da454a0205050403005402c07420050004ca05501180086070b200c3d641c0c40300350b40200e00400d42d03840c040000004400da400383c03a000030228041c0c5907180007074441c0720015000b9200c0c01003003400030415490f40e440c1d01d051741c415040400701a071030702200f51b0303038469a200860080019100c210b001ca4101403801e008024041400403000310041c02c00d803201c031401c508100c81c0c107006242a0b8180154415003c1240c190300020b4011401e0b0200012030500b04031001504660200c52258103c1e180200f0001c2c55690100c01e50785c0203948190045899110240040d0401d4001c406050b0a003001140bc90448410800c40c4400c8810075002044003a4075203103035032007000c090301020700031009504904185403c290000740d40103007500e01c04c101940d202c400004c1e0740c0c42541c0c0414062060382c0001d10f0103180c84421000710011504149243c003006d08000762544030b99804050018101800d440202c5e1800e00ca04142e40ea44001541c0e5115264980a08220000d960a4501c80e20308113118 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 350404712 1250 350403462 350403481
    0xf0305090a150b010f360812040807080d0914030c220506060a090e07030906020a03051f2418030c08060106020a05060a020304080c0105010602010506040b0f0a170703050a0515 77
    0xc403050a080c0000d082035200500103c0c0c1c40031ba407520208541012000015101c8000c1c41078919800850030f80c155200c2c50302c17041e985000c0d416004002240c10416940e0020354010910504803100c0c000968110003d010000e0304248a0b482c9003900460a50351103500802d2000360320491040d00030f000c00503501c0d0a410710026004909082c0045030300400248210a10481c45690000c40d40c9070200b003029441e6030b29416a01301c25100404261504244100c010449043d0704000d900e0389404001d60b440c142d10210700d4602d5119280e072480689841000c014810020201410700d40403022a10540c0c0780703840c4055500307510943c241400b8190011805500c041182d00c0400c1c0c128000b400c150722400c0e4101e0007903002030320845100b90100001c8000e10030038090940206425000082e251400006008c1694540d454461280c2d01d00c1002c0b10aa40d0381280c00010344800d4000c0b02012428521014500b0b200c0b500050b003107201e0446010100440040d4000c0002d0003400520520344840804 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 350405962 1250 350404712 350404727
    0x50105030f03120f090f191a060f060d06050603090706020c1f0f0e040e0c01020c1c150e030f030601030b09061c06060b04080303160203040302010f0305090a150b010f 73
    0x1c43d585003002c02040ba20342248401642220300e04040e41c81070754603411020b280510710707454079850000c1403581906014503051402c524a0100460403010300d0710700c000800340c008211580780b044c000480d1018900c8802d0b446040030342000f4100b81d40e00d08000500360390310005032203043c0c010310078000c141c401da007850307862100c2c550384540900001c654012810348100e2070a030100c80c1006810150a0710307540d9603000c0e5090001804e0042c1c14070213103046c00203080c0440400214042e00403d2180c0380308400640b40d40d87d608d608481e041441c00251981c2d8005029000075000f0280b0002c6400e0f4030f03010460b00214000c910980341000720084134014031207240c8003111035940c0300c060304a900040c7c02d458803030340d00014440c803c002041030721a03800d28410380154000b05500d0b4000b008128035403005d0440c114201c0c141c1d000460501d85543e000a0002e412090140101070300c0d0808034001c203004011244040c3c0e0f000010440000385031000704c000f0101701441c1d40c00212880c843c4a0b546004622 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 350407212 1250 350405962 350405977
    0x304080f0c011b03021f09110a0f1a040f08030c1006030209010e13120c020f0d121202070b0f070e041b0e03030d090507030b0c0a09140f13050105030f03 67
    0x183c0c1c2500079511115001c80c060140419000c3d40522a6003030b44401e090340d102c803120b01110304005900003a5061039491042c01100b05801240294400d02c0700a40080d001c4049488210340e440410581000102042c0150340c03040c040b1650114011812181c0030018164011101c400c54040458240329401595034512010b504035601e00014451070035030000d0103520031241e0902000b04c0b0031580c0c402d041019115484000980840b0086045140c03459050b070100c101124201010072240e140e414000c0314a61020041c403c0c0b4002d41d604142054065548180d0401d00007042442c14401100014804850b050000741b08602400310b1407920b40b048404004036440e0420788402c201c6403c1c1d80d00488900046d601d84001d001c007000a081c28003c6d0344c00c0c0d0340325201a0144514500d05865580350180c00104c2e010001e002d29280607a0268000b421651007803c00da48604a2a01203880a2001e04c01150031203030807200e0304480007207504400e04032a015000c640303400d20b20505103900c9001d100d4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 350408462 1250 350407212 350407217
    0x203180304150c03021f02030709080c0f010f0c1205040924140109050d060911100e0d06061503050405100b0105120604020c06012c0114010818010e0304080f0c01 71
    0x5801c220b034030303208081e090035443c4240100c5142242110300b00c0016229500010441c0e0780000800c040d5550050810000b8541000108110100d0f10000f82015030020070b07150400c61412540b03810f45110b40140e200858020020048810000000401581c441d00801f6290fa00301003a0810b0019440c00e01d050b5001c0c0608003c030701509018a00301240ca1000c5072504100802401003000c2d41d99580300c850180c811400016011158942100c0f41e11203042024403404009902000e000d410201c862128402220010114185480e11700010805500f00300d05200c100b99101d014950103030711050003035003e40105c030340702441c0e44408800d5405a40c0010b00090003409480c03181e403c031034801034011000601c09410a4101d1080500c0c02c00700f640325400780c103251034140c5603844000814012030008a034410761198103008140c090020355001036810090208002161030004043c02003154007480024419104007201d01070303507a0010701441c0214050124140e00800000035490442030043c1c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 350409712 1250 350408462 350408489
    0x1505040605180103200c07060923010c080d0b0315240a0801020f041a0301140d03121a01120b010831080d150503060a020c1e010203180304 61
    0x142c1d8200c00562689186906250720f4014016035440140340c500792191a500b607094540c2e00707031111545003c0c100d61125051110090f8103100c0c2100f080e08020116007000f18841c564518840121029100301002800070100414541440b20041d00308680d5080c4c00c40450700b44c01c0300c0581400511070b040e22041c014440605210040c81000c452408841c0401080641c66640d43c01a141c04c1ea400207a40c000300c1400000e080c818021840114100141d100c15107905543c105080c030b003903000c5498210303840750444141040415120b008900340340e00242d5801c1c03090b000803890b010b10203550055001e000c502c5510740c640b2003803403c0c850050000b00584d18400b0315114000603200d000d102c40c7e01d4001801818148100002c0d15164181c0c20700d20906802d43e5030b00402c0400c90413551441b42142200850050070001070384d000840c1508840c0f50900165249582c1d1126490300c1c1460514202890704980f030f03c16600d0040d4040c51169074580321040000c805094016200e10a5001d0b010520015 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 350410962 1250 350409712 350409727
    0x406030605040b07210e030918070219020f0d0f0c060306081509060601050306030a06050c0304061803020705090c09040504150606020a0512030705040909060b030f0a030e040506060912071505040605 87
    0x36004030b06440441400d817848d081d880d030049051801358004501000c3e80003014001c00c0f681c104408000c0e02e8907038510032000303001640020b00700c5114030015031107004107880e55401e01103951851111950b00101e44000280e0324440034015040b28030070800e51740950340e18131410309041d4a8061082c5505030180c11290f07156001940c02c0c0c0c0001c0d003c1ca0f0103100f2491007400054842c07041078052880f01d6846a213074035280c80c2080589005c85458071003041201300305c9002a0b0002244801c0e40c82c11070700c1c503800340d440624034a00da0160303042c1c00b0381c010b00300030521007446180c2140243c0c1508d40ca10602c0100d4a0f14400d82e60384200e10f41c018030340e51110912122078683c040207150010030700c3c50300c1c80c5001c0d0307544041c0d029030b410200181d075501c1e51940d400d01e9034135003088895a01c9440b000a00300c0d00341f4940300038080e000564511030050391075000050260350380c0300c1140c6002000900e0040c0715540010503039952103050140d1482060040404545140500c0c181c8041315255a14a40b0300010b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 350412212 1250 350410962 350411027
    0x30a020a050702100c051002042102010311070602071401061d0a06050405090f160b07080c071d16031b030207020f130f0f0501150c08090406030605040b07 68
    0x10610881041014050b2200503a00d0f42c40014031456266905036416505041260900c01e22841200d0454410841007100c564800c400c81c075003141da201980314401c503034001079000d010007001c4c44d64805000501002000300c0e90340581103081c0a8a00c10b082d00f814450b6035400ca41c60f9001d1110342ca180010360006001c0b6503003003184d21400e1a00b01042880d030b54408101941d409441c9006150049a28000305503410410f601c0003003da040c03880f040718a000090b0b115841069000743c2071410004506054035002c01613180140780c2020b5200d9003a00052002101d0181601c008941d903941c49966083c56110b03010700000e0390700c0d0100706018041403040503002036000c1c1c1d40407030f0841a035030000b59880d82d66445000101080303400c045045d1400c03800c050b085511042411611a11340070040c00b0300d040350110344062600c0c1e4200301901503041c1c1021041c0703004140e001c9a02c030703040c01404020803120ba005180036500c00c1824070308988550905544040b15004200d0000021603044071784c014 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 350413462 1250 350412212 350412217
    0x5030610030e1002281409060708031f0b040806060d021908030306011803050715110303011202125703070815042003150403080c0c03030a02 62
    0x9041c00984140003803542801d00d18415000c4821541c08241041602d5881c6030810600b051340e810300510010039100039015a4281031001c0d00207001103900c00103900c9a00c12128810f030400c110b84e840c0d1030701040b051806000c2202c902020010340000051070072000080e02c0a482d80c010244c0101e070b540000740526804115000d0382d00040109c00b030342c03114400d6030340e0202820050001c3d583c0c038608900090141c10070700b141c51001a000100810104401150000039658141180f002d05204041c084444008074000c20b1490b00000000181d004c0d11a0280003200d407003500c1202200c2a80007030181c50f540c0a1030301104481d140c404400d603580d00c02480110012910020320000000c1d400c1e038400d524000c40503d0503001e20328984a80c24501000000010503520000f0907121840b20045e60088101500c001c001c0c08032044045036492414a44404842000d0b007140d001c0780031800c000000e500183c809030085807440002c0f56400390000222201c00b40c42c1e000440c07443d103849032544000d6 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 350414712 1250 350413462 350413489
    0xd05040b041806050405130c0f03030e0d0201020c0a08101104150e0301110a03020c01180f030810150201050a0506040e0309090406060302040905030a0207080312070305060102100609020a0e030d050306 88
    0x1903035039040c08240c4e540c540c41014043c04813a8604400030b50146071025081d1103c1d0040304c02050074040403c0001d90020001c0d89105080d55800b00f500c00718401070f45481d650f818015030115030681c01181d0f101000903203072000000400c0a11070304440c6e9502183e00c1c481c0d4040e01c0b10343d20301991400c003998018500f14841450140000030018000c4200340d040780c015001500000b500010440b81d045024010f0007500755070030300d1030400d0341e649039210310f41b40b940084000c5c00d004c0f15200203114910980075020041c401c0710f072104a00c080c1a0782c0203000b070600f00c43c49075100d03103404041000c2d401c1600c01e2003403608072800107602d0058084204440900c00410072034540da1a5071020006031190b000710500c861043d0021900d84840001c06410805035403c2204c0651040c00401035809100c142c107500480309080c001101d45602c2c004071b003000314203040e04801c1402d2090018003240958018070b0b1a284c9556803031700e00041c020406840741a100e401400141d41400800c070740740340ca41c4201150 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 350415962 1250 350414712 350414759
    0xb010806190816090b0406140d06020904050c071a01061b05070513020702030f150a02030618090c0411030f1501180602070608010e160503150303030103060c020d05040b04 75
    0x9036503503005841c00e406400c40c0400c014000c002005414491700034611540b4086500f070144506200c0c0b1210940d007090340d201c0c0708001c5940c09000340845d40d41190358500c0042d10a00040c60041440c1c0752b10b0b0f01c8020200e5180000c0c0e460300310910203a0b07803818141c8902c1c1d038401c8100c170615817000109029409080c0d03154000c10000048950300c00020588c00c1a0801d009615003080f80101418400c03007056000f550381000648058000303e0342d1a0340e130301141c01d40300180c6a84a19000c920294072039403410400140f61b030140300880d0000904070048020480341400044203509008005000907558005104900b1003c600e4140c41035000200c0c181c010300d070503000d1013a805098408421142d00c42805604664418000554491080c81c05010140c0c4260040d081000c6640080d6459008130b0003004000300101d100221032000180074017400804480d12543c40341440300040c0110041080544150f00700e0b1200140500162012154441d51580c00c062604500a000c502c00d40132881c0d4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 350417212 1250 350415962 350416009
    0x60e0613141c140d1103190509031005060907050a0c0206180a0e07080703020a1b03140715050f0c040911041a2703030f0f0d05070c060f0b010806 64
    0x840c485554159102c860150340b80d02401a0a0a1020b0070b211451945804000c08610350b1001c05200204a52101c840e5540100480140c560121294001c072030000b941402101494100c00f80186c004034001c22040b42c42c0240d039241c0000a86445c401c1c1001c20000c141c0300d80007040586000e202134101c120250000c1200e0121400000740d00e0261600540c14280c0381c442842421a40b00701040d601c0402420210710305912a00040c041551410900d0003036180b54442508142c4034480c900d4590898088042d191603680c5480c5030032100000c1c500c5445881d010000b40e07050214008140211912903506107441c1c1402003180241104103441030740341404000c001440f101d144040d02c0c100704402c540d00d84940300c805120744c0c01445600f600c1d00003103440400c407180d40c2d000f00485100092400300d00360b480501c0f142103040b40c09001005456140390070100603c1c15000320035030580a104d004204000da5000203214200c8007500010350025044000241e154100040442030000c0c0308410000c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 350418462 1250 350417212 350417239
    0x20f1c0213060f0b03070807020607051b0709110405030f071202090702030f0d0906050916170a05070e010e07180605030711100b010e01091a31060e061314 68
    0x4803200c3c100d500070f1050401c00410000c92a51001340c187d0040a113201416103810701001c024120f00603c90800c140300c0070314032081c500c24800c00814008105050041c4021f41c1005000750756a000340c45a0703070203400f40c003c080841040101701602602c6511050343d0000c0d0782a02071201c184030080032041503100400ac00c1001800b240c000c0e00d0f16a0550f100443d00801d1850103006030340d009000e5502907801300e10381050000603501c91600382d82c00003004e050444c0503e05410b02d010300010001d0002e0080e100d02040812448a986041e100c0c036008090792034a800e50101c1e4680300f009200c00d00d800003c02c0600081e807003803000b50342090882c03402007200c9c5040c885090604041050b2201499a03803103440d40c1650b0084040c1010f8a400d0801d0380c011403800000121003c0d400d98a54070005000820411050001340a203202c1020920383c1070701350751681c4820340c0585860280c41d02042c5a081143c01130310702501114400700310303e4003003c070242c5090628060440c502ea159a8029206a00700c0e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 350419712 1250 350418462 350418479
    0x5070512010b03070b07142d031c0c170906070e030a030207090f0209090a0606110c01020307140a0f08030a050a0b03030904051513060e1e04080a03090b13020f1c021306 74
    0x108c607200101c141c0c140140d0814550300d40450307461000b001b5541080c015511081682d02c00d0503c2c40711020404103401c46208411904000c1015861008291000c10301102100001d103c61003441c80740c4038074103244d0642c403c041e0388800f2301d030005005a005520511480d450b681103110325420983d409820102d1500001d010f103002210303d005243d82e102c40421a0300d0b803150100f0175580303001024003c1d5000340c00000f5100d100b6068043c24802709a040310408140400c01c0044c0282c000c08034003495108c515043c07259070700548001070b5007070030200401c1c4004100c1c8142080c5400040045140a0030300043c000603020041800642c0104850100125282d40104844801d100200011a107051201c504900c0c00e010b003882c17118244459450718a481d4003070800c1e401c0ac2c0c20481140e142c6081c075400310042c0c90040001070101c1c5582c8148012803600c4a010358060348229131180e0b11030303c00d00600030170700208840d64001c00ca40c00c20400150410764081500780c0c03a03400000c00c0d026100c8042d03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 350420962 1250 350419712 350419723
    0xa0b1309110a020c0a060c290c03040b01060f08070f0e040e0c090c030c03040221070303030605090702010c0e100908010501030f0c12050303010902030a150305070512010b03070b0714 80
    0x181c501c1c4400128115102d038113104030345004400b140c1e00303032070a420541700802c1a13020341002030840502c9603c49000401c40515170740550a03070b0007100c6580c035101d030180d002c5420688040701e003203201000120b00540111032910001030b107561100a5591407a5044030340d500c0b0000071701c06220031425542000d0300c882c040d141244200b000100343d088807a0302804500f60006208000d400c1081c0140428440322100b2070f5049034045825421712100317000c00170585000b8168130289441928030000400d0b8142c0c002c1002c0f58001ca401154580d11328000380e080c4e0360760f640d61500050940d501d0500b14500040105a10419403030001d1100342c6031800300d400c5410a030015900c90720544036071020442104101c1c00a030074410203150241c0c4282c6da030700c4d80c4ea02060141c07448003a0040006522103099a0104100d14001c00603201640c0d44d80c14480c2d00c8000c40c1c06014015075521031110749414050044c114a8000600201246032030085041c101c1d40003202c007203402c2a094034100c0700d07002c0e0030000c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 350422212 1250 350420962 350420981
    0x7170906010f050103022107050d020418050711070e10090603061a0307030b0c03060f061914130e06040e0d020319030c020c210d170a06050a0b1309 65
    0x103099950402c0070211105031241e01c00703030402d401080803040d0031180344902244070441105002050b00c0d92081500c2034001c4840410083d032000c60002020f0031132140820030007650940070040d5484101007100c0c0b03030b40300809820455004160810076040744050065206600c500000c030b80c0350300c402e05a0b065170500e41c800c2d208661100d041c0c102000c43c0016a45800b50110b00401c0ea043c0340d039444919107000204034903000040440010501e03120743c9404146c201004007002d82c1c0c1c103580c8950400a6040004110000341c0324014110400c9001040741c0f640c03801480d00081962900c01120020907006042c1a005901c034115007150803010410120000e00c0c1e80c000c1c54130f40c481c266407200c669440d42c50300400c050406402840084d00494501d03004482a1240c4819420701200007102c241c52403083e010390310038603800510b4558000100c3c840394440c6412400786840d00c07004201a54280e000385a07102d1410b0078204084042d400081c298800c010b051034404540c2c0f030320b00f42c0c200c0b4203046 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 350423462 1250 350422212 350422231
    0x306080d030b0f010206040201140d0f1d010506010509030309120a060204080a03080c0f030c0c0a0b0c040303271707051503010602010f200702010504030c09060e0a06080d080717 78
    0x180c2c0e6000349840040609412402c2c4010304481c42c143d000200500d4003445201204600003550b0340189600f50408080c28905800c1400310703804460b04040000314454103a5810b501c0c0c2400310b0701d0342d071090301150701d5124010011400c2aa0300c404001c83d4a00c561015001c2e072040c9031030316000030f8440c00600005e0003d000178003002e40450a014101200042c0914001355041203a11100c440600a80340c000418250302501c1d04004019149082c5000c2c4003d002000b0820410500350900c400a0007628400d68070520131804071b1121810000c10742e0214842c5014251052140604a44203500f03107041100880d5240c0da034801c041002c042c0d5045040244050000c0144101c0b502402a48001c8050210800c40c000329810181c0c4c0c515042c5030030030804100000c680040d680b181e41039402441d00525954105642d4a40c0000180710a106171011700781c00000041c00d0311070f00e03c580b604581d00007002c6c14517a0111402180d4119000380070340300b88562284101a5020200d0f5407a00c04c07003081 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 350424712 1250 350423462 350423471
    0x303040509010b03061e4501060207081c0509060f07030822030206151201020f130f0f05010513030501091a15011b03021903020a0c09180b04030306080d03 68
    0x1c0c2c061000399461545080c0c03c11070300084035003140c4c03a00446400c0042d6214415485005444444581c14140e1170305541d5800c7e020505220007241d002d50241220303034580071a4a225600c1010545842072b01410040c210f40003000c4001d414018001003001a01c001e0405103000e9034a01c076041160003555084e40081c503824100014104600034103804e402010351109426036040e0750095503080000c1460102880e003140352001070321507801c0700120900301c1000359141d1490008182c41504000628158000711030000543c00c1d510380c085c9070075900d4a1904031101c6090000540d469400300e40001513a1808600010101e0001c0c4030300c400c1c0c18801e001008000f06078001c50004041c002d0280d142105021303543d5541a0380101c0b51004070010051b550501c031207141400c0e800c00507142c06028210320038036111020541d01191044500e8401e40340212915100c4240500320b07210292140c101c0002811b440c4040360b8000041a0f200b031003844d0200b07410752141d80c42c904120407044c0c50030110380c59 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 350425962 1250 350424712 350424721
    0x307090f0e2a0a08030d0b060c031b070e0405061b07020603040f0c0b0a0909050405150f1e010f180f0204120b011d0c03070207030c0b0a020f0115140303040509010b03 73
    0x811120100d80b00480c1c0c02011582000d054603205c0c4038000d60310300e0550b0384841c10f03c0316445d45001d440841240b4019242c45410309002c0285001c1c42c40c1d0b403241240103030340003c40c000b1005803066000316002001000c05581c0d08241c2c04070840862030515038800706100c4500140e40e840002c40c412171081118494031641881c00c80c00c1180c0d41d822411001d903007440041241640004514106c5000100c0031496489500704907042000c0200c130030000441c01c01c10000448180b40740c041c080c1e0060202d0006141042c039035007415050a028590801005540400c901e1040801402215007811800036810060300d180100b260310907806414040c441c00450700a000900300c56600401c0c15030120708001030703188040040c402c0d006190626030a40072000c1550144200040d0010f1a0301044408282c4d44480d1036141d5a0005ca046034014840d80e012051600c0301030044500b00c200c1e50400c003950302d082c1000090204010305403140c01d4807040c80b0000d9a6500c00d28010300030301490442a5a9040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 350427212 1250 350425962 350426023
    0x90311010510050603060d020411070b010317040e060105070501021201061107050607050d0516051504060c0c020108160314100f0b070309050f060d15080f0c0307090f0e 74
    0x40c01403036030300c0c02d212403031080140d0303200c1400703e076031006088408aa0300401440010002d00300b84001c28160000864071204100b08003125906a90140c0c1008000842884441415104d20f02422000380818030129030507500503400740000c0751040c800581000c5070050b0b030b00f404840036400720380001d51f804a07c4011550920042c0d0280000f80e0b07865190500580b9031a83d1030155111745000c100000408680030709464080c074100d142c1c4103040d250204016040283c1328142030724140c929510346545031207814012142040001ea041c0c4032402e46540f83da010b440c014101d0340c0700c1001d041e01d80f07421805a80d550160300d44100e501c03092100f803503411324000c032280c0c248503003240c9020701c000c002200c0429081400c00084580803512000c0e003e0a00000c0703112401108261038555081c01030084900a00940b040b0030b0710091007c03120614000070b023203540d4481441050360103404c0000d051103200102c0d04800541c4410400214441020000319440e00c0b5603031220b5440d88801001801c11280c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 350428462 1250 350427212 350427221
    0x127060e060c0601051005091002030414060307080703050604061703040e0703060602071401090f03140c01090b22030b13060507050403110103020c0c15040e0a0c0504170a050109031101 81
    0x44060396101d05140c200b1007459038460040c040c243c49000d0000700c502d0000d10a10481c0d03000350004c1c080f4000c42495210295403a0880e000d0f5254400300c03986400e51508010041c0c1c0d10030401584e8440880d1540301099004041c05494541c000f501d038400401c45120408403200d03620b54460007140d0300d07490325089000712400076241c40d04050802108001c46940000c03a20190340907036400032004800e0800595800446d580941d4200c60b210400005208503560240c50070140001520420f4403031800450391171400303001e0807501c0c1038103000103e005602c0801c4a580c0010754800c2c5404142c89841d03803816141d0490b0004640480700d0100b42c1007010074064079400c413001d4100340b0b00382403d6595001c10001c07441d88441c101036003c14400d0001c08100a18a180031000d01962590000c2500100996010740207540c61031403000040340d46d00c05140305030042a500b65a969050600f010540b203030103005c40b40c0b030707581c0d5200341310300c0d000410020b1095001051107610b07140e8628800b02000e90948 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 350429712 1250 350428462 350428487
    0x30408010e070e0403080a2d0c020607020304170c060315271b0d0515010318080f0702010203041d160f020a03030e1009080301030309050a030f0809012706 68
    0x30b4002c0e480070444040c1080e0040d0704140e240c100b07008241e481e01c403200014040c9001001180741500044180102a101400c0c214a06410203002042c0d070445c5c160b0340c4802c1565680010b03401000200048880c88040c0c07503d2801c00710645000034580c07000940302d03800a64814005581c0d505d01915030786001045040e00001c00e004c0c4800940c00f002e14044003041c008c00d0001081c15402c40c1d6041c2050a10407544103c00d610403c00040c180024034109241c183e0202502003860154820301c1c041518580300c001d56444044d192401c80740c01e14814076500000c004905521003071102141000c40c0345144915030030440c2c59a1751610700040d00803148100e445074102804859442c4072140d03540030a81401e1990103040c00f08090b6038001016143c44900043d103182c1e10f00e0801044104403e500080d41241e010ba91041c2c11035131144100400b240d207a01c00100001c60498040700012043c5015210040707050402c00d40c81c030900100105500408040310034000d1211200340440b079000900340340c90 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 350430962 1250 350429712 350429741
    0x50103050121080304030c0524070e0d06150e0a0e0d0e0102030a0807020c0a03030903050f032109030f040b0d0e061003110d02032407050a051c06031403040801 70
    0x2100e480b01d04506214201516055002002070b0500d0300420408840d15405811600c0e500203c41c8198240800340d80c004000300402c0c400b083c0741d01d202b03050b80c039200d200050600068903000e030b07a0b910007032010405542d410443c1c291300050080019440340d100e51250310012480e415a0b800150510255007940c1d810322541600202c501c0e40d00200382c490882043c00c5c906850345070148281e16024180c10030f194001142007000c010507034480092000c407841501101d05104240b85a16128010300590100c107842e050200c00101100302c2485411a5402040c0c0e131078640009014065580325401070400c0b0380001950f00606903961044014091101000e41800d00704540802a03000143c4400342034046c0ca5500020aa6a05074480d25901d44c020300b1915841c450021060a0181160001c00224400310001c1c0016018500b01e03402c0e540655540380c03034079031000c00740c050b1400025800c02e6010740e2680003000280c1581c60340d1a91201c60401540c4030341c0780c203403614251189a10201c10 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 350432212 1250 350430962 350430989
    0x108010b09040f0204021c0204090905060108211b1b091003151e090605100602120a030c020a140f0c18010509091507180618051003090812010501030501 67
    0x10901e449041030243c0e60490b400341c3e41d84403214810303244241000566182520011380043d210203158040f4501d584a041500c00c41da0b641d5244607110100440901d41a494410035112440010383c000c0c10030032440c54005444c040102c280c9031034070b281e8030fa0034141c22251011a0415150070310721982c1c0141040d00c1c01d0026421036841610720390011311290a2180c855000e019102c51481080c641150503c0d0204004100c0b410400e01030401aa000c8402c441c1c040d40c0804c8183c80840c030350340c841898010081c1780443c5010114001d0000154a00841c01082001400181c03103480c0c130301601c41400010a0f07500300385500181000588038100d445400011300981d030800020f0700341030442d4006c0380e620f411551242062400c1c503000114044840d0003250811814503005180c00510110043c83c90261a85840055440c1c801c003040c84812841031031000c010714a0100844ca58010b018076021403a0703030700c0d5660181681c220f504450041400d5100511507540d140c1b00749801456451b94170403 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 350433462 1250 350432212 350432221
    0xd051617090a061505060711040c05030c0708070f0b04030c140f1009020a0308040906090c080708041b05040c08060f06041805040201170702010b1e0a0513230108010b09 74
    0x20381e200707038050740100f4081d112032035090700d804070004080c010000030b410156501404d01c2c004e00310100d0240c500d8461890490300303803c2e1500c501c058a10074603101d840545055020745a48585400040085a99078011700e07a1000081d0070b0400540514840e440e54180c2c0d40b41ea00d08040e071100b1040e08071040390b0014901c80f0041400050901000060b66000140d800150002c52034021240e00003030030040002500007032005035540603034211048004100041550903800711280f5000761031407170001d1070303c50210b404241030243c001411080340c2040f00640da542c20202c1c1c1076555401400000c200c4c01c01c20071a0354101401c402e80943e030704996513450f041c184020340e4030804a4107058100139036500d001500310b90041c0445c00d1240032101c1d050050386454900207000e41108001c0f9801802c02c0d0900070f825140d103125032005c4000c01080303035104508010502600011060302000300c292203d030204900040d0b4441c0004000c2080d08100315981030481d15403d43d1400c0400e18080c0f10103200f0030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 350434712 1250 350433462 350433481
    0x1a240604030b0c0f0a05120108010c0c0b060103060e1501030e030403081c0f0908091003090c1a1204030c02010807090b0306010e030a05010e03030109150f05060f0d051617 75
    0xc5055a5024500a000e6200c4040007001d5014a0102c0e9507040300000e2101d030f400b074001001d080382418500c4040030980e02c0c0d020003400da40e01e031041c000120740410300c100d000a000380400d5071300ca0410300d400902c0e0356441d0000c8418200a6507102c3c0c640401c0b000214031541e050207054103905941c0025860903296940e08030742e5100b0400380032820480c0d07080e1807103566010f801c0b000803012040410f1016802d14101804079601a41342144107000040e00714440b64028010300c000ca54001c0c0d128158035140c91040e41141d4000110203422040c10490410b1840060385100c0c01140a40d84415283c007103072001428001011300468107000314030a08000d0b000442c6c04a035030051082c03801c060503181c3d640c0420325100f080e400041440d42400000003842600002550403907000b1481804100402607040041c0b050602880504e40910078042c08141004002005d50300b101c4500b95141118118103c0212941652050108051404042c0d00190f00c82c065092509440350701c070a590030980e100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 350435962 1250 350434712 350434717
    0x2c06090c01080702121321020114090d1a1005091302010c0f02040c030b030624061602150c101407120e07090203061e01080a0e0a1a2406 60
    0x380d50400644500141e8814400e002142100d4683e911240d10703024600c0c8003900e100d125000352000d075400001c801c101e00491145064403190107031181c0aa0355408120820b003544051803040c2c210800031700110009141090301494088039550308200c1f130501c00280c488050960b07100507c207407404002e10404034449032000d840341c0d40c2401c0c10311800d42c8600d0720402401028401035170141c54803400101c40764054026440080c0200d064500564074600c05805071407141a0b0f0781724903005800091510b05004000340318101322001e000801040690004521558000c0110040c3c4d10128810302ca94004001c01c04207401d0740b00302401100c000d0700b5031500d40c4100030005070410000146400c000a00ca6001c002144091000d5031480b98484001c1c401950042c0c6a80340203269600d202d44003181c2e81080d031440703850145d661600e1030b1200d40028001d0420148640514000c0801040000702a0a901c003050b03d4001c801081510b840d000030040410800c05002e212004288504119582c5008 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 350437212 1250 350435962 350435983
    0x70c14040525090b211f03110a08030f122a09010c151a0909250503060a050403110c011e090906030b0f07030216080a030209042c0609 59
    0x303442d008000c01c0302140c201000e03501a0b84610b40000f6100500400c4039130324260032050301680b0100e81c4a401c001c1000c051044020400c194450f8410b00000b141c4200c001d090a40044c2803098182e22083e00031b003194010221154520381c0000d0003d0b0000c401544103601503420441401c00c1140c280d040c03a001140040c030320810490014040c0c10036809180040912900325004060300c1200d402c0c1c1100600c1c00d040240724154a503544000185424031003148540d159001074203e10103003030a144002081d4451000510700e075440082555141004071b035208a02c0b2680203c4c4074241410090721198285502c9007844d0020102040f081c0d0308602c035490b0003031824099211204210b001241d05c1c2c032007030700003480443c10000000107000130885841d014009820201085803141e000980491003207030401210411b5880b95030300454680340c0070309021030351030602603d849107420000b0111107504da9000300075041d03449410b41c3d03d2801180c200d010525280240560700f4403c913101d50b035045454 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 350438462 1250 350437212 350437261
    0x2503050d030917031e04050304140607050a02010f051603090f12120f090b040e070206070503010303080402151c06140111070920030414010f0b0d140111070c140405 72
    0x1011030000c103415005c00000c00c1d00700b11908520f0800d4540141c80754042c1c424036440132201c0d460b81104e803070b0810403560841e501200030303c1e40140b41d42c01595010f040b00704420a00c5030900002100403140303420702103818420794a09400a0030480c1f0340380c048146420110310403a81861200001d03216621800f801165410400a48000c2c4401102c072200107800401241402145c0007684094241c1e03041c0c0115466000e864081d0f4507006c08940d580401d100140002d15018085030141c2450626400700c0c00000031110702d48084041c2010407041011f1100141690714442009519100071003050581024a0700c102880e60582d40d55688425a00030080e56039907406003000a540741c000504100c0422035110381d00d80c5010700308008141d001c0c0240822035400c0040400d0510b1061041c00c18011000f0003004e1601c1c5541c44220720002459102002990307075030b07084565900060040c2c1581417140542c00d64241c2803560b2400920210a8160300807420301c002c0c840524840091810b102c9041d1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 350439712 1250 350438462 350438467
    0x1020d0c02101d0301090f0b061903080702040f0c080f01080304140105030a0e1917070c0608090c0a0f0512030309121e0a0504050405060f0f0609032503050d030917 72
    0x445004543d090120a490360540c0b9002d40a410000d48251110b82980a420000700654504043c8501081e1212078103589400c5402c00b40000b440d0007000c2e02c00c1c030340041c2c00080c40c900e01c1c00e425012210305540003804508c81004120305001d00b00c45017400b5144000c003440c1010b180c1110b0603a002c070b610010a041c02000b100085501c5001d40c0880354155a20342120281071000c200b08058021f03a8005807040070404001c4011000c03a00c040b035288983c85080c205e0081d1800004555040024002029500510050001603a20445010080d01101e038040e01003520342070800c0000c40b0f440716640782c0c80e08148104071082c2004900c00c449400e628102c280e51b0b91002c4501a54070301649503443e20504003140141b46681c1c82005001a100140ca041241b03889002c100980000a00c6803d988260130a0344c031801d80c10510003030000540b0140071202c0069074040c84003103e03a8100c804c000361a094080401c2800000c1014550800250904210643e1261149505140c1c0d504070b950b5640b800 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 350440962 1250 350439712 350439737
    0x100201091e03020f121207091809141615031407110304080d030c140712030e0111030a0c0801170304060c23070302031011070f020406030b0a020901020d0c0210 70
    0x2131100c42000c0f941301080d20307010403048142d9021600b221003000341c1d080350780c03001400305402205000143c48565510315082d42503c03074452701504e64100d00704d640c0900c0303118444d10480b04000100800b805119a50840d03828070320b00c0d240d20020143c0b01c80406080005040f14100d480030030941000143c509261036003051a001895071185510002c2ca603caa45c880b141c40300d0b41a449100348030342550320f4004038642951031741400d0151032005450f820003c0d00f0403480034080c2e448500380049a0f03001040c054500210700200c1c5d00101d0b010810140c40b00102d804490384180c8150140c100d11800348000c0221849980d0340e4001c40c00b42000340700f13526882000303000b009042440c032149008011442d9404901405031601c0c00f5101c101c0c080e203d19107502c210907040340611000d10300260180781c10881c2d10b40304c168403031148030301c00da82240c1c2e1282c0c0400801c125001c0306200e2880300d000582d94140e08030009182038010240001080f0203030b25558011380d1146041c510340180c61510026000c40d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 350442212 1250 350440962 350440967
    0x10807140301170a0503030103030c11010815101107060305012610020a050403020909030d1a03030901050d090204240905060609060904110d0e0118030e010507051614100201091e03 79
    0x344e030324050003520002c4000805c0541c042a0f41403080d100c0d0701107400529400005450400c001c0c3c1d44ca456240c24503035050807904055406003150303040303440d00d2003080c00070a4034241859031503081400060f1315540103001c40d44410b014000a800644600d442854800d02c0c2c60781c446040d00485007516070001802c0d807107240301e03100b1fa801440e0014242c905c1e5042a00900b0381e00d0b8000880301c100d41d1b0820f907036158428402c10340c4000f00d0720040d000d145080044001110717164007501c181280340f80e651104501681b9280325400f441d0310f41d141e074070450b01800fa50b40f0000b890703e6030040d11405d007810200801c1da00c0d10002d44004100903140b007070b1240b0840001030058140b00044c03504101011654182c05202904003200c901007030700082002ca900b43c103458458030615040580400d441c0400d45000e940b0490040c11480d0142c03054903e088400381c003151450900381d00c0003400002c81c410700c01c2c00f03141c01c41505407038190f540001c00400d0502d50300c2c0044a0301c0400200804449006000c1c00d050 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 350443462 1250 350442212 350442223
    0x4060204091401031401050105030706230406030204061b020f01030504020616060b1c020603130804080703060912050310210b0f0405010e06071710180b01080714030117 74
    0x112440c0c0600c0309140401e8441002c020034071055407640701198030010143d5061140c01e069401c054050441d032400c1140945424200c03071070070a0038074400e4048508440390100500040e001640e070250703682d032071700340b000308451440e0548051544502003178800680e0f81510b6500440c80a0a01040a5955000240840c0201302840d03280c2c02d0307001c2041e0100140d130303845481c40040031100700c036041d1504103441505449981c0001c1d00441c00304040759129146941d08042c451003405a1482c0c682c9070b6282d0307420030449910407202c40e42c54140003002c010704480d10030352180d13031858131600f10b05e001c2c000a81484194403480c00d13007000c64500740c050f1079072601c420180783d13410000c515607601b00a051015520402c540a40d265440d00f034250303910410200f45039004462980c3c0d4000d0002103042c10444580d000703000508400c042c100c0010361040c03a1001c411803510040c1000840751a45000036107400380040442e42000610865002d0085d80c017000d0340c1c10745001100c01d00c3e010403680303903140c50701 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 350444712 1250 350443462 350443469
    0x303011508071b030c0209100501021002160c0b0301320d0309050301021308060604090b07031a220e011517070b0f1308030a080a0b01181508090d080f04060204 70
    0x1218095001050540100d205d40344d0034400d40301d0b541c01c0d44e100706d801d5001d05003074021140180c02c02200b4103850450b907005094070100102030b0903a8500e50759640e0300c24a0280d44002c4442101000400c1010712103400c1010b0510300c040c0c841c146088414000da807009100c6c110601c030300311805605050ad442001c601e40074080180007155100142050300b84151224440d000c618032070100040d81c9400e0602a60300450b500050002840c3c6603803070260090008180145042800300440b08020340d032345042142c241401c810301228080c1c801900c28141c8040800c2c46a990307041200445c1030000c107040780c000710f601044c0024010f80380c43c18000e0a101250341b20304a140008620080d403c0c880000811f1501503443c12490f01941d01c24003aa101e0140072525004103801d43c0c00122a029560031246023500140350501030100c00140612400c8181d80104484214141e40301001e980c000e41069040800440180030f210a00c000041001d1401440212505140030100c2c007081703170b10303010340f00074 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 350445962 1250 350444712 350444747
    0x5040c200610030237081002040608012603040b0304050606090601050301051009080f0102091e0a09020901021504031112040b220306060608040c12051005060f030106090617030301150807 82
    0x1c80103c081101780c0a81d540a608900d0040e411402120a400e01c21101107441644070304026a03c2c0128803174190341003002e8a400904260703804031042c5014070080010b13080608000c0d07100e013004c0c20494039140004190501500282c0c003840100e0703800c00262811250110340711141a802d56804540070f5902d90700802161140c0c40d44110440070640141c1031740701c000d807030002e441103030b0340100141d6441e8200d1660b00020041e40601c2000038640080c203407a401030045401045c00c0491500252008030f400b0340008039900c0d124484664280001c0180c1d541010030349080c0341c200004400b20b0301c03510084403c800c01c003c10600c404506245003400450300000100003a41e507507440a0811401220300f2a1808104440420015501200c111080360040b0003410040780225542c03004000181c0001e40c0900300340d060359000e43d0b00340039240281076128404100e9a1603c2190481000100c2c40803010380c20500050040d0703001001da800320000302c3d1a008686450703020064039a031040540a50300b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 350447212 1250 350445962 350446039
    0x1060e09070501030509031611010e190f0605040605160c0503030409020703090501050408301305130903050a181517060411090d0c05040c2006100302 66
    0x94500010500364210782c42a2418000741e950310341e401d526031180e2600341d00180c030810101c0001c80c56840d4a08401041810300791009011980011a4888008880d0780c0000d140c2c10306010005070700142c040100744904200b400c241c2000c0015145000d441018803443e04019400c005020070450100001c12026098a40d585e8440b0640b00c00f035440b01d0400e5002c212038407030020b4103500c501c04980489201c40c02a04039060325044804000b441c0c0c100f104541c1110800380082409240000c0034801c8a08101c0c07002145405c1c01e02070f100444000c01d450051500c03801c103000c40d400c0000c40f65411500d180100044500d10702c1540c40c0640c80e0060340f5054042c5c0d43c10745040e50441c80a84071240d052044d1078040e03440c3c90811003907803282c0e444044004024800a00942081850ba071040c1d0312075010818a5030312000403c085900c090501c0001442c80841d1000c020050382c0c800b03030303c05010030107841d10340f40c00c0c84440c07040c802038403009000345a107909040c92460090b0700858524070f50202041d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 350448462 1250 350447212 350447221
    0x518180103080d1505060409020a03060b180111060c16080d0f0b01032004060e040603080c160f0503060105090c090907350114030f011112060301052701060e 69
    0x1454100c2c0800103466444e20b004030b0150b5140081c030108172600113003524039103414044804082d4020800d40818075448010128803400c500c0d01511444001d15507604c581e0901800040c8190b0107003800313214035000714007071044500e03015040701d44d03214060350001e29000b014600228584680c3c00c2501c1900e18103c3c00c68115030040d0003042c07410341c0076138051080a0a041107940c1700c1486a0212040440402080101da4050501c0d1031218a0061001601c250f6070384540c035440c5d1141604000617040601514050060303400000040c1120542c00b940282c18100031030b6070ba1a041c01003e00c101014070024003620f40000803034921201c0601084414208040040c1600450302d10794204c60304c20812644c14143c1d00c04203240b504070316110301d06c400d034030304048220380c0105000c409030503018031000300f003145200b4003a0f07540c0ca007503240c0c61507950081094540b08140c0b014000a1090341020203220240d1a11400707001102c03e100d0a03140036030711749152203004083d03950022112110f80802c10 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 350449712 1250 350448462 350448473
    0x11100e0f0105242d0301090c0e0703110c0c0442060c0201090317040e01030b090601090608210904060914090303010e13051f0905100b010518180103 65
    0x34440520318406010342c112100401c142c9019000d000014215107015800c29051032036a82c0b132841c3c00180000590b0716007500c07010825070359074002c07000401d0f4260a20001c1603241c441c404501604401c07807810908901c030314a458040c0c0c00e41c1e0742d00c659100c40c2c5140d944070140034000700108841c40c005403c40c02a008100c540c06019800401c0103c01810004600e4000c2d03d4212400740d05a40312020203003541d58001e407590842e81d440c40f40403c00e00000c142c60062800c0d080c00b035401600d020442d4501690903a00d4a0b00503041454010704151017080081d0000507403001140c541503070b11810320130015003507038203005900010364840e00381400028400c0b007941c45800b075544120b4542840741c2c5e541102541e203210a11668006c4003031300000400070444c2854001c006071182c41504ca0121154480c146088100000003100b950744100c83d104010b402c0002a4400e20350440910030805020000b900b240514118101e07061600c8440840b1503680c4106034652080c4d0340700000035940c580c2030a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 350450962 1250 350449712 350449741
    0x20c0619030b03010c120203090307020d050f0f0c090c0c0f191109060f06031e160206061206130303020c010e160f0510120b03012a11100e0f0105 64
    0x150110b494250945024241801010391144030b41d16904004031700101e4600082d8002000740341940018000400160340302d1b903c0d03800c040c3c003807401008000b04003e403060410843c400c98910075031010f020084c054442590380d540c0560440341e62500e0303001191714075003845603010401c051030044c9042c060b00c0228408008481da4080d81040d60703084404014030541240c15175046a1011000040360034038600a0000c56001c2c1c801070385000b07166a0040c11040c40e45003545e00d81d601542ca009204901a8100442a40502c0c110b42c961490001501e4041e110300c0090300050248503002c909a00b8940603404840c48885000020041c2088c1c0210781602c2d400e0841c1421080c85944000140e01b000d030303040850035510010580d00d0780b41e2001c40180d035070041504c02503500d0b6440e41c504000607a0288516071801c20708007446103c228021016401030721903801c00605110a40d110341070740782000250a4540d911413170000500c8840348071075034948815114030710300940c00d0408014076503801030003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 350452212 1250 350450962 350451007
    0x1106040b07090602011a10050717071703070e270412030506150a030510121a0a1802130603050607031505180a050411130b03060a060b040e0403020c06 66
    0x8035030b8046a29204100c0c00d8595440500100e20300d5105108010b180c50341c80744070400780d542412880c0c4141603507010582c0106442c00d0220710030101e562801d1040c0407010030402211100b81ca8a1031a040101620100c01c4a00d441e000c0c0701a034a02d5001c115451265204007844c014034a4200c1c5001c3c600058ad40c0849580381000a01304000b0400d01c2c24080e0f03200000c0003101d5181350030000307584000c4008207001801010904034500c4001080400300e1040d000380c0340251030344510300d0005074590017044805007042c0d003450700c0c180352a0003584e6129000c29200390b04035250060030290460308400380213180c10152190040900f8426041d0301940b0001100180d030700c1003000300360b0343e004000352150381d410f04035035040b1070b50002002c02d40e444c3e00144c1d00a1084001920301100003010400f40042c500260203040da490045104c540303000c020480d0b10400301391003030020302d040142524140c00f441c0700b2560328142e200b01003401c150084c450b600d0030762000b41c801034441d4440359101c00b007400c920a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 350453462 1250 350452212 350452217
    0x403120e2509061a071407050d03020a0b060109120201080415020429070b0f06130e03040f05040c020c01081515030610030506100f1803110307090b0d0f031106040b07 73
    0x200107907162801380c40400f00190505014104502a20342d001e003410906840405400b41e05000303e11030303507084c8483c50158040d600504100c540c1d0714004d40a8000a08154144180b0400c10420350751041c00c3e41d19040e6084c80c040030b0a85842c075007440c190710160414900e083c000304021403c25500d10801a44c0104182241c4e0700303000c01080b090043c841c01802a251f00031302030005854000303035010b45030083c6000e04040d41810b205c03003902c8119600358000c803402e500001010004248146840005881c0440c1d0402c044161000040d607200d40e2030000f14180410f280001e400810040014003180c400545034022924012503c01c0f00d540c13048444500c00c41d4409404084944280b007014403a42026201455070007245200303035243c0300b03a903841400b00078071041d00c02509803214010710011842001e480203481c41d410308160814006411a8040c0c0d881d1260001b0280c2d101c46160b0811500203800000042c07107820101e400910201c000051841500180010003621640162145242d076 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 350454712 1250 350453462 350453471
    0xe1302030d0c020906040c1206180e120703031104030b010312030f05092e020f04081504080703030b120a0b04060b180103290a020705060f0403120e2509 67
    0x30710081d01e2200751264007a4010310800005403490809038003002110307501b81420402c0801e42100d110590380c140c0c001000000d0412601d502c00200c6018040901208070080c001c10164450603070307418012114003600f09600d806004155049040490313019581000407001a0360712414400c20100044200100092400c10000c01c5503429100d5a40191800c0300503264046028102c886048060790050352141d01c000ea0f09e100c1180c4510050040400707055100c0d89540c45c010b61241410720002d07050541040c42030800001441044c210f422896250500190482202c804a410060010b803654440d01c1510104424051203030266403249119520602c42180e14509011180b146e018500c40b0403d244001800061107590380c03020000380c1c002c86070088468881c00440740c02c9003a00c03140900c5a000400d0024042c0600800760301c2070702d114251015081a81d002000340c0125000c1c54400d60f510003c4440c080820300c840c074410317260b01110008400103c0c0803601040c8191190f1900d89142 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 350455962 1250 350454712 350454733
    0x6060906080103050c0d0201112d0102210408040f08060604060f0513090f02030601060c030809030a0c060914060a14160c020d031707120b03010905030409150e130203 73
    0x400380075059a51200240145078070342c2003841854000b0742c9089051003c040d0905640070b2042002ca040201044000000101407030b039048002c446030303084031005900410145505449201c0910800395a0b20f070440242d54550038030103014062600406c55641202c18000344002e80014402d01440c0c046900b0810241e87da142145100041d100d01078100c0da1041c00800350b000703182d20131116140110b8400d00b14920907400242408000d8006e080403500ca52002028507601501c0154880c95045c0154504110240060118444501c0080280b42c641414200300002221714611140034602140d040781024074406014000a1103952030041d00d8000098044042072602c442406603621404518001340d001d000b400000c4442c10741c02d20001203040ca541c0441c034803120344035546942e0303070121181b01403043d5000d031070039140740a2190381001c440d04003281012003203800700c4900740c00000f609103006200054094442e8402d203507801404081142c8070303003200803100201307100302e0540340413010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 350457212 1250 350455962 350455967
    0x30c0d050a060f061b050f030408060a0c090e0c070c090605040b0406030f17070b040803041101030b09070503071209050c0109080622060b030307031205130f110402090d0606060906 79
    0x10144a0310f2824081e0300410000360340901c038040000c0030308015199040035107441e40780c079008100301d01008a52000404201000041c81002c1d0000b4449100b480241e60514004040384030340e0082c0380c17216881c02c0100310701120000445a0032640600800140c030398543c40b000040c0994403c141c041d500f0529a96114a41441590705480c0c0c000c2181c180c103007107034070356145100400c00b48034803140d0204170f8500840c810300c009a206074842c1003015628a054640941034000c000c4500e4140b505080054000356a8a00f00340c2d40b22409103426a120790f601c00e02101e0003e0b040202d44185481d0a12620602501141d614080802a203070101c00c1340c1c0c0c401815030340307400884503103c408403500b01d44000242c0d07038101c6900c02800707107101080b290842e200080c11607001b11001c40211301d00c080c005808a44078010740394400555004014007841d00c3e12540c00085481e500102452180e8501211a41d80c9a042d1082c01e02d01815604a50007140740490003090705014220104140600c001106403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 350458462 1250 350457212 350457221
    0x105180a1e03020a02120105060f040203131b0f030c080105010b040b0d0e010b09250509150903010e070f09150b0a0f0201060b130302041b0206061c0602030c0d050a 72
    0x65001a000700c100200070318091160000d003004500b140900224000940d84000d00300a912204600001d11820302070204201d100c454040e25010740d0041c030030803c04e58014072141000e41c0d045101d9000f000b54100004602a8094000441c0324240d0240801030011341c0701a035042e034a821000308040e9803901c1402406021f01e1040d1103802804007e0a4140180f42c0c01c01244c011220001143e0207250030001380201808440c08511481d00c11152040c111006e100d20441080600302145004d20312008101700b159503400e88241c600001844032412f8800b54444d242e043c5540050300e96042d00d40174500410002c45c0704900300641030031750b40c00d80001c08164000444030b500910524100310b05200384d6107408003034039807000e5550390740002501000100050000c00051125212001d041d071041001300d034407010001a1500c4045150a126a000112940c120504807002102c1d4003852030104440c5440301e400070b00c414008014082d04161020142a08110582041c8802c1d076446001a0458 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 350459712 1250 350458462 350458483
    0x30203120702030c10170a0516033303020418020a0905070801051e04060312031103040804090543081306050703020f0726030f070e0111010e010518 65
    0x107800c41c85140c601c505d018110810f104030241003e0000c40c02081580b01028800c403400300320542c6072420041034006c80c1c5002249003505040130030110000180d800e001c00300083c400715804011a15400c540009404850001d65000f0810f010004c1060072441061624480803402400d40c1900800c801d00c56010327451103402107580b0541c2030382c41d000c01c01114500e82100d0240e03c4001c5103c030f504035251030040d10082c500480014100c1002c00e140102150090942c1a01d90042401132100048810080740c0c11110300b010089504c0e02c4280221407880520300b12542e15256448203203801040b8941300c820401903290b12082400500e09060350300d18021a20711424859401391140003500d59400940c0080c11841c0050a050413080315122a40c8002c000ba02c0504101500c00e999a45485054500300301c0700c00c0031419070030000f00040c00503030b0203031540307080c0880c0c5254400780740d115a110201d4078004100070f01c0080f040310171081c004d2805031900c60341e160703d00c141500000400038030750703910 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 350460962 1250 350459712 350459719
    0x12705041b020a0204020304030e0d0b2e0513021c0b0a0506030702030307030e210c06060f03070b182e030b01020d03052a040f0906060e010c14010e07030203120702 72
    0xf2001180e0030032000390710080c4128203002c240c3d0100310b815114040c00c0e29400b031081820100c03030304068400351242d648000c0000e07410b000d56418990030f10f001c071003240c04442c816180002010b41c04050200079010314a01038000cac1c503509900050307403400b54001041d104401c2c0d8204c0859500c0702d09101c81444121103000142e402000030a08051282c1d0020b8031070880c1d1001d44502c42055150aa03180d01095002c1b0140640420f424090301018803000e50000800c03203e640810207800c0c017203501c0750001d10036650325100110741508480d00c40c003181c40d502d0750001d0a00781304d84920318058140e1038805016001e44546038a1100905000380314034a81b0001c1600200b010403a0f0078000c4000e010010900c85988801050f620b0610a00002ca0244001c44916984e221400e00d0b58001c1c5402d03095120b1580e2a003446000c00c91035410220080320300400f8603140d02e480805062405035002003405440e200d43c0f038000c403158042c10105220007600d201310f06a41070050031a4208101d40183c0001075031 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 350462212 1250 350460962 350460973
    0x8040f020105090f0310020d0608011802120304150c03080601181401050d0c0f080702120d24080d0e0415050405040203120a0c02101d0609012705041b02 67
    0x241d030150000c0c0041e0b00c00200b04e440d0700384244010a04041e2030801c0e4840c402d40108014040440601541e0007500b158002001500e420704003054013400f03010006401884c41900e20000c0c14818421240948400b09180b6012142400000c00780c040519003030380055402400f040c40c66104096640030310200e8900100242d040000074040100c2070842d190600c80104074140400e000c9000d150300c0280541c130348000480c54000081d1204100824807811500003442e250207005000c816501c00c40224280020510440190000c800402030440c03128040301c1c0c2800280e25100141000c9c1369141503860700703145100c1a05101c1500d80700c00c0c104105400100c41440b65080ca80d01040e0721a00090403a6540a402c143c1e001030760b03000103449000a010240040c0650516807403c3d6032084051504034200041c02d0941c06031a4440005a80306040c00507a0600583c0300748e03505224550b020000091209908500c09000c040d41d06c50903000e103080c08100b1540780080804201070b800b03140c01410 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 350463462 1250 350462212 350462243
    0x90c01090302011202090307120b010608040b0a0b1809160b0a0c110d0c080c0f270705130605130b12010b0d02040f0b1b0f0d080c070611030a0c0804 65
    0x140c03038841001c040d0411380d0f800d010011107642e00f00b004038001d04500788070840b03107803460400910640e0140c0110341400300e00003d10002034521550580d0020003010b00040e00143e00000500901030a0f41da40350214200c01404613160f40452005010980b5015181405c1c2d13a5419825060007184400d0780843c0c011460700d80850505080c0c01c2d198400106010a87c8003160b4804d11028030340d03041001076170f000c101c00003540c0c02d08107070701105070004440059a10f42a1168a220140d00e02c08071480d000d0200085400140074178151075003641048000541c03241c581100600d06c0d0003140e480200418081d000080c0105c07a4002c40b440840170281c95a43c1c3d03800e00c00100e00070f0b030202c0c02082c5603540c02c000003d500e102080d841130261182198043d5100b1076192085980c1031045588000340c2c00c0080148034071100040c1c85c5107a40030ba824070b08816a12401c01c900f05001d0220041c0003103007008803011515081c180114403524910700f0070006910440c0c801c4615003000c8070b00401154045e0080d9 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 350464712 1250 350463462 350463467
    0xc030c032d1404080c1504020901330203090913170f160614071103160318080d0212040f0b0304050307060f0609060915061809140f090c0109030201 65
    0x10058116124010940308480e501e40b40c8000b0048805864000d00071404140d504c8040c000340304550100c20240c001410f06400280c0a0b800600c10f8114402c00006500c00542c1c0201d4103841c816001c0a22615154103020040e4036039000030340f658401c41c44000003417425880802c805503d240c210030182150000301c101c407009a407000c20003030819602405102c070ac1d40703c9500c0c41e0031001c0c810b100115407855051407004000002030721080c20b0129816180c243c4c4440041968410308610b014070640a007582015101040c40caa4905c0b400c0d220100d003c101d2180004031400410107039030031642e07298580c0c212012140514092084103e0300b0b8602040780140325000741da00680200152850040b031079461000721801c91034040700141d207c2d24100304c03007901882030f4401001d84040c1407016110800c440b0a0702c0e99030703000c0e41c01403210000010300540280d400000151040c140b0401010440064040c0e10319021605c810f1801a90000528200790120300f0003001101a143c0301c8140f421980103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 350465962 1250 350464712 350464781
    0x608090a081e0304051507020d0f0e010e09090105100806131113050405010b0415050d0b1e0705180103020a17090f0d11010c05090307170109020406090c030c03 70
    0xb110111429581d0380c2c1c0095107824015409244110003c002e0707450403492143c5403000c000d10500554200f1006290580d41040c13a41d950040705280004441c0108001625105440300406401481c03420030001c0c0c0070340540c0000c1c010071040749000c0407140c2c5c2e448c196076903100844501d194900254940000640c2100500881050050900c040d0300c40e140d404c50101d84040ba02079520f40c0d1a61499440c80c1440d10403150841001d4007000ba2450600700407a244002c1000011305003c008000a00a44085540002746000b192801c00c110708000c02d000302150010b0105850b11100151703c8000f940c02442200d00d461b0355510b490400380c41305150014041ca00034840300c80e40c00f40100020f10204140301e4908181c8040c4c0755948801c1c0a89070460031285003000480612104000344e00550340e00007202c1c8100e6079114150320500202d150350301d000d001496002500f0600382400407803054900e0b0440029003660b550100007250703691800b1001e59400c070300d145c403182d1400b10f409170030075500400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 350467212 1250 350465962 350465977
    0x20c0601091104090e0703080711100219140c032e0b0f060a031b03140109060803030609191103071b2406150503010303180f06051b070303180608090a08 67
    0xd441c081b46e540d45440c1c10380e52106804494601c103450400c0320601d0840c400c1c120003c681c0c40200b0b5104042103243c0c081060742c01d4080c01c100c0903184a01c510003810083c1850210029054409007032400f40d01c1040700d40e1000720302c0000340c1d105e17141c10716040c898442c0303840707041d8000c000c0403003070682c1c40500145078081080c040415441d04c0c81e086801d211504030542421450380c00145012500c0c180d0108080180c0001904604181701000030440c00016a500100d00b118031340325980b6001d03180b54200000702071801590b41826810100000f9910181d0300c20003407511600c880c000a145454880c88805100074150a0006030045c2c040d007000c000d00b0203544013040000384080c3c41d00b02d4a805007007200c007000000b42000005108141e4070098440808820310300c0640c006050420058900415010765820041c002c916007601c01c022100c20750071304200505a62010391241001040c9006901185000c4002c201c00010594802e042152143d480308020304000690340d56001079940c403011 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 350468462 1250 350467212 350467241
    0x1c0c0809060702041104090b03010504200109080109050309010f05122403060901050105120a0b04080d110d0507091d0604020304050f0d0807020120090409051e01020c060109110409 79
    0x10b400c0050300c40b0b02c1400140c180c13005059807202d1501d08500151025400014000e0f4144000d0100040c640080003202c041000b22104400c3c41c10310048602d00500e0307004108540c03c280400061003c044000c0c81f204c00e081e41d402244d18410201561184078520b40c0100d040c40e8800000c90010607403100c0301241040c68410200401040000b80c82c000c000ea4442d1400d0359510010407803443c214040448010305080613100340425611381c20740b034540003800a000e048002441f210300303801c607a0213441001100880b05440c2c0c0219a40320000345012908140411040d52021425500d0f1003c45106071041c0c0c000300c4038a0340c40c6000d0001940000d002101c40348510400109103480a21000c0025070903a502d1090b503242902000f425038515004141805061090552068068808032800944c0c143ca010078048000e1a01c1807030070310302d030f454540d10403410180b101c0c181906400610505811078212201d50741c8940d805030455025600152110340e08100c200170300d255580042c200c124501 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 350469712 1250 350468462 350468467
    0x170702010206180106170f210307050a03090f051e120901030902040605030114040308060d1208043201140c04050d0f0c06032a08071d060a080403021c0c080906 70
    0x585001651010500d06c0200d139401c150b0304a09803480410801410011480704040300e8040714503078100c03038400601000208500041c030a119680a0b400011070b0941c040b03407060310311582d400c01e642c50b0f81c0c1200044500203e4440450f03010280000d2881202c4580403900f803501091030019002400002002c90300540c990300d002990783e50030f2164a000c4001c45141c0e44403840e05213002030251000500d46441030a070b10380300d4030200e00311040b04241004941009007094545040100380b102003040c0c81280b40d04100c581e0480c1111010151070349581000c000d005520416071840343e0054215010a040c0006020400042c68001a2489400e00908450100b40003648a00c8506882504100082a141c2100c03685951312180f2040750005012665a41f42010802c005c012600c090422400c200343d109116914800418090094110081203150ba400c44404050080d180c100c1d0181d025000c1c120740d0401f0b0b4040c03003418143c8100d89035038005482801d40d9400005070401946160440c0d4103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 350470962 1250 350469712 350469719
    0x13260a022b06020307020105220803060103052211030c030c0d2301020c03090f04050f1902040e16020d080103050c060a09091a12030412150b030a03030603170702010206180106 77
    0x620096005d0262503001160b00d103001d0000c540c0c80029035402d0f03420000501d0390403011a0100080d00e41003c000d1a0104072a107514551741114850b101c1400d460302d26442e4070303400b044900b8124484800c010740503074800f0110707802095114103e021100d600210060040e800140c0f0340c0f00000503070050001882140d403030350708103d42240c00c400354030b415070340c00040c4400030707407402602d034041c1038604540500003860b200032180c4031108041c00b0264a0645505205c4850110380c05540152001c21035542c0f8500d03141000fa4440e4800460400160154000581a09120b005680c0c1a40d420000038998400180305001c1c159000b004080100000c440010401c051039014030070440400c000d5540c5804003070001c001d8207924180c6420b0303459004001c10840f620070300056030582034015000210015034041040040d0011008440e4503010342c0341c0032401c2540551040080d280145052130301c2a4902c0d04460203441a400082e02590086000500c402d00c039030b040d40c140070300060011411555 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 350472212 1250 350470962 350470973
    0xb030307080f120a05040c05060711010806040e0a0b0117010c14030a0216052a012a06051e06040209011707030b0307120302150714030c13260a022b 65
    0x1060380e00015817a15a070a00c001c1c880181031080c00f4040807181540740c9040d664402107102c42ca005140c0c1401000c0000038450b40e2598001c0340c84043c50f209888c00060720f898807054000d424052100a0210132003650242d80c0d0501c1540700403100c40d107407081012040308480c21580c1008104410761a020402d0084001050120346c56150ac203c008000c0900240b030b0201e20207500b000000350103091540313101d05513039003c0112240f22103414440e04d91110f90341d09501d80b80c001694081c026504003010301c040030812080d10b01e142c07952503180d900192580c0d01004164892000c42c03500161000340740022074607900300116001001c50174001185420b440101381400515402103c280c0d2559804a05054040c40104015908405928441d1803c14809000b401402d86228405800400020720618100046680c2c401d01f140207003403895a154000c6000c8000a80c068520782c03000740e02e000c1060070004041c0030306540200216696080766503070303c19030740d140c0c0081105d250f49044004042207 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 350473462 1250 350472212 350472247
    0xf02030106060507020f011106070f03200a0906080103020d14030c1c030b0102011e02070c082e05060f0f04021c0501030210081303081b0a0c150b030307080f 69
    0x20f031030f4903444410320f00400a810703400f841500e0500c0000d81070062054008103040e40e20000358100442d0034400c0c0c00c000c030010018100020a1a0319030300840c4610860f00002d4441e4514640d50328110588400341160500000c0c40700a410443c20f0640000161034401c1c0d4080d400c0b1508101c0e0304049140070300078030b030201a400c0b0990040400c0803459000f549401031500da80402c1c0024080752102c03c0c0c214850400e240d213000002035010130504100b04141e11420000c0c610039013200c000300826080281c0000311b49210740191348040911034031148aa0103114415203005180c60300c0c2c0100841440b241c6010308011650256003000981143c07807001d0340d491000c4040a200040d0f5604600c140660080c0721800703c02800121001c10174140c07803c8401c03030002503040c03405030381a03140c6507002e0001c030606060803442c1020201d002c09510f0780c0040480e000d18050103286000a5520210700125a0719202164050304100460782c0403918003001407200443c7c4803411440c2290300701700c0e0001d29 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 350474712 1250 350473462 350473469
    0x1051002060a0911190501260109150510020304050a0f050120100f0506030c0306090d050c0718050901060504020901090501180b040305060711190f0f080a030c080915040209040f02030106 82
    0x1900f000900c59541e20445904d10700001d820200a0400e48c1c80c0f610044020502c41c8165003521b983c0c1e256207407150b40844200520000c4e1150300c4c620504c0001035200e8016014041c00781c1122203001441d104da00786900c0840d0b806846802c5c1417100c180210743c10000c40050b1808501c51402191001280e80c420007c26081b01400010641000000c040c1003040000c5014400e502c46014892032500220fa004081040c50522035611b15880d0500740c200003899120303400000074841c8554490015400080c415801900200141515038080004074001d01407110700040d9002003e00840d409121502841d08005181d6140307113544110480c03aa40c03160700120740350382000003448151034002111000d00344014015090429070003642180c100710140d40a06400ca01c00c25250a010440401e049a103400c9070016595009450780a0007801c07040100340009503681e0006a55990701240c1200800d034030724001c04a5886540800001c601d0180081c0c91098880c26404010394091140313074001d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 350475962 1250 350474712 350474749
    0x120603120c021822060b060403060c0f11120703020c030d050702120d0507152309070509090706052203060f0b040b180727050901051002060a0911 64
    0x4000d03144148201801043c0d00e419000302d0350010b01c054003810f2180b036604004480280c88484846041010142810301041504554005004401d00c040d907006200808078a849094040c2140101114040403604048015402a4011507106000c3d2002040741d1360081c4101c405030561003000a0410206203403e4000c0b0340d002030082c0071030420f80540740309542004007174000c0c2d40300d20344080c00368460104024441503503603190b146254515807141d92960300015241c003600e05210241c40b1500815500030481d0711810100052910349148040d03c0350f140003025001043c0760041c16180d0303400a0012080300c903200d150030010503041c9482d0030025800b6a00101d100f0100e1062001180d0240d040540110b08041a044064844100090040c07240180780c40166807080c0c0d04031001000803c8807180482070840035080c008040c0c20b03140a45608072030031400d50741e0f2081000803241e8802d548801503007141001450007c11640204402405509881003450b5848001070000d4503811402ea40c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 350477212 1250 350475962 350475977
    0x1e140406081912170103110402040305150406110405011704050109050a0302060f010e01050f0d03020304090f02070b0a090308040f050a0b0115080a0e07140609190e070216030312060312 81
    0x2440030b0212800307500344281c10446504c040c401d90750180c0d03040500001e4841c0d0300d5020544210348a80e4102d03001103400400740d03010a0060440049007030002d4178207a422508101c40c001c1860310ba041142e0848405840e0240384981009601510640051050781c03103550711415000840d00521804100500ca07030302400851401d070410a84007401a00039013040303500c2e4001170060340c480344101196402c0488000d24948003901d8200c2c5580b0654000c0d0221070300300004540107100740e4000d0720b412882042c106407a540c5200030b94007110000c800180008114002040104902c0f4280d0004c1c140210280c44024410782c0760840f100700c0a92210030f120b6a8000d0701070341254007201e01038000c040300900f030256420300020581d59a07050700940051b0038880301044120396440c01120341d0a58040e00f2a41000e501c002d05461118051242d54045020000082d10162000c1901424011400c10410006007141c40456100c401c5448038000243d40311404030109090341841c0c01000d0140d941c0d0305 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 350478462 1250 350477212 350477263
    0x9080c03030a0c020604080a0825020318090c221e080d090503030a0f0c050d0329060304060e0307020d29150603060a030c06050d061e14040608 63
    0x28200c0d10140c20f00700440d0401c10038440042d001004949003259945000d007a40e0300d0341d05c0c1d00419851010014011b80c241c03442107440e4540c0110142a90b1081407126404c08032590741031100304102141c040041c1d070000c0010b4903001815000c0800e07102c0031a420ba00724252543c5024502e514104101302842c20402c1c0108a0300b401004884034110051030a5040d4a20740400705e6074a000384403059051043c0c1c0260f01806a2044038080c510f590800111400030b030000c00302030014a2058801a9100c8810ba003411000c00c100c181412000c4010b8016481d46d921521940d000303081c514a102401c2c00100800b40c050396410041013203103401008041101071544a4840395000e01444880d0642080807c1007114012468007400c003c2c001e84000c0e94030396400c40050010350a680000b484492004004660564060050111403280c103030304110440e120003a000d1102900c9941ca040d40707128103003d0010601150308044109009080403070703000e40301c819050404030030340e100407148250300c105032 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 350479712 1250 350478462 350478481
    0x30209070e0f041a03061314070605160602071b0602100c020a0209090a021003021c0e211e0d32040812010e06120106120204050a09080c0303 62
    0x250454101e041c00c410044254000c40c080d041c0c2e24002500c91566941e08040d02c1e0281c03040e0822004006064030200d1608144100f5007050b01d11058403807141da071118511150b00000c414040c0c0700d898845a00b40140400101c10004400310708036821034003400000c000401c01c030340e800010070030145010030250900300028039119501110703484030350500c0001d004980e00811a91013441d01510005d243c1c0e611010500c0ca048010030009400840b01c2104404456240c2d0152080e01050054180790f49800c090b040160b80004480000640000341c010158508280700c0d06c0c1410a541619401e01600808101b0002420600e2100c0c248002030306d001e84980521841381c012064440311040d65109400d03003010f1ba28110191601c4c0401e140110302841160010b403182101c08104044a030342c2c4400071648064000d90f166030142ca50810621112074044c05164140c034400042c2640c00ca4154080001030100900521326240d60b42c0c20100c04a621040201540c0051100a65980c01c028400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 350480962 1250 350479712 350479729
    0x902030709090903020d0314011a0d0b0d05030c0106050609090a0c0c051609060e101a0f07111f08070e18040b0403090902030c03151f021c020c1c0503120406060302 72
    0x80d0b000b1728015100502010b0380b8010551902b43c01c80c0c82c2581c0325121120f400008004150180d5407004902c0f45000800800000030034600a03800d0003840440e941e20103108a07402075107a00390f07200581c84002411a9002c0e4044004084245021804a103080c0c44075401c080c02c3c0d100400b070f80c00c01100c05006810f003602444004201004540c44545001c01009261085c580116050b11122070320140307044240c0801e641e41041d07889902d5946842628100541950110400d03004503c80c6c40204604640000b1110360140640c5aa161940c0c407136008507010640703980c4080c5c1c40318800403880c17200351816881601c6644101c4640c40c0c5420700c1c2c1000340c50059268000d0400078010400c00c840f06481f10280ca401c001d180c3c1898100c0d850031800101010703604142c0c2c88010518501044600d40c0c00140c2d000c080c81100e81052011103003850403a1148070f01c181c3c0a4005010000e0760400b48940c801e0429803d01410507070703040060540181d00c4084065400340c441030b48600d4144207620b0070068 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 350482212 1250 350480962 350480981
    0x9011b02070f050904081801020a080d140c0a0906030e0f0f0c09060a12030507021f020114070903050a170f0d0e1612030809010b03011107110108040308010902030709090903020d03 79
    0x440b81384500c1d007941c40d03400314850111140c41c1c121050300b00d8599640204003c1040303503417155007a500d481d00b89501400808004468003040f01450002c1440070030f50600f05d43e4201030940e94401000c0c1407940683c00341104403200881440380c001d03a0440e00a00748000d4411140a0010b004845015002c000540f040503210b144182e0030780d08100408004600c400d01c0c1180e1500346242c070382c1141d00000d0484400442c60002204003e04d07010705036681980700781680e81038140f0181c8503880d0749508580410141c000109154070200300c40000c50701c0182a010080750343d07840c2514000c103034110680290440744034000c00daa111515900c9850060201003400504075100401980c5425403550b180c04c0c1401c00a01400a00800310300000000e40000d0b10610002e0700034480118800d0000300c46d944809000c1d40c03141c0b2903560002d120b41c0304003035940c061609507498109503405e220002009601c050030300001c0c070040f0f020005125131503010700300d80302d4000e4014000b40b545218002d021f07030f04810f4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 350483462 1250 350482212 350482219
    0x618120c101223070e011b0501020310060302030c0a03051506070c08480303040f0e06040b032a0d0b01060206250c03020c04050c03010816060e0909011b02070f05 71
    0x10000744603c00307108682a0711210510b48904012103c0005a81086440484140c0305200d402c01d0424080150021802211441c4c04030000300d031380e10011003c0f1300040c2e541c4111160108408901203210350445604200100c0030740500d40504000a0070782d50001b038007110380ca94036079410003110100f0f02c02d042d880c48a0f541d40d00702203906102c0403800c459001c00171141901d062450200341d803500c0e2040030036810002e001c1300d03075541c1c44850340495400c281c80782c010700c0800c40c0700003821350511b8000d40038903c1002e0001d2002c00d409841e400da204d005c01d0300b0708101074569601082d85540c3c41444d010300d1406450b40b070f030995041003002414201c0060500c510191541040404045100c0e002485042a80b6002c50110020b00e0f00302c0c01d0007031100002d51700174109010b0001e030f8089030340118100d8403200300300c4140e00c1c40b108003417400c911a88900c4c80441c820f103540900070b08050845a901580d441c0000072080c00034200d6460401d0001c5000300107a00c90f04043c0a031160078405040030340400c5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 350484712 1250 350483462 350483501
    0x141b12070203190f02040c05090a0f0305030f1e030a050403030b060306010e060904060e090303060a06020a050c13060305030c0a020405090a0f060c030b031b010306050618120c1012 79
    0x1500072980c3d07186403664650110350003480600510004003a0600710560040052000013100e50f002030040d004101c200d8400c007400600000c0e503020004084080b41d90290240d401d01600003154095a0840f02141100010030720030707000019441001948140f010392030000346410181001002c449440e0401d501a01c07041091001582e0404c0440c0700c0d042c01250415558100b54001c50301a1026900160b409103010051040c3c80e580070010798418281581d0440c8030f141d454404a91381c440c035050207401a0000f9428092506080c404c0c80f0410040640c04502e03940c2e2a61040e184d0381c48081c25070310582001403102c0441c5814003805400c40c8412006003d00221038076018840350068030004d201e03030342d200900e100642c02034120500c00300000301981e000c03000c4202c040c4180c1c41c2d54021607000030b1070f10354003046900e8400309503071030440d2810141c1405c1c2010f20501614003010315402000f44995030001c019a60340554885046049541d03074001891160040d409a9001110340012400c50 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 350485962 1250 350484712 350484727
    0x31c0305010e180a021e130501080c0a060f080a09081c050606130501081509070507051018030302070c032003060a06080604021003140106050403110109060210020a141b12 75
    0x480c01a810340449242d0301e6120305a000c00001c2811700e54161f040106009840356080c07203a406141290404800d642c1c0e00320841c7c0400048000354020440132800346510103120310711600c40b01c0d901c14103010001031032040310b8075075608a800c5985107426211003075407244003040450003085c0e0000f805480e09400e00110b00000d40d11880c683c080c00c0c2c1000340500018040070550450643c420b20090919012030905170700c018240d500c0094280e4203449220151118100c040c40341c046450300d6028030390300780c01c035590301200a548646005da81c201800200400411000030650b1040c8070031200406d90700c1031840606090800091148503640d240c40800c2005041c04170f5281e50082c0d04881c00400e2491841060b00105840c009049040c41c803907002064207a0400c0080c03003600c1c01603140c134a80c9001c4800468643c1d240380141d10040e0011040f0a08581980d00508480e06050600703007000050300d1701d47c6040e40c1098400510b22a4980400740045105000c0480d511600004107480c2003070 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 350487212 1250 350485962 350486011
    0x1030c050f0307060f1805123405130e10020913050609040318030804081633111009060e06040f08070609120e0a0501020f070e06031c0305010e 63
    0x20707841700000d0000c03014840c0621881c0301e9000018000092450f042ea40100340300c4d90780c50110b102e000090040c40d4a001c0c10903880e914950311001d400310992800e5505010900c100030042e001c80d20f001070b0315507a114000e00010302800c1e121214030303140103071201c005404100402c0c5055500180d0140740c90140034168860700d99031580144c00d0b0500800b200c09564200803151a02da202910106011a001c180802d010034500388005641c1403141440d81c0341c003550380b10304d940254a0030f031000c0d40003000f10b11080d90204840840c0c5d0142013207a00300030885080d81c1042d01c03141d59541216644c02480f0204101030ac00c40309400c00040040ca500e1509030388200d2002050720020b044800c002c41c4401c200316141e00420603283c2d12641d200d80100c0c0001c006410b01d0708041e1158466086000085030741c0d480012680c0c071652204000740881841c1c079a074400b2120b80504101d405008030a02e040c001c4011041d440a2187c2941d000501c40d8076055100a4412004d40b803400300c20b8100c40e00c3c520050 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 350488462 1250 350487212 350487227
    0xd1404031e08131e0302071d01060c060c030f1a040c020d05070305090a090609020309011409030f03180f03040f1e0501030c120e0f1009120c03020a0b01030c050f030706 74
    0x24040c0a869441010341c2014202ca80401c00300144000780140c4c100105540403400070f04030380c07001c2c4101c01103141d40700304100d88510900a00002074986404000803030004e412581388000726040000d2180c900380c1420301901c12084100c1c10480b41070140c201305007444d201790800340b80d140c4080c10345007800c00c0000b841481030032000382c01c020020400308044c6c2e0300c07480c001c0d0041403450002c200507507480a907540650804c450ba01c50325440c0280c502603844450307030094858000351028625000c5404001c0500b5000680b0034aa8204210b000e1110524104402e6251180b100020344d181c1c0e2030a20303000c0c0080c00e90b803c07a80700034142c2c004021504440e0b04418050750000d090100e046514494101d608482001079407248074100b080254041101043c0c0c42444854001540d0240441540c010306507a8400c00082c15400c0a400c69030180c0c0c898504000807901c0382c41a60482481a22040002982a0001c0c1c80d807040142e400c10035454058503000c0b003514143c000e00407180c5440c4028200c0c2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 350489712 1250 350488462 350488471
    0x3020d0803090142050a050607061b03021308150403050c0c1009050f0612130c0915090b27190e01020a080106051804110d1404031e08 59
    0x280d00800071600b0301d5002e400c40300c803250005140c0304029401c10890345a511402894400103004691941c0c00c0d648980c4d401016104090301d0180703075610b04414081158002c20382a200f0950741c0315440301034141c3c803101465044240c1c1e40503817508480c501c0b06001c50040d511140c0039501500c0d03503100d030034a00907100b0707441501402d01503203515118040c0c6060008540c40310364484084c501c1503106603082942c503004c0c0d560035210035141c2540c40c42070000c24402d00c95a04981ea003984001000c403482c400044ca903d9110381c58402c0c42940c2ea000c1c030802e41d030502001d0307600340341c51110601602c0340510072041800030480314200c950105042c00c007004480d84204c9045a14580c0001352910103210615648403081c00081000c14070b2592120300039006511540c002421000000070031600c43c20555041d24803a028460510312003804000040000070262820720310207118640c0a00c65611907c01c540314031000032121841e103450000c180d130b00c1d2004004d22116041ca8008a110b910500b0103510 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 350490962 1250 350489712 350489723
    0x909090d0c0f0312052a0c0a060f0b191806050f13111303120306051e03010b09011403010e012c07030c06110607031802060d06030b0a0c02150103020d 66
    0x11500b0342d080c03c8a621204800000603181044103000503018a00c079140607445044040d003490f036281e501e01003070030311800c250710045a100c00c29190104030568085040441064400120710700d1081c0450000184080301c0240540344500070080b820201700c3e10300001e200540100000b600b403a0002c0c048071851583d5500a081000b0354100e101e60a80c42191048480d140c020b440381005500e040da0440c1d00c3c0000c68401904000c000100b030701900030f81c82902e000414002403501c08030b50100000302e6110304664159201d5411001070380b0f441400c10301034050021005101840d6206141c29581c010441e00040d030300d0700b144a00302c50f5290b5022907250f003000c44c8885465030502c0200b0f00e0110240c001030208040080001007007504031002030a000114015100b150361202c1d03040e000c0383e084852014450860040080051030302c007005010301035920b41c3c0040c0d02600d0341c030b800d40e01354400c41d102540c542d81c030024031240540400c05801c03203102140d00c0402540c1590b01194503a03003082c600801c0c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 350492212 1250 350490962 350490983
    0x809070b04060503010618091b090e04080301030201050d110f07061802060d0e0c091509090f03040e1f06030e0c041a040902060c0a0c030c0509090717070b0f0909090d0c 74
    0x2407480c8442000001415142c805010340c0d02089d0360820f1031030506200c2d00200b007509100003000014610040c2c412a0000304060840c2c2c038540055a181d4803004403090901da075010140c003190400c402500780060028030142c0c48105070700d840c0c0102c2d076401c0b803071140110000c40302200680c0d4034411076001c0c02008601080300d82c4446091444c15190607640343c0d12042040400006c10100c001c0c010f031010303080b18907c600361507182019440c0c901050400300f25820070031082c48003c8503881c050b904118060848024002640e0070050210f480d9000400000d403240140800c0c5201002a400d280e042101c013004130071103002c25039500311131000707403640030725103c1e01c1c41425541c0300800d840a00040400b0f456240441d868852801070240c002118031261008011480f400c18401851280801c10000c02e0070303906102044031031000c0380b0b80403041e52142c001c02041040d0240302800c003440309a081c1980b22010b542c04c00030702c040010400340095000c58000800c159010068840e8075800009080 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 350493462 1250 350492212 350492237
    0x303030c020a05030f070c05101b0309180905060c0c0a110414041b0e0402090406090203030c030c060a060816090207020f0d03050a11031e0f1201060809070b040605030106 75
    0xd007001d00050020302107000c0426070717107031070076400f0b0080400b0340c0318588180341503480d0030401024400700501d4200242030300024800351800944c1039000b89c0d009083c81003c0c40d640c0c070b40981412101c510002e421315201c2c07103040d042080800400d82c0105141150505108013803880030b83d074144841001e02000c51003030602a043e1500d520160744180c209107801218a414104154280844040300c207070250303500300000d158141540f40f41c0c000c0354000c00d00162511940c5030500038110144040e64580000c0180c222510000c02c01825802c040034041c00043c50008986d104a4101c3d6201c81c119810000100384540d00710b01d440740039205100c40058070f036245800469080d440c05d100494200c0c10035020b003000d00d50004083c01c941503207581c6a05015001c1a030007034a030f029115142e4410081c801020081407000c00c0030b07003c0b0420452240e801c1c800c09404280300780c402030344004042a2040280140240c0600240018000000b1050b24107460490700501c948414071038642008038640d100e0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 350494712 1250 350493462 350493467
    0xf011b060e071e060201020906180f030f07140a12150207080f0304110a0b1b0a0510060503062d0705070605010303031e06080303041101020313120611030609010303030c 74
    0x144409a05000b01ca002546408002c86902e6100c007029260340c5001100292092050080320302e0800040c0455091040e074001d500440c4c2c40101503664842001100300407592001c0184400d02900000103004007071410740b8030221a07070b000280501400301c0e83c03003d00580c1e88087c0d1044415900445001c2ca000506074504024015038074010480e490010740c150015460502550149000300b01d401c80071b00c150b074100501e102007403103110080720007030000c201515602205420701c80c10b090103aa801d01030070381d41c40e400c2c0818804991140c0d03584003410311141c1400c0149660042e0758281c0c117103040c0c100a030b81d02c035810300103d0948620043c220009260500c0b0b0402c0d81c0240764010424019941c592801601174003c10000308654007c04030b45c070381c41504030300458003241c488030040c619580b92901d1342c061425001d420203055100810050b111700e10303504c008030010602e050044650b10309034070301103080d101b0550b1820900e56060052214075500c0042450442e5894140040c902c9600c0703005 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 350495962 1250 350494712 350494721
    0x402060702150c0304060908010e0d030c05070602040b030f13030e091806090f060a02070201120c0e030a080307080a06031208040c0f0b0c010b0907021504020d0b07020d09050f011b06 80
    0x1e0b003180100c003055501141c1d8000014005880003178455100c25a184e0003034030700700e03140704003544010341c0300340101c030003150081e404801080c5142c80e1a9141107000d85455080c4d078400c1c1d0100948500000400c03207905114640180c0001e00d014001002c1c0c1e120f52001000400300c00340c1a44038401c8540811a10f81203101e5088040c0c02910640b4010f29214000507150428258881003d02400d80041e5070819644216000564161503440d08800c403505030f50014007810301ca6009010f2a150b00b4422580c0800008400a05c1361121070303a2403034040c40081541c07101030030020980341440810310018600c0c0c1102e680ca10312070711701030035903070788900f480000b426699100c7c504100019a0114004407080300603d07400701008004e0168019031428030502c43c80403154030340141c020080e50071108040310801c070b0308640001e00c40c071540d04040c0c40e1260100c0041c0c4035540580d00519180d0600364020700d50130010001102d6000d4411240c10018090f8081071913005028110f9504803010001503911 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 350497212 1250 350495962 350495989
    0xe0601020a140d350c0f19171005090402210705010806030d0e0d030c120c1406010e0a0b0a0305010911031509070909030203091801091d060402060702 66
    0x1006100000b03000300b420345400c240c1c403800c00007511810040c002c8001c4443e004041000030380d280210500e10181c5011884030251141071014410003186d040c8240d458081c0003403415094000f42c600f07c3c2d19902400f01ca54548024038992501c60801004c410400301c000c4c219103040e14600704560b120310000e02c0280501040b107074900d40e05030019101500020700c074401e03200300b84c0340d004040d01c0e941c00305039582100c8000c036400901d080740514958149003542d03142c203500c02e050031008000203945488030107042187c403c002941031f00503603080c0f08444040c800c03240f5030200584155414625800c9082900404081c003030b0340c44401c040d5007521004800c00003107420400130845034550f0302d02489615481c08071940700e03105041c040107144c1c1084242d1405021580002c0240302d140c50030044c0504103581042e400e5001c181322106007601c0c1c5000588414244d81820813180d81012007000c103c44489824212900100342d403091015000503c9641144d01200c2c016101c15540c800a10001c81c1c500 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 350498462 1250 350497212 350497223
    0x3070609111207080c030604120c0c17060601030c030e0c220905030d050f10030335040312060f050f040219050307030b0f030a02120f0106030804030c08010212010e0601020a 76
    0x4002d45818102182e86000d94103854207031a0503260403400c0580d500404e40d4040e02c0c0640c42068401c800d4020450391803a1031140080b03811044e9554800301e5460002031064105800820401050350392622a0080340d8040d030504202c0032105004095071001c6c3d115a20340501025180300501c0250b6080100302c1c102d110346d050011001d50b16003991a034220126201120b402c10000c81d561910741ea500521501c00305200d00c00341807440d1001c03a82c1e81d5220f0800c0d0349141055102c102c001c807621011341c03c401c4080711003918906042c50010580059130101e000c542d4034100e01801504042c0e14440c0c111642100d200e060f4a95034400200284200814511300b030311840201030005422a0285116408070f443c20440c003c1c00c9402c2c03041107803400803040c0e4140c00020b0400c0041c90450150300a280458084030f800801c284121030071980a034105944000010a080042066171407005010300a540000d40c200791100d0402c042036507041c002d40091807032104c0020b2007a4800c10041e1b207283e4102 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 350499712 1250 350498462 350498479
    0x17031b030d060b04050907030e030a0e360601141c1b1716140d0b100c0209010b1201030f050f0d03050109180201022d0f160e06030307060911 62
    0x7210f00e6501c681c424802c05005500040c0050040c0e4000d228a0000300090700145d03241c20f1007080e04039121714940420b158040e2400c4c0071036150034484070302030307181c0b409078501803c035074007144034029890340c00611450420107500c403508800341c2c00c8000e1300c060040140c100244ea01141c0c100e83d014240a004402901e1200400c0d07020a40d4422141000c00c054070010b4a466103c0c80c4003403c25100340744004000c0380100c910000c065400900070f1082c20303000e46001a40142000018080c1c5048100000001e0160918002940340c43c0700030600400c0e5910b043c501e402d404a02e00458220140710180c449000341e0262014480f0511104900c180e41c0b1003a212000340010001c4d00402c0280038400c5518584505880928020720060500d9a016002081c0061040c882140c04000b041145031041e928049084200c80c801c0140641e05100040940416072400045004040030b55201151610551041c8038080d1000710880380380070b40220020030103050f24140288004603644403a130b00304180 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 350500962 1250 350499712 350499719
    0x60705030a2001140115050919051302180108040c0b030c0403060b030a03020a08090604050409060903020c0904030e0d03110a061a270601200105010f17031b030d06 72
    0x30a080c07001d00d00840d00c000c0c0b26203600212608960321942d85907001d01c03a5078014415052811703114402403581c0d241540c508000d060220f0240a016450034a100e209203405202c1854412103a904040c100482182020341e203d2100d8800c018142040d0305001001020805000b0000b007040007a0000d034020b036603030342010b403d09119540940f1060300c5141c50006441c200d45000300e040d040e020f4166006280904042d12080c0040d402031060b80e030300060402002031036403180c0c06601d500304e00403080018510f125040184c1480010400284114082420040040c1d0006c4880c90324010907a1410300c2ca400078a81520745103404800d40000c3d201e10704e0304204206041e005442800304513820805c07000200c4060200340d20002c050316000307190600c50030092981c20380c803443d40a80140351001c040510b1048814445000f00c821070780f540d440c2c2c00184802c0d000f890160000b4002003d520038810701040400b6120b00a0841110073303040c1000103a02000020020f03503042c45800c050030445140d6 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 350502212 1250 350500962 350500967
    0x90804030b0609132a05040f021803030903070902030703060e04050a1a0c160206040e010b03100602060601140d09170a020c030607020c010f02070e040b070815030d0e060705030a 78
    0x2c0301c08034802d1001a000941d00c844c0c80390002000e5511907503800c56101920000403e0719801001c180c0c0c28100c103840003900340e80d41c1c042d0554801011800507600d01a012001c004902400c580f80d0090b441041009800c1c0c500168181c205c403c142d03401078403500e449a048024181c40c1e404903008a000e003080c0000d01101084002d61075109403440d541c200c0c604903035010003e400300c41d12090041c05004589090b400844400c004903c011b046a146c83d0702c072007000c40300050a030851001e400c4040108000c0201c038591240103011070b4001454a03162042c0020012209100c00700a080400b0a0011160000e6005180310a5210b003d1500180c13180940c020503070070070440e4100500c43c081c0100003500703000c140d9030f00400c141d6004e401201c490000649030a0701c0201103108512607502e0015080003c8803607a80118403803082c80e8100d0410710300003400c4450107012269500952050b0b5a41940c0c0090000d040f90118108005680021400202140200070000c0c1c950301000424a040a5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 350503462 1250 350502212 350502233
    0x809190909080901030b010f08160c05070e0105030f0601050a05060d0207020a060509030d1b0311120304050d080601030b0a033207151106150607051c08010909020f0f030109080403 79
    0x582030307a0400004100a004548c6d84007840c0c011381c04100c81c003010680c03813502c10550120007415818942d460036081d0f6109403a220240d8003d0840c0c0c2861001031180386030a224884216020f032004041c10b5061400242001711a845614030451000a1489507250103405584619030020b016002150359000058240e61045010600c24096564840b05881c0500c1c02c030769510804c0f45c03500b0060510742d0f509460030710705818420305070300c61a07542c40410240030700214411752068002e0301801801c14405040c540014010760706050074124581784548840d5541c0d0101d83d041100c405040c2104c440d190070340030700511440c00e00d050103001306c001c0142c00034140c2e0495114070017000d002d1541440440704084006e410484503081600403521200300c00c21800180800104814500f08069443c0c80c0303403203840c01288a0000c0e2070b110b81980c1a40006070180101008a001d1090b403201e94006010102403c640701c3c4105102c9000c100300d03880951043d101c15510240c041e68070f0303480c0e0400400380c2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 350504712 1250 350503462 350503477
    0xc030f1506030b06040f0e360706080f1303090b1602090a090b040f030e0a091b1803061e050c0c19020a05040b030c031b0103060909080919090908 64
    0x80c206501100fa0703050800860301151240c03c120700c00703181020700c5c0c0b444400020304007403541c2101015407014100c500c8680c0c0f00d502e034450b041521441020681d41e0078009550f00c00c0c0c0900400101300804951014440b40c0e12900130f20b41000c0c07151443c602650740240380d400913005440701042e0014a0f9145540d40c43c038060003205c03040d280d540c0380d07000441580c004050080482c0e58a5020074005180600350042d001d1180c106082000007076804590080d6180d849541e581c0d8950f020903030813011618100c0694091460080184a5515078100300840d039440f00424403a039441d2004074959a1103160041607036120b500780040d003400008048507400600d00320105000700b05084807200c2c2c2c03100f0704580080d40a00001c1e400c914080401001f0186404c110707815000741548101c480e5400d00140107240000101a0121010800010b08850982d00709240d6a885d00d6800e002280e4601c007901d006460441d4000b0203040411080e00003030644d070780020059414200e4040400c966a406001c00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 350505962 1250 350504712 350504717
    0x30c06020f041a0a0f1d03060a05070e0301050108060c0a030209030a0602040609060801030308060d0f02040509210412080a1209050102030105010815151e19021e060a0c030f1506 78
    0x40c980c0c40043c905442641c00240214074500d02d0510428061440c4000084824909020309490100403c3c20088121210712141e41d44074100406150403c40d04000003105500820480d818101d142c1c0d502d000240c102d01c59468003050111100d4800c0e0110303080c01601030241e5002820038500840650480d02404d000702d002c413040441c03418440c24055040700c0d01542c407015a0744903002030198070b42c2041d106892010288580b04056111400b030540240c2c1400c000308044040311160076070004c2c58510380441100d0801040060743c0d83d0140101f03171203801c440e0310b550f11101c442c016100700da0384484011807181041d412034240300741940510b049440030b80310520760f0340c0c9003441603c0c41034581c1003480e4080c44588041494a20303120140c1442124100303820b010050042c80d542c0585c00c50b041200440301107401c10910103605106500d501076503280b415500500800ba00c5803280b6004080381d503090364903900a42524865013040b04610280082000681854000440d5042c4a070040001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 350507212 1250 350505962 350505989
    0x1180b04140d081f030f03090509070224150d051014040302030a08040507120b0603010b01030213060305091e0f060105030f10091104060b04140603070f050304030c06020f04 76
    0x1800700c4086650711400d4015640d041450f03994820f681c2c91203d1a142800070005400400300002c2d01d4a10103680c042d0180d21940509840e120400c21114030042401c0e0454000c1d9015058004040010711006014200065030a40d2100c030b050700d50b088030340086941b1241c03ca02907420f00002050004030003607440c500f40007032243c4042c4c201e40b83d0b000b41d5006005134010090808102c3c81401442e42140c420429148095900d86141f002030b0344601c0152210720788030040c1310b400c1c0b500344188a85090282010740c10800f065006141e003a21600c540e105054440c03002403003003002440b00d980214940d0428040e0784115100c101c0e61505004445c1046208203000402c09180015010504184050041c01304001031b6101b580074240e09074041320814402024010a5602c42c010303a0068070360311002944861074568055090301a540030140200400c105100009038803100380880c09403a400c0c17603503581c2c660385812102c1c00c2443e00c6c0940701510205500741d203895008014005c480e1001c10055 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 350508462 1250 350507212 350507243
    0x604060c0311070b0a0804050c04020307050c06010e04081b2107062307050d0207120c0203100207120807020a0506011707061d01030c021c08040308090a0f030e0301180b04 75
    0x1e80e40c1c0f11a0260070551141403041c00c1342c480c4129140c0e54400d04c1035003611544103103000403400b680c009403010000302d03601140088a503102001050b0042c4000074036090181000c0e1a22000c0d4401d10340500035181d903078200c000c245c401c20841e24014151040c0030700700d181c4001d1100c140d1078000c050100c65190030181e890315488401c802000d07a070140004450500c0d1182c41d419603e540c800803284481940911009011a4030035074251416591500ea8041c005600d2040500301100c40750501905841440000c001c602e55980001103920b05082482c4a03841c3c00c03c041e0328008098400034000e02c40c10300081503007488071100c41840c40c10142101c3c4042e0700e0312402e40e0150044041d5039980c04050007800300c0c96110350082204200c3c580190b402e1900300d00b022000b507415070702c106808118602d0500007050f030b0284600354806210701c06800c00945a0fa90781750300d22004600038003005074034243c0340003640c0d0a502c84028a888100700f80c64070541840c18156400c022902501d6075200c01c01c214 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 350509712 1250 350508462 350508497
    0x70b0a0b180609060405220804080613033504051f0c020604060504030908060901050114010906021c031d060114090103030c0803040f0c0e1006020c010905010c02030102090604060c03 80
    0x5038010ba5004100031001d0f6100000d20005240c01080c02042d480c0030408a00282e8071140d287c900c0c0c47c0034500b00740e0380e9414a500c0c1c500d004405410f101600900d05d40040c0420b90044002e111807941c0003414080c219084018058a500c3c0000902041381c281e041c0010000001500c0e07800d6013560b1500c04c0c84080302c62610084912080407d80541c2040000a0004140c1d9102983c02882410203451590311078840900d0007001b10343d0b0b01c13050781d5614010300591034065050b004070384003413170007080c0a0b080402c029200d803111101c0034200d0000f210b45a942d10300a0308480c4c0d011845e910054502402040303811384d00c4000b03110340d1840030411316a100ca0b50030203101c081c0c1607d4060304d032400710403080d680d001942ea0000700107607a0070184041160009041d4800c0c80000c1a40100104141c10b00c2c51803681e0b41c50181e805039095510084001c001381e604000e4580c00c84d94242882000c0c4e0380c150001ca4003910031011a198001000640490071a40108080d11058040c0d9107660035012a520740 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 350510962 1250 350509712 350509759
    0x10209040501140d020913050109030203072006190905060c010f0f05220821010302091e071202040b04080331030206090301020c0a030806130b1003020906070b0a0b 72
    0x4480d04138440c18140005400e140051541244501407807034440d90031501d400b030842da08100c0442c01a00009450420b100c5107201019064281c00c0500c01c3c003588600c0050043c0c45449480d006098400309027005080c014443c81009007000350548da910000c06000c00e008014400c0b60004140c80c0010309150484244109403080d10181e1051606080480344040c0704940c3e410201d80418042042c1501c9650802c07010070351081440d4004201e50443c41000220301340201b010300d902207002c03030003520a030349540d21942140d0b6504001002c0d6001c1741829000e0710880d040101c0000c2c0009001613090000001080d0b180100a442900035032078850901c03080f0381c4000c401550a544030300034809880d1090081440b508020001460581c500102d02d00308440c407a02540420454000c000190070040b01030904500164802c100052078035000510b81c03119081d622080681c00320383d60403552500f400f00d501d502d8004006441615003030084001030a90283e00c6402020500245800b60020910f07 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 350512212 1250 350510962 350510999
    0x13050a060e1611070f0806010306050705211008060f010f0f031718040912180501170703060305071502011b170604060b2106031f0203040812010602010209040501 71
    0x500c0c05240381e000c9620300c8540c00b03400f07002d00035500b0005d01c1030f004408903401042c2c0c40700a001190701d10b003400406c0794402010b04060013010000b83c109c0004a0348021504241c0348400c0c40d0689541441106121480e00b24103c02c0c443c035005d00c6000d03510940d900d4122628040c089a149881b4040c201c4140a1444010095207013540b0801020300c1c0c0300040d01e00900c10031240030149090b400018243c0b9000d090a840712080491141030f91584403104005c40d04051200040c1c0502d40b0300024040140300c01840141d18940c0d005c21038140c4a0f0700480010754208086a032029283c032107000502c826418141c025620b884c002c0711030824010710f60141c4034078588070725079400d4520b6941800c015005121560241ea12140490645440b0380648946912901028405104900b00912200024001c1c03442640f080401c00e09003ca043d117a091850818007002d0303241d4550386814221401584181000c402c15900040740340c03541503019208142003200d0a02059998074024081040b030600c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 350513462 1250 350512212 350512231
    0xb21071203021b12030a0e0d15021305040501120f060f050708070816090501081305030f0703090b070206030c0f090406150210140703020c070801060e06030607090608150f13050a060e 80
    0x41306d014028020403007904851800307090b0b0702451030755a491000c00003803241800c81069001c40d4450105001200305405400103803820005541003a05c603a4807100109401880c20700084541e60410119800071190f010703442c60288400d04000310090200030b0308031440782c0014020030000365200340d40c008520030381041c7c0d1505940e02c0e081c0001120300210003404142c400c071000603200c000a808000811100c1414500785813a60424a0004c1081d813090740700c40700d4044148607942c0580d8a46080340d40001c09080881d81c0c40301c91412084040c004d0800580e8014913050002952104100e1025803000040c0e0a40d22a000c8090700034040310000000b0ae4008088240044d0300280030364004c0c085d01d9444400c650550f0f54541140d82522441c0d041aa003001420341844210300b800c03c82641c1040e140d007001c8051500703054006006a0004050011580c2d504000300251307181c50044100034000509600c2d815008154140301511080d550903d03d6072801c1030001d14100850017903030040390b41d46d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 350514712 1250 350513462 350513467
    0x28030f150516080c1e0d0606020a05060a0513120201020702011101050f0c0d0204030816110625020a170c0f1203120a0b0913060f0b21071203021b1203 66
    0x880046600f18402810744100000c10403c0c408050326a6481c416079002d004845030b41ca00c48098113109a030000c0d40700f0300665100800441c0090300120710309601000304500040d41b956220ba820704940703040b10020300740b01640b4002d0110168190000d00c9024000e0329903507949400c90141c2030883d00200c0d819120303030600d0004566143c0c000801040c08100c2030a0241c14180c0b80d803240d040980c000e10f45440d1000c40303162a20104010b85c009860500d400311340c2a814110044072000c44200a00342d00d10008150504c1ca03001c65907801c0c0541c010b40003d50315039420850900610380e91340502800e05104065040c1c032100c10349002c021200d5510841c0d4060350900840c1e11502c01e2071307200580075504894a0309400000c0352900d0607440e1240c20420155100b403942400e03d202281c41c1d40709441001410b295107100356480b1303045508048100000082130655600200c1410030b202a00324501001c41009101d05050b400104001e410300300c180d820074040084d41c02c214801d66010064012078109 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 350515962 1250 350514712 350514751
    0xa0b010c0f03030f0e1615050a2a06020301120c081b120109050a0b0406050705040e040f030e100905150901021203040c0302060d0e060703050403020c28030f1505 71
    0x240c00c00482820a0303c40802d0f400e1585400b2403c000c51681b8000300f11820180801c5682a060024074020b050360420614100404000901130001135029890044044c4080000c411601759440303815500418115241c4d41c541c801c07000d40c44040b040c00e880c400183e031000704100e9004035082c0c1c41c0400e0010034016500200342400329004508003070314055541c58480d800800c4007407204010b424450005181c02e46841e03e07103e8110b42001c6c2200040060502090040784041d04404e5003160b0491804042200703030341750464018000b08110341c4c000401941c01f405942d00304030a82c007610821200c02c443c10003000d00d101124001c07000003600590200076610004c0840c1401581c015000384d1302d564080303840750007180c20b130742c0100140d094142d51603a68010105050140c3c5030040503524040c4014101510000c1d906c0906021043c0b1800740703c44e0b040c0c0d4100c02100301810380444820786914040d62401e10a10441042a064800042030080011400840c0c865144501402c1c414129014072 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 350517212 1250 350515962 350515967
    0x1e05030d030b010329011d030d050327060105040605040504050303010e0c160b250207030206180d060218150d0207080c01050a090204061205030f300a0b010c0f03 71
    0x780c0840c107241c0d49102c003440c402507401360f001e44940200440740b4050b800500060a01421250307e201c5a0805219031801c0d90300070030b081d10030304e585140032a101c0d190228811503408001c011022526a1603141c05240000800d50314100c483c1203408200d4070756114103000540b14101c40050841d08108010700072041072400064011a4401d03466041c800c2c1c590a0b01a0710004100c02c3d2a15613860040000010520b14800d540d108103000c428a04240c2d0100655100d0b1307203010003481814003055042c030480340c1100400c11010020500408030006080500007944407098484614055101d90340c440c0c1400b82d4690540d04800004074030b2300c0b6100c03070400025040828103c401290810010018850034040c0ca070080031403c0c00029070b030640348100300c00c030707185a8000365000140f00e0a06010540c0442603800c407030001d02003955640c5249154175002410944038007400610031158000300c00480301014403420085a080190b0440c880040d9030b54030a55000034484d80d04001071000191 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 350518462 1250 350517212 350517221
    0x207050409081b07180b041512030e03100911100923030102070c0b0c010605030c010c06020d271502070807060b0a03061d011422150204060503011e05030d03 69
    0x42e0b8801913603242174403030026600c50340d03510705085421a00e90940001d5854035100b000c01d4403002e070715140d20b141e251420145c5907840101004c0d090090252001180d6101804000d10450341c50000b00900822440e100110b080c001c101c1c14003070b20344209034a5a42d4010801c201c2a9842046060440c401505610080f025180752068055409024800c0001d10704482c0030090020491030546034600c9140180c01c4a007154000c500ca5072080c0480001e90341c10030207120046070000c80240e07460a0440c5401d0262140c07a00c03408800744080080e040550082c084468040c1c07144075120742241c60342902409a0240b43c40240c442c1e00200004030005001e5440f031400d130000640031108441d56511410110740811034400001c01036210381c014061400e1080080ca980070380c4e030030301c00d9003003140700001c80802d284401009540c98034030400134031060342c010b003007000751038041599100d807030b444000c009410a103e15144102c10b620419118400b650000b1305a0360054002d06844000140883c043c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 350519712 1250 350518462 350518507
    0x3040603140601140a0908150105192303071206021b010c090501030911150a020c030105010308180a0b0f070b010b030f040321180228030609031b060903020705040908 73
    0x7520100000e0000301405031410030314a00c82300d54009d614003418041d4050760802110200c42e942d880c1440040a07000d41c180084c511008120034035107513000802e00d041c1098118403030300d01c4e16000810400510703400030b21101170f1011081401c0300000c4001030a0b12040d090381c90120751100800e219651084e440b0000c51405980b61810707410000c00440c100c021020303614218148006160b01c1000c0e01040648070a0005400801566166880b07036200e80c001c41025054015902e8009103040d5a900710840282c0141956181e40708140c4040c1c2d20280c1c418981160003404580000502c14000f44c00c0c1e9100d1800704409500d59a00e56034201c5182465107001c40861000c09840e0030030b441584280c1300155280640307080166203c0c010081d1800e01000071081c5455012800104c3e081d00c0e13250202160f83c41760004ca038956291905644c242d251214030094076064102d00783c14021550042d02505019800b074808058940003404243c1d40581c002404070303201004141741d0392900341101d4882 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 350520962 1250 350519712 350519717
    0x70e0a081908070f0c15140d110408030f032403100509120f04031a100b21090c040e06060d030e0a050a03080c0d1b1112010e03040603140601140a 64
    0x608082d59500d54074200001e000f6545c6480307451040c02502e00d221910040c005980c00c02c410403c07441e9101908511036010708000568840061025081960054501400c104c000303030ac8d101c65060200940e641c00440d0302c800f0800c10742440d03180c201c690740d205c50038000c0f003e00680f01d00780800321620041c04001e00704407400d2044041100d9040310640180a240d203900300340307940c1e40d8a1400c00b10618001a00d282c07034260031b11800d01c82110302d0b040c2141d04440c00010074036100c0e41803910500c50054018013190f2052020003c002411102040d4101c1507032045504010920501e002d00345e880c401111065007101d071440c4504080307030080e40c41400e810402401c1c2030085464401064080740180d0040700e807040003241e130341000e100500070100d022803949480400c809010221062002c402c04001c2d0501689221200a503200d05000d413111041c5ea00007403000414000f11559290b01500c03c590000303181c1099040c110341810140c0780a0401692850b82d084503208094a007640714003500f100f03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 350522212 1250 350520962 350520967
    0x3090703140c01020c0312041214160305010c090501092304090c051c030c060c03090f0506070201140c121807030c1d2e03060f0203070e0a081908 64
    0x307000e25010340c407145022000c0c0075909110000a8030f03107524401002d00c80c3c0c103c2400c8000035101c20042e0b80c210780c40c0c070400741c1000c1c9041c00c0071444100c3d0040b40000320b01800495504a100b001407000440340314000801011491540403500b40800c0d01405000450500040015065204139070480d83d440380403032411008882c000070b04507003040310122080f4018050030412132030459041040c400282480d28010359181d50f0040003514004801450b946e651502120454800e611200340b09911100400849400341801903036010708403001c0005601f8500000941c0e500005100c0c0110301c520481e41c00c01301c1e900300c48520004020504040f503c1d0200c017052a400b0b00b009010b00443c020516030f40c44508180160a40e070407001c0c101d00d03064a8840c240002d007440e507105210040c1c1035124582414092910300c1d103042c4003e6001030f05071401d01e6290903120103981c0c000c41c001d4056840c1e2401408402c0c050112030035a9120700200f54000c40c007828045100c04103180c540d14400d219061 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 350523462 1250 350522212 350522219
    0xc151802090106031a0f01170f04051203040308191103040506010f06030b01052d0313020a060e01020a11030c04020408060a0f06120b070e060d020309010506030f0a080d060f15020705040506090c030907 88
    0x108d50104892000c0d41ca00040180014000c0070310141808a5500a0062440c60282c0303000d44400d00c046e00c2001002e010780a0101c10150316030103520050302030800c032540d80c03c2c9400d00c0e0350386550a000c0c6100300c0b85060400140203000748151401c103103041c0c541070b081c01c0807000802d14003c211090001c101c40a040d44c25685510f1000946c405e80130403072125132080c0a801801018841c0303070030960500868044008140ea00000c603207a03030315800441001c914066002003801c140fa240c08580d0014004500400d0f0303c280410540c4c070030340e010b03041040903074040410002950703514440c0c0a0309400400110000c03501c40d000942e4004400d0405100d0101842c0203c0d035503611080800d01001d5000c424031420060138001c10303130802411801040307200011410741d0f407104d42c01c1c51700422120340060b00c20165107180c1c0246008000342036803110b0440ea03502d00ca40c181440102c485c001801402d402103078030310342442560300502010700412113a55078468803604641c03000c0e24600d0103200d800c4000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 350524712 1250 350523462 350523497
    0x21513080d02060603030901090506090a09021606050c1216050f04030c03050c090906010501030c031b02070e0c070c0e04080702091609080303060d02010c151802090106031a0f01 78
    0x140010001040186189001c0c51002410034101a0045129420800000c0c1160ba0301890890594408548182ea20480240022012016941302490f40b03800420030300765030850364190402150060f6410b02055986650348109442400e00c42c0c0c3c032120a00c4040b401260305062491020169400c00f075152020020041d05280c01940c02140c50180d4280103104000c0240012840480c0036030b81c0c648581080e8030040d4460b40305004490415980301c00144405100342c01c84032070100285211184080302600c001e440e05030030301030482e0740c0b0b00c1c00020a000400c50400c60f894580c0103003d0300c0000c0d0601122109004003d007098030112014030111f005a559200c201d0b000305211815084801d00702e00c0b01420080203031b0700401d42e64105000300300c99500d401d4043d0810a0b030918020740300c1020f9140880180000703442c2000303403a00e4100e0260101824407020300282d4002c0310044030aa0b65017001700c0c16510b04a0001c003a42c1d050420720410b41c2880d0140310508a414140703031946e8130000c040c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 350525962 1250 350524712 350524747
    0x80304050f060a0f2d051f080d140c0d0e12030a090801110703020a15060b0d020702011706010c0f02150d06050a0e0705030106120f090b07090609080a0215 68
    0x240c80c0034a0360303a8049001c0714203038402d800c0c4802041800007041c001e6507280d100c089455a990170007903601c901c005000304103051b03141610a0782200c6000c0702c10341c03141d11503a52041e000f0611004601c0111044440030080b0b4241d030f0501000d0002001c2c801c0354404d00302c0c0c410801440351500f1030300007a03081c80c24000a1004c0c2c803c2d01c04656900d0561807601c44840c0c01e40d456030004003c0c84030200309000110b070340440c8200d0380a412500c03271881001040c9604008204692206c10014800f280390021a55150014403046000341d94411000400c1d01ca80204040241e4100b070206a800c0000c0c000100f0381004d10040c203000505c0e0240034407403048103030301d29440f0651450950755070f140b0910aa2a10103087c4000c1c01035a0b100d05c04614065202801c540f0040c01210b05000c0d041d0b81091201456401071086510514002d0000f060310b8617100045590075140400442c407070701c2001c52031500c90511141200c40034002062034810507000d000c40c0502d01403003158180e40c10444103c086501089 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 350527212 1250 350525962 350525971
    0x10e0d030512010e10090b0f0a062114220b011e150f0c1704030c05040515090106030207020102030904061215050601021f18150c030501080a080304050f06 68
    0x19010360b110035001c0c0c10303001000140c1226183d41c85041c18800081500d210b90420745020b00070008010032060b0018800d1000082280d600c8001c145012a449030300101c4e00000c0000c140700101c80078a802d02e10001e83e40c2e00c043c4012015480030000e03254034005540a01080b4982c01892204002611910050030003604840e02c24070191340d280e84016402050000245800302d284000706186840c014010000d5148030b00030408016103c00a206010541b002c824803132100746c0c2d40e181e03a0303840c100c04108840c0c07080900c51403801d400148000c80880c00c1e122460001041d07003215a0a11405800a4000c020182d04601c0306002d040b111b03407920721460b80030300108010101080c42e07928003014008100c00000f1042e6080030244100740e60006840410f13130b8540341c84070042c1361408070b4590050041c484d078141e2030410607000c0d030140220500d03c254a010501414415001050002d4098030800c0c800e50b103e90780280f200f07001144045d0040d40c0c201e4492015076030701d10780c540046480c2c00010b44 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 350528462 1250 350527212 350527217
    0x8040305070c0e010807051c0b0402060d0c120f020a0806060f0405040608010b030c010f0f0f050d050f011e08190503120a02031005120c09090102090d0302010e010c0306120f02010e0d03 81
    0xb00500c0158006c21100b001450100d0780d451004401100040d1046405880141580001d6001c1402c5540744d206030303043c804241d0400c1101d0500f455000303100000481011080c94030344841d000901c4001e00031500c40b100c3c1512403803000e03180c003801d0000903407180d828003010120500010845951340d018400c0200086400424440003031405c040c204041d42807824144909c0c034002141050700001c21105406d02410030425420023004280c400d0700c255100d1940035854102000000d0312007003060781c1620205100180e420803008a1a0b185010398025011030350b1002c03035901c0540202c4c100400019100c0e1050781c1c02c02c460000e4a06041c1c01c20703203405640c9034001c410003e0310002001c044004143c21540c200603540ca42181a80301d100d42c0710001d0242c240c24000074840710003501164425003004d80044441c040c40d081c028002c2c07411907580c00b0305500b80006044058402d001c0c06003520b103c2e0501406010007a40c504520040c8518101e040c0490021208100e82d00e04415118950107034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 350529712 1250 350528462 350528489
    0x10c0e040c0c02091603020904090521040b0d0203040c150801170102090603040209070c120e040f0501051005070c09050f060306161e02191a220308040305070c 70
    0x502044156100c08403807004000d6819500c40141e034412400719040400c128000d03e4440318807904070003134810300d21566002802c01005004000d4009001c00070804030222a000150412403401c0b200e1044c0d00c0344400d2400f0500c09250100b20f00c0e07008640161040304420129585e803070071800d509103241040b0b40400c10703e4004201200030341d0708900604c0542c070001c510b4490175000240b454000500042e008800030400a41400d0144400c02c110540003e0181c40d001032040005003003016100c181f0380200e09020850b01c00052601a85042e104000d1242141010318030082310142c1180000b6240e5142c044400680301c4083d206240c003685002005210500d0175a050614062000d0700f0500103007134039441240b0103640f14050350007044030b2803400300090170700070022450060300c02d00301070801c111283c5103404c02480aa082100c408482010142c070741e035034400c034580c03440460032840d841c00041050100207446010700c1c035440342c0319043c0300d401d060703150306c5025031030ba600d801060038141c00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 350530962 1250 350529712 350529737
    0x601212f0703050a0e010e0a080c010e010903020a050d0f0b0705031602030304050601050105030a020d060b0c071706070c0c1707031b0b0403080a170723090102150a0e010c 75
    0x89824060148440840e0189405810381d0b0051040c403c0100c00c204201c90071322240303650fa01c0307041d032040404002464170524070340b1408042e4072400652010340c089015142c50b02d055501a5845030104d0f50010089070303801c0d00d40820f0101da02030a002c101c2d03045004940c100e00107141540141c0c000c10b45596100d440340341011249903414920444401554418820400010000074030507040d00e40a00e442c540f01d403500303003907100a40600c1e0480d4441d1414040045a1207410750301600750001090b01b220740082d642e17140380c284180200c040304e22a40050000920b11800f607507801007014411404428400e40e140c0300c516613050000c61070340180e004a41c04105005030000005690200b41400c00079552401400c28028032440c84020002c0300c0100b001c480c424018440d005000080ca50028a1441c00400050000c2d06c001e180c070181e01780451102c000c0b00c2104080d15800c0c034042c1c0003403020b100030310030b4000c503200001d15510426886500d80d81d0307408405c1c040c0030345a140c162100f9003c0c000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 350532212 1250 350530962 350531021
    0x181214120703080601080105062a0f01020403080706060b070819091205030a0f14090114040b03010b070b01080a320d03020a0206010e04020f060f12010e2d060121 71
    0x14181d00ca142700e884184a07810701c000c1c800081caa00c00711000c0000e0034660070070614504201d200040d4402d20b5101003000418044000f008105191040c10100002e903141c0500388040c2c0140f86000c1c1c84460f0500961070340d041d00441e043e80d10016030500300d4560795140003040e1004140c007800c40b180c3e003011525044580c1c218200140741d42d61420100522940c40c42080450700550500b1030422045000c019003001114003103402410340b41c10066641c0d0307144c070400e00c07080d4402481129058040c400001e2a0200400ca9034203296010b8038103c01240014008038412800030900c2c141074500c0350341c1e100070307038001c01c840c00314020310b80c90158448074100c0019040c0309050348860f44030b80910042100680d5411031a46032044111025600e99281c1c0300440304a0044030b60807650b00741f40f94008110035400d51961f40c480d000100308a084c604640786100c1d4015010890300707541c0a50308000c11200d40c01040745600280000381444829114142c8000c199100301d291108800c0d03220705030010591 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 350533462 1250 350532212 350532227
    0x3030807020703051b010c0506070908070801060b07020409112d010806100315080706090f05060702130c020307060f0501060f1806050a120f0c181214120703080601 72
    0xc85a001510286103541c5600f900c0d00c04105807154801a030070b0b60448668081c9000e003000640050458030185010312002d13242e060b5074020100103101d02071000039008014040c05080c0c41d0360b40a0b003420001a9424040941075048086130b103800c8441d15220f6944420181800700c600701001c142541a800c112403030b65004030075507507040184420402c026910f0340103907900d8030385e002e2a000030307000d103047c00101b1000304079002029140249400003030110341c00603130030b42521038240c9442c0741c295036003040202038810200025001094010500900c40c016030120b048003034140181c1c1e00d0210640d45000848a000c541854616a140010f00009600c146216807041040c00e0079902003c04e9840c213110012188248010403070009841c500180c41411014020078025030140a40e0b4845640d00c07010b4124498814005045a040f2001c800000e01036001221140318603a03540c81d0781615054141c0050340d000b40210710408c8a50f103510307000c8000800c24140a642e1362100c2d420444001050007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 350534712 1250 350533462 350533471
    0x81605060118140402090c070c0303090806010905150d2108100906031703070e06040306020c0f062205031317070504022106010908031801080c120402011b0813030308 73
    0x60b00d40000c03e140c580d44005142c1e04540c0451304003000342d455880c51841c501c103000c4000c0a864059200204160700264580300b81c440b040280d603101d80c2c80c1c442a00c1114001c644ea0440008010582d50180c10700c0041464030a00070801800f0315046411000c0c005030415042100180841c0d040025038010440c610014004a103c01d00c003d503d16200c650004d801d900750015000000004591503034040e001094170110054000ca4480d5664200080250809081c400d240c1c0500b9103824403504021031950b20502c425417042c4807040c202d040f084904034034814102d403c0d2000700100ca5407600356500382c08c0100034090194801150111545040044e01e40c007090186c1c0c01030241d034200c039051700c07412510b01c2825048c0107682d0780d45500480f14078011360720840b2940400260045e1600c0b40b08052042c0040c00e8a8845150311040112031440c49003103a907032107083c00301b40460010361203188030b1890102582d000d8200c40751192900034960f400300d080700d003d1a00086040082580141a89900 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 350535962 1250 350534712 350534759
    0x4033c020d030e0d0c02130f090605070305090c060d0917042706030b0c07080904050a050717040f0b1009020c06010f06051608091c050706080112031b0816050601 71
    0x1003955407040174098448040000703200300300a618a142c6501181d2060403801b242d81014040c3e4003590400d28000c00c1c0070f03580f1100003420080003400d00b0310001120b0030120805031240d490403100041d540001c00c04039504a07107100c22800c000e04520900c10190010740441d500c42e0007450b9401e450000e91004905080b11070600784581000414491038032180e000301c2198070155100c0700740c541180d0a106545001394041d01d0003090000b812041e038003d91103400c40340c4445035800c03602000d0054100341190f0040000d48103a50303410000f0800c40009030001d5225032000740071354071001c846041e030700140c2032001c1d2584048010010000340001c0d000040c4200d080003880d148518280d4810301002c190060310804000910802c40e07259860400700c5124182c0d100d031340495503458503540f01c00140c840d0b640025240c400106006460f41e40101c2496410344920841d0b0304e14140c81c04482c0c5401e14156140b030303000e0080740d5011408690351440241304001500003903045c00102044d5183d8078001c0c5030b5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 350537212 1250 350535962 350535973
    0xa0203090312030a14070206280c0908070f050306040f061112091207021305091204080106150f0f0e0d02090403110d03150b0f0f040e0a1404033c020d030e 68
    0x116690003169158004923141d8524100d09da2000206410555486003000344519000504115580c008081e000344c5010360161031206a03140380c80d0f00070981901400390302da0459004600001e00c58600c03800c06900c140004520603241000b502c070b0b10b4105642540d6a949440c04104106c00c05020840c1c04d405428001c0381480c0454021501c40c0041000300030310280d83d64040340405004102500b1060368002003d9070303e5844107901806400e40d8860440041204c07045825245e000381480074101e80c140d511143c050722010021500701c0004052190401e008054020160b01c40b242c00701c0c400d9000e0b40390044048103810343c4615181011003403104141c43d140c80015601742080c280c80c125024118640c0c1c592074124086c680510580c00e5140410000240c0021011111103a41e1701c1001203410030400c6c064480440d94144008980003000500b580e06440c1c0c200320007031400d40c03401c1e2070300070380a80041d422941c0f2814910114103c0f8096802408640031640c2c3c94020701e060060031402411 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 350538462 1250 350537212 350537221
    0x70203181f0c0c05100c0213050403080f0a06051009080d090e0114030f030c16060305151507020a0303030b3a05030708030408180904030804080a0203090312030a14 72
    0x20042203800804104403180c0201c009003c510075a0001038540180700d60700c1469a0b60000c0c00a03030780107100304d000d15082080c40a0030301c0c00d8803c40d44a02c1d0180c4031049569070740c084540740310700010140300a050780c070880400c094594400b191201070254480742c8501e810061800c1c0340513110071402c4c08005064009102c1ea2543d090b48604617040031a26241c501001000a4100712a4840b5038180b4400819424504034000560914032001580a030788641d88507074040b01651070403102c40d24210740c0c81c410f004060a15040d00b01406020189036410141264000b6100c000680e10550000307443e01003641c9285402c3c10000300000b519580480c0180c112024000000032104070301012a061110b00000d000f401c6c800c0340c085550012240380ea920300f41c900400d1a401c00d01c488000c894801070b031000d41c0d0404d21209070142d40c0503103031504a5940c50f500d4003903c0d4401802401140820300c241116a2010402612881c0c0501610742c3c07289098401c02e8101c1e41c00080c0360064503404020301 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 350539568 1106 350538462 350538499
    0x31a09090d0f0216180b0909100e011e15080703031e031a0405150a060c05010f0203071b05010908040e060a090c0e060d0e0607020318 59
    0xb030200001d0700504030303500e85480140707046020f1002000e102c00220000c0c0a80d000f0700c50100800c0d80103014011641c0844203640c0c409032a4021052040f903803000303006240246040e003000f0424400754600030b407c28030140d01c815401603601c01000c00903450381d0441001501d5072000704d8040d9a40c0780740050002c00c1c4600da000b031440e2601d442c0d0390914842d02403d880c0c0703210441e038011920740c20010440100b40280c0841c0c00d8044550b0b9441c0180c91300d0f031290005103456280d40a050ba950305105094920340001106040d1040003049a00d607000301c008040a09840023510f0400041d15102c3d00508000001420b803420205e000543c0818682c1c90501c10403055403078100d803039941c40401c801d582c148040ad00104582c01c070400c00d03504106020300107c4009400205042840311104c0c0d0030400140c90600041e00000780e619040072001002c0c0581c0f050a50700c5410003402440300 = true := by decide +kernel

theorem cover : BRFrame.Cov 350359712 350539568 := by
  have h0 := BRFrame.cov_init 350359712
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350359712 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 350359712 ≤ n) (h2 : n < 350539568) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
