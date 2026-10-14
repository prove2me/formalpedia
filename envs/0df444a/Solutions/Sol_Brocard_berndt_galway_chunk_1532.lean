-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1532
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:26:15.509823+00:00
-- url     : https://prove2.me/submissions/bd89b5c6-32de-446e-987f-950af95af943

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 275359712 ≤ n < 275539568 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 275360962 1250 275359712 275359717
    0x150c18090b03060c09180c070c09092006040902070503090a0b0309031e0408010e0d0201110903120906041208030703150509182508010f09030f0e032109040e06010506 73
    0x1342e01501e440050070004548640445100800b2680c06070913403424460324050455226107001d031205400b001000c50408c0042c8614840c50394400500c2580b0305004003000310b503460319140303694009401e1000045000341400108111031154002e0355440c0c540c681007004030b40f0290010496400e06104104500c0b900200710380c11001800d0780348900f0320382207168640c4c912464105c0d800d6942054803054221760300090304000881250020301c1f601200c04425070030341c0210756015905d940071054122290105600402030003601402040c80e103521014007040241c0d241f1411aa00708000003002103441c3d041c440d9044901104d900300802c00d02c0c1034005404290302a24001a14042030500034683c001042801501c1e107548030240600c0700c2c1c84050340c58800c804c3c0304940c56542806814400b03000d981c45074000d156415242d14141c3d126203007040740c507140301d8210305805100d8000302185a4404c0801035452500031041e159aa91341642444141d8020b6290399610380e010000501c459500d0105 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 275362212 1250 275360962 275360971
    0x601090e090c060a03050a050f0702250f0308180108010e0601120b0406060201090221070e1b122e150c0c0b030f0708060108060409150c18090b0306 65
    0x5011006031078114a450801c41d42d0004a0751044000030305841007a05500001c2c42010400402c11282c0c2d45c1c600340c03000410040322000010381000d502150400c1a59480048074045e000c06541c210391200e1410300d4508054200707481108011501c80e41070142d44964004c0c011080c80c1918246d4503000740b60001e500c002d400c0b02c0c1448107110b4990480c507620350003207000100040c0180140c0b6644c542c0a070007000700400c00c0e030154110040c4056001203180ca0000c40d11001d50051401c2494000e0307070860410090250703a03032109480c110080b02c0400b40302501001880354040c0c680c03420011100b070800520020b000100f0b803140501314608205584641d000c403841d07807a076200001e0b0005002c440100100c00020440e805600c008204040003201540c440d44007505c921040e0b4a0300081660511070880f070640c002200c2d83c00045c45070401d07070060151760703204413844681181001c220500b0b4604242c0e400001070044880030200312254003500c0b00a000c900010000306240e5808039495040051 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 275363462 1250 275362212 275362229
    0xf07030506160e011b170c0d050c07030303090201120504080414010f0906050a03020403020a03060b030f030c061501030e1911040911040b03070f0b0c0c090f040f0305090a0305070504050f060109 85
    0x91700c002400c2e000d0314182c085551042d20141d1403095010003400700e81105034000032520070440250240d5000f80100c0315003076840d600400d06e240c55a90110050002524100d04005035400e800058a9550103001d010f584201c6003161640d0a120b00c18405442da18400c604211110b0502500d2a4020381c900c0309803181403802d55681c0340b6000c1c040c0c0181c41541c2c4000d400240707880380041840680d86c042483c0103001c9040c1c2e0104401d2041e0107580e80101c000300c2c0040c0c1c0000000c940605620109141c5542044c10302054140b01d070090f0324140a58482d20062000f07040700c1d141c04004152100c0150024115820802c1d1102a00c4e11500380b0460b440445c080c43e03680701d460815560402c1203000070100c01d00c0c0f0101c42600e402100303902c1e800c840b4261170300340b18074000c0514501d8407020b4203228110340d141c031030429582c40d02d03407e141401120054090180c1003004a915071a842081d40c0a5801030004004252420042c002141e60041000600158000610509170780c0200030104894201 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 275364712 1250 275363462 275363477
    0x61e0604050d050105091207021f030b060a0e01080a150e0a020708040312350406141303080a1a011202040503070909120c02010f03020c0703050f07030506160e01 71
    0x40490100d220340e8100940c811038620140c4204541500b09902c2062081c05440382541c1c1d0050505c1a030180940003580400b2a24009400032032018003060901c4240c80c0c042110f000090200d4429403001034000c1c001900d5134903940442d40c0019031a500681c00c0d20342040540700c218100310300c41ca024000c42c9420304511740860300101080d01541e09094012000955442c2e032031814001c4060348110110203d002d80d044402c204c803000005650030b6030015401000f08c0c820320030060300b80070014000c0780d8480c1d40380e190804448140284503c0f480c8041d040c0031020080c2e040c050700e00c440c02440d010100341800d020170034030000b0400c2450816820308210b9420700c0e108140101078000c0307400041d0140715a0000007001c030025001002c0041c09265440e1041d002c807003003101c2d032030302c03007c00680824950a80e0061a6110354010955030381818107584510303032241d480c18100800c0ba0303084040c56204042c2030040c00024800190494000c1c007180d112403032030a8010340443c81b40001e003030511008 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 275365962 1250 275364712 275364769
    0x70f1109040b06100e060a0504081204150c080c010914010f020c07030b25020d030b0f01090308030903040308031f06170105061b01090c06090504140402150c030d0e0606060306 77
    0x94480c6170f25103200800058448542e0f2200901035006481072940c0361082034070001d42000c0d240c08903411f03503e002c101030504442c2c0306c0d0151112000444100ca0701c100c02c00400401010030300c599101103105812800203190051384040c20746205542e05070107148100082c9010303a40002c0c5120459034031034042031b80f03070303660032081010440c00c40c3d410048044c0000d414414680c2c08103580c040f500356500e0400c042405202071180e008103c01050340400c030490020700c08110100040c41d8030100c02c10072640b405481c3d6a03524459001900e100c100301034460015100503105981150140c0308d14540160494000e131940503865406200d02030082c100045c1c0c04800c010a01462841d450f0110700a2000800364600f4840010b114401c450000310745e420b02050b81d1a10780502005402041d0026100391101d400700004040c4d4a1602040d00f40204105142800b003030002c1c14441e0361081c0300080608413181c0c524204017009010700c0c442c6200b0420132405548210b10341c10301c004416422015000e8 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 275367212 1250 275365962 275365967
    0x1031103120c0109031727031605010b0414040203030f13050a0b091206010803071407030b180d080c18010903081611030303010605071b0902070f1109040b0610 70
    0x1c00744188001240d0000d0045a101d00542110b8083d81c881e075200d40e8070b140f400161014502c01590390380a00a60506100c0c101d40c0303102942e0380c9180704c0e14181e80c034001034024100191180018100d400343d45035815058507140034800c00c0c200c480d007000030f007002e464150b00090b00ea109946032400c154401007241c40100c00c800031f50034007401019280d28072240d240c0790402c54980001d454a44151424a076a50042c50007140d00e90403511a04001d50038818a50713107032004080d03d1690801c040c4280314000000c644005c400074010141996503800e04421142100c3c14001c4801503074092280100c240113800c0050030880f8520307120382612104240e40764004841d1078455a00103402c50002081125034902c019a4021038a4130660f1070308601503c040a01d41c43e400244103902c04650240714640101d4600403202c5070040c4041c91040b42c90352644a51800c076007004d81d041d5401d80c083c2c113201c020403400e0504108205030483e08002285081e40e5541c4400400401031030240003d007085200090 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 275368462 1250 275367212 275367223
    0x60b07080d0e030f03190905060705070303020c030a030605030708030a08040209060420030709090b06030a0c200102190e0f0613050306090a0209010501050408030a0513080f0a02040c0306050901031103 88
    0x740b0310090301d554002a400130b0816800a40702c8000141403a030392a46641c08070711860084690010141c03c03282d80e101030644064105043c281c1c02c0c10380030080074611075800d1005000390a00c40d107000810500304000d06280501c2034008040c0360380100054501103400100144e0301c5a4100d582580325075039140031a028200301c048940c00034131142055450b01c0e07028005584111801d548481074a40c3d500b0021b4107654410002e90b411520030004070300c6202ca181c000c660140c205003400d99842202a8040c8102c1c1d0801000072620395000c205510010b480c00b08036100010907103020205c0355154400544145c0041000510812001512503641d42d00c2c02505002000001c003a40c0d41442c06034041a02c850b80c03040100d00c140444800401c2c5e540c010410384082c0c171781e40710055041542118081d10303035038444020300c1c3e00c110744610005041d0004002d400b65941c0c8034030292010b11502e10510054074940031052081c5410120144000d0301c40840d807904481e004940c0308070340c1c80e941c170110341442c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 275369712 1250 275368462 275368481
    0x5030f07090902041404030e121f0203060d120e03010f0b130f060f18050603030a0512151002100509030306010210020d02090d0b0108060a15090c09090e0106050a0801060b07080d 78
    0x1142c290104421f150b0444005030042c00c0c16500000751251380c1c08007984a0f40c5580b2840c00003988c003071a0424410b000e42c05582d1001018082036203015854490380400411107410030005944404d001c62941000e01540d09013500e210030a0000d034a040340082e80f00703080007030280601035882d1402141500d150b0001e4000f01101e454145140d920346010300c04d030300c0404030810890f9080101282c501c0c1400801c9800704c64056680d982003420480c490444044080c001960f03039111141d07020714941d215a10704405520701d40080132052042611001901c0b801071400545030414010440581d802043d51001c00d03918400040e5030701800341446000307004031030744a40c0002d140d24003201001808030040307041c2e49551040300c41c955142014202a10031201014840410b00035040140d0a900c0c1c0081a05c031042e800c05103603503903d60f0082411504001030700301c8203030b440303400400c26810203828503070280c1405002031049c1800c0051a407550701c9024002400800005100e42c19211a0790080868 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 275370962 1250 275369712 275369741
    0x14030708040b2802040f050a050d0f05030f031e0609060123040b07060903090801090c1a1b070504240b030c040b070609030305060103090c06080603190b070905030f0709090204 77
    0xc3d8001d16010300207410074007441219059107200810386103072052001044034402440e0b6006003015942d400d5075814040d0040351b00c1d200c28010b2108007a070583c00b65104001b000b030801079078800781001480000000e00064022001c08042c00a00d9030310500d080102100c480c0c2003020b260801440b031030b843c401c41d03102c11400d00f0b01103640010010300343c01641025000350350700303984140c5502005003241d40184d0028074246a551040003400c01071102c8003024950051800c0c1040111109420340c030304644801c02c0150811041400140740510560310090f06454462400a801400084840042d0300510104240c00320000b000d0881d0102240c01610384070380065203501041c41e200c0080c00c00b0074400c5012074105030005105510900c100d006035600a8403158040745000400e0340d103800040e00c140e4060156009840b00f030040d04244410701845503415440505c0c05c1034004001e480b254101c3c80c4242c108a440400c44040000d001e41030310003040c40055800031620000b00140141c58600d5030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 275372212 1250 275370962 275371021
    0xc0303151707051008150d06090206030f0a0c033312030512013213020f032202030604061e05040302010c020706050a051617160314030708040b 63
    0xc600004500c0b00c003103650555028034001c008100580d0a07079401c6034001100c60803901145c2003454905030020106001d80e000040d6000d0b40d40220310554011511440000280010b114240b20a4414160110b4051074100b20707085400709804414100e1466180301c1d00301c036000444119005446050050100408484143c1010302e806010b6401074820528001610000020000000e000220190b910040c0354002091070311206508507842c070380b50030340102070000c100100c0305641c401440a601086912a101e1403d556480e042d810180500702c8100104001c280058030300003807a0350880e0f4004404210740c8a003154041404c59680f000200c000d0501044c04141070b01944040c41110761603080d98003a039142ca50070399261043c90a0440010b00c02c0065407004a81584002072940c4103c515201302c07020884803880c01e800544420f60842460251542015000303050350301c00a480d4500682949094503010b081d40b00e00420149c00d0b40c001100040d1401d0141080d031410035014080c950 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 275373462 1250 275372212 275372249
    0x608011b030c030b010903030c0515070c060b1c0b190908040602010e0a0b0a0209010302190807021e03120c1303031d0d0503040911040b0a0507210c030315 68
    0xc45048821861010a241001c000b0201d44a40124110510180c40c0c03240d8a900d161b5048030402662070041d9824001c511070b000007031000b000e105008032503c0e41e030342ca0740618a0400c58115107114000502c0b940900c0c01c461a280024110140602d4204900325071503582e00319514000721891440028452601d4010b400700447c02e0702400c25540c180d8000c00025004060080e512900a4405070140c8450800103a041c5040e4005107010041890090700701710900064001030594104d508010034600b40811000035810032142a40d4403218082c041030340d650f500102d840b8881c194210314034400f15000540140e0101017140d0310400168183c0715440d0392802c008065000f40f0b201a2850405c00340d070100d5514111065501d5250450091854945445032060082041501d500030012051200203808110700001c0e018a0b203107038031020390300d80f84c52034424640c40b5001412000800c00d244c401041c66440350001c9102a4036050000348411914801018055941d0102101c04030549542 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 275374712 1250 275373462 275373491
    0x2280c0605070818150408180a09050f130f030c06021c0510080a2001020a02030d0f0f1704060b0a05060c0a051c020d050a03141305070b0a090b070204060801 69
    0x644103c6138202c0c004580e0a11044050302c5410320300d0a00c1542000300b0206010452500c0100080444a2100746070302114601041d5200c407664800d04005654404100501a100c1c440c0356105008041000340707903940d03070740700001c004007200c0103810011158215010001141d04680202d90741d10101d890707145414a055016204c01c40b40c6005004581800044801c1c000520507000c55008c03210180c0c54040107603c04110001002c06411031059a1a10015880c00d01600001240a03a64007503c1071800c01c01503c101140c2c64040108030402d4400d01c4110740c00350109801540c84100828094101c10004086682540019601600006504c450200300007010641c480c0706400707841c0c40c03400c40c0034103640502458000d0030258202c0f031300150381103111788000e02c0003400600300014110407904021a400c00c040f521000c1c4084003405c1001030220400010005241e02c0e200640303003407e01d0300001c0c07107209107108505a10502080070000c551303580e04418041e1034540001c1001c40e4060707200 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 275375962 1250 275374712 275374727
    0x905010e0709020a350f0f010609030c1401030615020c0f1206010b030c0f030709060210050103030504380a0801090c0c0f03050712110d020102280c060507 68
    0x2892580c401c01d60300045107400c50013075502514041e250b1004a01052120100313110b141054024110a0043e0401841209185043c09003007009200004c07490808004a146581a0820400c1c0004400100005111860100259a0311004035440122000016400790480780c0020101000d601e04121015074005520244440700b220b0290803201003005101d0300e00b1100140d8101c80e00824010700c10818407000540d004042c02003190328005100c130b002c0e0340342e41065844da00001ca444601300480c580c100316074540745546800070050b43d450740c0da018025120314880c0c0340c1216000120304841a14003070344441402103014402060390a8444000303140d44c050307903401010400010010071004620304c200410f01750035844410705821503860308400a0101403045003045801c20213400010040104222550055254040c1d003451400c440790600492014031030031a031061085c1860040150b10b54000c0c12400c5205a8099040d0700084411076035038040a040141040103214415030700040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 275377212 1250 275375962 275375981
    0xf2f010b0d020604050906032a18092d0303040b060405090715030504150e0705030c0f0108150102030c07080714040905061b04120f1b0e0a0f0609090501 67
    0x8004110031402040414109000040e4208200344410b1005003001c4000b580c0041c001030488540302c001e407072005900030340045040101440d196024696081c44000007403080c00d41c1c0d40d20a61031400c1c42c4141d130759a0600c010300010441d2041c1000c0265061441410301ca881d01c1c0c180da40d40c0c0f0307003824401000a000e5400d40e00036841e103030002d60903000202e40c44081e036103003da40001d64210440210054100540151050180e94045e01d014203031b17a21803000350382408006010360300e10780004c06003070180400d0028043c51606910001d541c0c2e01620b11540b0680d2604a1503814542c3c000407031540c01b80782280c01031403152003004036502100203043c0b4100d49a4000c82501841e00e44c3c18042641c101c0c21000307000e58002d0011a04011000c0c03011040181806419408c0c10341c0e0314915541c8030080300c82910101c0c05103000758213114001a80000011042c04100140c40c03a00d0352036108240010080c0c01e055603034002c202c5100c0c210380c000300300402c0742d40c20600c002030031814124007c00340e994 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 275378462 1250 275377212 275377307
    0x41e0320030712110d050d020f0c060f01060503090a1401020d15150201090809010c060e03270a0302010905010c0f06090b07031d030d0f060b0a170703020313030f 71
    0x2141c5981040c490b03113050048142290281c504543e2159095815410078001401c00315000c1c082311448200c14009440741000c11001464182404500c100c101641038001c841004403c000300881c8040000d010700c81c2543c4000f00400c0c00e29841203c600a0080699403501c042c2001341e41b0150010148250040d0707810446000c2410040310400d90803603d21610041221409005d002525800303041850308443c0514800700c0e5191003040701604541c4802c0304071f84903078690711610200c0191446100d40f21326094803162081c5045800280003920580310325030402c10b400d00a4010010b03617001e52824160302180034849150640381502e410102116000300081c41c00c0c0c00b013030300720008440740c041692005014620b490f98500340d1002030b0420880b1004440d031541d0000a40801010051241c4d961680c0c41c103419245111510079840c1c40500000101801070080c0182400700444105501d5458248040b00c0800c0315015100f42442809100030392002030581304142040c0040049200b2990 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 275379712 1250 275378462 275378483
    0xa050c03120109091a0f06010e03030702100f021e030409020306061b010b120c010c0b06040e0f060406110f03012306031602071e1701060f0602010b040605010305041e03200307 77
    0xf03d01501103800106d810750261a03c650102e42e995018515002d1100740190543e494014680c0204e940c080c003040c501c0d000203440410301503079070340d0502c01c00840780308034203107008580340c030162246e500e0082e8000c0d404c0c1c00b0380c0080820703801d903541c4003110250008009150203200c01c40d500c580c000c10104080b1401070441385511b802c091300103d000c40d40640140c441c924000b4040c0c07542d0740300c0c2c10000c000d0b41d00582d60b2080344103500c0b03041100b00c560100b44802481d4a241a1401700251440e20560342445c6505011030501041014140e90640300410200c1c00642d000d030700000041401d002900760080d20000600a200d400502d1210020140343c08440242da0340b0324040303403400040c480409000414042c1441440100d03008100f815024900200b500b54444140c4000900b1307a6000c03101507991214011000e0802e406000010102402d0420440c0382c582c441c000354911a283e040e00c65044a9241c00806005045145004e10140c1000b11000d01140b0601c0d0b50303038002103046c1c0c1ca510390b5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 275380962 1250 275379712 275379743
    0x1051c0c020109051b010210020c0a0b0405032214090c040b071a040803040204110a0906120b030d1106011e0504092423130b09012004030b060111030a050c0312010909 73
    0x7235000700c071180100030b0010201d800740360f02d80d907001042c040c0086506000c02c000c001d0400e04070143c0300c50b0074114440c0703d103407552912581c03410914420203000c0c0a16810350801000c0401e81041c0c4080b1018852140d544001a01d041a007c0c0203010803107600b0304e40f0006100034009410080c40c80703144240e03810840c5802641e061100b40c041e824240703001035040c910520a00b0700c14082038500c206105c0000c5032060f0100b00003400e090200c0340e154001240014800c0404004000e414010b01009011074104820a0482c50f468103076800b4090080e500d64441388100911104403a5000709041d01000340d01403500c00c1500540700e02e207880c031800d01d800c0001e407400b01e0f02c50800781c1c003919040030044d0f002d0311036039615007503440b00410000300da541e281d085a07110203501000d14480310a5400360b0b50f41c0e40c21880e00100b0140f01900207130410803403c0c0091503091001088481d00c450344e0400e651142503894030603140d44900b850200400f802d82000081c000386c1c0c4e400c981001b500c540485019802c8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 275382212 1250 275380962 275380993
    0xe0a0f060b09100903080a022d0d0f050c0105180c031c030b12030309060a1409060105060d0b1504030c0b0708030a050c0403050f0606030c01051c0c020109051b0102 72
    0x96004501c40c9034401c02082c00e40346024121003201c11400d0414410640da40d4071059003e402445a4801603000514030466040a40380d45001300350801c1c0781030804440c40640590303140c03c1c04801c042400301003040a526280603606690300c0b20f0307407030000f0300091900241162201d071905102e030b55a8454814415810f00c0c0100c0d010800700d0070780c541c04a08001180040780940030300388001e81c0040e01a85000b419003001d00046115600030002049035041440e042800c480c03803807a01408a000090a004965001145450440348112011030721064480c44100051680d00340c0035512a002745092400020710801500449000301c038410407860740e502682c5c0e0184100640107201480030000175640d2429584016040b249454010781015282e54a2915154540b43c41070a40d5214900300299841c00b00803d109007442880d146080201041c10f1710034145c040da08030039030070343c0350210200d2f880c0c070035841a181ea0341c1001c210351070205148052081c02d044100982d00602990a8141e070020 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 275383462 1250 275382212 275382221
    0x302030708030c060f1f060f0e04090302100b27010e0703020c120a0221030f0714072003030f040305010b1e0108100f08101d0703140c03010203010e0a0f 67
    0x20403107409404250b071800701310380c0c0182c001070800001030303c07070313410006c41a07614441c15000d00996116011074101a50015024542c480c0c1d15600c40d40c1815605070000b54003140c69900c41c0e181e03110200e05881424000b40014101c1814407054455002c8801d49410041803818101c60300204c80b01036644500d2800c906a10525030100704660041d049048002e0107140101070a00003841554020580000321121050070030394a0b0558076000320501c00032504520096402c0a07460414210200380c101d1035401c03038020070802402c0e4080c2c01d904000a924122101000700b000242920360b100d41410020f41590018001681c50b513107405240c0c000da04207540c07000f01c138103048101d86c516030303110400455403a240141101480040b51030002940558805481d0207002414061b0800ca1808488401140d01000c10346840381010210140313448408030341c1038107032038126440300d01084c2d4a040c81f6144c0002a8203903905984004000079580003002205805080030810910080c000c1840c51402c6e107 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 275384712 1250 275383462 275383477
    0xb062d0903060c030709080d05040302120607080106110c1f021005060f060f090a1502010e03030c1204030203040b0c0c120a120f0c0203010e030306010207051c0602070807050d0207030203070803 85
    0x15803000c1c1c00700f00d43c95180c0020f5640405c3d42c1c41e0000d400d0380c56071122410700842001d41c40120308049410700861611103007a21101d42540000c042c14a40500000d120301410702c00c00d03007480031010300c03241000024400262180b01c060b10500f0f00301c2c8e8010701007400804040c0524014010124200c1d1014100d0041c1801600c6c01440e554030300d0508410016190b1025441c60b4000d4000c10a500e2240c451a2210004211864880c842c120050320068207451034810722581c1a001001046130080ac1d100a07030744049004020312103941e480d850141d2841c405e03130700500365900000c245007401a0000074020a003281c10f840c5942448074499090ba42d40c01e200710b0041c07051009901080c0c03450300c01d418400b182c00031b5282c964041110390300424216001e40c403a5003000e801c000204400303540c04100b400b00802e4103541c80b10b4031307203101e8540007502e0324003c0e001007803581c0024040c01841200c1080d10320817030304103040e0b1b9001c080b0383c2c0f800b940c1e420306444200c0c0240284400010f203083c02105072242d8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 275385962 1250 275384712 275384719
    0x10110703050a0e1201140f180304030f0303090516080c010e090a0507140f0d0c0f05180a0f080a02121902220e0708060c041d06040b062d09 61
    0x81c10044442501c080c014a00307004d820035006101c2c1094140700340665800e007440a22000010708028410000780c8500400072000c0d40074881141d00b940400200b241c0031a9000100040c0b00807140c581200034202180380074003180306004115040b4004044480c00702e60407c0100d40060244c1c40c01560303034012150350b00754018010030006100300d1740c0c2d400140c4d01c05443d00e008900e524815002c00c10f580c0007031840031604030000c0743c11403000c1040d10070f1000e8219a810954050001082c0040151007610248401184050721140035a212060482c000d8424040303101072007519409200e40e2005d40174402d81c82020541049006d90350042840030980b043e868014001400603001d100c0003c1045860b5868110411600807009409200b590a0140840041c0406510300480340e0315282000c0c042c10712a250400013000501040000c0f81100d0b1044101d14110f9a190400100200304a0b040950464000512002c44800c2458901401d030400314480200542078901c403e250700503148450b40 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 275387212 1250 275385962 275385967
    0x20c0d0305030708090a06020406050a030501050406080a030c080c0a03050711010c0c0522050f0f07090617092422050705121606030b0a05120709150b0304051011070305 74
    0x60540c07044e5070555000103141c01b12842d890680d9109003ca91040c0d00c100c00168020400511003680340c0611801490200d8007481850f00b82010903441d900d491400800307009907036503004200320840d0103842d2030f40c5000040d10b000380010300300a80301741d02c0250121a50525120b802140d5800741c00361000542d002903981c000c89080100340007018550240f4911841a0a407040310848900d014951003201e41c500f2200c400d09001c0030100c01c0c080c000e41181c0034001c1103034040c880603078401c0200c00d0704124204d004400d520b0328090305080c44600300d00c0c50010fa01c0456041c40e4800c5001000b401004656980051000031490300c00d101c0315085002421504007042c20041890028050140c18a9040c20359101d201c414101541550060340070300d000c603885004104c0c06140079400e800007010103030740c02401645101c80701394691303003180921b0300313284d41e54081c03840f1226410b8241c202038600e00304500e42c1c038103113400e10035a0ba803010f81e807083d0450b04186481c0480b40d0190141d90300e050b030640b030b03090 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 275388462 1250 275387212 275387221
    0xd09030611090301181e1101050a0903080a020a050615061803031201090c020d1106060103150521100b0109120303140a02070b060307140906150a0906020c0d030503 72
    0x5807600080e04141c0380c4061040d151980d0b4280b081c00441100b40213100c80e5245146030240c03100b00c1d0020780300c41c0d10380f02002c0107005c5a07d81c29005003a1000b403802e90303a01e06260318141ca40790083e07000588004401305002c2c5c4519000a08100c401c0d000700100c803416a03410410803080801490400d800070b009000b900401152001ca09110220007000e81c0e0900c888168664080e01090740030303a5100c3c4d1281e0781818410707018001c00c9901d0096180100d040c00c0000300d107695030203004c0d0010741010340d078000c4119407100b60090000a408010301040520928005009038420101088082c50140c00c0c00031130706000e94801c807a000c070810b07150f8810003460a2500026562283e030240c09058450104c401c264100c00c1a09200e24440d0f5070050b02d900c0c40c0d003000c0d98003260043c040c600980c841b00b0148004008081c2d20040041c00701d60741103060780c440300464001c085961201450600100c1c050900c2508142c015007035540903801c803201c401224003003048800d070901d009408901e0800118 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 275389712 1250 275388462 275388473
    0x102031515071502040b0c16080c0f0d020d0203010c050d11030f040b070302070611040305161809080c011b0f0201061406030402010203130b0315030708030d0c090807120c080d0903 79
    0x203003e005001000500b07141e550a03640d543c982c000641c810f215080b45d0b00308482c5443d0084400090f10440c4002c007602c006900100c2d1001c3d051034400c500c14500740240004540c1c42000c4c842d03840747e02400a102c001064603000d091504041004204e203030810400705048103400d4140e901c1805032030800049915141c880c05900e000c040c0c4002e007016000c01001c0041000c5011358609002c80394059540c0b1441e605140741000390410303201c400f60960a50411400e0611907030384c041a215190002554101031501e4a2940f00e03c1181c078950f9401c0c40c500c808203001c00c4080396031a4000c0d88400504402512080f8204e400c6e0740140400c031400041c181c025410005c1c00307140d00500c10f004582c940f500140b4802c5200303c140e8406054800000f0401c03110414120310300e40140b00540c000c1c03a00c9802c0c00740c031640728058071103c9405c09986402c8a41014070442031500280303010010380c0d61241e1942d82d41203007001e192905590500030502d000590b0807000860a6100507941d6802c01001d0030b55540 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 275390962 1250 275389712 275389733
    0x60f080a12030e120c100b03031801030213030615062303040b041112061504090c0e0406090f06050402041a1011121201080c0a0e0103030c02060f0c010203151507 71
    0x280f8040c480d00c50107040c10500d040c0100099402c0b80d004040314603c01200710203540c1801c1e0b070301c1d0181c1c10900c4910005801c0c0d90031b00400c0f000c242000340c2c850f16585054006008554009810030b81015101d00901940715501e0090755074642d501e001c510290b0740f01603802130000710241d54629040000802080d0304000594002c1d109403510200d002c164000070f41c180c0340803840b90b9159000b01041c0906a28540764110341001c0036035040c8210480c83d1260343c41c0f940d00b4483d556189649100090402100d40c0c405004107600c18004d000041e10782c100000201000c4908034080e41c40c100c2c0200001e00e00d0040e0303110042000b400c400c9081d41104040f21104900450880b007440360b03140d6041040310560241440e071034107194602031503140c03420302c0d4981408922024051500b0344002d0100c0c192601003281540d070581440c209203e498408502107101c0c241d42c500050101040320140c0d81c3c0103400a6018240d0903020f8245a90306004102004208001c1da40c14400c0070000040098100e01a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 275392212 1250 275390962 275390981
    0xc1006030b0a0917090103060905070206180c011d0409020414160c0b060d030c0606090c09092c0f060103120e090f1504060302030105071e0302030601021011090301060603060f080a1203 81
    0x401003171041e6268021812b4510544418000d40c00140411480d284000f524034901d40d0150005e0800c041e0b1100043c0464807119066030000e590400031014584864006e1115564080d208102c2c480442d00d802ca8a03a00542e0151000e520020002d076003940b1584c1c01c044025008940c0c0e0209131509800c0003a030701d042e041d0440a10032066084000b18a0174814000200b081030004283c2203040c50004090071100e0308058001441d041234822101080100b82c002040d0302508001d4078501030050760b1a01000c0008181d26220303080011003040a0042c140f1b0900b0280e0f22880b560241400070040301140480d100820707006400001541040040c050540800c0c1c00b030320001e8113a032a40c01013401d488085481e40085070650091121055150794800c0c4c010442c3d240071429400d00d100002e4681c05621030343e96400f506d4403008050316800c401101c6268078020300030030940356520400340103000c40b84600c9078503507094000090810346c040b800b0380c10198802549105e0441d8110150300900c00600c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 275393462 1250 275392212 275392217
    0xc09010f020a060905010605040b2205071701080706080705160209130204022110030b010b030a02040b0d0516020d05030109050405190f050712020102030702150c1006030b0a09170901 80
    0x1800700441d074a48100d6044c0e0340644000b25100382000b0900082d00c0034050080c0c0154048800900d80f180c8420401e1202e8002c184081241e8032000f504071491000300c00090703910100d48000040702640012038804891403600c1c6c80e044c03555224420341f0076000c0e04008a401c90b06801100006240040c4c005178003038181800486181c00f6034000c902203030400ca62222119400302440580b4072800f03490507610540c1d20f1800e222150035550743c1002d0381c0c0c045c030074180300c090044007080040340160150b07005050743c59003407615101418481c001809043d28025032014010f554091068030110303da081e5160f154a8181c55030346006600f00062800034410b803040d018821042e480f46403005c5a4094141c090950040100c05c00d04110341890050740c010f00e520114803041e0001030740c012041d240c000ba0100ca80111400542000d420740d80718a07031841c400b40c01142c0c0f0802d6808a103034020740540e405040c0400c0c46130340c0c9090800c01c85581800203080c09019402c3c103011400fa1000138401e06c803061 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 275394712 1250 275393462 275393473
    0x403090b0a0e040501120f030e0a080d0306030218040f03030b040906050f1005062b0605030a030504031a10060302090117070c0302010f020301060903021201090b10030506060a0302060f0a03060803030109150e0c09010f02 96
    0xbc02c1040d047c0b80d180030007400007030b8480c0d1040065240114945000064a000960032400c141d0365016201240c240000c0078540c4030a030b809810350b81ea50080c22059008001444030b442c0c10844648181000c46a8001002e0f0380e08000c151802c015090b56501340805081d074194201d50700c1c0c100d280810109600d0b1003e9141d51002c0b03000c0d1014442070030610700c03a44481d511641149004216070880e0074030703144004009410064001e10301c01c6030400300c51107420010781d030f19092001220700030303003906c1d0300e85100e0401e0085c000c001703070301846922010b03010794020400c0107040100c0005030300c42846048001035140340f013031001d8a800403c880e00941c03401c0c0001155004c13941c0342d20019100311b5500000d039100c541c0070410710030103008181d4803c0341220344a16070360450780011300a0040c80c00d40500c207032020450300c0c880c502992041c4003410389403003126229a0b60706040406440764200b072044100f000310780020000d006010042c01403625032034041c1095040d00c011110007004e10070220840c85031 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 275395962 1250 275394712 275394719
    0x70e060c010204032409020603010b09060d060b0d180b06120a05060a0605010912020a0e0603031204200109080706120230060f01090e0403090b0a0e040501120f030e0a 73
    0x2d1000f000118890400d00420f403040348103119500c0c1840c5140316005040508040040c1e561008590544c0d1250a4140e158421040821214018848030a42c0d0919000010034030607088070244c00800c0028405100c455031201303002c01125030203a002032041400030046505864030348807540c0750702488012078001d080c0d645c03149450454180e40034209166a204240711a5a12802d45006094880304100310308145601281c02000c1e98403801d02d0f01c0307440f4804034902c4d90302401118a80e00c183d103c1030710103080504114005511040c184105004400184249540168498800c032220b0b8006840714030314140058800c4030400e4140c145056080000000001d00039600c220820388800d004940a084c02c0c002e0655034202078000c920401201c92031481c180e07441030900090754202e007500e10454031949020b8a4403c415040006004000f2540c0501a07030311040c6c102c041102241c0610541e40c0c3c64a0b640741d0350a283c0e42c054001120020404082030090054001e000005455a108141d9 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 275397212 1250 275395962 275395987
    0x203100c1107060c05060a111b030405030102130e130209011e0e161205160e0a0e19050c030106080c07020a0b0d060f081c12060f0b030601031d0303070e06 68
    0x15000400800c03080d01300182441001c1060991101c0140c1c404c2241c000c1800d1b490005028101d40c03005a4000d280034684001002d109440040402500964440864001001e148034150040600c7c024040000983d151400c81c060100e203600504a9200c507400e16014804950460f814510801c0c4000d100003014400b2226040c8100c80038000d100181e611183c0040c4401c40030302c9031302442c904107010710181944403250400d07018554104149418034180210311980e545074031881100b001c544c00c104481140c50036424910981c0b500800507503039103103901034030341c0005e004000c0001c5041c0b0001e004801c4080042004500081105107425995a851299540b11034054194642c98a50800c0501121041d5a01410901000d44000c04190660381c2c10a00080c1c0301804018080c4064000400180c0c0701d5000f808040110104d07240d100c5000311560340c000d484440c0042c0c80e18030484420603201001120075080c940c00340d0b01e140c8840c0703400c030786443c1224411031340500304221140320b695 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 275398462 1250 275397212 275397223
    0x81303080a050909070206071b061407020102071b030507030b0901290f03060c0307050a090b0a02010603120819111b07060e120d1b1b08190203100c11 66
    0x20480c2d65003e40d07540304401440410740c40508903000f95480320050040241d00201828001035500f500c50381c110180d41410005070034840706000d0041001c10501000c0e69043d00103009031805995078800c4040c0d2070811800e9441c02d440094465004100300f0f00000e08107116440d002a901c100100740d4aa0310301c041080b0150600c110200c1844014181705141040116001031f000220040c241c1850a25030135a43d5101c020000c1042060016a9481290240b00881c025007450345910391150b003000d030064000c028500060303c4040120f458a00110300c03c94041e0b11601401145116941c455009500509048641d0f200ca1450903c8916050801406840140303c20350340100907561614002038410035000111a0085001102c2d4800c90200040c440f010300f61245404c41c8000282407034500342120403e0002c0c000100000104052181040200240c2e01c80300c1c2a104070540c84581c000e074160784210002c1d01030b00401c0c0301240c504659445103800c48064101504105150000305042c0b0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 275399712 1250 275398462 275398477
    0x30a080709210308060406030b061c1403030613020406230409020f13090b0102060f0703140405010c120216020d0501060e04080403141515190609050405130b0408130308 74
    0x102c1c000600101455800b5003155004641070f1000c0281c40d0454940d410080c000501a40c01109045101c43d40c440b8440d40512030240c0000e1039003003c0042020054503940240d803964803441d01c0a42544400e540d034800c4400301d400360788800c040c490744440c44191440300103a0079000c900c41484001051203240c00101010004c8440d0596200c580c00c4a154008080350000301000f0b1030324243c003140f0798001800300d803c64010312080c62144c0e02e01408034090441d80702e0749a80741c1c21100a120070800c05400081070020261624100d5961540c50b8038102c0c0140c2c01e5035292551030001600250400441c40c0e42c15501070000415400c0c0c035440c050542c1041924101c80c1000002020004c1c090005145140300e80d0a1011704094054180500704902c4042d100d12007a400000880d0410b80e113400c200008044030f035074070749c210070341e40c0b40e01416041c2c00d441042c1c052070400d0001160f0318440031598003c1c0e40e200c0b0000220b5110b94803241d0f8260007107001521880080c48020020a0a600150608 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 275400962 1250 275399712 275399759
    0x19091214070f09360201050c070305100903080604140129070503070b0a02030114041a040e0c1c08180a170a0c09020c100b0607080c0a0c050a08030a080709 68
    0x510002d00d018410844c00c000e01d6100d60705540d0807000700140c25420465143c0e03024a001c40d2500c40100f80c0070b003441c0013a03000070154451015000402d0500d0f401001906010f600c0380c00307807070352080280019254407140705601440c0c0c1c0300041c0040d45850300114540001c0101c4803003680143d000e07120440d07200365001d41d0b181d880400c0da542000100100540c1c0308410001c10340c1103500d8805401c0040e98a200c149220300d441d012154094000b90351400c08041c0c0c014020300005661600443d02c5003030a5280900600d55030106200303c00340c16500c14007880c0c1c000613480c41c03c1c0ca88518030020b0014010383ea54000340068001400340814018885060044005000340201078a00102032908a910000000c2d00500c0f6290b04424045034007100c0e20000344020820303c14410001d101d522031b00000408041c0e020820350303140800013414000e124800c0075096015600c440800c001d5840030f1241d034003207038800c0180d00c0d20b4034072031f820803600310010342020094580ca400d21189508000c0458024 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 275402212 1250 275400962 275400971
    0x15020304031b090507021b060a1b0b0a050705040303051603090b030c03070905010801080c010806010521060f1507240f050703050601051801181a19091214070f09 71
    0xf1840c041c0c4901c07500800c0303e0008000d000d00446a051115281c19aa54400ca00c041000e4800781c0c011055810841e011500380079102d500c1d480c01540341e0f201071711b0f8109490b1a0100141407903020b0000c6400307494064840a0500c1400740340c00360b1490310541c0c104e041000740000000c11100401c0030318050703410441c02d0381c1c0742d00e0045c500800c3e580c4030f9449641001031200040007071200118035160030798000c0c40d01121564030703140162a00c0c800c0c410a000d070440f542c100c849011403034802c1c5a009510403904ca643da00300d003004101079100c000078810150700007044400c00140e40c540d10200c20715801e03648040032402e0110032004482640050034421503c9408004015525103d041d5000409007003081c02c0c084603602d0390906443c030f103890606201c2511b41f041c40c40211880702900401d00c600405070b81d101c4482c6c051110750042c10751405800c05500f002210a40174034909420f64140786281e40d007200568560f01c2c84200c141d4801c20440c040d59602203203501d902002100500044900400d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 275403462 1250 275402212 275402219
    0x1e0c04090606270f0b03100b03090706090b070209181f061409101824030512040b090108060103020705060906070e0312030c130b03010602010903031d0715020304031b 73
    0x1043c03800001007030000500380d010700b070040b407048a015000f034503e0303036501175226614043c04540c2818940c00003e503111020080201a2100040d100b060310b907d82d4a150203596a0320f488042c1c2e00a00a00035030001c062000250411098003001c000d80440d8412100005c0010702f6005010281002280d0915200d040c02d02241f841550100220304064502140d43e1915040b2000c119500e8020004850910480524085440e42140d90340021940104503074507130940c001c0a50181c50310040788c180c0299000030300c045000308141d4040b615018082403405010500448050400401c070a0516a00707000f44000315008100e004e2007900442d0040080c0d0401e500b01030031520003914a184264014010b45a6030b4450320700752900b10030030b0000d280d181c4c104801d07070000a6031a50070500722500088000102290705400142c3c0d10b80c0240c400704a034404001c800d142c108994048030760b6652120300b040201590302500c840154201e8410341342070503103a54079911284030034030000502d00c0003000e090 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 275404712 1250 275403462 275403497
    0x908040302040b0105033121020106050a1a0a1b050c0901140d11010e090403020304050a0b16020108061201020d0605040e0c0102120a120606120e061e0c04090606 71
    0xf190101090030814210301c1c0841600d40046003d2420070340c24840c0540004203034880a95141440354492108060b40010440c042c60302350110f07140000540c20440e00003071a0600c2e44402055072103205408800f000c40340c11042841d4030041d0804100503603144800f65089503c140e5201d06445131016000d2010b901c02002520075060b04030181d100003000e150703a01583d036910002c00c000c0c1c0c491240d070701c00780b6550010b0316074a02d60f1240c5da4110034007804000803d0f601100800a035001216400340c20380d05e42200b0407490007071403c124401c00349640b08602640c001c600341030b48488014071014101703512040709400da8000c0c40c854510292034841c14026441c050007001c5000c035540004140c4030020000003945c990790004c4044024100083e0750b01c000348110722000d41103450007000d001d80782d91244010718842c20041c0c0442014036017030038058401401301c0c0c0140107400c4880340c40c0b0045141c654a00da140000391075610b28130402c0200281d00c1050b4042c0d031005148e6030702c076a141e1031034000f141c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 275405962 1250 275404712 275404721
    0x11e081b04061d01090b070f0503090904030f0809030a090b03130804170c04020c2a190303020c0d0b06040f020c0a0515090309010c0809010309050a1101020f030301121212090804030204 81
    0x40c0f03818400d43c50002e12110414106070b540702900040f0f40722610403141005415889455211604030200200704014503800401c001481e1b0340c40c2e80c0d030306081c0e6982c0341859107034000e03849030741c0004960704402c1180c004c0c02400340d40c009050340d095800d0000386540301089a405075010141c0074083c40c60a200920051225142d1040144c50552604580081840e11501c481c080c510301d582c0740d0503400720600c0e40c0c0840442d6020b4003805030b040d250448046404e507c500e500c0105c0062003445240c150034245200c0c2c1340c200342e501140380c480f107480c4c1000b0080500b40945d0020101a42840b01d000a50b40801c41200924000d0303001c0e040c40b00c1c05030141c0c4551a4003c0001c0155401000f1031175090f40c0c001702042c1d406070050071003502d0754031200040300600b4030542d01900d40c1c45803c030701a007800103140303881350b07034542c02d03004c03074640e445c8510540b40c90303000c2403246800070807a0090800100314401e402d145169a2854001116180f50102c041110315070301081c0d40603400401c00f841142018800e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 275407212 1250 275405962 275406017
    0x32003010605030a02091e09031b01140609150a0e06101407261306030c0306030201200a080d020307030b0409051902030705030d020f0606011e081b0406 67
    0x24041d140c10080400d5071810080002400741200c10000b4030b4030000c00d5900c181d012801400600d160409001080d03484d0050194900c130704940b100340c2c1400d02014481c4030080f00c40c5500e00880c03035a4072400c006071501c00812245060090880d501c8056031075244840186c0f19008003003031241800810f10900c000d80903915414030140710725099904940000380d40c001c0c2e0b0f00890300c0e00d8145c44055011851030001900380c0c29010301080ca407000906c801c40070000e907605aa030420a81020060881c141c601c2844042c0c0401c1412030104003101c944200e80000b602450103c6154900c581e94552a507400a50030480740c903404014040c100740e0500841d0032802c0b041760b0600c11100641c0394036031030b80200424084104549030469046460a00004004020040680e50814036082003e5202c4c0d059521060080c001c01000505641c020801000c0034050341d000d40708510006da909440fa4030740500300d891422010030011080401400c000c10140040703079180c10011004607100c10207049580c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 275408462 1250 275407212 275407219
    0x1d07200a0c0b1c020f1b01050a0f1802010302030a0b1011060a0603120e030a05011a0a12030f0c0809031f0c1409060a11070906050a15051c150320 64
    0x4040030741d2290448016000403e000010780e034020301e04e4100810302c40c40140050007491980e00c800880019800984a01c0c40054280240042000040d08461981c03508550300c10650b0510fa01551181e40034590041c0f00c0f0100107261004072001808004402500e40002011002900c04840b0144401c0c2d412190311001442410b08550315101c16100c10355051080141084d011050fa5030304000407504160410b00030000c20382510b142c0601c285c0400c04560080c5201000054015412480d946206416a590180b44020300b18121080040c80030141d80c1c2400031b200c000120b99091150030621100e88214480300100c000c80c130001c2e00c0c1007891500c2071100103154401c900108000301e450901c412501981d8901e14210180c59528803800b10301e40b5441620008502501c03d64400300a0700c0b000c8030000b2407541d4414500101c005070040050000d030051081510294001030462181340802c10089403000b90b904800300e140c000d41d4400d49000782c0c14034611030f40c0c907511070203500c4000098 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 275409712 1250 275408462 275408467
    0x303020d18090507051b0c2b1211030c0105190207020a140a09020f030105030f0d090b0d020408010e06100602071a0d1401030312050609011d07200a0c0b 67
    0x6021000740011035201d04003070306031610001450980308208a5000c2068000780b480b2601501005540d25a400440e55001c1c07188190103016904520111400c8002c3c1e801c1003008504490340c40484400004e80b80600780b001c804807820744004144080c0130311405500c00000c051601110030f5071811a052a0000b1140c4100400e5005da03d450b12010181e03070b21525580d0040170000c0200b2040c5019600c40e00c0c0f2144041581d8100044100045040700e500324220390284410305010380d101c84514941d04041440e800c8104071040307819000e0401c00b02529401400c05507141c08450949103200c420458a03000b43c420449000324103410314025140030f1008117800e17402c09801d055040354210103240026004038260039407000c0e54000036100540c40e0884002035a503840c01506031001d4a1751001110704140005d002da01302450078030304880e10b403601030f00200c03411000400c48140c090700700303000c11802041c401d000005a00c1d81c221510b5000c4002e282c0d240150401000c2d14250317400110106004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 275410962 1250 275409712 275409737
    0x71202070803181603061409010e1506010302040306061202191a0309010626010c020d0f110a02062a070605070201050d0603052d0c03101e150303020d 66
    0x508003580e0748601649030701c1000104010a1610308050040608105028090040301b00081500f0500e00000b400e800254240c585251003801d032100c00c5184441c941c4602c00300544244030041580e00948181401481c3c592282c9802d0107a50b102e4016160b40041d400c2d94a0441c1400c03d80c03904001050113148444a080c1004c04c0d10f800b01040c03d411303041c0004808a00e0310082940110010075105d4405c0b41204400c1c1a40340340d6140326032101045500e003107002804180089030303a52550000d6500e00c115044100b505462811001d05584154494900b4030001030715050010034100c00d1003e0742180503508085540e0411070049071040e9a6040b5540030090513800500795060030780d09081c8580c5030800c4020490081490364006013661040399a074644c01c03540428290307075440c048880d071051811502c10159076407902466180d099400050748048008445d440714021110352001d83c820041c0d101c2c641ea081d1101040b2000100905910403c01c054040010460781e00f020304001c1c1c0007100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 275412212 1250 275410962 275410973
    0x12090a020109140f04090f021305100302010827030301150203130608091504080706050109140601030c030f020325021203130602070501020c07291806090a0e07120207 73
    0x82d4481c03000e900300206180c2c40107680b10040354030400001740041240c4110b5040c20f040d84126010140d00580038090711105d1100d403406074a1142c0313944000034a0741880d42e801115003140090406c40c4d0203044c0d00d8454803032003881c18171105504840c4002d50b21b135410a2800050000040b5515040d5402080340c4072400d00c0a88480003260358a003400002a592800d1007800c181061b403030449040b9030001044100048200030b400003034048c0e5000c1286a80b904109000c0301e8040a44041c02050140014002d61003504031140050721441c022510080c905072400517a0400c0c0c1c1d00c2080b40014165032240b5540d400e42100080606100401d0200010171006200f0300c07000d0045006200035005042c14000b66404035501181e0220085540b00b18503110152100004d00444c595460709030002c040108003020000070f43e0740700501241c0750421101b1404018a05007411903001380b401e021144a955804858000419001402d00914540102c009040c180c00e804584013481c410700025000c00d1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 275413462 1250 275412212 275412227
    0xf0f1e020a1b0501090b07022103090a02040b0102010e010e030712090b0301142d040605091605092e090b030103080d1e0509010905010b0f3607030212090a0201 70
    0x494400d101c000042d5410300c0d0740034004215025105039512401e0200c100c0d4000740c41090840440c071010840d00c1000712801d120304c402ea4031000680e0000a0071005031420381d00480a245050000058107110900403600b528085255200c003500081405c6081c041c40c00c0c60308191840c00c0c900508003d09019000312540018001c2c400540c03c5184840c501d43c56502421110b8125450b0a22800e0703591400c941c0382e24214854980600e0078000001061f0130010b030303118001c80c0303540f03064031014007030150850303554003c0c14015511480e1031f42c000c1000448800b0b03000480b10801c009841602005602800002240e030241ca070703070441000100041100b00054035580e910400000c41c4102038008002c05044900c0e00302d40440c0d1400c4248001e40c541544244a1180306400078041524010100508040c444540903009055580d0a059800300d0f140805802003261100119086011144c0c0790b01074422200329001c41c1d8001a98410020081c045540c020300c000010b00c400c10b09a0300007003201 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 275414712 1250 275413462 275413487
    0xd11100209150706060e010b09011803022b021c12181a0d05090102131e0515040312020604061407120513021305100609080a0f03030f0f1e020a 63
    0x14602041800070011941c1009005001c0380c000710011f03503140d03101100d03aa80308101d1030b0301041203501000f01415807080178008881c0c00030015071030b60241c040e100c3d0710241c210b146e5555000c00c8d541c1640050381d0300440003906500741920084940000d00e080f60102c90300c621740000788211030712041184032400020314103a61100038400403c8000000000c01401840c40c0d01e202c040c00c144c20001c2e4503505501a19050f01e4613500555035660301c40045009400784001469800c3e59140244842e003482040c03482220401d000c0385291a07a03c1d12003d42500c8648118170048c1c00890511051000074010044c40104207004070001d810300c0800031706590300916400400c17039182c10001d49140101c0302c5902c10140c0103050507601e0b50070440e08000600045400040b4240e0000003c1510f91154176008150346040c5d0042240c4402601c8050300050341000c21010542c4071510303544903403c50302800030000340c180f6000c6596141d443c802400c000c4101300319805c59105005d907103d100d0b0b001c00d158041 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 275415962 1250 275414712 275414749
    0xf2a02040e03270103181b0f050109050607021f0806030d170a05060a050a060c0512030105030a060f09080403080c0c010203090109030311030d1401210210031503050d11100209 77
    0x711031943c0e00580c0508040704030350400c01d4048500c0b40a11210214003a02a040c0208580880ea01c07054038030340c2085540074081c00548201c00600072410305000810f81d0741e0009124100600c1322141490030078112030f0f00d034000548140c1c03d100c1241020058014180c2c0181800e10303120409440d002c48403030703000b001100c0e0310762101c0c080742081d1902c1d41c00c07001804001d0194894161213032000f60084061900803a01481407101080c2080c819006490685800030f0140c10000d0940d2552006440e55840c110f00c0203965441709030004002c80c3c0284019031203000c1da02d03191442900c0840c20300c0440c1c0d0744581950410410300e0101c0e0b80c44a0b1038000d599160810001d10301140c0c0c24103245014200b046070026148c0450f0800300440d500002c0d040b00e00c46002c001e421610340314110005c80c9141c030001d4229184440d100a03c0c1d00940110f00c0302d01210083c10040f55480d2511807400001d808400046280310f0300300c0c00c0210062106a0005415500640c07615003000d01240b4000a802c03a44800c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 275417212 1250 275415962 275416027
    0x30601120b04090b090a0309080705090414070909060c0e0405100b0c010b0d030915110601360605040605060906040501050a120f060e0108010e0d0f2a02040e03 70
    0xb0703a51a030008107030580103c10501d10307181480e41c541e6204100311095011848125000a00802c0001c06105490000d04001c501345c40c1c0350744600c005035014214110714000d80102007002c00c0c0301d1280c220614000e110100d100410441d01501c803100c090240b50050f03041804010707014111800c50011240410043c030340d02c4030303064042801404041030342980508000044414954850240020384203110008020300c1048041940c006900d0b100c64109a0400b0300100803007001e291000c50b211440303888216030740301012491039903e07920210f00d4041603500e260070301582c2020700c1030078054402510880c1c030300b00c2f801000402c47e0159101d041e041150010701000322511601c01c4d4040c10000d1502481035941842c1458040c101500814451f0700420000080000050107159507103200703030010303040000c0c044604070b0303a402008014030b040c00400b80e551755440c00b03800c8c0014001c0103a405403440c0b9003c0ea10402c42170300c4081e01c203800580d1040c0216880041a150010000d1454a25046 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 275418462 1250 275417212 275417231
    0x1a10030e0c1e061201031e030e061b030c100f02180906040b090f07080604020a0c0611040807030804080118020102100504110a06082502251a0712030203060112 70
    0x110040b21024140d04580302151011034082080131942c103980c4a041a201d44d80450742c0e0011508981c5074010f0001031008000c5101d078100709004012041d0265914500c211002c000c56103540c0c0000c2c05213a4982c0480c901d0700c400d200c81e1086800c0c031700c98401e05501e0b107111102807100c0040d08401301481508a03802241c0c8541e140e500c05828514090190f4940d13103816000d052030880700710b9840b404940d001c80015084c0c5094421255004003071f4890114440c0151203010041041c01c0c003030895084200004148050100001c03070040d8429050300355118140b20358a400d442c6500840340543c65466955030042c0e801061125600e41040b0001420383d54505065824500c0780c0012a041f8022002c042841913010855a1189003902503080149000000d00d07070782d920036024400010303005583c035801020051401c2d0002c0f14000c0c0100701c480d644903540e02403c0d8441070b8280781d00724800540c80d82040244e5145000c800c0b600e017411400c501c1c14400291000070908031071444241d0310b20445 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 275419712 1250 275418462 275418499
    0xb0a090e100e0a121b060b150d0914030a050418020409020d020409150e2d09150f040305040b07050102070c0f050f0301020903100e0a061a10030e0c 65
    0x110709001c5001c002d00180c1407158440b0345800c0d80d54802d40c1d01d8550707003013001403a50289626004801c040151504100080d860750300040c0f0036500002d0b400710b49443e0540c4004150000b41040781644900014218564602044c281071040c0303c8500341e820922690164503001020751701214041e054400c07405161006c4d24009100d00e400c1074040c03d101161002e207055450707028106403216440204444110b400c05c0c03103002046841680c815080480005440000c0c0300d0520420395803507011311030703c0003e1032030031804c1000456603584180d000c1b5261083d501d50a4411079000200d10b0140101414a6280140795116502400e00c92450006155080003c01d41c100c80440780c008078541c0e80c2d9500c40e1601308203103003180704d007521a50311180381e2815490188216003c6200040040842c04121412140034002e210708805940c0552008040880c07001d00800144541e04c0c2000f41300b000e0000b0030001c0c0e0a80360b0f18500d003058030384005c0807090f10001403c035007510411541300c2e00d15190070151 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 275420962 1250 275419712 275419723
    0x40803040f05071701054c03020a2315040303030c090e0a0b030c030f03031303110a03030905010507030c2f160801060b030402100809030702041119030b0a090e 70
    0x540c010400b0962003102c80b034040d03100500401c017031f8410030108441c029100010701e1011000070502d0415140c0750b240310141002a001090b140e03544109034036541e40019090500300c0e400a101108141d044481450f5840340407050141300b140d0140b0b88244d00319050449014a0000805050303886807501403042c05161400e004108040c005a0030380740136000340d400360041040c1240280305a0303110061902d03020507190000c0290300021402c40d81e80c2d5546000104c5401000e400f800340d052101102c00c07009210040a80313020361802309000000f45800340c21a0402040030b07042610f041d0100d040079600003040350103903d594070355842d18005034018460406402c40301015a220340c2c0c1d01c80c540e1145074041d000882e280103000b005059503d02486050b40f00486000750300025401d1042845030203200300c41d8101940e00300312420306c0710550101c5c0841c2c00083c8804c0c044000824080314040300d81c1e0032180c411426144c280040c101003000b04080a540b030107125601526520701c011808010070a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 275422212 1250 275420962 275420969
    0x15180b10030b090a050706080601021209061614210307111501060908060c0f04211a0a1506021b13090308061305070503011502010e060c041508040803040f0507 70
    0x290000e42d400c02088040d5500a040d50480d15030140c0b40380001c032a40030b0360041e407103040c041e000f400c41500406520b400303030b85c859650035600000502401d40000040c1414582c258403a8406080d0355422003c8949010004810000c004004141c90880c40140301c013603a401440c1c604008110321009140320781420500000c8000040b0350a0001800b2a8407040c1c6200f02c9242e08140c92050f120704004c0d041c1c611400031001d0562070100010001403c40c454805a1410354a440c1d171804005947ca15201d049500b481d060356180c45014049401400c1c03181003a020b40c90328011158070714200c0040d4517180518089060724840708842c0c03180d600c42c4401080c904402c202c04000c200c03210300d0f019109003400e0b10310a016496000d102e1031590700902c51140110402d0719151300310780c07921001c3c002d91160111711138115501c1794142041d0b51170030025180030382c040c1400700351214104500e01c41440c1c2400c0d01003042107140c0041c000441c00c0001141d07086500242c0400c540300090034420316180c800c0c3d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 275423462 1250 275422212 275422223
    0x160609030c0b041112030f09090c04091b11030a020a060b04020f0d021206030601140603070c05030d0c030c1d0405090a05060106080a0b1002060a2c0a15180b1003 71
    0x420001000700510141010130022240b4807150003803210031559a0081c5c011000098200708101c000c5460400d40c2154049000900c640c500b50301c481d240f4040d50301c42070300c04500c03960b8500c100324072941103081a0a106517800056081c40355004000b561120b40c0c04025082070790341c815281e00c0d031322075804854101504012a03903603454800007000084d4003c10000303c0030045000800d010345808035900d8126008982132a40b07602503078040080303c2c0c0c005402041806850402000060420701c0500003198007410001000c0d0040710000c2c0c2641c1c203240441c410070225506161080c00b8101e144024410142d070300207081e0b03980303003011880c1c80c4100d400900603105440001400c2503100a2084c0704806000c801d0020091810030f01c032054810290ba02d0160b000704000401c41c590a501205002c01c4240540c440444564001a08110a0302c0c08524580110307040c10b0510201041500032518448801c00c4000c140c0500c40915241000000f0021340c2d41a0104108070070030108072010350b4004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 275424712 1250 275423462 275423483
    0x80a0c020f030708040305010507030b06033615060405160e03070b03190f0216030e1807050a2606060c01022a010e0705061c1803020120160609030c 65
    0x60425913500c1d0000d00c02100c440d0f007054002544e5520038090400001c50290040b41141c0b9400104103441947d06540b083c448903010101e06880541d40100d134490051101030400401d555075202c042c58401800140681d04140510085103204084070780c0c060f19a1410b05442481c2d1400241084501c0d8040c0604800200610a0082004800e295a480111700c06c03c000110071207400e06078020b8004141c00d000240d0311940c00702c0c1c06851500c040d41402814460886280513200c0013254060b41c1720300c00510040740d0602c02c03942203058160890b80c0280003402100c02e1941250403031000401d218001c56001c2241c2200e2402501901d9240801007440c29220581640e101d6107194040e035000015030802c0e6403404900e402041d04820740d00007504044c40c1c0071542560300c4202c044240b4900c18190758440c5000b064010440011117144240e0011500d000804c0e910a5019054551852459070401400e01e1050407020340c910310680c04500801c52584a090590703a880500700301803c0510315 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 275425962 1250 275424712 275424727
    0x31501142710090612090f020906060c06010312020f06090601050d1b060804020f0103021303030810090905060703201234030606020a030c0206030402040207142b080a0c020f03 77
    0x4200740a044c0c0b02566201c0150003103407038404066480450014041c0201701503004090300f411107a5a034800703000741030300e8503100308034580030716104091b8410303076a14484c000d4080b0343d0307581400445030810b118401040c15042419125455610600c14140704d64407141d4500208107002195641c1c84100c80a121103e544c1d07101d02030302031401150100e1141d0fa0f0348032100310941c028404d9481005000e12002c42c0607040d6030701a20614006880918080c10350b84000401c0c284600501004074801c401030002420702c9000a002c1d5040001d002e20b4000b1103850b44910108007600381c6540f14000c81c030000701600e0b0882c001152400b881005000c0480b080790044c8a25461381a0407003016407aa010010340b5070300c80c4101c3e00c0d0f064901d00200020020032115001d85404000386801c180020001441c001c110342e140d1040744943d101c040220b070440082c1109114241019060642211690040c00740c2c8281005025420050502880555900c05800014420450244903c0b4144122550b9054 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 275427212 1250 275425962 275425967
    0x4021807031e1109130b0613030c05030703020d0f03030b0a1203080f010f050402070809030d090821030c03090109020a0602030c0c0d0c0302060a0e0d0602031501142710 74
    0x240b0003001c6042d0300d80015110b0b04850748240410040c3c24246542000559002c108001e4500740002d403030252a15441e07036003a9106801400d200481810b140d40c0302c1d2643c42c0811140c0d60702d80c04a4420f8221010410168480c2c81c181e044c0f003903000904900780c6aa41c03a0507802403862054031604000302101c0800c1c000c2a0004608090340280c45846a90f40d0b108101c08000e1801d0244612102100c1c60400c640e05241c5c0260510b148a10307441c41c1400040700203e07152254100d0b1b07000c00900300345020460f01e20305004100140720100301f801540c5c0c2d815200251280700142c0b100702d20140000006000d10000e500c002c0449a0041c241034240d907803540000d50380d403c2815000f585009400780c2c00194603004540700c2c0425441800400061f01c1c1d03408108180d04010004014480c07a042016281d40d03a080b902d08400b803050400584a00b0101000c0c801c68007000030319030501040c444200780f500d0600c41510300c0a05d058181d044910b8500300d41c5100f596000d40310070b03000605007524401381078 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 275428462 1250 275427212 275427221
    0x50705030405010b030106150f03020d020a0c031d010806010c02060c060901150602060402030616200102070308010605120a050a09021309020405090a150507210b01080714030a050402180703 83
    0x1e00950013841090303030402c101405c9070007a200c0c425650030f000d07203e40310b0b003802248000c4082085040040c2090301c03181000090ba400104074400264205503228200f42d00000d12a900d0101c81c40305026600c030280028144400c00703081c3c60b042c081203900c1c00c41159559411551140c082006541d07041c180000c5240c0a4100080150a40345c10f80300d002c50010300c00a07059210300e80040c010052034580101200450740307855003160030040509454090500b081c0310203808040410300050740e96242d410300418140341a005a410401d042205a64180d01c01220641000f03094100040946a81c08020010101c4ac000250480441890240d04c0501944a0341569000303480c18001ca40d120340c5000d440d0500102d00400301000c16070002c13451019907200030350029090801c0101c13645810b00e03c440b07011030b0490002255407a085241c01ca942d0029840e9002059814100d41201c40400000e040c1e0000800d40c01c0445d0752040000c05660341d2007503170140c0009070340400c01c41c0e00341010f0080151 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 275429712 1250 275428462 275428471
    0x405040f0c0e0316030b13200102070f180e010f180203060a060303120209011704210e030703080c0102160b0a0e0a020108070c0c030c14030f030a05042705070503 71
    0x10382c1c0440b0070360041c100803402da101c0c500c20145500c40241580e990302c08001000d060001615a20f8010700000750800d404c1515102c2014105580182c15800080c0f40c20340c0c0d40c119600c10700c4040000c00c140440c414055141443d2860082508002e10030b8903070051100814000c89a400c200b1000300402c64503a0020080d4026010348078160b84298140c3c041d05c14511008001604020302c0031005070240d8050320f010320051501c96400c1d4000041c200c120030058a0035142c0d4660906244e00392644100c081c1e02c0c0a1060401601d410003540000e61180300c0346c0b2024101c04000113880080041c00c0d811140310070341d2240c0303485640d407450400c5820314004030b5076444120b00e08446032904060020b4400481a0f05a4070004659162003044544000460301101c00c01e03075004001c800901e8402d6002c010f003c2c00c6403100000c40c24103041624041c21b190940ba11500b00304a81142d03079074850100c07800d60b40081e9a4103042014a101654200120400007801c90326040070301c0000c503401001103009 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 275430962 1250 275429712 275429717
    0xf020f18071808030a02070608090111030412030513080d020c01021c06030c0905010315020d020d240608250507120503011a090f01030c0c080403050105041202070305030f09060405040f0c 82
    0x8180d01e0310240380e41e1703206251095026034400700c01080784522032410a60310101c00d10004ca117900d4000c1c03802010380c1082c0c03004c44049a96040c005070740ca501d07200e0640e102009841441c41d26049446403c420306c01c4103d4400040d80014000f10503500035012a410316024500e04c40941614810380d10040c000f5010440716081c802400080d2041640039140c140c0740c00608116059159420440096100300403c03000740703809000341c0300349200c9446a0395486803210210500c060640204401060851300000305000b00002400304856aa40644003810810040340002016440c0260341c0303800791540041180c108514090551036002010394104e44604010b242c02604090f003409041c000d4103107032038001c50216061802c0350b201c2d0b04019003a003110700344004001810340320b03222180d0040d0800d0310240c0d1280e0606c410491034180d950110b40b014405040b0603411942c0e40d40d03ca2042585a007070704803010a0b8212141c0e00c0d14200c50046c000244104660f00318250006c1c041c0007152000d00c017 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 275432212 1250 275430962 275431007
    0x60806010e060909060c03270312060a0605210a1103011d010506090102150c1b0a15020a0f11030d022101080f070302090a06031202030403120c0f020f1807 68
    0x10310140012001d0081d061b04076158110340c0e032001703c1d006660f1040b404001800c001d10107011558020b00003040d145042c885509074601d40f44080c094546247d1380040c041140400c01b40c0800c024800025560b8000700000d03d2450b1034005c6840050f1402110302110368000000024803000b00701040f101c3c860301d954404c2902e0b0703600d0b0200b041d00e020f55548240035810401000030707030125a440e402e07403080c09400611300f00204024001414012004845019030003051124148200d07000300d40449000c991082d45400d9501000512000c039041e0502c007400101030014403003910600c16a014083c04003003c54540c11400f40800c000c20070f004410850038003000c00402d80c06408200d4404080480d001442e025103035500b4030024801c0100300c040b04075991100070001030781d004840400b0f140341b90f008644560440c20311454a00780030702d1601c24021240003802c00100b18014540c80103030101c920311817203070002c07000c42c120b424001c004143e0300e01003000304224950002580e029040040a0805 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 275433462 1250 275432212 275432221
    0x15030b01020d0c080310090c0c03021506151c140103020f030f120d060b0c1507080108060a0207050c09040308010f0603141303050c100c1202090108071101060806010e0609 75
    0x242c8441c503100c10000060b840920040104842030000c61300031940c49481c5414541d00d880580450786c6910042c03001036010341d0341100b030540c10050419601445403400d40305041030350014080c6003da00303030441032001c01b142c481d401e0042040107004000c9441d100703000944490041d803403240e809000c101c1c807440e03613504c4409107400d00059611030040c940d001040000640c48810303070603412850804101540321100820300148c1d03500074005503540440180035074108071800148916008240f84104420303d4010880c001f40020780d550000000180183d40310510b04181e0300700104c185080b90880d0341c402c2880200356100241c00c0c100c8014880c04040c0585074a0102c098880803200031254940e80c030082100c070420700301106807251107401c040b07240000e0b9100081c10300c00e604601e03911290391401c3d10720f803440c0c2003240008086480c41c0114500900200081e0001c94040c0501c0200b1408500c100030f0300318254066000340600c1801c56600e03680d0346102800c851012913009014950200101c2c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 275434712 1250 275433462 275433467
    0x30915020319050c0a020a09140106020607021c05090913020a090c02150606090a0f05040f021623150a0c0804030c03050702011206080a030306141c0206040305030415030b01 76
    0x20350b640c03155680003040302481900c0480d01900034070000e00c854001d8080c1200141d03286030343c41000b000f00410102d030a0303032240240018550168420001d6401c20401c00c000c0c2a030206841c50810314414100c581e0310f14201040300c9602640751000e420800c6034007031000a00e110799020080c58800ca4881b002c8a40300d606190650b01480e020f440580e0202a8992000e80482c0c401c5134440d00241a490912600c030307000a2281405034049010180d5959041c015410240910f500b8032403885000d5203042c01044038600c071034804610103410701e03d642b014142202000041d92aa5070b00d1081260298004841511070f403020030346518021503d440c0c01490100d0041e2100b0b441582c15403105200000c113520280d80550040f0800c0f0704100b202025040c0000f241d1042101030403a9400411000e407007490041d0489078142c0008195104003c00000d0035592887c101d05103515288211242c1d03016807012810601860300001e00c1c0380404500418a811080c0f004d041e0721210355028803810700040d005 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 275435962 1250 275434712 275434717
    0x102040b1606142e0b0d0b0a0f320918010b090f0103020108180c010c02030304080105010306090b0c040302032a04110d060b1602040c1b0309150203 65
    0x24803800c46030038800e081d1014680c0c41020051406040c020542581051003116482421551540d0504d21152503116002840c8140c41c0e00142c0076000c41211400c00e017205556008040100340c00e662203000020594a4880c1000e0040001162200c00280c03140c018000f002c03a803001c4903803580c2da1039070040030b83e03403504a180501300b2000e010700400d6200c0040b031403d266040300500429640702d1298014585070003100c18808c18a1107280c0c0255411403000500414002c1c1c04c4040f42000d262a9044103000444c0401401800b401c0405e072900c058804a0b0540c0181d510180704c5506c2c0c540004240300a90304001403192040c3c0c280416692581c025841500a41c080039416500c40a28035001c00c01400500c40c078050031055503004002c034000001d040d03400700000c4803003040c1c000c110b8400c95030060240101402d0003210b040e040011442a4907241e8524581c041e116a80700d980c9e0301c09140c010810004001d56103211202c10f02d40c036040181622980d40f1035000500309410441060314804410f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 275437212 1250 275435962 275435969
    0x60507121104090902060f1204021003020c100506030f0f0102090907020f12160f06060302100e030604110604080706090503071203080402010324120b07080405060714040b030a140702010204 83
    0x40241028200003d2400501c0c24400881c0c0104080042c090000e1411020303040c01e001200d007513002450503105100030b002010351494241030040c8070b01c1d20075100200d00c5e0400100300c610300041030381d03c0d1800207281a1f61190b1850441c004c038040030031351a07419002000702000945142c81c19031103040040ba0788101580f0007510350b40141024509802c0032070000c003842c5004100c240b050316583d4868580700400e1601c1140c0780c540d40c0340d0804c1103003000381d94404808801e00b400001c62079803d0100c6d8a03850010001402100c5ca6000c0000799a101e006a50207000300b80700712031046488560140140105001d0180b0a210710000000c00300c1da010003200300c42d58180c0c0d803182c0c203850b82c2d070040d8041c0407001407a500348018030b44d0015242c110190580020f150180e8140c0103c075450a00361220100070300b005003003009040070040494000107443d1b400c644545400c80d003025a412002c00c1c1405150044054140300005200d01c50f2242c2e04003038810080c0c07070700e100042e4886003c1a8202d21a43c0b0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 275438462 1250 275437212 275437241
    0xd022d03040b0a060302040e0a0309050a0b070b061207030321020307051b011b0c0b0c0f030f0403090909140d020705030d030b010504080a0c1517060909150406050712 73
    0x78001440b107181c1c65040b802c45040810590385960020b026110440c0c0d0108043d403024140209150340449800000c150554035500c0b05810702040740c14521982101510200922020070a03a0301c50506a4800c0314050050300d1803c1d440c0d141c000e1400340b5915003a410111001c060140c0000688212402030440b900c0e618517020700c0d0083d41407248440c0413181015580e80100d1184003001580300482908160346540384444c1601c0c20030303a000b502900c011a036107c14020b800d120100e0300c040300c1d00050300c0d964a02c084d0b507444c6012501c42c07481d03412100030541405600c600308042d1030701400000681c10b0941d80a003140000c201d81d01c1609100e030590541c4000f03051080c041c060760200040e4070061404618094403950407a1034041924801c0710b01402d590000c006956581c004840000074a2030140340300460a09584c3c9154802f0b00380510444101010480784c1034108030b42c0c1c0048000103e0007400c0d1030941031140062800300d400724003040c01c00308941140001c91007803600781007226 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 275439712 1250 275438462 275438467
    0x9062a05120601050702040c05090114070209010605071502070b06010e010c0b010b0928031403030c34030e0109050a0e04081b0303091b04023a020d022d 67
    0x11070580150080d1500c2c2c14000c0402411025890b5401420140007554449a55401a2200040409280358080c0403032030002d002c4840180d850032849030440e290741c03900949905050900d04100008400008003041c0f00007065001c120040d041d15116041c2601c42d0101003c1700d2006440746500d8840041c5441c044a0050012592902c060000701741c0280c00182443c14071008450201c0c0c0d550540c0e0810110108104200440900031600b01482440a50b003541000300300a4aa402128440764942c0b958030115110000c1c01021000703041c0b46d441d805064601d250a024102007882c10800d4001fa40c010b101044034200b09903c48210b690516401d0500d135216101c6200d1034100d04903210b080182411291100c0c035040001d54011044107000e03002e9207480070960307081c02500c03400c585d008a005110005040c880000c009101a0103004004450521550081100d41e080703120812003501c04500c441b084800c1e0750182c0642081451030001001940300490804031290144d0030700038108 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 275440962 1250 275439712 275439727
    0xb0601080c030f04120212070506180a150e0a080d050a050603030309030f1803060c03010603050f061e0310061e080c10050a0c05070e2208090103090f0609062a05 71
    0xb5a0b00724240c103040c2c2c030595407e42c21500014041c2e6000b02010780b000c1c1c0c8000103000c400f4807850540602e45820000402404400d9038914001c0950691a01d01c401e85d910070500c2031080a01c032600c14154001c18103680e42c44101e203c540103120030340390120303554688400241c00b4100041101c0c01b44801c07200a50904c1d41410044038583c0c0702150401d20701e0840c8082c5035072514104115409911500c1003d6160f42c1001030090480d203009110f00d05100b60b4005000807a121a158417000700ca503c0f01c0100c0c00c00000b40807034903005000c4a40210a40b0741600098402080c1c41030300107181d0300c0d06d0190034482e5114174640c0d58440302005150722500102d8400d050500031401482506030a0900c0001c2c65000e0b11150704203090b41c1d2120b0009114041042130700a401004c60061031401c07a425498149c40d074071200b500d4010002911305055590368082c0c1032200b42e00202034195442b440600400110b031410708080c1001c2d142c00e80d25041c0c04001164640002c040442049903655560b6003070194 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 275442212 1250 275440962 275440973
    0x90507020f0309061305130509060a0524010c120906021608060105010c05160303030221160302031e090f240a09060b0612010f0621020309010e07030b0601080c030f04 73
    0x6803204171807214000500103100d485100030780c010941390210004c1d06282c1002a0707420144006d004d407406a107018104031007406440080b44040c0c0c034005554640050b130000690b64810080001f502c5800519441d42c0801d500c06038281c07d0303d207507909484810425808000d10382c000e42c01803803401c1c0c100100611540d4420307a82d401c0598010700c1110058045000d82d440300c0d169a4006600007078000a040c2c409075501d40304000040030041c49040280751118220052412500c0d19208241c1c00101280c803048440e443c0c065224200c02c003d009a0408600c901e035595003c0d250180180151001c04075490500c5002c070840c0300c10020101d002c0c0e0345480c0c01d80c00910101c10115039403903840304803107015143c12001c4c08100503582d0051029504210113050380b01c00d10741c0000104400300c02000b10500d0780040c980a80391889001580702d40310501b40f01d01601682400420900c22a107000003889020070b4028002c100c2030b00d07002c0841d19030f14260b146910003100d00726004445600800e0020f40d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 275443462 1250 275442212 275442217
    0x80f06041107030207050a1a07060b1908070509070e09180a0c180608190615240e01081006050703020114150a0504231506070606090507020f030906 65
    0x1001040040d00581e51140000141c01c582019001640a01c806224900b0000361070409090701c10640030700b20b880c40e03203d04d40610232000c0082c50b40391646684111512200c00c4101c61806085002e80780755160460355590703a080748540c45c8030713101071004100001d000f8005640c907441c2c040c3c1400000d0765420072080e80103c5050f4910458800d00c11b4000118149403c6003010346121a210030202c2030b507104840540d2450381108800b034000c2d1032003848481d8185409800e5507880100401d43c04803c1b032204d019405a607028282d40b00144100500900000e9208042c0414a807503030b500107111540111800d44046405000c5030600341024408039000b08041c107100b510920000c106181c80c00c0e090003d2010650b8510310b18800316101c100b851500b004060007070300c0c041d2402c0001d565180400c007124a0752103a800030702c06078070700402c9145064881604e546003002c3c0c00f0359030700e1290f850464028142032040f07038407551914006c01c0c540d03440480e10500010a00c0011410000c8000c2000241d6 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 275444712 1250 275443462 275443471
    0x201050a0c0f050a090b0d0218010f02101a10030534110f0d050d06210803190509060105040e0303070f0e0406170c090606040812090d14010515040c080f 67
    0x80005da80005128a0400040192808060002d40c40d040b44001799032400030480e546505100c041c071000344a00d6400074240340207401c407040109001202240b00401002c0d080c28094205100106a0300c04982680281d4003a200e012164491030303201d10111400c02a00441140042c40400c5000d00780a00c2401c46043d021032000542d2500b171100c00c2418034091580c039102c0c0204101140298180f84544580f0b8010400c0c0f45102151141b8018000c0304550030700740080c1b00c9900440807811100b4540700c0e00e401c83c0031402013048242400151035564080c2442600e11a0742004000c4031181e1004c82900d00031501c5885000c55140c1c031000c240d4561403102d03241d0780c0244e5200c000184120f0007403500301c1f800c1c0c070300c0740903006948243d42400700f103030002030505010340000c00041111480c001090f086103081c04640d6912200da500000e2101e50751058040c0410480b0000d03079007010b4042d0b01c01c0b8020001020100c0c1d0aa400f0414401900d01c0c04801a01180050000841020480c946682d00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 275445962 1250 275444712 275444717
    0x3030712020906221a0405060f070f08040e0a0c0918090524010801060f080304030b0a06090203190c030c020706080c040e010303090602060705070f02060d090203100c0201050a0c0f050a 81
    0x600003446a01c0700c600002c0c401c1c524401084031010170455140c43c9024403114a5000e00318900b6083c00007080e52413086200c48914000c002030fa40c0c050084904a08100ca40e00400350780e80e559076501d05c2d03641b15805079410010140781180b20f402d2f0301e00500003541250400c0108102c0c91000100307510081007900e00030703240c40c010222401d01c20305917115441c856441038403588110b54101031495085414039040078202c1182c40d4818814000004151780490360301c020007030603030390740c8070b560001034000c45e403000c2005400881030004168201c00030845041101000b003000340c0d4021011000c0d240600020300168100d14024071050f071161418690001c0c600300301c81c0c54030307564414060304103400368010b0b00011291031050251540c184049034203c0f4541c079001b41090700d152507c1079111035002c80284100000038549003a031800d40c0046030b100760018103580d100d08182c0e4118000c2c00f28855084019484c000008004104038030480c081041c42d551203060340b030401841501c1503800505903009 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 275447212 1250 275445962 275445967
    0xc030e0301112a0a080301030b07020c0301090f0b0f010b04150215042a03080a11011b030c030f1406220606021606030e061603090c080604020a0803030712020906 71
    0x440802d0032008050030305050002c00341e21583d039800300c2c000c03078410186454180c01030905103020440f141c0649065941000ba01581601d8091040c0d1504d40200740e501d4040d400c2685c03860900c80e41d4111340780c10a000c0d00c0d000d5942d54071300900940f218824003c08004480c1407000b8003001c00d00a443d00c40c3c01d1500d004440085841d4003200814880c00c4604541070760100340300551b000390841c0183c101c11004594604414203540d40c00c4660b0007455141c1c820090300c041c18509074002508030050350f40900d40e20304080b0094000003000380c40260301d50004030b4242103c50035411a01d11030050500581d00542c03015440b09400c100a5260310183d41c110006192a540300300051031065000620a580080900b5400d408004800301d00700c1d07002d0f005040c98441c4014130303610003080091744141505240700ca00d02c56000d00350300030165940c0280050380040000320780070000050440c0154001c4680b0185640d03503424013a83c0c0d210840300480028999849103000030030035005482c241800901050 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 275448462 1250 275447212 275447231
    0x614131a0c1204030c05100203090f0a05210f2a150301080703030212070803040201140408010f152c19050a0b041415060702031c05030405070b0702010c030e0301 71
    0x1d02c1c09680d400082002c0800060070410018128000c0340280f074140c0d85c40721b0303008032154040c1d2640111601c040c05201034510030345082c3e5640210300050100200140c0080720030095250010003503100c05502881541200038103100001855801004003080c50341400c00d4007024070000b07040f00e070010b98011400c4948c1108441c0500041d5020740981e500071328925180d410000e2920032061705260041004001c0e01e03000ca0603d8003102d0b44280c0a003048600881c41050a0705030380700d1036001010552910f850307007084080320381003400045a80507001207090740f503058140030b002c81c800081c0e103405503081c444200b001460307040d00da001518903800c009642480c62400161001210003030505656001c04c2e500c1440c0c1441107500c600c4060517000c0041c80d00300c588586840f072202c00940300c0c80b0040303a040110742d010400c0c04021000d440400c8101d50705150302401c25002558115034074010070601041d100d40403010340d02c285030140e4074007036403000c991808c0d01d4150351280d4443d015501c402c03024 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 275449712 1250 275448462 275448487
    0x30f03110904110903011b171509040302120c0109020103150e04241b0810050306060411070609030e0a0b18040f0207020a0b04050a05030c0306040605090f0a0c0614131a 74
    0x420595024004c2010321801c003900285080400a84e500c8004428030a12109c1085424020305859044c2e0340c203001c135201c40c01c059280c4102080707050040040018400e0011806400c1354510314401c0e282407081c00504c54509a07203210038020324098444003030014020420101070f80313108041007200a12440c0340c40e0090310641e11b118594a65013006200d084032001d9014403482e81c010a1502010005400e100003e502c0c2c03100580214030a40c3c0307480c0e4081501840e0000c8a0996034070a508000303a03099480c1c054420300c62080814482c4450000001d84131800c5021921640c041010240c01d050401e41040010290250381c1013030796500b4880d80780107803a001090380c050044030355001d4580b8a03003130412683d003000343c0005000303410520b080c840c0b5460000300c0d01e030459440503000c40c0c166548403285161140702d02d00034280c3d01c0303420920b070f0500801185481c1a901259070300d1226001c02d01c0351074040d220300d8110811800030018204000e00c0b0391900912620444580540f81880103441c0d03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 275450962 1250 275449712 275449721
    0x40203130b041e12090801020a0e0405100f030501050f25030510030219090f0c02060a18020a0f06020607090819150212100602010e03040e0a090b0f04030f0311090411090301 76
    0x440d0b04c080e040c1d20440003103801210000081071154000d601d0b203195000002c0c003000080a00e1801591600041006009c914503180040d00c4d106038256034699682c1045400f074030065032641e0043e00c01c600442e1414070031003070710589030b115100301c600c54503180c8004500900008084070481c04031720300e000c0010303900c000f081203032404443c1c1080c514034201120301c0c0c12035039843d9404072410315280c100a44140c022480347da019481c0d54001071800700c45074108030103a0290300000c1d80070348540400f0901c140d951512a00b07461071503085540b2556200b00070342d803406d0540504401a44840104001890485248100e6920600030300a8001d01c5c4900381d000c0c0e07000240320000f407106000c204000700300c3c2d01c410400144030f188000d003c02ca52054107140c40384a20b015005050b20080d000ac4c0d22070b01d80c0c0d00074865941c1d200c1c566014501c2e0072041c0000d10401030f0f40480000e08451010030500b4400e0103404802e80c0c2c490f142914180711181000001e002c0c1500d81500c00000b480140c0c06641c00381704 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 275452212 1250 275450962 275451023
    0x30f020f090901140603300702030115030c0f031502070203160807050306060307151d100e13090206090105090103060503010c0908070e010807120f0b010611010b040203130b04 77
    0x10a6410070240c9422040d41c00608490199001061030f44104101c410360711041c1f610030912000c402000b088604061007180806501913080c042242c40705000384015030b003102d0003041d070001641c0d1140341d42003043e20703140b00140c41026080d0070f9061030282e9500520640e4401021903090243c0351603480007040c1c1503405421180c100607400c0216007002c0c0442c5500c880c0c02c0340500307011410000360202601300d0040120400a20320250b40c40c011100d04149e2041000404082101514640080604c61500002c5000e00703035075040007002c142d05020380c0504a9005050358100052070004441a07000012190f04264441c1c0300014a500c0030710078810302d54203d91b1540452402c100b0318034074050440c4c0c0007190642010700100900350f8044ce8030301c25182c1d02c5000401c2590b15043c01041003d48a41c050010704c56100001401c0750000218a10000c000c4000c2c0048200c03102080124002203445c21180c2d07c0400802001860301d035405588188a01c0c0c3c0300518910001000c1e2030b9545076030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 275453462 1250 275452212 275452231
    0xf0d0908030601020114160309030c0602070803010603062102190b040f1707140d03141308010609020a0801090b04020c030d020d061a0d0c1e0903141204030f020f09 72
    0x206002e280d5034207010714905504030ba010070801c0e051964141c8420300d550782c02d89042590700c072500010940301c3c1c4035941c441d64000c00150b48900c25070800b01410781c8203101d00f20110340341c100002184400300c411125001049aa101e03020741ca0340c1c007805841c2110803414500e0102c00b00010031030b4051701c4054800303010813580c0b0100329800c1c030762681d8400444c142c54408980c01450100a6110107114000340002d0a858461080d2170628081c0d411305410384007a03188100220390040d040095045450864881c01c00a00c8100d565110701403c908c50040c90400151300381c001404680c017a90840109071034060b100519010000700e0040c25034015081501085400085010001d4040d008400182203024200340c00d02102d00b00608042c41590380f50944261110602c03100280201014881400c0e00089076500c4112190010b000fa0f65502003145e414440000d5161441c50002d44c90043c0c0c4090350415107001e08580b60f041c41c0c54038400342282c1c40840548100941e0310740f8126240111102c4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 275454712 1250 275453462 275453467
    0xa03090305060c090901091e0f090b0604061d090321040b011d042003010c020c0301050a060602030702011d0402120f090d0509010c02040902090f1006050406050f0f0d0908 75
    0x500c0c109040040280aa2103c00c00902c03400d812a600c0704011811a0502c1a0005407c0101c58503480c21100710400404094900f02c40240568007503003242c0d45403882140300003100e039941c8040004840543c024035151903202140000154a5024240c0e04050160126814014010201d000d90b40031050043c0c0c00040740d0050008000078804c00901509040c141c00f80005240540388601800c010710281c040000c4401076040800d40d2442c4c55800b07100500248000e00040e4006076841c1e00f01c0c0c4e80380c0d01a61a100000d042050b50303114810541c0e0b140d42c041c502e407510540045818003140c40c40c0d5030b00380c400300d0040780880e5102d10040c0714801101010844c6807810500329140c02d0801010824a80c00c00740c4c25a1105500400b1221154024280b100502c0e109001180c0101031840000350805843c0c402d018821040c55142032080041d000f00c2490f180d2030380001c0b6024000e5201703240100c1e105105500400d845c0f2030241800394444807409041040306007000f07040e00c01d08035040d104c04100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 275455962 1250 275454712 275454719
    0xe130c0f08090c0102030a030b12070305010c110a170a1707030c0f020c010f080a0b0d06020c07050307031109181c02190b060f0409080c010c080711101d0a0309 70
    0x100e2030706540035040c0b0000d0860b903044040041d44a104150b50803013015900c025001141d41c560b0a80145840c65074229a02143c4034500b00c0d00030010340500c0302c04030fa18103510840751940002e0012251394030006010301d0b5240c11300c0490603504040381e0b420034400514204e00c0c50f040210191031141c5d00540d008225010382c44005050754031240310741c0c4110742005513240c441380d070420f030050360108841c94803105030b9039680c410034010300481100a50107080c1035008024084c90f5005442016440c0068840d681c3d50f80c2c1c00c050340d40415110050907402d69015460b010720300000340e41d03880740707501000c400c1a0320500e400a01303001c80002c10b4142d0610303d00c40d0080065040000301403984501540c02c00505094640702c40d0b04400500300c41c440c901d040c003403407007503100c540000301d029511401d02c981352041440294040d112100447c0005414100003440c801d20035940c007414400004054002a181d0341c0280c005800d00d0803200e05078448200c29090050400c110035441a4080d507501042c481c01d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 275457212 1250 275455962 275455967
    0x20102190f12090308090d03030609092612011206062d320303090307030c150503070f031508030307090303021027030201060e0406020a030f05090705010e130c0f 71
    0x10706a0040c07042103c015002c1c00010149030444500100440c0c25102c40c1040c0e00c0e045024140c0ca8102c900801e0610140508001242c0e60b84a120201c419028a00003802e42c0940024001d0349828465405c0c0b910040224440c4414052071007402040040f0b81c480d200d0000080c00941c045403003401c49110a130f41002c10101c0da40000207020075190310264800420500e102c820203032450301480f400420b03035240b4690780800403240c4c5200d0180c20f03a08a241d490420b00c106000a01c144c148001140c0d1820b1701107803054046910600ca20b8490b0301e9040071140b0100c0013410000305203860400d40c1d030700c080b40c1c01ea02000998850486550f038040c0c0e003421480c2c000d00340802803405200040c101100c03080d00145900e440c4044982901500a01003814101280508003d030b0007010703050700c104180018401c071a001058a81c50720f0300c00b408201802036440b03044540071620008581c01c450380c18040c640c41a005034a000600030f20506080c0d41d410065000c0380c020a03031070004a803070b560410030001e8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 275458462 1250 275457212 275457233
    0x1b0905030d08090d1107150c14060f010b0304081209030c16261c0f26040210030b1504080c090903121003080711030714030304050607020102190f 64
    0x1e403421055030708090075907941e104201e90382c3c0d000340003c0c00020104030f44200714007002040f0149401c02e40c1b0b41580000352040d614044d0540e0903103050a440460350400060f80d502a40414200340b00d20303803a01441c160742d504040c0080300d40a4080041d1000c90902e40c00e41d0b8001e83e01500915500c100d88004945407441000c0620450000c2c03200c1000307140708540b002c01c81c000082d000c0c0502c41c040c401641d1309040703044103820220000c01d64070340071050340001c0401d00244640c0343c1d144000c400781c0101c80c007007151030780c0300004e949100005030050900c12070403070000718982004140354072071000103002d0102c200d220555152010404201c408810015a404150145c03050a29400c04c680c19944038810042c0310000c40f00980302280c520320031980300e04001e5401803001c940f60001c51030515004030302c420407144248100300c00800c12103e5030070054410310006005600d45441d28003840899041b0344401da040d80110000360a038800c01070a50f07030000d40f10b9500601140580c0c50300c041c010307 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 275459712 1250 275458462 275458483
    0x8071b0620060a09020a05030d020a030f0905061c020c0a110f01050306010206040803091207031d0f100305061c0813060215010509150a0602010605010201060909080a050a031b090503 80
    0x140c9000212403040c0c020441c0d40d0480908180400e404c2c406001040f00d0440c2688010b40520034414105003e541c0401c10b0f00c400c5201c0d60f59051039400c042c5045407015102e0080c50b0340b1120411240d00d11505103031054500004803031000d818243c4103c541c0c0c0c1000702c1c0a2083d91030101a5682004030725141c2c0c3c0100554400742041820750500f100003d64a090080c030003414140700201041c4161801c01200003c0440b2003109aa141100e2800038031107000303d001d85030300b8884a01c00c08000e14051843c03044598000d021500044a004030403405024050080e5400c0b031001c00742c0007a1100c24501d40c81543c0e02411044d51f441b02c2c0c207543d0401540751903103e8421500b0501d014101d00300300401c2e450440784216244401d580361018903100d0783c4815485030740c0c000d00c001400684d168064000d84103c4109030020080320b0340e01e9020000f9101d1a03680200a550308008045805000c3d6000c1c1000c0300c01450300060107070300301400520f0b02000b5200f80020442d40c0500300071500c1c1c2040f100490 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 275460962 1250 275459712 275459747
    0x1b080c0d021e0703140f03040311010305130510091b0f03050f01020405131d06150406080309060703050a11031602040606030b030a170c01060f08070803120a0908071b06 74
    0xa035002c00c0c25a540b00c1d0010f01004004541540441c5181c1030700300405083e00700200c082d42d41d596501e261080e01e944407900000e000c64280700c0040c0e01615440300c19000240c12030064019500d201840d10020010030100f02e0b254160710503a00030348548007020801505130680030407049401c50401a2400c2000341d00034600d680100411b01042c4c65030401400d01d1041a9008141c80c6040384030050600001040c0d582d82d4425001004581d001c99400c0d0304d00c241003682d0401500d0346480b507054813442403007030280d0040010403000e00040e01c104004c0089182c103150036514021300c081140c2c11540311800092071000480540c0c01545458410700b0014172070f0f41020401c044d0440c0100f601c2d58550f5501070081040c105001e15640c030f00400300d65007008000c00800020b600c4d6000c080d507501c2c840c0144c4e0b00501c0f840a000c521b40c43d000044a00c0221090050340682e6520490a006010300c004212409001401a8800200b09444403290402c011515011241c10000014015061820319040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 275462212 1250 275460962 275461003
    0x1030509061003080d02040302101e050408151e010801060e070801051018050a030501050f06010e01020604061e050403030c022e0f060b070b040501050a05161b080c0d02 74
    0x245800440b60b41d0040301e42c0030380240e8a50b1607440d159802401150300203074001c90841425500c040e13200400c0c98100820f00f4080c52040100c0d0012503a40c000c60140c103820398040003c443c000c0030810400c90b80b203451040302d11020b040b07492010451920a90195000b69110324091140c004c0c2c1612496021801e842d151510350700d0000040d40200b802d540100074088148214a01c00c2c02c0340e106000a4a400340004034440c0e5603140c803034001c14080f40c00300840070603e800b1681542c0b00c1c80601489200580c001c12068403203480d4000144000140d071429400d000c584544005918021580700f2802900c0001c1c1d11130141401900b072800c4440b800c10503003c1c0084d1000400603003040221401c84407503000582c2441e40300b01030002c042581002e40611404501d22040185080c0301c207204a12440091010f0307240d4101c480240e9070280c942d141c40c0070031001a01402031150400d81e9000e07005c1840a860f810540e10754151075800f64030a15116088a040d551110b40c04002c0660300150203040c514 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 275463462 1250 275462212 275462221
    0xf0201090308060909100203090307020a21080d0f15080c0108010503030a030c03020c1b1c020a0312031407082e0b090a081014060d0b060402030702012003060103050906 74
    0x82c9014030040c0100c0c0310742c2e11800400d41d0001c00300917003101d440401008565070f00345080d80a039681c00c1302c40308074070a0901e4400450b031010000c10040c0b414100720350919035502c65603110070803078200c1442031a24580c0c40c0c8010f601c642c82406006030100c0c699007401da03018101072a480c06c00d6044400c0e981440118001001252800070403500103800910b4001030040d04031500302c01030310070468080d4151040118801c01c8206200d134190305540d0488a05c84006446000a100c16090002c041d501c074441090400c08116207440400aa0400307180005419a55481030241e29006a45a13000128400d0030850b480c1007108640d01d40a040c403044008a0b003560a01e1001e500302800f80040462000c07441540070745401510101804542055811144841507507078010288008040d0742e006507030340421440c0c2003125082e034040f904030082e18002d5450206100c081d500240444085640c1c0e54510a900c00d0380036116440c43c1c0a034000e0964900f0680d0004050300c80c003600b0002560001c17420312 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 275464712 1250 275463462 275463467
    0x4110c0a11040b13020d0510061d01090306050f07031107050601090b060405030607030213122f03032a010203070c0b0910050901050a0f0b010207060c020d050f0d0f02010903 76
    0x80a41e5000800703104400800d070100703010b8402c1c04200341d000f000103080240b5880300c0741c019001d060103400d0204075690b80d81d84042800c8005200b40c0010401c0e504004200c0704122100c0c110b02c04060501010684e07980d601d039021684c08403481d481b8a10300500344484550705000d0740c0303610b0455401d031034205101070719115103d04042c07203034221141d030354010150710761910b8081d9402010020b090712900d04d05444050040c0d84503107a2986101509003001c180d03c0300014801d0303c00ca8124111403c0c1c2d1501c075403107058a10403981030500b210321003448e201050740d081001b031000c0204c90800c40800c180c01030860400b52815a40d4800c075900500c100100103030700424114440340c01c11a103554a4940564941c141600b00d4036201069051501b00701c0922015041b00d800f4a081c21030400078114580c0007041100d215042c1140140c00c01da0003002001c0c490004a94140d0000300740101c2c003c61966014601620407050100e1238010705116003102c0e80080c1101c04c0022a4002800011000ea600 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 275465962 1250 275464712 275464723
    0xb091305060f0303070c03030809060112080c07090c09030515011a0f070f060c0f090f0504020904180303141b07140a05010c021c031104090905030d0c05030604110c 72
    0x402036454002079100e035203180d151040741c00c0c0076050ba595501282403042c0500e0325800f06601007007480780440d500d4000042e03400e048554244450000c40c1840d95541003680c055180d2041601c900040031032800310758031412034214143d89892074007030715514166080c1210309640c03041c081480001007119100028040d4810f862000d080c41e6a00800300034441c0c3d6005a08002d00801200e40001c81004541d40c4100c8481c0035a40fa0090101e002480131103060103a401313140c80b03408060400308194101600503140310013000b04007080120041030041210f0301e04010aa00190700c1c0c404440340c44403c0018190003075071842100000d181030540a074100d214485006100c1c8081543d840c40001c018000501a00e0f4000300a001140c82204000e50741c0d91001c14070744008050303003814103041d8040d00c90001f80e00d146d290030600342803500d03130701000500c0300d80710035103a5000400c10a001846c0070f1044030301c41d040c5a20b03502c1d00c0381405c50600049940c4441c8100346128200321500168600145 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 275467212 1250 275465962 275465989
    0x30050a08090a0f0b1e03150f031e03090a0f15140712030c0806062106030106080601060f03140c070605060f10050304020906010219200d08070c0b09 65
    0x324a596000c15801062902c40194401d12040348195000b1a1540b010f2004281c60301d115100c1e98116248402003201d9440260303004a0030f2840e03011103a02e5410140d406916226008042d154040550041c000700240304899101c201d401c00581900e21349030400040703018009c01c0d407a6a0045041c20640003585501c00718250500c18810030b84a0710070204000c55002c079500c00b030f003052002004240038000e019800c0c2c80401041404000034003034101801514090802c01c0481c03103000142012081c296800600803e4040d501c2d44004a00d145081007014001c02c8d407070780c0e801c071111074114009086504191928039060210014021000c55580507208115003000e4006029229000004c130082003c11500c2e400500701120302a009030004042c602c0345000380c4201c001540ca0800498442a2070301020494101c142007801c0032070b5030f001c10309003003009039420b182a5112210016581760001c0da0202d514000c0007494000300328085407054014030001202c1d9080031008000202105117030b08 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 275468462 1250 275467212 275467223
    0x19020a09150902040803030a050c0310060518031501060f03091110170903070308010801090206070b040f0203070b07062016080d11030405070b0405090601110a020a30050a 75
    0x300300070482070020001401819084000c55031640e039004510b40343c1d0001c8a89156062520f070010b907151440301d084912503c1e8080b260281503003080001da5090308002481c080303641d101707800d5020039201007200a80c500b1900380b041165600d0541c0040456001e0140040bc241c00c000c1d0081c0005c4140500003608081200ea415095000c2c40b0700700c3d2042070b100c01141c0185244403d0005011000c0000c111460007540c980c5020781c1c86400c424280c0301d100800a410400420508001c14000c84803246c205204000c10a110740f6580c0010346481c0e0b07280c2004141201c001402401c112071403050a2024110500302e0810b0045404401d03000e00600b0502d640050621103002c041058200840304d1202d10784008020400e034503510000c450700119822569440340000104522500354141c1d03081f203600070301d511013648e942d40c01101c8100c080000c4610718070175810032000581e1101205400b0b0803440164025260302465200ea1116588800741610441c038202c43c404200c0200300340c0348054129 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 275469712 1250 275468462 275468471
    0x50603100b1c1506150e0604241b050717010b0d081c020d05040201140f07061104090903020a05011802060d0203101a0405030606100804060c050c0a0303020c19020a09 73
    0x10b04080612041512100c500c103031078800702040202e4405107045c0109a2661048840c9603000240420380c85240100d410900f011110f6098244507104d0148035480c040c9005070031484040c206804a42c24280c040b038035a00540021f1003103101d50800a8192400714000380103244421021030340c44d000080c005003880c40c00048074903880c10241000015864221f43c1190b4071420418031000900d41036404900103503004d03500c02c80300c0c1e400e00107460310021912aa58500704959882c0c100400f681c041400f840d490900c400200103200e440340f062034078001d4009d003c40f84030601c2c0c00ca003103074400940041300550600d52000540c480c1c0c1e058030203418003c00c00590b01c1d12404244021040c055020805121002900003018042d12010708221001581240c055803a150100402d49415507210710029118030001004a0200e402090f00203609060a0745400c59810711582400700f50481540071940018803005100c3d020410140300d05242e07405003a11100c9a400544906114070642c075549494 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 275470962 1250 275469712 275469769
    0x10c031103040f0512030307092309130c0504051003021905100f020115050607030c06090602041d09030f1c18030809100c05040515040b030a050603100b 67
    0xd5508500020003201140d4076907694001c8100c41008074001d05010354842e40b598903003001c0002c15240142c0036a1035500c180e5080c2240052518650524840110f0b0000290032413030310303080001402501800185190040c8a0804510803101540014000e52510042160015130080440117880c3e0440d8400d160205002004510103400d170840c640c00904d14042a8071030340c000c650105000030030f030024094084001004003459015100f059006502001484002032044d02c004800c01d00c6000002501a002d0f11010100d80050300103071a0304007030049444812003559105a80100050000d5140140c04201500a4040d14098840510802a01c4070307403c4080d8101415800840c03180004030241800c0c01080f1820070f0301c0c2c0041501496035061070010303281c0030b4000202c00544a062926280200380070301c2500441828011300302c180300c04181014110001c600403203030403c0105650500b5001c2506045460b907200c11054078103224107140380c036410081c54213030104c100148015036a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 275472212 1250 275470962 275470967
    0x50910090803040e0108190f0308041a09010203060310090203190224030a050a1406060a020f1c0201050105010f08010311040e0f0d02120f120a0603021002070905070804080702010c03 80
    0x90035006070945010200e0702280802030606600e040780c4061040710320b014401c11200081139094000075046044802c000c0c00424002d0703040f140c10501c100c2c10310226806c5400c2594510328251007410030b6035000402d02080303280c01c01c00008079002e06c0a04011460103680000c2e9103003180c02d214990445058509400c0d542d80e406040703005802c0300d408509403541c0004100041d0700490f0410095444c000225100c0740b00c0c0c0c070480703c4200030304207540b035943c5803041000300e0340d0010240c46046101d08102c110484a0500c4141b07100341000c0c00c142d9480031586406425584140c1200e410000c4441c01d015080743c2c000e40301411179411601081010460401180144c50760040d1a40e891145a880b80141140000c48400c50700c2d0035070989400d0000103050080c2445070300b041854950b800e0000c8404d0410219078141c00180340f41d8000740c1d56030303a80d002c00c20665105004402603000000c1c104021101401581e602c0340b01c500e0020024501603549204600518002074104564551410109030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 275473462 1250 275472212 275472227
    0x10b0c062202090403030f110f07020d0507080d020c0a0e0601120b040908210a020343050d0c08010303140306010903020a27020708070314040e0403030e1c050910 71
    0x30b8014120031554601400c0140c0644103c225001e42c191405407120b08514018050340d440818a6808503d44903258003000741d02c01e0b20341c100752580c3c0120000050035610802000580c80f40070b4003d0180d040801f4108030807035203d40c2c01042d42c001409c0c208101a0b92200b0a600031140d60100010380c900d018000c28024544003100a0401c2c0e00051410000103020500b8480c02904c42c24102c2540d40d024001c900f43d00083c0e5941e000c92140c1c0b602c101302031034980032404808240c0000b010544600481707024001c01100200340218030009404040e0581346d0090003031446050030b0042c000d5155940c02860002c20b04420103540f240403010520a170b120358040c20065030018072444045442e20300d480710040307070800751403001307a451f01c4802c401c09520f000352081a80c001c0449420040310f0b4030184c400e44031a04104505180400011030b034409006002d6010300c0c003da50003c0c4409000ea10145403a40d0092010401070500390722582c0e05520600f151400c00054500781c010100800080d140704 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 275474712 1250 275473462 275473531
    0x90506130305030a080a0e01060e13021212130609060818010b0406080f10091109060a0e04050307140a0221030c0703200909190206070203060403020114010b0c06 71
    0x9000015180c4c0c84190f100766076601a45113580f0400810040c684024200c0b4600d04c11030030055060703000154a00f031030a100e0f0798045d0019240001209810702d14138109401207007544214000401c04400c09201c00c0c07900d0010b42940d0900180d21810290080c10211000b85485c4803050504280740d400307002900f0a900600d405041030000c05c0c0c450340304580320b20060380c0c030040901c2191400c1a90303941e64002d02c02d405400c116001070b801c83c0c034028810301e0180248a5500855190800035038800c0380019544102d00800c080d41d1104400d251104068500600c1d880d826803040841402503500e050081860005500000c5068100708941d41d0031130182010000140c0503c070400428022007031b01c14022621180031040070f1619003400c02c048804103503400e0f051071744003049241025120000504d2042c0c0000d200394109101680068035020044a00700c006035140c20074100481e90550f071103405410754092550802c3c0c10034240581d1400010200e201114080200c81401c91000903450802c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 275475962 1250 275474712 275474723
    0x13080105070305060d03090e0a1d07180b06071203020f030a0501030c120506070c05161e050409151104090f14160f08040f020603010303050a111203190b090108010f1104060905061303 80
    0x240003a03024a442f0440351041d40444164001e00805240b030501c41c00c1d56aa000500c22030410885440d40202c1121000c00c02041c1a402c00491400070036440c01ba42c81403007044004030f51581149084c03450305945a10050404406464078000100e005c0f912643c002024a494681841c5da82005854a081548074070a503000e03141c0d020071140d52409411501c05441003603160b01035070360310510003100c002c2d0002410320042c3e082064090340181c1c200f5500a030091040c0782c28143c5400c0740d00d08803000091650a200d60b6017955000340c40e12500340c1c6610074240024002c01c10100703103016128050750604541000003600020701000800e840084c1d0f1139801500f12620b039a141d2a002c0d11981c0b008980401003040044040460200060391030301001c804800e80d411034559199141410240d00014040542c45800100d826240c1540b024000d00c2c0140000c14001550005601100c0c02000364034010481000240007154000340c4841c110350701540e555598010344005000c0a06698100030203 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 275477212 1250 275475962 275476001
    0xc050c060a030b1804120f050f1801180f0506070312020a02070e010b0a1409010e031203071b0b150d08130501110f1b030313080105070305060d03090e0a 67
    0x1400c99040e84003810600d81596200b6241d0b07000048012100341c12a80184009003428400941910034041f01c1c16156050800c142000c0c840810b0004581000741d40c0700c03018541c0c003a894540d6a01c04140c2200d26505c0e1000c80c0c41c1410962441410302036801598050400000d030302e01018464400745103400c0310510110b4036001400002925540c10344601491182003000105051050904a5100b42e40689491341080701040c031112841d00040120b50602002c02c00003040c5440038051082c1e9000d60b1010b031940c1707161002c0046e103003401040c80843c41180c0015850005a110310225400410304645040c2500500c0300060a00312a03010060800c07801040041000c00005001c1c0d0986002745c070750070314a40700415110f07940c007800070050b001507100f418040072505010034190b0403480054156840c0440c42000462000e4060384649006d070b5494040110340b0741d140c46883e8100700c00300c0f5030110382a11a00e00410403032281c0546861401680080f5103142d0251b449081d42d01c26000d104c05 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 275478462 1250 275477212 275477227
    0xa0b0612010b070507150206160e1f08090a1709030718020405040617030711060405030708060a05060a03051f09020d12020c090603120c0f030408031305011e0c050c06 73
    0x603010f4000910441d4203100f1000042840822003501d41d48142c1180d00915442e6120002009501202c40e030302c8091104c0007040e200c0d56100c2e00c11200c44020a650501c0907a681c00700010b10f0400005d126203500e4221444c15000684000b41c00e1072244100e04580d5100d00000f40001c2c203064040c3c0c040b0840d115800c00022807041c09170080c00480300d003203070100281517031418924040b444908080c98190001c002c9a0002204620001c0e40f5100251031181440e440d41c0101e860f040e1a5048101d1640c450020005461b54a000b6507074882c00507a010b010062035991001d0765031464107800400100310a594107040e0246070300c1841c3c10790300145882c9035614141403c80a815903aa81c41e4010b0003260002c8034141042c0001e180102030250082000440c100c074030000700d8200c44108080c42c003560404844002e81000500003600d000c10107155110104042c5070300300c0d0515886541401803070146aa01c12620b500c0703601030304c401814280c903030303d445141250400d40104030459003d40d0108100c0c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 275479712 1250 275478462 275478479
    0x1504080a0c060914040218120a15110f07060929010b0702010f0f0c0501090309030515012612180a1505031303020c0301050109050a061a0304120207152606090a0b061201 74
    0x741c81601641e40300e00c2b2000c000100c0e00680f142c400302424015010440c8900c1400313040d004000050061900058071007030340d91291074140c070002c18405030f080314040c40741d500c402d0284864010803040e00c910303280043c9940003811500003064064180f000300e0685d9180b207401240ca141c1c849078840c00030809814180360181c0301026501040d9154403c03104240c4400f2041d50b07043c0c0c1070300d1042003082c111850300d246056080b611000c003c1500d0243d050301d55010704450004e030040c0d038608031880000601038028080381d106203501410a1880103048041c400f80c0086c112504192110a034110a205c1804d0a0749026400784100e60150300e4400001840404c3e81d000754051040c824050240c580d503102101400e455012a810100d041000401c001605112412010740304074010b886400d80e681086404000741c03883c03030f44041400c1c03100c2e0481c00601d149039416910f030000110031340b03401d021011034800b1000418600e400c9035a60501c208079690300f0160b50001c404400101415030312003001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 275480962 1250 275479712 275479723
    0x1a0711070305070321021b0105130e010503010b0102060f0112020d0b0703051017030f0702120a0303050411100e1201021b0304050f030a0803151504080a0c06091404021812 75
    0xea51242c40300e81d41c0c01700c1546030000b84c50042c01c0742c0e0090494400b401c4900104080702c64002d410720504000c682c01100d40941610000d04007241218030035894007080c10b094800301c03520790341150000c0c1c08010801c00245102030544280b8860700c0c118130756910115528800d01d50028002007045000c212400360715401c603078402c0403240c1603283c000d6924800e04800c10400c0707500c511103410074400328002d0000a4090654580002d0504110164441c0000c3c1030141103401540001e49542c03c000c1440400688813030303080800d481d028521800c40c607005000701d02603501e03c6d2050010028402d003000003501540c1039444498201c0c40102e0360309564599903800380c45021b0045000b008000070500d0081144842c00c0e8000301c0051455560b1040703190440000710b8066400340030001e01021120840380a00003405100004000951150401c1c081d0000c06500c45001c01503404c0e01030003081d01e03024525140305000d031005030b11001400103510401c0400e407e0950031584040101c01c0080c0009007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 275482212 1250 275480962 275480969
    0x213110904060501020609070b090a09140121080f03090c030102161a010b03071b1b09180804060f200319020601050306010314011b1d04091a071107030507 68
    0x14100b02195450005980392001241c001c3c1954219900c00c200d03052845009020201d0020104071203582c8070708083c4119074204001d08200c84645005000c200d0006c421212540d5000084030b1a0111584c0d44180f00d125210103060310300030101c04a203140c0c208001c840b4080e00010000c1d525105007204003030700e034180c0103801d80d245440005400b52407480501554162400303050400e26507a2107100c2903030074007054440ba0304805003c09401000c603c40342200015042c800c2100b140c05071a054403034041c0d40e2410842c0c0740b100302c1c0400610001d0300c0381d011039080b2043c504150048007100031094800007644d480184081010480f821100c1034044020b103c1d10080a8a00c24070001c41d0b002266203090901516405a021000510200d45460b2550108101e0f030b20022400096030b0001504411420b641030000c980c069002505680105100c100c04020981d020801e11189848003003001c070204000b00740140b11003021650b100c0c81024211600c0c00300401b02d0707400a9a030b03d0030960f070300503034803 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 275483462 1250 275482212 275482219
    0x406050d1812022103010e090a050109060203010e0a020a1205060a0e0108101d0619020c01290d0203030f070614090a0b06010309050c041d011104080105100605030c0702131109 77
    0x100104c54107200c510600028800503080d20741183e00b0f1104566070b14001810b000c000d44944081440000c0c000d0089050491291a0160700c95240070600035101d0300240501c10141c1c01802246401a440f4404102c4a044050080381c251070355804200d00c0d040340e03000344110451410010540110000d4040310b80c582201d0101306a642540510351540c0c002c2e2510380440e0054030110342c0650000d440d040000a5507000103242c004041300c1c0d1030850f80d01502d2014070445608034540301d14040711050068080c10380340c500c044000360b800a91648102d01c000810030381b001c50000107008042d44040740c017070240000104641040c82407141e4503007120004031645200d28000822951203409944d1442c1d07441001450104081c008001c0640a80c00c4c0380d07039003030000481545002c81d00340941d800080b042c0421942da5401c21816900750358004004007070450400c01d04002c480d07409021a0350003652032540588540c00d0388002800b10303400282c01210241800080e01ca00c94511004000216044 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 275484712 1250 275483462 275483473
    0x10501050f060304022409040504120210022a0708190c12080307050d14010b0a081f0b070311060103030905030d0806010f1d03030d1509110406050d181202 68
    0x1d00402c200d510084800940001c404070090a00f95000101e08040c03c1500c0049030400714000c0c0424100e900494080d41c81c66900d0001865180e0180b210039400c0030146010f5141400d21091003945e014a44a400d9071100e40c1c900e2916520028010603010309041e400f52516000c5040c100844900c070284282e95044444400061540d8030303502d110400780c6e011031100d0035640c40500c1560760f03410041842c84001c0e110318085a0003240054128068030740000b400362103c10700f19008000350801801e40e01c111016140e0185000c1007542841d085400544a160b500c4129140032103032041b00c854090341c0303807080c84000b1040541081c0d17100c0588074264121003018000003422500448180d480b1404036034000e248084462084100c00103c6030000b01503640240b840d001709141d40d00010b00c0d0740540740d59181c564108070701451140014a5a4541440904c40a100301c00f041d100e14030680003800400660b201c600c22040d02f2900709500320000141045900d414804001b01d00c8010350300c01401003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 275485962 1250 275484712 275484739
    0x11070302090403091802090d08090d060606020d0215010e0c0915030c0d141603180803090c01181419080303040f150903120e0703142404020303030a0f0f0e01050105 72
    0x5038829910710507001088c240c0448c0154560b21f00561140c02e205800840071290480860580d0048800030321304d603401001c41542c901c60090a00c160b029055403150041c0004102d03640c3c4082ca19074101203220709107540d4460840c000b850714950820a01c0c80901e0102c01c1100120054028010205d02c542c1c0c00d0055080700301201d20040c604407201ea00814201c64105038a501c69840082210510164a40e241089480301907240c0c0080700c0c54800d83e40082e2034051079591104004041602c0241503c8406062003d49045081f0f01d2800c14068200315141104600c00201d011b0f000b440000d0903250f482c1400d00304401c0801c1120302c01c0d101c0713100c2180310611a03074040c41403000f0203416560b20410300441c1c60342d290161040c040d80071010310540e4004008114000b42c030502c1c0159078001400007442452481000403400030f61245003040000802001da1404021240d00102d114000110b510140040f84000c00030342d1034191202d80742c00c4c0002c000e26815440281652402c5800b01c041703101 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 275487212 1250 275485962 275486009
    0x270a0506030724030b0a090906021b06010e0112050307020a0308090108090c150705070e07080108010e1207060507030905030a020f060a0b01020d0c0c0513020319090308071107030209040309 83
    0x29041c00c01d0b900025000c0e05004074403a45c0a1001c03a0350085c210314915980305407100a440d6140300540307609500180721031041c0c2c403555141c010460060003400903585070000c1c40c450110148503c440b05415000c4207801c200c0d05000325082030381d00600b8402d05640364101815142c210341c0780240070500c1d000c00300b40e045a0015080510720401080048054129a1150040c2d003280a0407a407522442001050003640030b801c50340314081e80d994000b1150314221055003503070429039840d51550040d102c00d41580b0004000c541e43c59802450100b02e80d100d0503021001041c62603405801c0740000700b1642240b55022411242107440502202c0c0c058561401e80310407503d9802800c0d0240e40484a0054001d0241d4030f140341e002d0182840c068101c0d1307988045001c0341d8140e1002e05c0d0b95640002040b580102c0487c240845120032882081240e01c544d501608d40300300600314600b800070300d941505000d002084124007665028021072981d051500c0c01804925890050640c1c2a01c0c4d02848140c0b001c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 275488462 1250 275487212 275487239
    0x7081c0506030106051c02060705010c020c03120403050d0302090f040903020d030606020f0303040f0c0807080a0c0909030c110324090f0f070b1c0c020f0d090e010302270a05060307 79
    0x1ca00411406c0311241110320714110300c8850504036000f103030030301852022890030b00c1000301031641600942101040c0404141c180350030004804d015500620051003c0340b800580c40300812510b00300103980e1b00f6058002500d4140940301681d005040c500080205940403a42a0076990241c84c00e1010f5501c1e21410b9846010700400a0b01d598814000600807450242c1c1c00c000c182c0c081c0c0101c100d2161508205c03428141035400c4601c0644c0120b00e00340030040b425008200408040008000d8454181e40040900d501030308090030710124000042850354041c0f0041d603c032441c100c0122900040700344a5101c45401303c0c3c118955008119680c00e24600c0030424021407100c1c080540300060800081c2c5070f06411640b541c6192425401600381032038940e00ca12500c500417a0000c010045141080c03500d00480702001038100308882e9805c00206030a116960305580d4105c031050202e44024220302c0803070719200442d030201404030013441440a0f0343c2d40700034003581e01030701076412654445004040c0309 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 275489712 1250 275488462 275488469
    0x8012d0b010e06090a08120c1b010203030402010f1b030c1103010e0a08031e090a05070504110406031e05010b190804150e0a0c09060f0801060302030d0f030207081c0506030106 77
    0x340c0051080511460f01d1001400e200300002d001101e12600d400d5110300d018500107000d100c0740d03800104c100a492040118111200390a02003494160084000030b45030b00001d4402414415090314500d20180580781140000c2d580724000c0b6100800b80c113008091000e140015120074940c480b4843c1c850130180100c0000500c050014242c4020f6540e440507181e00041282ca04030712100e00d405448046d200d070743c0340192110001040806200d0410608042541d030001d48a60f11302040b04c0d01c45140d041c05d0303a0482da241c3c2400941281e146540758580e524041138282003600d000004a0b416901c80040c1001c5c0c00c0ea00d40240184504032000c0c4c407404400d640203091101441c001001901041d0060807080000c101583d04001a075514201c843c9103d811010071140c0b941814061190101030003402003003440c009100092442c1c0100e5102d00100c100c410801100d0003486c0b80450207601140c6000d640441d11a5076201003a0b0181c901d40c0c1442d0b19031280314241004a2114901400b03a901907 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 275490962 1250 275489712 275489717
    0x3031104030c06110c040c0507150516050c0c12070f301104050c0a021504021003180c120c060329040f090b01030b060d0305040612020408012d0b01 65
    0x215040c5031040e20904d80c54000c0c80580d02c203000c2003e03100c0d211800303034021186850310340c562640d0551508201d0302c212030038044c100707518000400151070383e0740980d061450480d04010b590303920b803100316604090070301c0c012641114080420000d005030005800085802c2e8003000c210840d150290f4081c0310000903030000c0302c08450350100c90480319103160007400b02d00c940251650fa9460074040380c180e910440e00c40c0038401000c107040c162550184402c2e4118480c6611141d81031409600058200642d03490340c0040541d25801d148049044140504140d500058000211a43d4055140c00c0c10406a001c40e03480c010050001002402801152551030104561030208017a018a2450030701c1d40c00c410650090b1605450211b007411031080c80c2210f801fa08404020350b0460034114111400a809203000e0620034003003c0100394010160703000d6a0f240d140180704048441c01090283c09241c102ca49194a07280c4844503404e01f0b0090f132119414000900d42c40c035429400040102d81403100c40c85d01 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 275492212 1250 275490962 275490983
    0x30b011d0106030b01030b10031505030a030c06050604061703030412050c191112100b030c100309020612010815010506090109030201030b120607050a0e0405070f0e0406210303110403 80
    0x4003d02a8000100340e10040c90005200c841860000f6100d5250a40c00b0011903544c603611841455a224280040d210941c010118002543c1d402020500e42c072501070071581d0340d040401c000380c1c0c2d41e412000041103d660344003802207406500988940c02580c0440c0d90041081401860318013030816079202091070405800b404220b00780300521560039030000c4034500c800c2c418111155403854184c40c1504072080003004000505009501104c481e05c0305940b02c0c0e801542003005036550f10301920f03060700c05460082040806480416080e000360020f501540140d00000b255814002030002e0f1440c100300d1119a040e48c2c1c40d4248091403003040320143c009180990140055402074100e90060700018002d02401c5007507201090824609640e014002078000465900003903001d410401e80c04401c85080280d0700308500302034000800f68030780106021a203600ea0f50340e6511540904004e00b201918400104c03201b9a0000c0c060340d40311012804240341c84181100110700c0810340d401e07245d000d5212031 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 275493462 1250 275492212 275492219
    0x30f010f050f060d290f06132102040f051f08030f0a090b040308030403080a0e1b04020c0f16240503090f0d0504090e01180b0601200601030b011d01 65
    0x51154403414500301c12984401038014019040095000403044001400010140c42c004100d0411b28401c00e16205417014030004004403149600d52088a038800c440e004c0c02d02e58035247d00c0704041500c002030f5120b071401d2884052a4095004207204829031242e1010b511510040c0084e118601c0c024880b1079442404841240300000e401444030311024140b0100c050b58998215036203a215810840350918007005110805411000320380e04040030356000d104014240c0705c615660701e042034800785000902040422191510303811a01c500031000c0c151600000c18030903850780c640c0c20130080c61300c03503942d0040050a4001d015002541c42c840c00c458400800c5007000131038036600040e000b01a0780c040c481c440448900c040014604400c3c09031078194072a49030440040407030380d03101d1070012680d040ca108900d50908900c48203405550001954505032603803801220054070031003108261500c190105d2826072030029000b41224480d10080c810341e07880c0c03480e43c4240070005010210400e440b10061 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 275494712 1250 275493462 275493469
    0x804090c030903141b030403050d020105060307080a060504030c020402190801080a0b040609560f04110a09060302030c040207020a17010f1404050c061c020c0a0c030305030f010f050f 80
    0xc1400c5030030030850017031907851441820304580c85a40f007104c0c1c60384414808001160280101c5501c43c808402600000d807408010a446002c20300005050035035820004040501480403000c4a50700544110b45403251903881040e10740100b070151010400c48800010700c0320001504860b0b0650145402c6081d4680b41d880f100030342080c02c02210154100410003e0211002c50450346520849420b00c82c050030150807180060406c42c0110303600500447c5000306040841111a0065103410398442695210b00340080b0310502e4581c010341c000544100000da12142d0303000141520300031020b0703440e900030380c00402040b449140300003500003100070420410304030040300400c2d9003a01030f0b001013824001c10410108543d15250384060420b40e010038041800380c00c003c40c1110000544100b4517025043c0c0e400c01c1e2010f00e541c0c1165503e078001440c5010f03940280447d0400907445601c0108003038880c5405005504103c6882054072081c03400001c501e078411242400300d41010b080303030010300c0180003030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 275495962 1250 275494712 275494717
    0x9060402090d0f06061d040303110702012c0303040f060233090109060f0e0d031512020102070503030a02010c080901050c03010b090612011806090209031009031b0804090c03090314 79
    0x1c0d10116a17840c0e001848000c6280441d0b0b13110003980250344d2078078283c039001c1d04541030223203110300d014014420742c00180d800240040700c07500d06440c0564018094404840c1c0000d590031419018000842c000801c40480c0307610009481c015003c0c0c034103082d90076000e00f1200e408500304404d111400c00094420540d010241c981007090500045070380c9070151509000d5501010321803900039901c81c01c803000d0315414000726034018005c0ca0244820341d041c0054151218060107034050500350002040110382c020043d0100400000d41034039200e40070024080c0c0200f010880ca40c0c00700309520b002528860061054034817548600c114581180d08021442c040761708090006a0000c2041003541503030f1007004401c50007005481e010790700c1060308015482c142e031416840b40e00140e005001d024541d940209045149a01c0440001005000e40c203044842c4e680c200322641c20500e21142c00303028840ea940c0108141c13200d841f418803083e4a800021401c44810315406030006004155070882c9603480f000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 275497212 1250 275495962 275495993
    0x30605150d051911072d02100912050f0d052805070203030c0d031d0a0b1f12031b0201170408270310060509011a0d0501060e09060402090d 61
    0x10f0314a204042003020800316041c09400000360940840c801c4c4c00c0089130714400c606107840210710711000448400c1050f480c108540024030a0b4084824545143d200c0c0386a0002002d04a82d0b101c480c40190600a40314001c400d000c01c014007801c200718800320f0003402192038000098405d0714280a400c6104c0315080081340300c0324100001086a6009a9420005040c040201c1009000b002c161030720084c0444998002007407401510a00c0030345154004034003080d801c1d800107070f084030550700c0708002c00d8824941c2160b02c19408141c0000f040e0822018010210356104c2e498608140400a8050300d5030403100100900051085404911850100038034640207849445200e0038081d0b40c02104107010701c443d104660401d04c44503403510780c4c030b020032404803040491001041018204004241181d005000740c0001b40d40f0007008543d1000848201c4105100780f04007002156100c0200520005900c10f8640c8209819000708400b441c05c4c0c030840c0c0c20501e00400807400c40d21140d58440c0e00e05810380 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 275498462 1250 275497212 275497231
    0x60402030d08070e041e0f051e0a0b0a06020d180f06051e030915010504020403080a0516051507110111030a09050703061104030b130201170402042a030605150d05 71
    0x4c0078040c05488900035001c410042d4103140c00203a541d545098200c0304518840348105d424181488004407403000304003c82c00001c190840c29079a049d40360f10103024030503001c60300a20041c41c001401076000c0f0b50040301003400e603560030700c00d520072802031407661a5000380c8a0005440400b040481c1c003540052468200c07554186c00f60040d5000c0d404126002141c08018641260010380151040c401000c1e02400c4200c90440c1400d00b5501c82c5c19041c000d0b40d40030004d1000000d40001c502e0391124201c94000c0e840302c1100c42400941c0002002003c040d5030340d0011400601d04040201d806004e101843c0320071412403411a502c1220001c040e02420304140c03081d00030f010010020132058010744040c4c120b103050b4103079141d2440c900002c2141c4004d0024803440150052a80143c1e8000640321101d0410500d42c4419201e0f80001802800b2042c7c41c0500600c102d85845a424010490b108000880e81c50412255079076405101854035141010350201c0c40802007104000c120b90320103900300d801d0310f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 275499712 1250 275498462 275498477
    0x402031018061b0906030e120a051201080307022e0e010c05030c07080d05040815100801021602040f0603020a12031806050909060f06070f050c03032a060402030d0807 73
    0x1519240308071000b071010b90301480204407080f1200750300120840010085071504102d1b503040003080725219201c2c040c060f24168400502c0b60410b902c14429503854088034444c0e0700c09540d40700d038a01c0c1d4950207140100d0041e001000400c8021011114a540820121507a2110390101000031a49003110a038000d041c004090540c01c007081080019007881ca10820042c000382d4100b000f442e00c0c040510300c0c0303c004c0103410403040c000e07040085046141004084002000c80e181c900400b01c4502041c0c2042c1d03000d6101080c085114282d80649180c50390090758100542010500c03c4407e031119800080c1d0008200882000034452040e400010b00c0e007e440c0c0101952104541d804a040c100da01c400d000900c041069403040c581540c48540141080f500d64500b41426404101280240300018185400b0554001c05000d014003560000c03100040981c0e54565a012003a0b0a082800136082558000c1c603540d1034542c0782c005089402036030010010302d5100d07a10041220b00c0c080040c0402e0400065 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 275500962 1250 275499712 275499761
    0x61206060432060307171b010302040b0c010c09050f0109170312010303090e010603020415030b0a080102130906080a02061c110715050703050c09061312060504120804020310 76
    0x1807040111403081600c1602e0581072100415203081c01c260060780c08282a000c2000c45030000141420424500803580348601e00c100b8010380080c050b690000302d105c0c1c0c0c001007101c1040c1041d4000c1041110710b0300c90102860f1540148440d88620680305400315915020a1211080c1102042208610001200d15210060f4441005a04203030300c100c01140100d80140b0640c032182c08418054200c80c9421030615181100311000d4900b04040f080a065642c005079910b0b0301d450180201508051009565800380b02181c02c58485c603e10660001500c2d003900812440000300e54518041d800805190400d0340082d1500d12482503c24036615040d0356030200b204031480362000e000402c3c0109120150108900c01c401300b07070340e8010300010070075140c042003100d034005140c140c480c1d01d8016207000351515850f03205042d0100140c0c00403000b07880032644030420401e02e40c118512841c4a031194003070700154600151441c1e407054600a616030403024481c2d500d91029480780c0c615072803445807898011035 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 275502212 1250 275500962 275501021
    0x30d0f110a02071a03090c0f040f0c0e03011103010810052805061206040209041202030906131a07030e04090204020405060d050402030f0312010905061f02010c080612060604 76
    0x400503610150700a000d0030408800075038240c2c3c5991213003050341440c0d03261002c4002e4841c5400ca10b000d00c500c00606080c1101d8581c0e9011341414a014801000001a8503070086c1c01500d400c080715110390700740501c07240b0301b2400320107507412904140700410306003641204a1024000c000c204103ca0117110303110031203c0c03400d0510301949600e19440010326050900a220711400310b90100300e0a907001c0703400c3c08010380f5021025903100d41c010307820100c003a2090750202e081d84035000500368801d001148092800f1885a848011608a01c450302c1c3c040d0000d0b0356494050148550141c041050151280600d0506401c908152440100014039140d204c40c0050035036040700100300c5800ea43e80007080110304040158648540b020310003181009106048140031080c1400303000d405070340b5100414a075456090a40c007880380b001804000782c2d4103c1030000d00a141c1d950009001600f01c8011444608000303d003824003401d03d901514080c2e5914080c8000b8240b911001c440c1c2851075500c60f070300e600 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 275503462 1250 275502212 275502217
    0x11706150c06150f181602030409380904031101140a09060c09080a1103010e07060215130f390807080105060a03170408060c0903011a03030d0f11 64
    0x210452000482c6181850a100700e94113421856405654200c2c2d0600e402c040c070f908140d0380060700000000b002c050b0010100c0c114011a0300c10541079080c0384144034880d500006940a00c40c0181180007100d0313011401e1844615001d82c0c60f5000390244010401203480380c03840c0c0410041010004c5601035640c03880503c2020201c558070b0802c3e50700c1c450801003282e203000f800c8402600d8540303513048900b0304e01c2d5039444d0008450002e2000d40700e10b0300d9901c240ca082d0400158000c031035041d1000381c0d41e200c0c00603444000c886105030034904403100180d10051511035502ca0350742c04c00390314860303a89181e40c0c103282c441d0151011001400a000c03820145030211880d60003400c0742c0845e40e400c280c0b50000301b5207002401d4002101c0741c0d05090400c40c1d65210200c000040fa600301120141003186c1940320b004510451f080089640511310810084854460061030030700710503002048842100c1c40e11545130010142d40d070360300d904200014200b9100030b8112840110540030b00080010502c46441401d5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 275504712 1250 275503462 275503471
    0x2060c03070c060f1d22060b0a03020316020f030301091d07080309010e150d021e030705090907080403090b03071b0c06031d03040b0d0905010203040b060a05011706150c06 75
    0x49560422a04155000078840000d00c004101c03000d444030712170300160388880fa4034805404942400302e40900d02019420203402081c0403040c5580d01c00c1d0f0101d0047c080d40c011506904000c04108620300305620009e0005041340e45040614207517424443c4000181c200e04808222658000000d01c0103c3d01c24070803603000305503850045035644602d0b0000b50848402040380ca100d00502424040c1042c09002210b900307108040b00140d4450700d0848030349040c0c401220459690b0004003c0101c030682080051000f003c00f120300e0241e0342c0c1c903101c08440c801e1342243c000300019200841005006004000b0f19013002c8a414000441090f60700032000c0d003210700170296001c0e49051010000a82c0501c102d5210b403420381c07110060030f41d43e844089d6403446644076400b1500c0c4009403050000800303500c030088065000d0001d568a00303050510b41000102500c0b074070311508403001c0004466010b00000d903c148543c00080805546000410115500da0009e0701c11000c4200012041a60180220ba105 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 275505962 1250 275504712 275504717
    0xc0702040e0c04050a02090d1509051905061305030a0f030618020d060f031703090c09010e060307170c040e251406040501140310030c06120b03160302060c03070c06 72
    0x2c21980c00c10841a544040c0c0f020300c88520405c800c402c2611119030240d0107d802c0307140c91012550041110009041001014100d8042c0c01282ca0350f180301031301041d46544c0901e0172102d00f61944140940b801100a4004100740d05c2048500d51030350044038800100c40207030500107150b035504c030400c000e52109070740c4840040f17a0020358000c50076554401c0d0340c041c000c99405041240d09660b1000c400314480c83c1d0300e0030000e0001c00019584ad6080101d02c080719400f0b0040141960b40341b612005416060342c24512a0044881c082040759581010106004c284001401071504070f40600004200c403003120206402030646060618021341151481c00b03400c0b4810031800380c50500c26034009403541c00218441d400400007085180c2e4400b0041e2480d8843e94030300d0360750391154903071811510481c1d40014080b0f0220722700010000d030810700d40c0403010344085092241080320340805032135203281c180c400c454a162000600c003605040015206074690b40c0101c1c1d19217400c0d911090264081540030800 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 275507212 1250 275505962 275505973
    0x618090309030601080a0f02060f09030703241e0903050c0a03050304031106060102030a03240e1906050603011a0d050a0c11060f0601030b0103182307031101080c0702040e 75
    0x41c2420300704001c9005020343d8002c0e0100c44840e40d280f0085aa64200107445903202051140102100400301d81100b200113040728002c9a980c5040c04004011008051882602d002c0443c2201d24502401900a42e0020011603604010007044010f0a10b03640c1602009020312034104c0b1680f08000c0c90050341d020b034440a40302c0c9064900180340d000018040300342d6170002401d100460340c000050355007e14082c1004681481c0840e4014151600e46500302c1e0280200721001546540307224045000e0404c5046440c2e08407015080742003503456903c01c440d0031800402c0100700300c203c0074103401c604180b442501854510001400c0c0299107060303492480b1941d5900340030328020342021040042000544c0648020315090714540d03401ca6004200c00e05050319400880f030305030f21071741c03181c3c2d65080d22500f4260740408505007002450385017003d01450120152201c81410740014481044030f900048081403e0303488401141d500902405050f0f4415062007001e00581d1180035046100020b4802402c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 275508462 1250 275507212 275507227
    0x2070501060807030f0605061c060f0e03070f02040f02090612070e04110304120908030d270f080702150403062a0207050616051203100e01050a0e06180903 68
    0x500312290742d0300810740b641c488941000001caa0150910b5055045100052166104408038154410000d02d02110705103804060040081c5603001c540010350350b0300100b0a0300000c001e0107035207102c4e10002406000b80181018014a429000f50300507a87c00c4c600542080c40c5180800c2150300300c90401d0040404600811a40e41d0740300480f5504080708640602c00d810f00c803da070852511020700040c0c117840503000210481c600400da40c0b4000c000e0482225a9502c0e9488070200a01154400a00803000741c0d0640c003000956000c0c5040c000c0c1c010700340f1259030040350781e00b400740e52061204076006425804008000300b004406070004500580020a0a10000007400031000410358401043d10b1400034413020306600003a19020f80b407040e12115514980d00109188181d0f2400d00200648120301620b400d04d94500040c41c040d00540314901100390b203d001e61200c040d001d005664100403071200c05c0100d10340c0c00340c1203608980040c14410310740002c0441075944400032241403e26520009405 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 275509712 1250 275508462 275508473
    0xe10020a0915080f0f100305030a0c2001090e1b040303080103050d11070b0a1101021308100905030a140d050106020304060e0a03050c0409021201060311010801140907030f0902040207060207 83
    0x100c9803861403030410300500e01045070b4640c050010f442c9044000c07400001501b100c030b613240c6040280da00101200e80301c544080004000e0402c011007182c5040080d00f90700400b41501c0fa49440c0788030140c68108405003850711202d102c00d8014440003078200800d05103003001d038180c0010000345000f50b66007051581076052052071300104000340380400000c00c180036608080464000280c2e40401229650740240007001c5800303c0070108441120351000036001020402c807244e1070202c036a03000c1540c1c004400003081c841180c20403d0081c0440d0420450000703001d10400648600c000280801410b0890a012080413910240c000d0005039000007024071005821607081d65a00500700d07044102c650a594070b0f2a1200181c0c40000d0045444003030040456595020402d400310304000200b20203a641d05100025882000d40203020881e60000807030000004c000c191248540070300022410340340c2110440c02480c0310300e107100d54540d41d1140c200050f902c41c0000c1c40414012000543c40300d10b42d0030301 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 275510962 1250 275509712 275509739
    0x30b0103030519081005010e01020c090f0417031927050d02010608070308040b030c09060c1b040606020604030e031204080c041d0607050d0912031b1407060e10020a09 73
    0x750030604c00340e0020046800101441107060340c100780b03020080d0b04107200040c4d1410b8000c00344c480d03000c910007041182e40c0e00c4c013541c00c2c3c0c4a2806800b05201d0801326242541c3c65100581c2c440100804100a100c030b03202c00c40d08040e10700080511f80c00ba1131041030740d882803440b605180c12500742d0080700260359800d5090107114041c2401802802019145646140080c8118800c40c203a5280100c00101d11a1400d030a0700e00b044405031003682d94440300c1c0540c640301c0440e001c032881d44141242030042030b801c00344100320a640013500280780700e407200d440c140d0780500000017040c0d061159204141613000200d0280000303124100051010b0184002008196410391500e2840d0ba00c0420310070b5980000016025001249070030200d035a060140407100190140302009000711803400c0810340015411f9000c1031400d00c42d255104104107003001304440442c0c1040c2c60204054060000c040403032403503800301e1003905282003202c0003085406000c0c07060f40c0040b2031381004211500f800b0004492000003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 275512212 1250 275510962 275511007
    0x905030607050a120b1203071218051c050106060c0201080f0708010b030a060b03160e04060b0318030c06040b1006091a16020d08091305040b0a0203060a030b01030305 73
    0x6411585071501005000780104128201007004480d001000044668440c0c948050003401c0844010404500d4a584c0d9021817001c6600b22880070504800d11b11a29081042c904110803030a603072480c1000308a900b00407496020064280082d4443c00582c00344644402840152070748089400076000141c19a032000382a0042c2002c3c180c1000b5120341c4c0030060a055400c4940210345075210001d00c000141041e41040c040c0c0303800003045c4800e180b49055154064035155598424480101040c0030683d030003445480d403282007e00209041e2050050102c00d070241c044102c03030410703401d13060591501205a0b41a1442c0b030000c0709001020f0340e04003140e0090107844c104040018a000f40301c202010884211102e512404990301018106030703050120780da034004024a494003c84c0c200b4035220b0f40300f18a154030400c204021300414a20901840b0301c5590001c08403600c41d500c0c00210030184d80014000c070351000c400b441c0400054104a03005002e580a9074032103480c0c2600703c00700002c028020a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 275513462 1250 275512212 275512219
    0x3020904152102090703110c01021c0608011506080a0e0625170c030402011103130f050d050601030f050a0213020a09141c141b030c010806090c090607120c030905 71
    0x240c2d840035032030354802c454000c0018900010321100d03c0005840c2c5004000112605c1d5000090340348015954503580e084120010004024050360780301e11030300f2500301081e01215900f0103503041062034011906164080940003000c05c5400b190740703049050503022150b00c04035000e40c40312801c1d0034404014090710310350203003040420242410740715414181d004005141c0000004000b03011a481404680103030302048040b2919410902e10303101c0703480814001d000c0ca61000c0c7d50005510714000c0d0881600303c4c1c12801901040e421600e4010010150140507102d1344140700d04040147c458034920405048450720068039181401e0008040d1410342e1301044000540801464141d0780d0000045c00d100300a88200715500e00c4c91031310b0108041111001000760142c0109982c00c501c83c41cac6400c2c924007049040d01c585250190040d00c00030404c0d91015000149100054460300d00c08004114030f840042409003440d0a50396100440c04400d61a4800114084822000c044d040b0001070003800045 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 275514712 1250 275513462 275513519
    0xa0801031a040f060c0203090d060507121506120b030304060f030f0b060319061a0417030a05091e06040b0d05181c201509010e070501050a0302090415 66
    0x944030f492440e0742c18140989002e0366420310b104d4550080080742c003203035006003030001d24000ca81446030040c4070444040c0c0120718507207080c241103001e81c46190071464030b10b400f000c6c90038104030044420b0481540c00704030841e0340d115652661340d801c00c003a000904460f6142c41040100300303001400d5801c4084040301d21402d02c00d603000705a44010559605c400b00f840258403003440c02c00b05201400540e80000c030b00048910341041c45410302c00080041d10451003c100341c21040f84c42155407440341c0116080050000e00c156200e61800b01c040d00e625a02e90041240e13801e8202c00040d40d1503000d940401044500001d83c041c6030009409201d902c1038040218696400d0f8644034980c9800046010030b40241c8003441203100c25009000600701c4082401245c500d0340d2079100c005540320107c07000140381050410001d181e110301402560b680448602c0540641483c2600540716500000300102c03e1540a110800d0140c0b03807881401c1003643c2c82c00031203210300c0c940901c0d00340110b902e1000b450b00c942c21 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 275515962 1250 275514712 275514721
    0x1020606010c020d0605090102091c170f040f0e011a13050103050603070f0b030702010b0901030305070b0a0b0603070c12020a0b04020609030f1204030c06090e0f09010f020a0801031a 80
    0x214500380e00c9802800c0c500b00c0610385200044c1544880c120082c091352414090101c002015405096141003d8130483d04c1500c010f9170304a0b00d00307151400104020b908104030040320440d4005800c1c0352081031030f141d08068450022480881c01d980155081600000041207240100d03000c11007510303a102c1e09980f170140124075170816200c240c040e8174103154550021910640341045054001c0042502d402c0200380c442030384021552090310310100641c01c041250081d890310f20410b0381201c2c0d1584070030340703402070a80d0784070000b2500070123084155035a008060140d84644008520408031561034080b50010361804a4803446c036024204210760101008a0014900340d00181d00070b03070120303211519090b10800280c649032110b0500c0c001d80c0980307400703040c0c1034807030714090001c1c1c03071007101d000311925100d2600310380741401c078498061110001c074041200104403070511303a0030044940c0081640c00c5011100c009983c0541041c90004528500400500101100060760514141001c0d5124140b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 275517212 1250 275515962 275515967
    0x4170f0d0905100e060406050a020405030a0303050a0f09080306130203090c190521012a1d190e09010b061215041802010201050f10090c05130b0a09120201 68
    0x103480301408095559600c12042c03010800400d1030401c001d180500c8081d913021005030700c0c0c0000392000c8815a080501064106c0580d0080d0340a51b04064000d201c04680f17074400700d024000281c0060002940c41c0b400001c119410302840784128001c0d005039559003017203414044454500908040785910500900100d24004684035841310411181101041070300c400c44512180c5a40c441e070352010b12036030b81d10054810342c02026091081e06000b0461403062100b108018111003100c4240c41e8000900d00c5c0256024802001c1c112000040c1d40c41d951305c220010520500210011081c2c0900c1c9007010420f481c004031800ba80400104000d1011501102c085802030047c040079141c000806030005540c0303821080300c880e019100520510405071200817071205d4100101042c0d0065007040c0010b2000e54400e0b4440d80529002c50851085604d00507100c00144808a01002008010090407004006224004000e4910013000b01c1d66804040c10103032170300c100c0d0762007401103259041031080541e8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 275518462 1250 275517212 275517217
    0xa110a0b06060c07080f1c1704020904060212090c0316080c010f140d0f1a0a0504020d060b030a05090c03070602030322081308210711010c020a030b04170f 68
    0xc01502c515485005214002c0d0500a01ea002200c1d135101c1d0f0290405c5405000643d130014041041c2c1c03910540c01901c604847c100b680c1024480704400c0f11001c2001800c1c00b86034968858010140181401c200b82549504058150307003c3d07140b41e220001d00115403405000040c030018281c80d032401d0036890101d40e03a4450034550003080c1070141410191100d1406400007180d01504000b41c240d460300e142c800c040080004d017610841e00c41c54002008038604801e20540c82c0f40000a010f00c90709450403041001961041d00390f140c8441c0c843d1742c0051000e2000c406507000710390034103010880c1d01c0c05041491a01a070310030200d100e41e01040e403c0000c01d0700801101c0c0c1040c0241d52089003a00c10000144500c03520000041580c2c00004101505400d440107000680707100e0806d44185d107240c10702040010600c0e95540c0c2221404101c4a400100d0384e60544240301d0040c18500e81c02c130800d80016009140341d503c00c1d0b90300f0741400204410425900c000000c0881031800c890b0031710171219407800c21030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 275519712 1250 275518462 275518471
    0x9040203150a1e05090a0e06010f060305151c110d03030905160b0d02090f1309050606040c0207050603060a090905031206030607080a09051c02031c060501140a03020c0607050a110a0b 80
    0x10b03031700d080224082032150380000150a106070200c2d205941c2d2044405041142c610070100068a0714010840c8165102010b10350200c0040142c08180000881c000c1110100d0310708583c600c58620701d03400390780c68025240f55118040d880c00115110305041850901034030000c010b442150420301400310180c504180c0c0c11101006900503125071044010035442042040403d60080702c3e09801007401c0700c29040415828890300a90320141c55900500c070a6501000c00d030400b41c0c118003014845401c01002469010000808540d10660759804003011560418030a035280c0e000005c0032180b03003d007110b640782c11590503001000c1c0c500c0c10340030081212002801302c00d081030b2694030784000c0c010f0400c40b903050601a0040e450390411124006036503a07100d103070380b000286145803d07070721000e0107480b0b003c00b100e8040c4c40302d15401502030401c0c21039502182c54202031603424000000c020500f00a0340e0312500c42911000d5540301842405000f042c5004007404003648540510400546400f0446400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 275520962 1250 275519712 275519719
    0x71a030f0a0905011a011211090618121c0f20100f0c020d080906040b07180b0a0e09061003020915221505090d060209040203150a1e05 59
    0x10348031070024001804030341c00060070541c2000d1045d1034401c12408283d01d100c1e0b00b40c0b03a801c980c02a0010340429a000002440c41c13014007805020454104007004104811100480000c40004080000c100b10520960055517501103118040b80442c14031000c003000c40c00d4181141d10082d000300041c4800c411003520030700d110b0b1840100c03d03829010041c190701141c5625052040700f0581c180a40108140d000c0c0304010b110310840000b01a0203441124010001c0c0c2010f40040d607a04d4980314610300d0301405c04020044011005410f80c03030340c48005001b0f02503405645555500310300e801008042c01054403441100c030807041c40b1030740d51a06686d510402440c100961269075100000e11400c1903840164101c0c4800180f119014400803140005501d8624a0746800e80e12000401d05102e81c2d4010040032803020400b0b040585440040c00000c0c41c8540381c0075261038100c0e0003141c01e030b810a4400c0090060700204401d200d160260981c070103403001c00d210310301c9010161121841c000c8540b140b130b0701 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 275522212 1250 275520962 275520991
    0x41508060c1303081602130c0e0d0c03050313031104020301081b01140c0705040c05130e1308040305100c0e0604030209100801050106081501020102031b030703060323071a03 76
    0x10390b412901421801150030a82079615201040c4620200d4045000201c4c03003800c251103080101400c0f845400d00a0079aa80c0c1c540c034440350007041c0010040d00000955040304492030010004074100700516000c500d4180c01020207103145804a84e04204d02442c600c203a00601c0140f001760400606e40304034001440412100303460310401a24810701c5c0e451911408800000d110000000008642044403c1a20f0402c551441c44e107045a050203000204207648442032000c000c0d050302115259005221400765030809011950f070451158040d034821a56600b003811310040555582c85222414140b80c280f0714034110042e00000c0ca24402d40c04000d11400300c010129400c80c2c5548005005030070840001c001c5540c5a9001902200003119240c01c110307155010414254410300a0324061002600e4005810b07528001c0c1c40e420b5000240038400700b44e6204000000b044005a40314a4007030b0210200a211040360780c0c15080c1106a0032900910410003800c0c0c1c4450180c07400c5039030120701c6c1c6006c2d01c5c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 275523462 1250 275522212 275522227
    0x15030c07030e041a0108100b0405060d0f0203070e0906010905010807051c0c0903022b020108091f1b03050c04090507050c060406021809130305030a02040306140105041508060c 77
    0x40741c80312014070b00c0d90041d01d0320704084201000c2d00003401c01913009884001c01507881460084401c086c9010710000c0c1d07007085c882003296040c040d002d040c10358404a000b048405500c00c4ca0070498004650540008000065103a02802c150b1600e80c1c02c00001e107000702c9194100000640b18040c00750690007000400141141d800d2620000486c0b9414481c50a01500b1110302c0d000307045a07030a001c01d0b8030030208001240e0030201c000124074000800c44440b800044032030b0300103440841008068003030a014002090405c1c0c1d40002d801011410350788000590801c001c0444140001c2c2c00d03030048149440c0100380003440c00410b0030359088500d0b90802080995809804903528005c981c600c200c3d911400d0240b0082085680290590800714131805150303601040800991034401e4454040030ba26080c41500803a203d04025603100403c0c0c000136261696990700c10007110000034400b0b1031b0007a058010b203c540f0781030103600d0900c01d0003c00c81d0783c941d0a003480d0a450706805010380342502030019404 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 275524712 1250 275523462 275523467
    0x81602010605150a1b030c08030606090d0605012603031605040e010609141c0f260403020906040203091203040201031e0b040f0c050a030b030316050a060b15030c0703 73
    0x40301400020f85510494040c220035a91503420002c0d4050100f461001d5203590300324914014040300b03405546802c80011130340c5a10340e0359032010341040d4018008118520b0b06446010108030460b20829000030158586114009141e0310001c0d030504091440c010714120314000000d41380c0002500c3c864410f4408503a1040c1daa6100e01c3d4030031050082c4400000510640100e0000122104100c608503031501500400850301720b0025440c031022240c0440f031001c110080400d000d020f216000000d44050703001c0c1400c441d910541c0e125509090009803d00860909c240c0b4543c02140a680c254110b007000c400d5942c403000c0c9100313404013090b800b000181c1560311030380118041042200850a10341040307241c24002d8000c8007011405107041c6000120808454420301101405d0340d500d0745e00300700e0380c508124064422600c043c0d50622041c040314210040d254862003004e803152006169007007951515509a1b40c400101d01c0c842d901e6003420b1003401c201a0102c90b4000d400c0e90205540780b046190a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 275525962 1250 275524712 275524721
    0x11031003021909110c0d0903080403150e1b030c0d020d020603070302090913120807080711010902090907050a090e0703030804140a11031605150f04090c120b030d08160201 75
    0x2c543d880e07007040c0c0c4401450404000400c608002e100075102c034001051010b8540b4003580c48005c1c440c8204000410114000410285640509240124800301c8032500306140500303091080d82075524581d404a40791400b000303084a040300541d1280e202c8561034002614010b040351001c2c0c0503440010004144c02c0c031035412101c0c2e40f10010700802050400940f00001142c2c245000c8030007045401d040c0c80002e001c0d004241c070a51003a6aa49031581c1c444e60100d40940070000701e44025074940040386c0069441302c00c4648a811580002c1c03800ba80f078401082030f603407000c0c0e00c0040038600c4c003d60f0300581a0041140c0c81030340d4060800c2280c603102c1d440c04941420014041644902441c0074642c00c1003013406510b4080e4608800b2500da00c0404650000c1e9104181304999000310950010400480860040c20f80b80c8500c03c1d80c00e04103560b484404041d0b07884801c460000038546002d5080e081128410310207840000d900806c4614a00c09025020b82005400d800310210751000c01074110b8800d421 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 275527212 1250 275525962 275525969
    0x6012603070b010f050108060603100918080415020d050f07030804020625170c07050904061103090601030302070b07020d20040c11071203051207090e160201110310030219 75
    0x40000056944c0d04a40002c20110f000c0e0390f000520a00c0800d4440c0b07400010380740076080d1808604000c2e4582451714004100065400d0403540e81a920705010640444c0944000c1c4041c04d05445040b405c018003d0521445d99121402c1c400240400d410071030042013603c100d582d00d4202035400c0d4586000158950150344d0040500020050f450403400b0703604002c64907218480c0030410031000c0c00b0b0003401c009004582c261078465000040400a81c50212245504a80220380005408480030454200e50f0300840d61040700f540481c0c010401c040d4100450346c0103000281045003016525800104522002e18000d85076103294070041c584825100401c0c0784481000708104190ae482c0da101a20341410116004103500a0311000901d0303925000050450690687e5506d24120b220f0b181c4000100c40a0000d504010034941c002c81c03c1c80000c0c490314043c036084401ca140040302c54000070700707413600c1c0f8111074180d40003403080c05229440303100c5c01010360b9030445044613107040d150490b0800340e03020750 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 275528462 1250 275527212 275527223
    0x40c210807080703170105101d0301020a0c05070e0f0604021c150302011103090306130609052e060f1205031606150801020403081207180303030c110601260307 70
    0x980c0070801c0b50380802021064440c1d02c0790409440d00090b20b01810f4402d04c81c4039081000e40d2403024241d803040090200d82c3c52180820581504600b0110b422600b0520906000c03580d46012402031141c02c0042000400c3c8113030381c0050710700e000c0700c0641c1c0c03d0501a001c075000d1600031850400100a001004031031801560080000c0e612001d00b005040c02031b407006a0105258408480580c0b0002c0100c0302551005002019079894140080c480b4114500341603d00550b180c0761751001070800c2c04122007001098080301060f914210884002600a480002e00d4030324002c01000b2407100c42078840c00702c0388154010500070301e090900074198441c00f840307020a440c06a44010401c000d99020a51010001c4075140b412911203c1d01d500302e1103140006803003103a05101030450080e0900382c2c56030103016841c261210b484c0310550300c02c01c80b40580040b0042034440000a03000395100b00d00703c940503694001000c2c10352405000c0c0c121890500d20100343c0d1040031045c0814030504000300c0740d0096016 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 275529712 1250 275528462 275528467
    0x90c03010e070513020c03040308030c120f0703110903060609100e090102070c060f050f1b0d030b09060f0105070803040618030e1306141009080d05090414040c2108 72
    0x1c1c0c40d9500c40909010b8103101e40b03040c84141500d0308562013070f00d0768452200e004500e014107645624015400051030805211410010b620404144040da80e00a0a405190030741c681048070019042d18140c00701400f4065003030100f210980c0c2d000403000e4100a065480c1001c40e194100c00c042900002d4204850090541052118855055000340491409030b004041c455450302011601c001e401e403501f20008805000481c904c8030490020241e000e91880300016408110408034100042c0111000103c2d03a00d45403401d4908040846070781c41002120041007004103000080c0044c041c0240207004010040000f0f000c0041c59408034003020b0300360350060155480c500c0e0041028601c494010300440f88407603000132040450080c8001e5882040030345c42c2030a950420b0ac0003468241d840c06080140d1080d00150301c0b40e0900140403040401d07541c842d511100301c403e01050340c051901d40c0e01d03000d03480c20030040402d001c40b8900007500d405030072200d000c1110204201d11441c040c94081c2218400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 275530962 1250 275529712 275529731
    0x9040b09010b0a14030601050307060807030f021b010518030a0f03091b032109140609040f020406090306060f050d080a03090231061a0c01020f16020a0b1908090c0301 73
    0x604c2006040780108500719120b681e2580141034a03083c0038402c000220700c046010a0100f8040d80144007064000300c00142045200f1b201030085c00c1c004900109a83d44d10414042c10f20040c0c02042ca0172010480110310740704010340010f005078030304e210040c00c0507a201030103000c1200c0ba99401605c038400000101c42c003601c908060640b00d5038406541c043d002c0b99004100814010700c00c44013106c0900544840c1c45034003e00340040c0303a0080070702641c00356031070a8500c2044041e1010300b02405a580d44d6514550a41c03812004440068012070f580c1100640c0400031903403092540034205030b0004806890742e541c2601907020300b030014030080d070201040e40c41443c100d2060a08012801483d4003407000900172400403002c03032300140200340007482045001c04e03410304014004d221001010000510300f0701d800441e914260821040441590054150b040951178110b60b00300103400001062403030a0542b0354200d40c1c01c4200e90030441442044400142440e10600111110004c090002d100c1c9056 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 275532212 1250 275530962 275530979
    0x61b0a0c030909050103060b1e0a151715030c01020f0705010c140303090a02041b121e0501090f0623102a05070f06090e0a020403020d06061a0909040b09010b0a 70
    0xc0b466075015222700001c0344801004200e0034002003801400354030065040c20014035100c041e00500c0d83c01d1150040054406500307c0c02c866220744442c0221a80101da00020142003400340c520301411544900c5148e030350b108000c60042c2c01c90310242050b140100303040c0380110140d01da810084000707000101c02c00c01c01300e901048540b00b161003268200064520481c111208980e070103540000990b1800da5800c0560302540b01d00c0721141518506100d05405420384429580c0903040191a561101c0d50204036107032a005407009000f61020a03450403414070034129403c1819846540300b210a030f03070354a010901400d15071a8001c1c0f241078003058105051200004003401c000200c46611940d01c000406010540301c40c402d0395010740d80c03d44410f103001c0b220b59107614040d00742c6020036420130002006a0394265522500313807103981f000c12058501041008d03484000610343d003051070100b080401964a038551594403035400080c1a10039281e203400140140416410303070f03800c06442e0501088410 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 275533462 1250 275532212 275532221
    0x241418030319090b0a02030307080c040503070b04091407020a1e021011060106090b0703050904060f0f0f060206060a0b0711060d060e0a020903060609040302100204030305090102061b0a0c03090905010306 89
    0x80503445850500c1d030780f0801542c4c50700c90809034800580083c404101d440b4401c50b0403a400c0103071084604d00306500c41c4002414810079500000c40d000002404000e4000c1900403042c4090800c2c0100c102032070664170194503580c2411000b8040401c0c2648d06072008000340142070741130740181c0390782c0c071848000c100070f010000d05050285903882807000002d445881800e0038026a60303d145801c0c100f01403036030f0560b038640003248800ea21a0f10307004086096030780308000d44000c0c401d04c0c1d050345030b036443c0030700143c00b05000350009011034001000b001001d86a13030600d8400c80301b4051b0259901c1d442d5041c101d404010382c501c2e4540c00040080c1034129840150051030075580611520300964452a40d490128410b05c1401505500132200040180c030707101c02e6040e4070500030b005456400b0114040403040340e10a400c2200807441c0810040240e503810001c07103501415103480b60360b108801030402641409220f074038100700001d0540e2003040611a50144000b0440510280082e5071686014070140 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 275534712 1250 275533462 275533507
    0xf0f0c0b0f010311240d090209091617060c030720010c1719020913050406090614040302070b0c030906040305030915041206051509040c2414180303 65
    0x4800c0c40091440b8038000c00d0401c0e519803515005148401d00551001c2c5c43d03000150841202940c5240010250b00c0d15056031744241c4900b00a091800d00c0369054450040540d0422110b08070311000d001e41d81c2400086040d0440c0101440a84076910b0000844407a034118a580301080301081809001c0075054000d40d207480b01584820b4580e483e13120010803001803c0391240180465600644560b0075564000c00c2001c0d000341600c00c41d070f080b51008405031241500c04440341381d80e40c08000180141d0784541d00340d407a03040c400a0b15500f003686009503a10624000c00c2500d060015030160340b41c004004582e11014080e10a54650303a880c1441071300c9030090403409004505078820441c0002c0d0503001c9070165402c0181c404003620140e00c0d010f00030300008110140103001d0613100b217140e07500d55480074442c0d40308810140341030342440100c482c50402d40500c2c54900d0b68110b10480e089401041c020b0910085c2900390303844000c11110340c44d0460f44900c00c640c050000140b0080d13000d6003152800c091 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 275535962 1250 275534712 275534723
    0x30c0807020a080d120f020c19030306050a140319020d0b1008120403050f070303120f0f0617010606030203150108040f080c1c1409220203090709050a0c0f0f0c0b0f0103 74
    0x7440460300d50b031b001d81c444c0109145181c1c02548072140c09505111031940c2c054028540050b4131510303400420088070854001d04c079408010040050203240410460303030790241c1802d1a60005c40c850f8045030000b01980c0b002004900300d0303030002d64000301080000008288010444120040050408400364028081501c06009554148442090024010742129071594929120044441c01c02005208084c25070904c41e86400c540e60074002c440c0110030240c0b80308002400c19007200c071846800c40b03001d0707031003e81814014001c1140841d004200c1400005c000e0a1103040c1e076a4a150003491002d20000040281c140450440018080080d40b981515883c4009020a051301c41065130980c9000745c40c4010803804001462503030078254000b1200c0b003101030300e504540f16030b40c07200320a0303810441c0c44006070b500c04001007180034524000c85401904591003040056811070b002402811100c0c0c44130305101c81c4a8160100328810014400f9580c0c0211030203000381802e40c0070190710070003840251907 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 275537212 1250 275535962 275535971
    0x201060503010c140307030f0c05180a0308040918050a0308041403090603150409060e0f0d0c200105190c0209010806090d1404030507030606051507030c0807020a080d12 74
    0xe65080500c6150a2540c40b9261003842000480004000c0c1e44010b02d40d0307040503141d80c408088400140103103940544103481d650340301d00c80381d50184c3c01c05040b8480740c2c2c81307104034002c02c00120b4003200c111030980d0725075000852112102240d45024510125008008d8860204048145540801701c2c40c06148102c40c1034030103440c11f000483c1d0f00d0260303051950f48841c040001c11145800b00996401c140005003012802c0b1200da00d40303000711448020f015006400520013000640300500070314040368a84e0030905800c051645400c92140d10f0090110104184403194020903800340040d220700d07110b91441c00c072420542e490010001100e180080380140d40d40380002c26100f40225410b171054aa21008010340f030812042100d40942e00c3c0c105905068040001001043c014050600614060080410400e2410080c407205030041c050702a120041032000030300095001070607566983d0010003041d200c4003903000040c81d40071103603c034030006e2160302e84240d90507030814941e40119520050400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 275538462 1250 275537212 275537219
    0x81b1e0d140108060f070309020111060906090d020a15230c0c07052b021f030501080d020a030903080a140403030c0201020d0302090f15120c040f14010c1e080316020106 74
    0x260380390360903981207445d50021800100c40c01e220f0360124000600514041007105ca09a1409040081c01e40c0c203900507400440421401c14010491203441c0c881a00c0240040501901c800a019078040071a0054a403110b690103050b41c0c1003164448141c0c84a01480000d0604070030042065200b1800f403100c0e40a0303400002803528040724001101e008084a0310040000300512801c41d8400d41c104907800081107040e05080316200c80482040300090b1000250795040c00792081c68801c0d0b100801d801c55008185800000e40c5c0045000210399029011648840c40054141c45c001d02c600d884403980d55000c50700000b07240c1d10100002e58507000b83c003960000725a1034421400d92051071003192304450752290707403283d9050410348500324400c1ca0450b40c3c108006058810588202681c032088510b1021400780030701d641984d0804c008040d00c140841000d40e0300c4002900c000c5e090f00001d4041d400750b00325003a00300c0d490500c41040641c481110359807480c2107003c00010706c00031041c0b84010342c030700714021 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 275539568 1106 275538462 275538479
    0x5180f07050109080307020102030a050c07030f03030903030c030b0f0d0305090a03050706090806010f09051801050c040f0b040e04060b030f0604050604020907081b1e0d1401 76
    0x140380c11403408000414002040e040030005810401c14000180c1c0c0000c00c442c1d0513540c13400d240f501e0344076403501d5a0601072507034030103005145c000f00500c00b00343c0d2562004d001c1c5031007501c0421540d050306000b2001c41c0c0582c0009500054800039070282c2d071804046045c2e0461281c5401071034420040b001c1080002031798021140c43d0b00080e07083c005240c0003400800503102c444004d110940c580b500400050030544a85607a096403440815480b5401d40c1410803003c100700001e0280c0e041c05244e28010f54010b108841c1071400b5242c0109000c15402c08580446101800311845a00c464032004020160034030555414401c4020b8409034410a004161255000700301070b281d28a002d005100c0001002406002080102801c10005a00d40c0c100b500c07101c0300d80c0100e07540710050355040b0080c0c504030040d5031140300b9000c40e480c4003846454202503402d4110214100469907503e910 = true := by decide +kernel

theorem cover : BRFrame.Cov 275359712 275539568 := by
  have h0 := BRFrame.cov_init 275359712
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275359712 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 275359712 ≤ n) (h2 : n < 275539568) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
