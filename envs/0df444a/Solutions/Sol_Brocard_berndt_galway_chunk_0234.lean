-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0234
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:38:31.652475+00:00
-- url     : https://prove2.me/submissions/31aff0fc-b934-4fe9-a954-4baaba428a05

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 41906479 ≤ n < 42086335 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 41907729 1250 41906479 41906509
    0xc0b04020f0a0b030705070c080f0c1201020d020c1005071b03140403062d0207020d021e0a08010606030c0f0e0906040e100e0f0105060603070c06140a1a040506 70
    0x101c04540c1c035010101d0300c031645030b500540c10540040244001d007644503004001060142c550b09810301d45561219483e000113564030300b505d80c400c180b4003000341000d51807051426640c4000504168503482c0e4a820ba0b40300580c41c4526130064030340303c01d511600d031280f150070000a19100c0300d5a01d4580d821149006070303420140a101c94100000340312003001003114090743e884141400008404441480b01260010000ea0700811542c1c0744104034903203109898100e03800410b001c180c003000d6020300589640c650403d00344c500ca5201c02c07615940301c0300500c03401080400000180ca0340740100040c1120064160a0100100c0801d0888180d0344900400640c031012940b011080e19480000380c01080d140c000249140101da94156040ca041c1e4800780320301014105441c842d07015043e00c0d6007210301c00c49695500c810180041600c5501c40c0024140480c41400e00050018007021517000781002224542c0e40d4079107401030090040c1e156081c03003035410401d40301440304e070030300c074000400e41c03041038100c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 41908979 1250 41907729 41907739
    0x1060303050d05091c0c050f1908090402040504060602030a180b0301050108090a0b070908100c080115050c0102030c220b041a090904081308070b040302100309060609020c0c010c0b0402 81
    0x4204280c00600c482c4500300070b82d105001401750300d54405800e01c1703107840c403d46503801144c0c05081c2104000c0341900d00324004c2051030509000ca5641d00940e07800c000203032034000350300340004551a2214410780e07000d01001d400551715982e91180042001130030b91010b81c0400d0b440d9000700322809011013902c1c10364400b400c1682090703507003003138507860500c503014080c11003501c420621034555008210304066900000c151410403076040120760a44498540c50000a1081c900400465603c4800d11214103a207240c5140f070402c0070500c00d802d981041d41e0358403a814002036282d2448926015440d000e4809140424070f07503140101c4290180260700c500400002c148040c0b03030f846402d000032a50310203001020844141032606190000d034100d1403503a0f486900b441c40100d003840000038140121030700c00040604e41030850b420321285103d162000d00905031244c1c071000c0015140e0044401400c004140140c8070101c2000306071a01005042c91030601054030351800c0880c99a0480030790064058076 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 41910229 1250 41908979 41908981
    0x3050d0c020d080d02071704060f03050f010e040c0f0e010501030c031407050f07081804050609040f03051e0d05060f1002121803060906070305010905060f120705030321010801060303050d05 83
    0x1800000f0348a071b000014051040040c0e0842c0c80070203c000781054542c40c0d6a000d2070807940c0441601203a5090701c000c0707001900e03000100b00c0401c2020205078024882c050190740c0c04d0b910350710700100111f140c00201284807144010300032940d0501c40c03811041c900e45800d0010550410954130b0050001e0294030403c540046c0d40380b0708101300d800b11201240d01051181e0f8443e620b0703503400320002840304081e11881c04d15010440074503080040d40c0c051034010000c0f01d2244490750b026a0303d580b003201d03242641103c0844c29582082c81c040684440b01e14a04045a90b14001c400c10000100426a81d4494000758a5170b8503516400201704c0407000d0b010800c0b554844894140030301b201085603000307500d48288020003041c0a030100310030f4051046a20144502e03601da03641d900a9a800f00c0d03046401280d1840040341c20320b440809194510580000d555400c1d4403080424110350000500b01d0001d50140203040c002c280508465004014030002042014110b69004000340304070b00502c2069034643c4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 41911479 1250 41910229 41910247
    0x30708071407030c200a0e130b0703050402010f0504060909180b010b040311032b230403020a150207150e031009150c021f0e0a05060103050d0c020d08 66
    0x4140100c00303014074030a09480b11450310b401004501034a40454108403407684d00d00e00c02c0c14640744580030b814024070841d50141040194101148020071600c1c451100e07101078400304a001000500a40a60740d0116480c07806000140241ca140707031080042105c104000c100190340f0503000e01c141c0f0400303c00410050140e400744503d0010055014040729441000060030a140000520449102c1d400100d40302d404041019280d8194a03c0b000269030500401e0011411201515006242c9418440c1c003210b06081402150340010381100e814620014084c810b52500c944803c0003000f0080e08641c08030100d5100035100c51252003199811400181e10600e0b480c0039030003203180301d0740240c2100e0028141d200454041c08440c02c042d161700007017501e0701e64000c189004541541090750000c020006c290361410810003c5c50030024011503403007035101c4420700300380a814202d6001c0c1d0000e08095041d41003041c00c10f0261911401401416070107070006031a4050320384200f82e00f104410f611030702e0f20 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 41912729 1250 41911479 41911487
    0x11100903020406061107081c0507021c060b03010b0a050307060c02060708030c090a09020703080414070b0c0616080f13060b12070e060436080d0b030105070801060503070807 76
    0x1508020742c0541400c2010803001d07440131008610a04240c1243c080583e0b43d5515510303602c1c41c07050700202d50031034060038010700d0042d0000c0507810b01c0a42030390280a890107255a80303852410003103400311380380c81c40b02d40503150034000d01d41c05107000ca42e580741c1280b0704400179664110a208a00620501804103420340d0b842100f03549001d0f4016602d1030707503072a000001c058550f01060708284940181346001ca2640c80a10a841c40c0c0ba0341620340c8105521692a0f02c050040044440360312449408408120b82c090400035040c40c03810380b0300410650910041d03003619072004a903040700300481c41c81000031403a0b42080d00d43d00812041504141004541411005460014141074008800c0503041100b01000240031045616070310b5001050348443c01007009032040e4070f6040c1c007a06000080d0204240c3e80c48011040d2194140e10404441190b9482e0003c6400090140b200f0030750380d4401c40040d040178040d90368045813a03e0030b00040d606103c0040c0581c04080c0074141000b0002c1c00003180c1e42c0c01 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 41913979 1250 41912729 41912747
    0x6010504051510030b03060a0203010e0a05060a050301020c0307021512130804120b04021206070903060b060705071206060b0a1b03020f06090307140c01020d05070515010e04021c1110 80
    0x603010303142c0302450083c09400f501c0401c01e40c134041d1180c4400660700440a1003170701d068412070250300d00c240e2a0740d24010301a01020b030601e1783c0a404502c0014003513400f48000d00500003414050740d21030341240100f000342c00f00000702c11301c070560400c111b04000b1307901d8034425030141c0400e032122010805814440510700860304040741c5641801c00ca04240423103e0051442144212240e00142001c018481d0311401c058411002180c3c403410300b80700007000d9030442090b00b00054542ca080c21280c1d201e00e40b0703054072903111800d15014031801d0780500c907580c0101c1e0003130449110018585030480308000d007c584199101c0d0b2449030320f0344401c0300f014400e204040701c1c0b82c4074404981341401e124080781c0e102d130310a00c0f0868006040d074000310901c080105074441c41c503e05070050310182160032802d0f5101e6000c03070004c41c0c83e4083d105222031031940c0300c02c20301d01a140c10350040302145424418000800c10190900303004801c008080c2001807100c504000301480305454244070b85c3d20400301580c2441c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 41915229 1250 41913979 41914021
    0x20c0102040906150c110f04270c08070501020c0f06070501050a020c160806070c05070e04030905010e06030402091b04080f10050705040e0c09010e040e061f080601050405 75
    0x4000074002404000300d0f0884015180908801905244101d209a945088406000700b00303032510054503140d86005c2d05203103c2441c01078004101d41c0c88080c6545010703083c0342920401e2180320184081030007132180c46800640b030035a000b41038003030a0000107980ca02400f09600e210307046001804405440e44400e491034a82e000c4002d100c03d06090310300b0302c06034009084061a605c1010110714010210340e044808940410700030b00925141c248080390700313951003001500c0e207210756000000d960350b908269600c118002e9131410411743c10140010130785503074011501c1c45050140240805a1342d440009038000d468054600260f006118042006004540c0681000d009404140d4803525010910501e0444c5218080201d565a0711003600c1030300650003007807070a50507031001a10900e014030060450610504118480c0a110000030301520990484549690004820700c9101d003000d0381201300000b0310700b01130a81641030020696441c28140f06441c41107441c0c80205000905800403070a030030b0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 41916479 1250 41915229 41915231
    0x2070807090504060905100b040515060301050d06020702031f0c0302030705161e03080a0b0105030f0f131202030d0501051e011b0c0b0406020715080103020108040c052119020a18020c01 81
    0x304d03421101401010008e81c114016420100021800300d030f00c02400d0040f501c0200028103503400c0c40140300440865403001c030b40c0c5503030800c05040540d03030410100c007298062022410007101103810403419540c0b9000c6200a1600500500150641007000e42c0d103032014000c1c0c403000410b0907040c00c001050100342c41d01d4800840130f503110140f41d44141094030455002c0001e0100e2000703100116081d00c021198071142985a40100300403c1400141d00e0700b003040320724084100025a240c685500d007807000c44402590000802d01603482e00c0d03006007401040e00b100e9550702401d004c884504050440c04003281000300c003014115140f254281104203042e040180c00955075100c0c1404925039000f0b009660251003441c0d000200c001e018000c5c214034004a541e503010fa40d00c0c0d6030040d00c01d407501520486942c00c440c40c000c40c02d80c580c800f40b0a480010003c0d9030401070440c0c91150f04001c4203099000d501501c62003090702603120415018100c812500c91000c3c5200a06603050007801240804e5003d5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 41917729 1250 41916479 41916493
    0x30c03022104080c0306010b0a230f0d0f0b10051308010207030512010e010b0d0506030a051606140c0714060706060b07060c0518040b01020c0303030f041202070807090504060905 78
    0x1901c4600d001e401030f034010204568402c0d030f0701420140d81302000d2107003860003d820404c01600d04d104100c0401c4048028021b80160136400c54a510301e500704c156400c040210116009010011a001d051002c2070030100c01c10489a884011445820424504c01c082c0100003400981c048402e528200082a000380215211407180c41c0041c0540d1000800c1d4803001800800032610641d00314685040343d02c044e01c541d1520480546050203460014103559260244807043c102158050010350402c4c1004650095001e04107000a00300312081d000c2c0d118460b8081c0603200001400040b0002541c24a424602c6982c82c180c000800034425844020226400d101000a10f40d909001a0210707a10401c1d042c07041c1150304100b144c05009228004d422120f003c1c045111509040d841000030b0718042c816602c44c400d0950110f85544d0003555042000c2c4845000c00083c04600208140d4030400c62000c0c0410320300d4910555650907443c0102c410f2a83d852001c42c041010961011007a903610005507180 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 41918979 1250 41917729 41917783
    0x1905071205010b070b0c040b03060f04020d050703050105040e0106080303040f0501061a0c01060e0c1c0f0e0708010f050403022503020a03031701050324130f0f11030c0d030c0302 78
    0x3e60050360088620071050700103d079409a002c81601c00360b42d00110150b05580d20f113000c1180e850000f01075107030043e608003c0681110503034040c040c07084c0d01e035442c0840c0d154584801e0004481e101c40c41075001d40d1501c0c00500210300040210782c1c010b0341100d41c503015803906040030b0380100035590060755124065000c080f941c015400181c40000211002000120740e240d941d1815194211038404000604120009203001b1a800c0309034a888c1040e0000740ba0700201103080201e902441c000b45440c5d0003c18104080c48003402a82807034a4141c00910040c10300341d80182d03441c9000a08407484896600b46c003004124042140c00013981c0042c00f5640590baa0304004d818200c00380c00c0e90010b805840008a4076082c0000c440750321800c040c040c1c0f04280071820840b455401c01070551807010b0f48806800f000709491030b0158864501501d080c0240c00e400e80b6002200c0843e00d4840d5010b500721407020b20743d90750341590907a12a82c042c1000104550345d032130202c1c24040a803044c20b51845950018400e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 41920229 1250 41918979 41918999
    0x50403020607030e06060d030305040302280b01081902060d0b060d0b040b0d0305030703020906040914010806180a0809040914010e0705040e1c050d0501080a0218190507120501 77
    0x40101c0340c2ea1010091070561401d015142c102c01c81e00d164000100c0e90f141c1001030301c03a034003c55100f4001e02c1900c0103118003203101500401c0f00e03440340e111440910325071000c1c010100c8081e40101b90940003007026141c401002c1c000c0c0300903000041d10402021805908040b21504280398407140200280d035100714254409000300a030b142010302641c600700500c080c605140e61804c0035240c25480e02030440d80e035402c048004e50300c80e4011a80201051000050740b0403d402900355201d900d0081106540c10050903c0c50405c0003002110300c028025006000c55101080700b0154507000420b4658829160b400f180190940900040c144980200708441b40d80040d4803500d03008a400c02642d06081e6503401b080b05503540c0200403100781e00601130180c2208a02c05100904415130b003070640c200000c0d0386019040f600c0c00da000c0c84130b070f800c10015201149841c0185100d140d940c0d0b55602168180050074080349407040c041c04162a9407600856070047c0245120408510111428002983c4548083c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 41921479 1250 41920229 41920231
    0x13031407080d0b060c10020d06080f032212031b21030e030903030d09030903020904051c05040b07060b06040506040321050306013f0902011206050105071103010f0504030206 76
    0x122919181c51542113107042d070115090071640100420124a5241410000f58442c0c0480c440742942c910001510302400d2107014441041600a95202c0b1a0310015903006104490b8080501484050502030404a40c12081d80107405140c07550fa40303c80c118206840c007030310200c060b1105c019000391428101d0012009040528566010300c1002e00701d07403a20740c0e41d000b09400310b0340c0342e042840039502e0b100b07140d40015120b6001e49000780ca61070b602c0e004500c2c48001a00d05851507080710036075081c9680311500500c071070141b914266280074580810a00b49003c1c10308003c0c280c036210a07683c0c080740d4500c01903802030140144417680d41c44c1d80386400c102084400c011802d072006180211801035010b082030328070802040e11440c2490f000300c0d01b071482400c0c00360b425418410103ea4901c058020355482120030710b400d294005120381550001402001d102d410070035444e0705280081c021641c0c01419140031a038840c82940c3d00300c00840001e030140c2100e000e00c1000307a203844100805e241e0300007086 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 41922729 1250 41921479 41921497
    0x6090615170112060b030a060903120c0804030807030209010306030c0617100302031203040f0602040e090c0d030e0609010c02090a0501240927060602030a030e0f061303140708 77
    0x480e903140040110701000300901c074a200c580c5070103c1c220003188064110141d55134004060381d420829503035501e812500c80f50800e50005040317030311501d1440068031540421480070300b404c10861400355070080c580c04004040204260300442c07030007107a900036001040a5070340100034468a80c0c40c1c04005150103510250b2110061680010407814003403070000400383c90300038020745928141c0e2503490720302c0da001038030131500750443c40503800101e021413000e4800340c80341001c0e600840c14046201c1e4a0144d6040350588107070b201400840c0000d0300007820252112042d105203803210714100050300c000f29003640c00783d0000d08410420114030315070360185068070729504a010325800b00440642407902d0080b0307150040740403a1800d01c00c2600c1a40244000c905110a0900b5032404103c200b06407045584410003590012444804154260041c9098400100c00034942e0680021880e81e07280000341c0b180542d60f0848020b43c00341751042141d0719480c56089074195a550084ca400501e0760312403105 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 41923979 1250 41922729 41922737
    0x20f03030403050a0c231009021807120501080a021e030a140a0c0e0f01080a1e02040912021e0a0c031101180e01080d0c150f0204090c180807050603071206090615 71
    0x1180240c0c41780c91046a2344640c0140c0488940701d80f030115400c0054000d809541840304c440510030300713400a0b000d464041d0428170003800d1640884c0c414007202240c040b8003410034810111034110a5280001e040c03613403640090a0300d00780078605603800c1c2840320120b0040d0603c0d0000c0030108070200030041c9540690f000c0906241e4581c5d0701d111803619500710200c0204940451034914482d084100d0500003130781d00007000040c0b001855030b01c03c1410480580d0100250704071086000035411007448a0807040112000b40503614403990320207040c0056400002c00e2030311204a064401d0f44910102142004404101c1c1b4800d42c54038480c01c2000424804c42c64148101c030800184a0710503880901026440071666981007481c0080c030014201200c54566420b03070a11001032401120b0081c0e40d541e6645449415094012651102e0915050342040d10998000d9000700460b4035000c0880b0b40c40a10b610300011007480000300c2c0405044150300110b5001d04198022a00b80c2c0c40325843c1d600c103907a07a11 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 41925229 1250 41923979 41923993
    0x50f16170702030d03020a0216090c090504020c120f070204050915010906030305040e090a06020307030c1103030402090402090a0b030d050a020d0201110406030b010311040603051006020f03030403050a0c23 90
    0xc45400c034441e812000b50140c21006103500414060b801922103401103006440c01c42e0041a81d05100099550011001d00d4441004a1f042d43c5c01018110180200340c0d42540742c41e111540c0075a903650021861820786c44001414140c00c0e00000640795000e500800c10702150030000c0b1025a1188510720200901c903000000084245082c46203004aa5058075a00e090138902459140d0043c002001302c44c50740070300304642000030094402180b09490340e4400003079034a03400728010582960840725074882e9000b00b042c00302684d1946400781d4400d40c1281d40704101d030380d018141c07000780403000c182a8240c81508070071220550081d002d440d2142295088030040810010220309a600d08030700c59001c2d10040009001d243d219411640c40c07005d040c100030900680540747c001d16644154403880000c0d1341c9400703100c5500c00000014009003020303c010025044441001900c034400a8030040611000040340000103000b10954105250000c1c010312624200c42880140380304c1712050600070b1300400c2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 41926479 1250 41925229 41925263
    0x516060309030e0103050612060f07090504061d06060d020c0c090a02160b070c0503120108160806070810180504050601080f03070f03090806010b0a02010b060304021c03050f16 77
    0x4401d00a03034a400d075980b10300d0201001c005400919000d010540c1000510b140f41c0c0d1111b800304501070151019480140c040d2410700f100400520068004521a6007044001c02507503540c10089103209041c002d0340b402039113030500055554854940d11803419800400c1d11003a5100219801d18020016140c1c1945680d65810040032842140d071802104983c078a03803200450100000241d000480b8144049042000e1302c0d40307840c0d504030005020b40c00c0303018001400841420300c6504108801404c2400d1814280a40189c036040014040d000300b004110005071400ca9400b030880003801c1c0d200043c040000189042d102819046405a07140d03c222030000502d4600000c0100300800c26802031810180c5590341e000711741551405c10350030459034000100d1340d03003401e00c05c160003048051546580c03040e0304a0040e0a484480c52032a05c180000e00400c0051784440785000e5403203250405043c07090314681f03030555690040c11034903001b030305d404214201e20042001921030183d015440540c2c41c3c0703a00ea = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 41927729 1250 41926479 41926481
    0x302070e060d1101050d062306040602031602010201020910120b1c0201030e0109020a1205060f06010c0f0309260f0f0d08040515280b21070302090405160603 69
    0x2a40d00e10340202c501c41d40075000c1140401980c0044405241107454a60280c8078402521125082401c200d00e0443c074000d40005a10b01402d102c15040d40c0040c282031030030002075100d00481c0e4059030010034100022007160b100394121404184010020b240d010f403c05001003900340381c02000322060f45030520400340c3c0d141420748440c0c0b45100807450603071000c2d2640110040c1c100114101055074a41e80c1a0b001641d4890f0148040c000d01c1c08810030040e4241440781c41c1ca40b000e081e006042441200348042660f1100140b004290800d11017004a0300b1481d0803160210309610601410a003440203c24045889081d40013250256044800c00040380c40d0b02c0740c40b00010401500b4540c46403500002c443d00030100746a109000f00d081e42c80380c03000c00c00e0043d40c0750000c44080d4400400f0b5416804100b0307041d070f002c0c0703000c24400c4002c0000c20380d4080802c0307114141e454856100f0398211824541490100240c40c0076690183c040c640b07908080c50059a01d1583e001c10030802d410b001400700d81d051007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 41928979 1250 41927729 41927731
    0xe010c021605011412010b120c09010c03082a0306010909110d1508070b070c080c030703031110110409050915130303060b0a0207060201050c280306210302070e 70
    0x20401a40c21070b1601c4010340f120355003000b0202040b00c2c203101d0071050f503403119142d500074460100070700e681e501080310490010000408140c2401c1c01441061056640081d2040f20b040d0706040002a40d10307054000840700428a816007048943e80460001662030080a523000d140c0c00c0e2941d0300b0701038984120505680645402c180042c40600c00c26804034401e822050b0881c4800900e10652501c1d0480d0714280030286e000603c40c0c0c80001884020402c0040b406001056500f0251112408000021391901e000c2e10001d001c118072901e41e010758032024440071034031002d10b02c804c1140f56140070001e07481e81c0052140c800c0c0360f440d140c0003440250011800c0d0200e41c0c0002040c0705240d8807104026140081c1c1101617080603a151070200340d00518000a2100300b07c0c90b0020f001140c6031001c02400c3d2000144221481201071080f2103e01d180800101600860740724040c2e81e843e00c0000840007081554030000c054107a4248080120b01d0507107080d4035280c000c0d42525482a00e80e0804135400c10 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 41930229 1250 41928979 41929003
    0x30606010f020606130605060c01020301050f0d020f12190b0105130b010f051c020a08040203070f0501050706020c0f060c13060206040c0501081302061801020622020d0c0807090e010c02 81
    0x24000500b4624001a00d045403201a080001b0603d4403040031501c15004942413030034030382d800001440b86260204442801141c110382034450407030716902050703140100014450180e041c0c4007031020480002d04c0781700201c0b0346400348030a410400742420b610810003803140e1401030350b2100031141c2c41c50142c06441c1c14480306848407107692681d69030442d0780750b00040a10036100043d6060508410480c00240180f140341e0340d480400d810140105820907a00f54040b045001c03448200700140d03604403050303446140d088000140c5440040c1142824258041d5048255005034010001d0002d0352901404c01718650250b083c950350707281c442c2645d8440e0f041d60050810300c204001000258460844240d0107d01c100440d0f000602940c003188071500101030311412030715103031070540080d603041011a0b4006c841803c1c0746095100031843ca8100c011520340a030103411545036400900600055000041c40010308030349185541e801000300910400c1c20040c130b41e501b08105807041078800605008190 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 41931479 1250 41930229 41930233
    0x3030f06060f05070515071115040203070506090d021309030f020f10050a0b03060403030204060e03061003080702010c050604030f171009020d0e01021309060f080703030f0512040c05030606010f02 86
    0xb040d0a8400d50040d5508880300c1c8150740741204032091070300c02140195001d88449103640640380781c090801c2c92041018441c030707803034504002c056600000c1c00421a0b00c00c0d19595079443c40c80d07022850380c0194410280d00b044081004401180b89503010398030b20b60290740e0702c44006000450480e1584e80f04034401d0310b541c0c848030000c01140015405290001404000054800080c5002c281001411a0203502090740458104103468000e480c0781013500381100982510710704101c001038410316900000e000c0c504086842011a40118a040286070300101107514601e0903140061140d4900011080002c6005401c000846107a00c2082d0040c12500c100c1e005480c1400c0701c901c000d41090f460010b516031125940142d80c0c074288000c00c84419500a640d82440c02c10b0508410f96070a90310906000303000d01020800e41c0700c046240000d03a64513240c03c6040440303c610499060080300c010701e444007003010511003040f81000c0880200c880c00e5050301c02640d24500151441801d808549000da = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 41932729 1250 41931479 41931497
    0x17010308030a05150414010f06050c1009050708030f0717030405030d05041106040308030f06010c02061c06050a0b190e0d14030c01020f04080c0a2106060902030a02040303030f0606 79
    0x40c5a1580082c2d41c080b13a44091280c407900c0c4c0100040541e11a000c00d81e0032840810f0062000c250f40340004c50240800741403291409440c000520f0341c0712000e13100c50b00c41540e600030841c100481403002e840103011072801c40391924030301c1a4000d2030354800d46e401c580310440e90010b41d0200480c4020f8a1180d42c12002450801c9000d40c0144060480108101d500c4c074519007080200e540c2c1c41000d0b00140d80212070042d22032506003645440c040000d003005062082c14040e00006079a132404843d40b2089043d490122050b03406081005440950002c07980240c2c101c101250402e007100143c445032064001f41803040a0a01c1c0a0707680302460400c00350001d18801ca4900459600c07007030101c804169808aa140c6910b20100d103089822155504191500000381008408010003c1612000d800c44401c21418503081c000b1034034403a001c040d00090000b024000c000e219403584104010983e049065540740b41c25409003001354010302080700030030301c6c0c148940c64071a014441c09081c0d07030301900d4401c80 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 41933979 1250 41932729 41932741
    0x8040b0d0e060f040807050a050d0c06050f01030209010611030f0a170610081b0d02120405060106140403061d0a050105090d0c080a03020309030705070f060908010c1d01090e01030809011701030803 86
    0x2966102903007d454a204100c00e400000340104a00074143c40565120002980c4502d8040309503040a00b17800c0551004900500c0540d48112109044454504001c514a030307030a090075085d4059003102c40742468000ca0309919076500702c40090480582d40300f802200759198803c12019404058038180040c03060000a10b5046200502e031204031022800d01c1d051080c2e12851600703a0344050483c1180400f40401e1100b003180030025280035001d141004050400d020503c01143d00443c80040c0025854903d100040072502110981c840500e8080ea16582c07001c1c1403550217018140c9807a0035034829444c0c1040c0e42441428100f1080303521a00c0c4910b060040345040303002c0d40001c1c01c101518007013005404001403003000000014403d144426003d245085030140000d0b040d5440005181d04200302c44003460787c0306124406009d40414070a41011401004985072201c1360840c500b241400d00001c0140180800603012522090361190140701f02000d000a00d03902c02e20004002100500100ba4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 41935229 1250 41933979 41933993
    0xc211009021b0307061d0607020303040b0a06080604060c08090a0c030210090b0730020309040c020723040612030807030b0d0602040303080a0506270903040308040b0d0e060f04 77
    0x21400301c8141040d4009848042c0345425580300c001e04444065481c8003544151016061800c02607580358040c007050300c0d01600c041e4a034407005000500f017a825000141c3c90510a52010000e003580b2021540345161600d8180c1c02042032286400115800f400040d10444001400d28103031a400a0355821b00340c959800c0c8480c00c00c1c5501180240480020046a80304180c4041c1034486e012340c5004503910b80d1072941c11403048519002c1100c1000101c044c02c03030150000f08442c0720341d1040d100001c510b5401e5070304a0406c0c419400c021801c80c0140d1054081d840c9501c2100d10101086a041086030b50316015104071440a05005020030b444400051030a070007540000610900540100c0300e80b8001c1d503c0348100c0c0d00980084000c254540b00303125201c101c0340b003159841001079032080407120307120020341d0280c2c0c1c015002582c402d0384200002d0000e1010f00680d4020b551040000f503d4030380b40c070603541c0c44c0c0d04a460050704061a1402510210a00241440c0a900500414501c07902c031901c0d060 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 41936479 1250 41935229 41935237
    0x71505120a0e0105040f0b0105040623040902060c01091a0609240d0804060e0a051e040e1c080702012a0201021903020414030f060708100e0c21100902 66
    0x2451142c0d81e5018182c14440038000d651003113100e588114182c508030f15000e1131240c010b0700501d000d24509071060105542c4403800d0008060051100c0d18428400300c001409801c150340c000750406000704180b120044150032801c1c8062041c411305090174a240407030700000d44115161640405010b000c00c1c00103504411600351000407410b90443c04540030049050341c148402c0c203c0707900000103010456594041c0b102001d420f000c94041d00b60518010018510000505141d0351403516441c0304a2207a40d65032054025014100075500800140400103119040b035030340d400d02103108040001c541c5803042c8140b9806840d100300300d4041c5100704000f040032844544030703401959070030000100d6400811544d1034264510741e40c050390712400e040e65032403a03400a02080340079511844002c1104840410620350000b90703407420030340310b0b0744400c110840070b01c040d407000c864101c124082c0291214100010540d80c0c144110701d01c0b0012010510b44030000c021955036070700060801741448001c003550010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 41937729 1250 41936479 41936491
    0x216030c02010c1703071416121808010905010b0303120103030e0a0302040e01050702010e0a0f02060a0302041208040e18061303122904020306011b05011b1107150512 73
    0x3003407a610440e603d1159029402522030109440482040b034000e6000c03c0300324248100310a080d003001c01c1c8123914032006100a034001d14401e45200100910761080301d900c507640240c0700c5000d003525902c0c0440c500034a0b070300c4002d45a80d401e00c8008031041c20f0010440d03000e011254400c04581e80382d91021600d501c50f110b052035001c00070398000005646c85000d1038450903900c0c0c0c0009202d0601600290031a645002c0054580e0041c500c0d910200f5003a041034a059038058501c05d5a03000c001d41c003100244600c1e00011503104900b0841e80c14480240050000e4541141c403030759072601c802000316103c8680009048960717200000280c445810a0904581e41c1d00c00e040c00c02c4030080c008044000d4900c6403240405415989145424442c1c038519002c00b5000d06641c214654241100000c1481e00209220060010344141110811200b5030110301e5107079101c1d08890701240b07000002040303000c003500120a11f126201010072132a0507009001003c0c42c090b2a01443c01c1c01155410840801c02411 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 41938979 1250 41937729 41937737
    0x6050315040906050c0315032103060d061812050f0a030228181d010501050f0f0a0503010603140105030304050d02040608150f09030a020c010c060207020a0e0a06090216030c0201 78
    0x40c02000845030300130140148101c0e90404d8803858204000703c0050003c0f442248a544051441101c52541e130391000c00d03520511a2041e40e95586d140828120f174060100200340b1441c140032040c64513031250134003104510850321080c205a1509049406014800f490808041d0402030726803050b002ea40103001124106020f5101c03a02c000800e91500020b20300040003040e40040f5910141401c00d00900113032142407881d8070740b507400b08401d04080e1814051f041c140200090303604518100c01003510006948901820b644203241c00c3c00425540081c0b103009c02180c2802c000c8803900b92800b0030141039620190040d030606240004000d60032800320800e81c1c21035039841e0701203403125080c000c0041208120759004c01c9030034115a0001c490b180240b0450003a0418804001040ea000c210000351850910b0003481c1001d490801700005d10503014000c0d40460030700c5002a40c14808000503100700801103003040903aa4802c040c81c103030b124120321803840c002c8603040000040d0003100c1c80f2440d11f0041c90 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 41940229 1250 41938979 41938991
    0x506010f05060a03092f01030c0507050307120c170a0305070e0d060f090b090a110108010303080c0703170907080c012f0a0f0f060b01030603050c21160905060603010605031504 77
    0x10650b801c0f0306c1042884c40005506814641958040c020f46064414a24000d031400c4a2a21603a17120700031000d00805225040d0802c00ea824480c3d8038440390306800014a030110521444031194540c4100900d10119007004d00003100b8a0048072403c680b200e000d41141c00026080d6a03003002010350710054082c1d0b0782c0d10414400030694a51040d40b042c001a001441043d5890078000c01400c1000b1300d00e41001400801480040d40c0612120340100a5644554943d582c0c0d1030140c0300c1141c92440e2220707900c2c00c0700802c22515000a40402203a41c0c034819200514190001100d20200900802040c0c0c62511060116012003802c90f8100401c40d40c16a101024656a4002d1944c1c2c411810760324081004054000d0105601c20001c1811003420100800c41c61640c50790b88900c3c0240340785203e102921460740145c1d00007030b0043c441034030a0007a1901103011448188196450380a154400751400c400140e1070708102c01101e05030b0300f1030303102c0600b556070700d0624900d902180e007006e81e0060b8a8003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 41941479 1250 41940229 41940263
    0x7180e0703270305030402030105130c0902030604110703020604021002072909030609030703030e071409060f0405160315050a0b0f040e010f0509070804021c0501090507120506010f05060a0309 84
    0x1092100d4094442c1d44c9803070790b0341818010035007502e001501c00308095080020303980c0040e181d203203400c04860700030102680b21f0390b904000030001c22059441840603a40020808205580450550321070b0b48226124001e0103540c070400c076a01c0c1024098402c10800e412480c6903640b00c90781c1c0d112051000515824039001036100444e00704042516900b02c194000300b40c1004054050180540c906100740060000070315080340400c001e0541464140204101c1c1d01082c440c0c1c85d0140c4019a02c1000380081c44241020300c01d000c2c92641300d00c107a9002038a0806000341c910440a90b01c0c0c11101e008041a480303d041c02c848900711360155003071684000c0d0820001070b40c0001e440d54540245020800251101d2810b010b02c20749840091002003041141c804020042c3e035803a8088941c0318401040070188400c614000d401400c562201908500c02c1074800601d034100c2c80d0303d4902c1d051042c4191649646c1e1411484d414003003c1c01502da119500380802c140c400e110354062a0114040e152824020300f100b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 41942729 1250 41941479 41941541
    0xe030d0f06180b01050d0f09020907020c19050f010e0315010f0504060b0909040b0c04030203100b120d020a0605043002010605010509010909022d0307180e0703 70
    0x1524240840a40701d00d010815a411190039031035204031128148180b4100c03c00007800d500c9104560001c1e5503603055000082403166209010031603003c2e01d8880d81e42841a0080c1d0344580043c059441075072007501c41c4000d003500900000840d2006042c8491000301d540041d5030a11050140c03a07003511034417004007030203842100882d00a02c0f6140589041606110074001a01c11641090003068002c10948035283caa03402c0c41039029420080c030301015142c5c004803c0b03c91183e90700c041e51602c100921211040d03456400a40300d030900b281c0e499400c210300e06010313444c0c0000100106c0076030000c0d001d0001080d0365400050b403192040c1ca8105041e080001c1c00c9d01d900d40c02081c0c02c1103e060321040308070710980903c01d51000e008242001410070042400081c03640055000708050710383c0200d0b2258508400c101d00c2202082009512174240036a1018110140c108031800f100080401d00050030a104884000056500c098140e5980e5600d01c42e0590180101d07a0b03c4121052507103181410241714 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 41943979 1250 41942729 41942741
    0xf050303040606030209010504020c060a0e010e0d030209090f160c06090609080d0c020102030c0702220903050c10050103020105090907170112110603060d120c06020d060914070905040e030d 83
    0x400e500c009580c13411030040c00010881600114003413403041100c4034650384002011544100002404034428500f901e189014100103442003a061003111400e640e51500340e000307030420b00300a072010591940e80c00c0d032400f400c0006072400100ba14140600c03118182c8581c2e001e001542c00780401007850203140e82c84000700c5a10900c00d481281c004100104c04004074001c50b00c0ca140703188029800d500b04a40301c60258420404000c1c07280e2031403a8254205e014080400d581c140310800c00b0022482030b0b04000e401c540c0501e40541c0a0300400f18004081d00303051240e14140ca8040e0740746410302040f1828802c8404020b4240000d008994002080400803580c403580078107002c5c0581d034428411032030a224003240422240d4400d00f428020880320f80c403050504e4288a400600461013a00a10703001d0786c2e01000d042c0c0c081c0c4158000102c0040b07040070b5400c0036088641442c0c04002200c0d09403007216107200195114030000c1c0e001c0004016518140c1c0111840c28100b0341501d1030026540d102508803a0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 41945229 1250 41943979 41943983
    0x7080402030616200a060617070902040e0106050f07021e040c0c11010c1b0603020a08070503040c0306020309010204210303060614030103121407050c0901170303040f0f05030304 78
    0x410104010850074107200840d0050502441e90720086034041c0b000c0e10080750746802000503000300e0302c1c0342450386081100e404a150003c03403c001039910b513074115159107030120400c241c52160580006003e0f070355108640441e456402201502e9090400c2292540e111007070000e20240d05010040261f56042c0700c100b858203030200c03a604040d0100061109460134070500320709002c90304440f100132a4043d28062510142403900340b8005c0090f18201e010f8040714100c184040500242c089a031680641c02010010016216050035a807155000c5600e403004a4000b06440f002110400010b1040c0c0c01441d00950303400005400d280e161803807096045c0c023101603940c942c0118000c0300207043d0940b20707260281045140ca185105e0680c82d0021240c80f062000070040d00c540c80e10008110310a44044503030002d6007038401e0307480b5164201955110241c4a520707106e100c8540000804150401101e042d551406c07000d981181d440e9111405201e0000f03e00741c620303244580c0a60005841400118403942c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 41946479 1250 41945229 41945237
    0xc030204140402090a09081603180602070821220b0f120711060403050a02070302062b05061c110a0e04050106090c0903020f01141b0c04020a050702060304170307 71
    0x102d400d00410080d110040d02102c002031500295101090b090000c036440780d0444a40100f10074403625044400e0f40c00c444079221401d03402e031004102140d0100f06a800c840c140d60032100da4081000d0a41c8a03408003054030003507003030100108842c1d0f4103044182145c00c0641c0b903a07130800540d02d4400000c0365103c1d90117000030300000900740c103d50004204450300440c4600d0700751000502c60402c141d0740c01001e4806400e0100101d44060705600c00c114803009540e020f4800d90304c60128642001c400018000311101c5064003078001c400c500c44070b100e1030380305400c014500c2e540010074110300740313825072801419103424498405850040d224189290001c041c03080490415207058180307503084031003d8220311442418481466400359000071954141c03038040310090080d03e10000140c60500f441e281c40c00e10780d0380c04104070282c00d14040300d800c45004440b050320a081515010841240310b11081200440d40510540700541001c0f0007855005115814001c4582100502c01d50580c2086421030005 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 41947729 1250 41946479 41946481
    0x705011101060303020606010503040c0306020d0b0301050a090305092205011d0c030c12060409060903080601020d0203030108030409020f070c0305010515090603060105100e0d1232070c03020414 85
    0x15640324448a51610100c0c00800200b401c6950082d250200130b0800750410801201040074003500b00001001194080004c564034400c4181b1000603140d0303a80007600c070b5443c01c1c0c00100602c86601800c0302c083d90696a00349000260001c100c07504100e9502c0115000d40212100c80a15441c85058080c29000504900b000c605001400000740d000300503c1504406005012a0040d8a000d072400018140f0700a4683e988440100d802840e002401404642c2440c0c103040c103040c0c0004840e0b00501c0c0a0b0f003a201201064201a44d40303101c28030401078a5401040f0400ca8050168040e1901c0303649600341e1444c1c009952680320000704a60010b0700c80780d54410038030200085269003035401940030f5a0f40c0300c00d440c05800080d1901014401c103401a1080c542c042d100324428a03420b10135210082081070807892900f02010140046e00200010441004e11306c42000301e203001411a103102c010310740c0551511040254080d8004141c11504802001c00c0440180d4441c003801c02103003662002c0d886c0d070b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 41948979 1250 41947729 41947739
    0x9090c0d0501080f07050607021201090f060c052701021606031e060302061b030409020c01020408060109090f0f1a010e0703110a0f03150302060f07050c040216020907020703050106060207 82
    0x4551041c0d022001c1070340642c464420004d00410b00400f211802c51301d040c7c60380c070980085012101c5a40503401c195180040d200200000e250410b4801030141100308030402c076400c1c01307a440303109070241001d4032146111008180420384804852100061043d11209040c80c13054808d512603d40100300413a8507031a00072403043c0e0800010304a140400d505020041c41d58000c107403144a010780802e100100c503610007100140400498005258406003103545803204001b0b28002d4101d40224400703401042c000003224500e60041c030310b60b0780c0c100025052a2040c0d68a2124013060407500722442c41d01220760854190240c54071f10b00070601d1440014203854800e034001d0807508441908803059100b4422491103075482440e00c1101305e61418005084008040c00860f00401c5510080d441540000c0c562411600d80c0b001d0019144910111044800c0c41c00800050f070143d080d100c82598240d0307440380c0c0036281000011b5001849801602c640790703200e8540c0350030340300c041c0c00c0800546e03c289000c000c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 41950229 1250 41948979 41948981
    0x103030f0806010206011404050417040803040504150f050d03030b18040618150c0e060706020405032107020d060b030a06060501230a0f050c03030406050403081612050a0209090c0d 79
    0x540b0203401d03c0031785125030410410000e80d0701c21035000d900031a0340700002020041d04005203110f10540348003245e00e81e90b8405402e41e50794014011240070314103050310100c40301c0840c40303604140ea010311030a81074a0306003401d200ca0b0342006801075040545501e250f80054480001d00343c0d20342c4855800400910301800c0c590203072070741c0d50760321600c50a1210414000c02c0000c001a0b2000300610000b00c2c0d4489541e800301c40e02802448980d500440010300d003c00c0051550080c002c549064041e00c2c441c88604240e2220070b00b10b00000c060350481041140300600e00101155031403031290000003400030750240802c0c03802c8502c5000b00e0304503550380001e01842d030b00041e003d21031208588040c1013000d414081040c803070044110303200c1405002454100784071b004000b60b0314071142e00400c80e81c50f40f5084c281803015003000c0c0c1d400e90205a4010106031a64140e6900c00c5003a101500c13074941e00e0b08205410001841d0007130000c010031341d00384200101c0d541d40340700081c050b48036404002d443d0070395192140 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 41951479 1250 41950229 41950231
    0x1030c05040605010507050a080d0e060a020315030d02030405040c03182409030504050f0303040e09030a230702130b030d05030a0f05090712150e0d090509070210050901060803030103030f08 83
    0x107041c441706010400000d017000588841c81076002d40303c1074aa103d00c400f220050844200b91a0752406040c003088a2135916a01452103503040d410410700b9041030fa02810b468500c2c4000c6100103070800c12092000c1d003440d4202e031240081c1c0d4a000210604800c855440c6050750140031103061202070403040c0020580e111081000e42119000c0208010390754000c0e0107407040303100325801a4070385d000506881d5400d1051f1001400051a05212440c3c14520180c880d441250b0715400304114000000003801e541d404001d0440410001501c0c02000e90200300490311030841c501d010584032440e030105a20207100015407842c00b0b8482c152242000e0105c141030b20088140d80c2c1c403c518002c01c102c2c03920030001d080412200d9110640c0341c529100c0c1045411442c500d119020018140402d02200790000944047c03281159a030f072a50b8180c440c010402c408000303640c100c0060b804041c0304688086240d00094001840c02c00025500c1e0b40d0308070003825500240d00c15000700361451038451110b0382111082e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 41952729 1250 41951479 41951489
    0xc0b0106050a0e120304080102031e01060c1218090f020406020c0d0506060d030e03030703090e0603060114100e0d1119030f030509031005010803031e0112020418060501030c050406 79
    0x107141450903900300100a0200610104c2c80f61000600820121000740210340140030300c0c2c40250750f203280c0030030324806054404a000c1c540c16451400090011312400022442030b901500001003c46082411141b9041328041078101002d13003c3d002622a404d0711401c40c1204841c60050303181c07460490b01a0400e140007003894000d255003444c0b10700055020405a0f4022422544c803400144c4908080740c0d4110450356044c0c1510000403614249900240c00c10122902c03507014858950300d200c103041c2c07601020322a00107400d0f04500d800c00e283c50220007c0f40031041e103262100b40e280c0303039000290103484034607801c0d00d001010400e0040d4a003040d2810343c0003a020080301110181c42c0d640c7c6d1500c103034103500d03000c2d0411502184400b180e603014821700740d150300d040100703100f2035860300c80103070300e95005552174005e04c030b0f480318202e984050111619040711130001003068026400d030207010251a0f100107a21032141c500c01c511000488038812180654042e0780d45044140c2014148030458610b9004 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 41953979 1250 41952729 41952737
    0xe120d031107021018030602030c030f060f030a03110a050703060b040b0a0608010b091206070801090507020c030604120c050303070503090114010305100905100e0a02030d092603090d030c0b0106 85
    0x2c41009600c0f50101204a030301c40b8a44045200019240000f899400d0b80008010034000414407a810340b841000c4c43c01504510540c40454603000d0030014940d10500c411a0075030007400c090b03400309004600000b600c0450031306503480707040c0700e55486080c0150394008031501c580d20700c2001c11505080c03050060080c000e0b00c081420324107002c0003811101e4144142401c5803c0041c0001c46925503080e4401c50b5424801120403034105103002130f003100424001c0503041c626003400504614400514a01a0f05019029014035169034441e451240c000707522031400d11860810030703c00540200700561098005a556907103e041c022802c6086d07444003040c1c1140340048500600101d500882c8840e407405603403000080701c420328546141042c84440e1422007a51401d903042d000702c0c201140d00036485100301c060720086844000140c2e2809902e0044580da0b0415600020a9041103511003c250300200200e0f42000c1c01400080c181c800c44100840000354082d441804018402d44090b001d0615820 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 41955229 1250 41953979 41953987
    0x62d01091d0405012706050903090607051506010e0a051302160b1f0f090f0b0901140f04020f1606091b0501030507080603060610030906050103030507020a090b01080c030402010e120d0311 82
    0x3ea080000006071005c2c06803075447c008034900d20405c100f00d40340305c00054030311501d541c91400c0032a02d51000041404c080d131042000201e0039071264151440c42400104440c0c40d841c104000d01c464210f0003000d00c1c4040d82d00b0030a800061035005100d51042e03108200c240c0140c540202c007040d4849851011103010580154140a00d4000c1130442080d5503490f00009681000d4001da00c2c081d11101600340d8000c0f1015002103909a0110302880c1501c82c241c51103c403100003041840b0480c03080c11001807901006000c1d50803234011114111200300d0141101040d81145500c51102251070074141e1813000c21030070820006ca58260140c40d50000a41c1002d071000e01e0704c2c0300807940794803000700301c544a507202020b8042e2150003a0301100c0d010390480380400c2250303103a145c082d069510128003a48501c554050016202009006080d41c289069641c00d81c036446540e09440c4070742010700304a040c0301c801c0f00c646000b078031000c0c4900c8240300e004000700003102c2d025401500b00c0b0342340304580d110b02000300 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 41956479 1250 41955229 41955281
    0x4030c0807171f1a09011403010606020c030a030309020d0606060503060f0d03140d1409010603420b040c030b0109080c010c0822080a02010305062d01091d040501 71
    0x7800c0f40394001c0c0c810300219160580140b0281010700640d030856000b25044004911030f03955110345080c111041e80200b00c4145c444200b070303035902a0481d4080e41544165440b4001a20903080184882c2c4050412000320740d1682e900c2050b0703180c98211100049003c001c21180f031400305040154584142d41c03091001d0080e440c0140804060321283c15418400203220080070310950201c0800102105c3c2242141001c400a50103044c00d840309540040c0401e141c412100170054020050503031591030005240380030364800c4e0011514652454000d5540c031944144d9490b41d010703000c078045443d50f00040d030b03480100014042071015006030310301d9404028034020590300692202006504500d80c15115110701200300601d441401409505106002c2e00003988100040e01e40010b9100340c03814003181d91114180250300a84503694116035007c0c07410514070b08039400e4420440c0302c0c1803400446094691407001890a120002440503490300c804020030300c0170a00c1100b8542c181d005080c00c00300518 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 41957729 1250 41956479 41956513
    0x703030c0f0509060d0506011407050a0215040b0d0f060504051306060b0a050919030606030804030c060201050c03040201050a02070801110c0609010c02060601081806040f03020d1e0507050304030c080717 89
    0x6145c00f5134202d43c2d400104036917a00540040c00c080054622141c1d44001c00c3c40d1494a581c20917500300d0080d202e03144a50001002e010075141529940005030381001c61030501100139180d0480241211a5103420100390b907111805014801d4180102c0500fa121980c6000d00c12100c85610100c802c00c810300088010f40d41c000212201888200c0324000720076180e40c44a050785007036074401010700e482d00300008108420321016200300c900032201e12080303682d12030701a42a208121046004c400c81080001c00540c0510094607002e00c42d441142d501d20b0319403000600b110711021414410302408680a98120780801c02c403a0302c18200c0c80280504e41004101035a0707040041c0c01a0b042c004180001204100c90000c01c441320320400003103917100d041609045004a0004006030018000c64244207070745801294041e05052941c0c108440d201d80890048a09420084086940c0d0000300400008103161210180160651101070b00c0c1851a00045020308410142a89107a81150090b12f550040b0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 41958979 1250 41957729 41957737
    0x30105010c0804080d08010617010303080415090b07020105090c03070e070509030a05010c03090c0e06010c030f02120315180f010909020f030a050c09150a140d080703030c0f050906 79
    0x800c0c20203520710a001d24081c0b19602840e00610301c01c1c861402140f00e1180d01001c0c05040323814135114218001d41240200b41a1760b030901000c0c1c045425070340403a00041c0d02c40c1c0b089229001d8442300084200c0345035142910400240c49200060b91580e091041c003180c00d0110a000c2181203005005191a017810300076241030041c44101071010204d010301c041d46060095866895001e4000c22003071441d210040c0003091000750944044003c2400800c4c00030300a0700f00c5000b00016101d9441140040d60202c4141121030019021800b42c01d072002402c1d1198409507016841aa40c0c00160201d1081401800881d020300c0600e191008014440111503012616055032203003180030920810500126181d10f03e000d41c600d1309403184d0401b01c0144035002c120404022011070b0710300b045403924505c0350300c00700b01000f030b090348809150000c11007141e51254210900d507015082e108400c8032a2540b41355034115500c20b4020075112303840c003105280e11800c04042030740c3c1414030500742041180458010b022b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 41960229 1250 41958979 41958989
    0x3070c0e0604020f04090906050117060f040302030421020411090a090b240702040b010306050f24120406050606190c230c1201050717070c050a0b060102060601090b0301 74
    0x42140049941d5448540480e9000710749031900c1c40d42c40f41d542904000901e10400c0655030070b4a408004100822000b00d495420705103200101041d4460300c0d645600410060021003e41c4820030000400a4a5003081404c1180d004038458801c0d1043c0144000c2c0c1d81000034000c1e044408204c03810740395607032411500543e8455440043c81c6108040814070914800e43c000010300b804480080444481074010134803540b00799001e003c100303500d20054040e501d081c002d265114139400082e01160410840c140e08600700c403008240c0050340b291703000d10582e0103411034000d20401842000240482030050030341185080d580286440e4000454286910060000400b08100e000c00750051040c04a031207a107001480c0780056420221501c4285d954811000780c2d40180659401600300000621a440c403c031010380b510a0b028030030702c007126800980106040244070176045010301088080109003500c600c41c408404190419100180c90200000c5c000b40c100140120140800050381096904440c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 41961479 1250 41960229 41960249
    0x315080604080a1101061401030e010e060109020706020f0d0b0117040506010509070509120c330304020102190b180c0d1e0632040c26010e011401050303070c 69
    0x40c003c101290540300081004a041d03007032120120b81450011038001400d502600e080090882d4803e1b45802d03944640d403404025000640104083c1310f6540042111503c140401460204807006421940e0001c80004c03544581d10700680c500c3e540c001440404905d41d1042c000300900d4950b8900d540c0c0d1005001d014051500c3c0808101d1044c0210281c1e01c281c07100902d103681c800368010142d0358800040e000c441c8a20904441100349a1440b10009940f9403000d40034202c03c162a0184015544068000c1781180701d4058442c02854805183e1b02841b0f03c9013100c1512428901b01d41d1840d03000b03508a030390b4a50040914240c0503502c1d00c6080f04001ea0100b60b244410610708003c03202c640301c904025201506207403411004d102400b074230b00880703d40700304180742d141c6251140b0010b024003110014400c0e200010140100c95250039260f240b03402c00c0c4e0038064080101e149a41c250b803d5a1080e42c401e82d19946410f00a0441c40045409008291300560a200498070303075481558007407184108038 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 41962729 1250 41961479 41961487
    0x3030e01050d090b04060606090605070204020c0f060708061005031905061908030c0601060203070c140402070c09020909010501020c0f010c0215071401060603020f030703020a09080d02010606031508060408 90
    0x241d000320255a181861558100420720060920080c02ca02c11102102c0442c5444804a8018002d00a4200741d42090307550905002103542030100030760059030030302c14511800f00b00d00f0f0308503010000c2c40e00c40c0c0034582d9410024107020f000d100311b0982803100c9200f485400d004200707070bc415601c5d00301245e0007050400b151a407140c101207885c07205014041000c41d0180100030030501da000008201804030039003245d90a0703a8601d0203d86134000d1003c014440307400c1c41410090850b140c0d8100d403020500420041ca01181a603c02a40a031a640320500e01034000c0380d99030726440e1003840e1a004000038000340c10085a080000343e213516251440b05d05100a610740c400c1552101c4403c0c10b610703919607102c240d66140c0e0303080a440044490581480343c1d800c100c400b00e86e10f4446e00070f07980ca01400207076481c15500d0341c00c000d90294111414441c00c000807440e00003050342041011107907c11150700001142810610700506803462001d0241c20303400504002c21408000080c0d1079849a00401c243c1d0722 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 41963979 1250 41962729 41962757
    0x2160f060e0f0115120206030103030f030605040f060303030e0c06251407081207030203030f060103020d14010821040306110c03070b1e041a19020f070605010503060408040303 77
    0x1007030340d00d140c1c070410721582c400303000300200550160940a111007484140300b6910b060b8517104030300c2030314004d403c03410030b100400000c0e001e15162000803500741004a801c680b510082000c541810401d80d480c661580000c0090580610a50303080c2d00442c0054843c200d80840419250301c241586452100b11020407851440691090344141683c4680700c220f000e81c260550555a004600440c4403078046c05150002d40b20000d002c980071240d05802071400c40d525483d482ca91120000c0455050503020400e0406840d00352103841d00d440418400500316506158280349003005003019842d2120026000c200d40030000010348003141d80c40f020104610402c3d0a00e880140180c4001a005200206400c002c000c003d0904038400c0b800100c0c001070b031010f000e00181e107106054802a2100c4038401c02e1b850070b110400890f0764007105030909050b05500030020030080360301c900307154624090701013002000c10581d4012640102012001010b0310304158031124528420b511004082c44241c60348149 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 41965229 1250 41963979 41963981
    0x80a050c0a0b0105030f0d021207020f1206041401110d091a01090209030c04050408030604050702070503030c060115030b06160f020d050109030e030303070c151401080307120302160f06 81
    0x1000100318000e8910180aa107000101140c0c01e002d560300c2805900540d10080500007181981d494099000307000f1030280c038040c0d5590790701990083e42c001d10f4150110ae02900c84211440d540200c000007898117181c14100000114590b01d861140369050003c2031100c14060030582d00c00c107101c0040000c94558a141c00d195900511122034080d40c4d0349000062003405660203404007400c1641511021001c00e010031040300d8044038024451320041c4080380365814a54413169004e003246c01264200364035800000d10390381001d0400340f010f0380000c0050000412000320080f00c071003036003000d000002010000400501500d011304060a02149600c001d0158050b21258800d03000b90141540401c6810030b680a440c02e628190046401c01c85030a41c64103002003202d204108503134500c050f404490f900e415201d00c1c0000803020040e05e8461519141c2540095036000340042c0d0700560303950303910703181241c0251424841e10040c144140b04030448071002e090300030f00c503983c00008884074007014900f141c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 41966479 1250 41965229 41965237
    0x2003070e1e0907080606040b0d08092103090a05030a0b010b0a05071b0602010b01090513020f0909010e011a120a050702030705010606021e0c030a02010e060c39030a080a05 75
    0x80560481d00c020301c0049000401e8038002e13155000180c4000760748003020300050710020204540c00101101030342c0c012031046806000f019400900c0500500711100c1040d035800d1100c980561301e80c0001841c0c5603c2c0c5490205d80008001c00d5000c1c0072401540e0b1204801644148075490418130300159522140340b03d10203d41d401035000120408290301c000d0074a041100d50b00402002d5840c202e500d6829600498003602104e4009004960ba0207000b60307070720060340000f080500c0c0000c0038003003021560f44080704030b03029040c156071100c15503160850b102c440c08107607640141030500401852250700d041010995110303009600c04601d58071489802c910f18031a9801c05400d80d4a8024041101580030500b810320f0003100c10b8150b07619100d02005503d030001d24107015072580c4a000c3e12030055001e00340588804100030011410704c50a8900181081c80400540f4013031001005207900074031800864038040c0c1c901d610000c410340f01c1d0b80c02181d81c0e5000184003804041012841849841c0710704111 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 41967729 1250 41966479 41966521
    0xf040c09030b16030e0a0f02010f200102070c0e0405060129030a0e010516050d05070509030d080103031403071d040609020d051005030309032505060301122003070e 72
    0x401c0991030003c090303000200502e141080001d0401d6000380340324030005600c0340c0d416048604000d400e08281c0c01524404a4001e150061040380042c1b5441b0301004480707130b00740201540c0056074a204510304047c10038a140c001d41c200c0070b41c001c00d00012540000b640350559454290109404040b5250b54103000c055001402c00600000100071402c9c0300c940003200d40c094014028802a100d0182003c07001c444182d0714000100c040c001d0323401403081032300403030303080300003800c0c1113150030740c8007000ca030414180f006004086002000100308040d403110445000b070507506149401d50401820040000c1c403c6001050b4840e1404032848056440d035001d24018581400110342d5882100a88800703040200c428400750340160070001210705003c402c542c1c80d4440100a0020900508176407034590600c819910034458007044082620344030b01c0700650207000c4c90b207032450290825180c9800706060442d00303140b210101d8081c3d4551038900081c1107040d80d4120200c4001d550742c0d14110350701060381e00300ea = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 41968979 1250 41967729 41967743
    0xd0212040f020306010605043f050303070206010906030206070807030e06030a14010b0a050f070f0f3005030105100e030706090e100e0403030c030b13230103020f040c0903 75
    0xe10003000a04078455003081e20a5007950503681e603a05090b00c440c0102d21035001b1078043c5941071007401c08118840100021806040320f81e011482c0e1007405229440201141d01f903000005001e070742501001050f0040070f0340c0000707200c00342c15940414146c0c02426802841c100c004120202010b000d1004148454401f4101d00d80f03e00c0d00706035980c090811000303590b50941071200040b4008110004446800e001d81e00c0b41c0d031400101c050030a81e179511200c1c050760031582840c000d60005009a03414a40c0d0340c011041c1401403545000f04007013445417030043c10800082940c0e030003201d54104040d64111007040700c06004d06045124240c0341e54421482c015454062071101158080d001201c1400340c844180c5000141e64951600900c02207480c01064084d00220f000140020301ca500590070075095460045a108020004121040a40b42c080700d1800d403154800d00d60881240f41d1201c2c101880700745131300c0d954591340200d18001d503601c0b4030b05c0c0100d032150703000d280003402002510011548912 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 41970229 1250 41968979 41968981
    0x8070501140408031e040f0b04080705120406030608030702010c030f230301090e1515010915091e0f030f0c0b0301080d09050103112a07090905070f0315020d0212 71
    0x1a028800303034003c454400180d0190300c5c0800e0b00700c0c966445540300e50342c811136400035040e4030340307a20b996104001d00c102c8840008004100c0010b00c00c2c014010203440c40182d50380c4680c1043c80180548105030840612940706001100150f030303000c49a07906003609030034404a00e0072504400c0311000020040740c80c1c42c4004400308060003c03041d00541c101e03411007100300310084403070101a03110700000e209100a11389600c04285002c24030128086220f8050401c134122580d07030076801d0000c00394045804045191220100440c00c0d64800d070303441035020805a400c000742401840c41c01c0c00c0541c04040d2901e41a0303994142045131141c42c0b100504280300d807044c0c0b25030303403070510075590320036144080005605d6980005080d4043e00074040c129086048850410f400312600d04d00005912041059802001c1d0007541d00c40020701c1b1030710180100581c08181040c650a01d146029019801407034100008030080022440b001d02080f6111041400540e83e80c641c50140400f9000e07000e02042c244050784 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 41971479 1250 41970229 41970233
    0x4090b0103060b09010305030414030c040f05040b0601080709061b050609100b061905070c030b19060803030609070c0515010e0105040f05090c0609040603080d0203011818080705011404 81
    0x24440c1200d10440c000c2c440d40b2014000d01008032001e00c0020466841844180820207605c406c01c1000140602104c440d441c4034000a01500d04002a1500e866540e405001c117112004d002c156010f10203080040842c28800e000a080c0e80c854071620003007010321801d510303d1034248001007403c039401404844146c1898402c01c0c0d104c5405000c0319803c6c52801d5404403a5040c007070f003030300d603c51108840d1685c0c0290a0500352119404034804442500d260b010200c0051101d11656024003c0c0241c00c04900351000c20241c00c0780c410381c202008540c8213104000305540c510f05c0d25544a40c551620007504202840c0480c41c000750b1004402c4003054001c00410804408400c03141201d030102c8003071204407680708d0110111001a140c62030903400a66a10f415810000024a041000a00f0010385c8940d81c0e16801c20325000144014030b20754002004004001e00001c0c903964000c4c0c224410400d00340d0341258450403c40690004103d00d401240300b1040c0f1000391300414042211001a4155152074 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 41972729 1250 41971479 41971493
    0x507020c0a0f0e070f1107141008090d140f0a0f0318020a0611190503030402240403060504111903030f030b13050408040305030c07051f0c060b0a050409 67
    0x140c1881c02001c8081c0000b0301c00200700d00d84070440e882443c02040320744960104640002d241d00049060250712910101c0c14030080004100400c0312815113104040b0010030040c814072102070a204105101c0140301000101080012400c01241401f4105419000340410b41c0d0242000c2e001010002156841754280c10900841c3d00280342c0e601005410300d44150100c0040007054041c0d0480d680d00710910005004812078801600003104807000800c080440500b00044090100d4164002109000850900400c070741e0051112141c0d20452100c1c45606020a00640c031002d0f00b0545c480000c20b0a001c02d00aa1040c0c04201620940000100500000710b0070400d00c0100c0000f58600003194a152280c0315202080f0741c01410540c9800e02c00820001512025006403040c0340308100000c0020740420040c02e89445000150041900c0c0001300000d03084010a00e42e040c040107500740302015400742000070803a50150002514071000404030f0081e5109030009500245000102e200307002503 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 41973979 1250 41972729 41972743
    0x30a030605031006150c02011818050603190623090a021201200d0b040603030801080105091504030503070e030d23070203030901050d090f0c05030c030c0102071a0d050702 75
    0xc00d42c100c880000e074100440f01110315521940700c0480c851455500b07607a1107045e400041500500d04490702c043d04031134660a040d810741c400501c25413000d00d1142401070500596501c84401c4019003201555082e140160155880700145a559030740402c450b40890310380d030450640c18518180f5124900b000b1a15591000e0760001c1e8411040709080e80d1040c01c2c140118141a2801900542c443c0110608010a074106072041241e41d6140c0a5801c1c445c3c44900c1380000a501a036a40d070b00c90352424400c03601f1203401034000300c000e8000c40400021501c41040440d0019450306d40180d40342e4443d00100c40c0790040465040e07141c000c509d403400c02d0b0b640c800d188150020000c081d801c2d0030160b01c2d403011a244610319000790180c00a1003103120560042002c0d1004ca1403945e000300d1a412607a81d203c00c84000300700e08452020311780c9001d101a090130020744608640c2a0020016003000c50b002035074841c00d51044400d001c018500d411361401202054a8070700c00a0342050080d41010500a901c070700b4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 41975229 1250 41973979 41973989
    0x60f0b0a050f0f07020909010507021e030f030a0504030f0906050313050c0307091b090e010905190c030c0f170c0a090503010e030405030606010912081303080c0f010b0d02030601050d060e030a0306 86
    0x1b801c00120703984400621805000e207519400800d41320700f40068080100d6028899003100b40810701140304101d000b1802140300c0c611022001540386814540580b694402070b42030340400190307041c184012038000c41160340020790307400c00465141040c5022072800783c80121164060098541c0003070902c0107500840003c1c50441711400b1030240070602228070032151320802c3d85181402004200c40c0100d03901442d0080b00b088a00c503025598001c42005a549250070140065600e18200e44901d40c080a02040086a0315092203444520302c5006114000a01a0300e480c89001503240200c0d80120b410744000c1001500a11803100001d0000703441b40c1240c880c250003400f4240000304e066214110040680c0c240d0f5505e5002e885158490080a4011241191503c45590804408640340d071014142012000c0000d056041c482541182918442c0c60140d005281c0c0105030303c016a0007040c2c4c1b0381900c01c2915065140205400c0c5140a4000c034024074005002c006480380c816585a000130080d00c1d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 41976479 1250 41975229 41975239
    0x10b09061923090102070b030c1201080a0b01060e0904060f0e0709050103120f0f08070c080408030a090605190c06060504140f01061d0405040201230405010909060f0b0a050f0f0702 79
    0x10a04081040e8510034203c9650058110302e1040c0910340700000690340045c100c690b86418869440700002e0344d1042078112107020b0f030091003442c0802040002c0b0760301424507440d0050f42e14900e400441e001090190008201948440e07005404402c1940310341200750001045400302642c031403c280c001d107000e020956503000f445440303d0303140e80030f50445007502c0c9007136881001100c50200e0843d41003102810803c1004107148461000c5007944000d00050800f981c003865445d40c507848042c001030000c0d4040800d000040c089a10400144080b211850700103040c0603107440d0042c60f05400030311841d001542c1c001d00d04283c07400010203503000144213000001c28486540d882d040151000ca241101c0c485000c03550501020a40c10507400050300180306040003828012040740c00c4811f1026400c0034100000041401c01c0030350b0f4480c408100603c008207003008900e00f80400b40e083e110f81805900c003910030000300c0484041c4a0000c56040c145c080011341c0d01c034454000c0b02e40f01940084401d074803070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 41977729 1250 41976479 41976527
    0x6030c11030a0801061b06020d020d050f0702030d020715020703050703090e04020d0204020703051c050a060f0e04030806061c050403090b12010501080717090c0102120f03010b090619 80
    0x200000442d0b2210200340c840c601e01e0f83c6050000ca503021022542c82045110100da680c2c0000d00600142c003004051b1305016032104441d08091080301c0000f0f0680c44000f04150622015540200449443c0260070401590b921642d0400e0791160b126a21401c240f103100281c100c003403680c00005400e10344c2c8641e0b5009081c0b0741e940d07003806a65805071000703988102da10601030018609980140394192182c1401400c2c4a600100f0307030320342c4e40d04440681906840c4c40c00c0001d03001c0d0394805c5001500040440060450500c1c41c042c03541440244000c041c060144040750207599004251180400c60103080040b443c51801d01d074002c5e080035242100801c4c00c1b081c010a41c2a0040c00baa8120088000300000c580e00e000011503030340380080c0c041810302c42c0e082e402040203800307401c03414402c07680d200080100602003c00207203480300c0960a141005001d221800300c02c00000d0460b07044504011042c2d45030a40000083c1e10b92249003007600744105282c42c040201c80e041680d2508280e0004c3d908100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 41978979 1250 41977729 41977757
    0x150f06020d1812062d0605010c0812070e03070b0706060f0b070201030b220504110d0807030807120e0c090601020106050d061d1228090b070611030106030c 68
    0x1014002c452094031550600360500151410a03501001c103401010b01140d1840b4542807041e8420410a40010680b0459580800040d103401040002c140a20b000c90a8152940394031845000e54841c2c0300c80d0654180110781464400e12910009000003070036a82c260b5603c550f03440d41c95018420450b1280e003812400511001c951002d882143c1244c9001e501e044619030045000f820443e940b21b51100030b5441d54405006191103428a1100752800001d25080c03074184a11110103804210781304031902c1103142e001400b0302040d90030701613042c2440a032940751300e00140c81c0f1607040e2944102a92400324a162902400a00040358420079220500180ca890004909036102401402e8104040c411603100191342a030028446041c0184e040742442030141696091124074002c07690a540f011030b0705c20202c0c03000844000207094034505030004252100c400741000038103114018021102246000500c0840c5d04026440d140240c011b580d251f0311100041c0040841120801c00a00c1c86000b5001d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 41980229 1250 41978979 41978987
    0x606050d180201080f19020a031508031e1b060406090b06010801030b071409030304090b0a14030d050c0313060206071403040b1305070803070b150609011e03150f06020d 74
    0x2038140c060b581c20800e9500d12a6204641c0703000303000d404d485010310b00103a00c41b14992000c1c0905100315940031443c1010f5214021901c82e003a04845050b40040100345010358285040c950a4154010904e4545c0462501e101c0800901c00c1c0103a010300843c0104010806d42e41e001d152068401c0c030342c1d00181c1d114500115440c40017400003c041c2c400e540081881c584c0100074500c0f5081d0706503515480c20000c180440c1c2560090f5111120f50b6485840e0800946060b8040d00040c08411000701c2c0b140040b90300007581d402c401011070080c03010000d171486983c8000e1040321644070f00340c0318401840b641c13000020342d990700440d007000000380c2e0f446962040c81540400c81c0d0065030007107031080d0726484e4040c00060b038011401080b120f520881000083c4034600344064032943d402750360942a1391401810580005040058642c0304250420130380003035a801500880507041303a50f216200c100610a0260000c00c805d892a0407045401308000031038584a40c03595003039511950a41e1202100408161 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 41981479 1250 41980229 41980271
    0x30c0102070c051e0d14070815091507020304030f020a051c03030c02010207030207091517010b010e0a030308071d030f060411030303040c030f0201020703080d0203040212060112031b060606050d 85
    0x1907030204000c908440801c2c1b0203600f02c05541c06000944880f1603454002c0c61500c0c295000900c0700c0e2101f4020008407800510807100304d4000540f5034845c61622120080d00c9103e503001c01010b000c01e0071210415500c80c40e0402001e40300c054424101501c1d0200410701030380b0200001ca000a040c106c3e11030345070384107009842100350300d60002c10101d0f091881801c003900040b0907038041a4240300b00014107859014500107030b181602c000081000360b040c00102038003580801e042c06404402400c100081d4000340a1354001e120b440d00c01443c44d161802d08000882c04100c1c598144240004d2850034007020808a02071071240c082c00c155406004180740e02c9010403a03016103e200c0040c3c0c00c001041c9a20035142172188144151000261aa81c030758030650401195160195804010030045083c0544100e00710b0521500400780740d03142040900f266074000034018200203800d01c80d0036080c1e070545041040b00740e00c07000500115417607410043ca145c1004422500c1d050070580f200c0062101e00b1210 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 41982729 1250 41981479 41981539
    0x90309010504030f0609060c050c0c030724030f24050a0e07110f060f0106080703050903040902090301110a0203031b03190b0d0204110903010f0b21030c0102070c05 72
    0x81c5060518540b90344078030400c4900b0a5400503101d10158000803240d20404149803029152aa00c03202000b42c01e52030120320130302c4507000303034030400003441480d03400240081103440148034400c407181c004000b1000b400e01c00381a08022420481240d160502101000385004464200a89910b07600c20400071800114410f03400f2800510000c41c03501440b58103100522140701e02100d8140400c40d014510700745040319400c0728004104018001c407a4021038264100e00c640ca414880c9080042a050302e034811841802c03030099000031030f07019584081d08070180c690324002401c0e885280c1c82c0d030040e44035031048400106604091180100c54046102524041c007503001108804450750544500100340c10614958021171801140c00169628014030004503d1242c5c185d4485030b122044c9420354000380599602c1d5801c260b6075103019210310208882ca55440d5a00004510000750b0170743c1944910b0820750959400001c28100744800d444048085800c00e4480480a000d11064485050a48000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 41983979 1250 41982729 41982737
    0x90b0102011a06070804120b010510080f011403160902030f1003120503100e04050706081003050a15060f0801020310060302090d2003010f0b1305060a06050c100f1409030901 76
    0x40b084103050600c00f034412948101c602038900f039281c0103526481032000d031085485040210041c4214280540082141c0304a0300b071860031424948040745140d10140500110400c082410102950b810016000403007480c42e580f010913603c2d051104043d520848200e40a6560b1030041031040b9003036005101101d403c4840040c0300801d090045455500c00b900c0c0340c00c004a0440301090354403804080e6406148600d004100007807800c080940b070f00381d0040c0315403850710640504001003800843c1c524502581b041402821a120944510040400b900b0056242c034605001044010781540114085d62490501d080c804c1d80d1070170114240e104a601064001d18a00a8240011004109405005117005200c4c400f00801d1000c2401c5078908080b0008041d19203d011a05042282d06250110091401400075280060105281d86070328070404040241c0020703107460074042440007029507400b04900380805905d64030b60724050300145449200164100c004114240400001c0f03034003070b50045c1c40e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 41985229 1250 41983979 41984021
    0x705060f0d0b130c020a02090f090a0822030506010305120f09061303020301050a0c0306090c051204060209090c09031605210307020910030c0b03060607060504020f0a030b01090b010201 81
    0x811034003418010301115049080080442d00b403ca80303008032810304405500804d1502d6140c0100122800c011b0300134070880d80164240840a2000300354049207580000904c0c3d6201d004412500351582d06202c0b40d5820601f114002c020000c003c11298100c80c091800c8a00d1460501600403840c03003940344002a0250410010b44941490707806802061034404c03113031444951f04d030003190940da011501c10f4001a03460031188501600751041c031002c0c140300141000f0307207005a080075041707104100038074180015202c000390401110360101e41e20490090301410540c180b0980b10009034101d0840c076031080c0101c3d09500d440c504807076000d40881d24020303e29100036102e40c1c45190019080b003e00300e454081040000c0242e1030b0b44000354060007140300c1e20742100e4175500348003400c1481ea803c202159003042040c407055640d800c06940c08035400074800202038031580700080da41d450b1031000c1604918240c2d40003040c084c030740386070a04840001000b1b0091812800049080311580f0354240d840f088810307 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 41986479 1250 41985229 41985247
    0xa020304060e010c020306070522030203070509130503270f2209060608030901020705060a080609060a03050105040f020109050a03030917030913061e030206030412030b040c03020304050705060f 85
    0x210b00c4210711081030400c0c4090380840e401003401e00d5003c488140c0800c0002941401c040c842010300000704064000420f09641903a0001762541340c00e01c1039a204480700004a100d040410780780c074010a0b03026040301c0d0b46a040109e00d440c0d80c095942590303100c2c00d03250440c03034060034041c40c3c031004560014010300344260301903141c40240d0b8422003071080b02d079500d00500c00001c00e43c0c0b0801001d00b61000007503841d846e0401c00245021100d42010340211414080c1c02601500808400c1c0c004804451107501907544401150740c58500341e0000e4015030a04090000744107600c5030b81d500c114000c0e600c11022075100c03801c1c0841c0301d916210041c00250004003c000140e44c02d5103090f20710701c185055920340603407040010580d910304000403500b01d540c2c48040203200c9044641c18007801c0b28603482c5034044c0c03079030700041c425000c000d101400d5100d04031501c0d00090702c69801002c641d480108104521f08240000038001d4104403405ca810744145103010400d894508269900c6460100f038240c03811140d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 41987729 1250 41986479 41986487
    0x1202030c0d120309080c030a1713080a260f0a05180d0503040804050904081c0605061c060305030d09110901030222111605010524010e0607080c06010513020a02030406 73
    0x501c05da032101c1d07040c083c0c1c3da0040e90500c01042c6201d51540c0b1048c3d91681c0303102440140074050107954411445a00400004001c1400c0c2ea807800c0c11401d00b0000309501c00c1d00c8414400c0b003032501c88405d89100042140c4020355414840c05074001580411195803080000070041044440c0b001059100002100d02180300380004e650092052546d42c2c209903499000c02e2000100365400c403410440426120340100400604c1e861b030440074102400b100745020041210791040c141c65180c2c07196100c4030082d8210041c0c0110380215403210890344e590403100b60760402020480c0089460005041c20b005d4285462403e030b0341680d40040c0415440e800100c0703031b2105280c0c80381680500a448031948042421084090644000d000c44107003900c0d038880c546a0308440001345194400103d04c40d04c405156189030141c02c0344002802d0442004140100140d0180100b120040031243c001801c1c071300500d00815074038121035080d40e1a09900700100580c03c02d0740034404034680164805d001c104441445 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 41988979 1250 41987729 41987741
    0x90105130605120f0f010b0a0510053105091b070f05030c0604031b0308010504150509011508130f0b06040b04020307030c0f0c03080a110906041202030c0d1203 70
    0x480c00c000200542d440000c1120841c0d101c42118494000c8032000841d0102440b0b01600c01404800801c003074003e4800045558100d030003518020541610104401400394045407010010f004140e100c0d036032249a42a105d088003140c1c0c1310170700c0c0649400038960402000886c0030f003191904d42d510010025100c650540c00084041c1c0e049007040c842940464401e10041c0b10041c10325014105624007410098646100000003c1d2192041c0c010b510110b640b0010983c19982c0484000c11500c030b00945080300180982c12803640328011070000100c210903215245c8041031035031a0f400080d5164040140300e074a821030041c242070361819440b0000b1703602c410901c0d8085401040041c88900e148045000c90300704480700b00c003003940d910200c90480c0c3c100c003000d1244600d9142c8080c0784001075034003c040c982c0180c8844645030b240d0203502d0346a800002603910050000d40626151541c2d00121092000d011200782c3c06802805104c2c42030381883e1002101d8182c010b0300054103070020340c00840050803 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 41990229 1250 41988979 41989009
    0x311090601090f0308030718080303180f0d02160e0601020604080a0306030f03030207060f020309031b0a0203030a0c060506030c060f0705011103090312060d0c0501180801150806090c090105 83
    0xc40b020000c91031440300300304600a140681d800c1c03901d902d13110001a120480c0d4030900d64031489607070420000c8050000440c2e600c0559400c0102c0c0841c00540c1c2180f80a036000841c414070301800c3c14503050380b5400500704141401402451019580e45d1000544102e01645c403540160003400c0041d0108807803000030310340403101d80740008640d6070343d854425428282d80002c900207500041c9200500c01c4502450006100302d60381140395040c6110f0084c0e5900c544001c0c408503450175448846840c406111405200740c0140c241d81c0c0da420240c100a0480c1d0404008035805450040860741c681000100401c0084024242d00c2c81d20072000c02049039030300311304030880d003540d02e4481084140107002c0113580600f40b04002161145005c60124403c030700018141d0b405108280d1861003c181e503000c008085030070a08018503281c810070002e2000041e107401c96070556080022500b40031401000b02c0f0704031286c0c202941c801e620780150b4651503402ca610103540c41034503000180300600d0b008880c2e0301e40706 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 41991479 1250 41990229 41990237
    0x118030c12120c090302032a0d05010f020a020f06070305010b091e0a081b0301050c07080c030f070f0b090d080114010201061802070221060a090f020303030901150603060311090601 79
    0x1401c82c1d00c0c20548240300d11000029075892000c10450070200046005a05145182c00c900c04800c14000300042582c61801e105100d2800308405108003984900481e000d0110150365400c408038000c1e40d0f03541d1300c0c070400200c1d10921f00001d040c10310030700c203560581c1c066000c0d0910700600c01c410001040c0c01345d030340c0c0003031000c080d480004165101d0003444020440786001c2e2609100110314038a52031441c8032514020713414401080040311500046420039540000b44075119200000c0702ca00d180545100d1000010000810f0420b2100746071003c01a82d01c54105580719585001400d42c0f1004405921004621208010701c401c00120301c07003003119841880001170b15070fa1112244241042150500120380c0e0004402080d07044c04180c1420340c100306c4600288589010b0000d0303588010060032607004a6a941982c8108180704220f01c084540040840ea1242056120b0a000740140c1078015801d501804000912034080d002d040704894000701c140300100008018040c0200c00102014100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 41992729 1250 41991479 41991497
    0x50714010e030d080901060f0b03190e1204050f0a051809010b0a0303050705060109020405010c030f030b180a06151718030406170105040b131e1a01020118030c12 71
    0x10381c0b42000107405608981c1d0303404140c0e0412103820340c210341043c0c000c01504498081b051190391407510849400c8100051024140062159420018440580c190310b49000f1039400e000c2d80c0349200302400648600300c86d064500c0d1a448100308850751644581078000300c0d82c200b08075040307043c1d10300c0f40d51120b420400442c0c05904200000c11064103500120b0106801049500c2800f50800c0501e000d4500a24214582424000083c0281e143c507540103003000308503a605a16184a5085044403440182c0105d02028200c4100840300d8411104250694504400003403190000d00c0060400281520307007a607002c282103818450110001c00c1c105000003500403c6400f030345c003040100014203099452001030340d0403040d0501000c0c07040e4445031050341070002100160f55101c00c509010442244000782500024a032807400d03500206443c81d050b4500511413143c0030603030340c1c1d14004800c241d0007004a2500c0c0118071000181c4650041e001079407507400b00c00040d0003042c030404201602c0c18401e001c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 41993979 1250 41992729 41992757
    0x6090606160204020a12050a0b01020c0d0303020408070f05120c0616030c0203061501090b0304051f150b0307020712080405012106030f021003020304030206060405130804030501090c05030a05071401 87
    0xa0760300500d0314400117041d40c1c1b03a50030381c22942d00c5103c0d0030004000c0e05003d41610040000c0d0340d00b0401780054840d80c0c98070750f00c1080600913170499008100d50001d4130444c982d6491b0310b2080c280e0034419980501a01e0401400b013050224810583c000c0040070070303040c5a03450207804002c80c1c1c005412010f00c00201c01360b0002d60360401619100c0c4440380500085500340391300061002e1a0b40d07201e010f8020040c014000007920101d0402c041920755480c0742c460044140b002c070702504001c10b5614005206040108a0b0000340d00218400c0195800301ca1000d941c0744445903010804440c0a40a240e0602c000d010942c0314242010100c0001885880a4030200c0c0502e403c481031070748112086081c18000e0021410f05913042607011941c0c2c20118214549500d000e501d4990041000f40724a035201d00092070aa40d00d10420307141e0790021801e81c6c035a0748074a0468001c0501c40400e494800c9c6a00001400307240c00170792001c4096000340549949440c10f012408640380010b030107030501070802c8403025 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 41995229 1250 41993979 41993981
    0x11e180b030304090f0b0603190b1c050109030e150d02090102030403170310060813060b01270915050a1e15080a0c030e070506030604020d0c0f020d0806090606160204 73
    0x180c800130b00c00081c0e604600d8180d008907181000c0e480d00403c001c0c4100030b204015000d4820810461420105e02e80702003100060030303d064522064003c0300b140ba845400d00c2815030007103000a210303481e070041d1928200100403c1401d04199127190031020440089085520b03000380141203810700460b030619449503204141e1700c0401680f0700580c0000300400c6a012018000c2c20001c0c511800c103413056003080e99101c0080040070034041d00582d29401c080c15240d02c50040c9141d00001340c0c0e0051015020b2101d00001e1519510403401c40f9401c102c0d615149400c031414030011103000400788000545082036040b60042d0b44816402176220b0305100156140042103a142074041a541d040e40b40e16000030140101d8400d415507200301443c060451032024000280e0000351101160a1030700d03592a070340090007900c41d003528459440d00b00408003c14542080a04031003004035000da401240f28140b007100e011104440c003c0e40300310b089011030468144031005159144400000f00a01c1c06641c001c60 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 41996479 1250 41995229 41995237
    0x105091f020706020c0a0807030f0302040303141c0c03060f0e0903030f0c0c1603060c1805060c03091c0201020f010e1f09120909140402060a051617040e011e180b0303 73
    0x103901800c00023200001c0640c02a0802203280580c2400c60906007551401014051a50f8100c0a1010b0009000e00c210b0240c202000b54203403a0281444107034440a00203010302468400d900049040b100e001c01c15205030210540300701180d40065080d90360b0340e1050805401c000e000b95117910401c1061111141061064469a60303440102600d60751070762070031608032649a01031508101e80f084108c21411503a400034070480300200c07080c5031200d60b407201003802c5114142c0d6a83e0300c00103184e071589141114503100ca104500036000d031942c0c415031006007401d0303c1075140122425004111070364006030f4a03c0d40318510a8461000049101c05682c030f005038422103c51200100d204010104041703c0c081c0901c00803106c05400c1d125080c242540800c07501c0c0268148002440004600480e010b109084031044894103d00540980145503001c808590700500038074072414503100020030041401d0108400c00110b05000140c0145001141c2c1c1081429844101a030368541140301c841c0e0340c00304050 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 41997729 1250 41996479 41996483
    0x1b0507060302030f01080f07030b100506070b090111030403021c1e0801180c08060d020d0803070305040b0c030906060d06021c0605030c0109050603070c0804090c02030c0105091f020706020c0a 84
    0x50343c900f040d035019203402405034070003000790b440780d0b6100700b80c5a0301060000840e6030203030002c400341e103c0d00440803010105821280d00250041103200c00d01090380c14481c0203840c144020815140d0045108102e0301c802c903006409a405800407032410440042c607408101c00704d2070058080d4030b160400032469420024000005031510b40140b1201050b040c41d00340098400e0810092211200d40290800c40001d007103900c5010701c2628203066454040420605036402003d88d6038070715200c44040d005180681d03040c1e0300d6900910005011141d43c0c02146e004045103001407507240d41d000200141c031861540c4c21110f40742c082c0011803111a0400034600c510007000030124a0509000606241204048445041046c2e0110070081901c80b80202c0350090301d00d1500b00700000042c00c0c12b00d514810781d40a400c02a24106003600860f40c0400607106c009072500080c0441d4031540207082d030f1100d15801d250304440410b03410840d0401154010590710307120310030140c200005516030034107103180034a003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 41998979 1250 41997729 41997731
    0x9051e01080f010503070605030a0209060a080f01060504030c050402030402030a0203011a01021002040e07050a02010902060d060302090a0c080c161407150215040609020d0c03030504170106080604031b05070603 92
    0x819155a0412401c030303408000b0040380c01c00c640c50b03d800aa5610038501c03e010130312100001141c2c48140c0c64044030100c07030016280503034500000100400c40312080320202142040d038000442c810740303d1400c403421a07800509000800303007008104030085d840a4803c83c0e052042c949110010f8070280521a440180c41e002948500c80d00780029050540400c82100070600c100704c02c1c480f04495104994014449280c5582c480c400203800364010115184017070751200740030a01292002043d0060025a40300f40c030000f8543e29001c401c00d094448503030801c0081800b07040024084100e00b40600040210b134030400d442c106d00c58a891881c445514010798060b00f0000c02409900101703204615900d2161005051401c01d12030500280c3c040507100400407522a41075106545e6005502d0903000c0e00006499070040e07492402400d668050711400004c03014481000c0300c0e001062180100300d46031800a403841c0e680d2950100c58001e041580843c00e981c40d00601c0e00480c000f004210301914250314 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 42000229 1250 41998979 41999029
    0x305091e1518041b030b01110303010b040501030c0507020109180b0604090204030506130b1302060d1401090c090b0318070b030106020a030801052b0c08100b0a060203070218070905 79
    0xd41990740407a02c800a02541c10881d0091000d099003480d8143d0000e203160000f200310805004035a100d8041820b0b030300c1e9110210011551812500060045a400342c0f01080702418115065625004040e4041d01150038900308003c10f0707018110640001d8041080000e8100740e00c4000382d41034000780c00c0f400c40c8690108040c810003204104844d00480040c0c150303000140305a44611044c0c0300102582440c1c05400005011522054142c1e5020004900248481c1e07041203c42116150244505040c003414044091100c40c0900540425202c02d031015515640e1660422100680d904034140198819010001070031801e0b02c018501a0038164007a11341906141401080b018043c6c11152089508404c01403903c09624441e1170300382c00c0035449840c200480e04124101d6403ca0380725105a0245038204a94100c10381e0200419100840321000040c3e2a01c408030f80e80d0207070010003500b1000341c1080c07540f400540200c0d281d001c1040d25060001036140c0300800c0c0040000140704800590f415 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 42001479 1250 42000229 42000247
    0x3160603050a05010b190e061306020109030906030c0905091b040803070b0f0c070f020102010905060114090a0b030601180e01090f02130b09060f0409051213120305091e15 75
    0x3001c0c484c010100c0c09405410f03c09150501c84807820442c1c0e204c010b0102d01d202c0c407003550b01c50344151124060108410454982e651202070301070408000100c0003d060030401040b014024480c40714130f49141e40d00d84482500b404c05019410701c02510b07580044c0c103001e80ba0403c0201d0540100003510320078024546480c0149400c40c07607120f0107000080c5c003014071001c0100c6140208155180e441d0040d402c24641003143c00140c0c0106241e10014015000e40c0001040d203251600a00d0b5a200d815a09510703523988260347c100844902c0c200e001e902d40c10001c010030004074480c200c41c1920a41c0a40055581c50079480d2508480040304102d5030144985198010341c5001c903010300380f0202d2018180028a441d100040c3c0b105401050343c2c0c800c2681c4c1c0a424215283c2c0da0018140c60740c41400c8800e0005103100c8254640c0040d01403003410703090020b001c5418101c2d105044000c59050310340904201c0540200007500c49228046000300c05140d800f400c103991401041da818920103034410307613559001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 42002729 1250 42001479 42001481
    0x303030702010c090602030a0f03020906120c090f0118050918030d060f140f04020d0216050c032802060a0e03031b0607050a09050d02060712080115080c0d0b03160603050a 75
    0x15500c05c0d002c0d50801d018080383d907034200b000b05030a01e210b481c1c010303640c4107048000fa03018001e1042050803035480c0310401c05509086c500408501c80119000809092282c0044440c2040342086008414101c1e104100c03908015009503080000c00c084040340f41c610022035071540d0000c002001e81c05842e41405c11101444040e090003030301004900c001016100c0000c1080080c88012250081c1d500080f401d0101026606840c18019141d0f0507250110722401d025a035a25115403039442401901c60010640ca118803034482c0c54000d4036528421552141c08225841e00702e54a100240121040d6402580e50281700501b14038980c1c090220b01c105009030031929002c1d005000d8828003a080100c55581900300e00d9080440d80125403a000b0070601d4800719015004012008001d10041c0d810404490303000384101c4d0613501c00c2507091500c076981c0c29040320498401d480d07042030014200620030404500c0d03009415401805412644c1c1101504011003850a01d5800500021b40d540207110b00111030f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 42003979 1250 42002729 42002747
    0x20d021c020f0d0521090607111201050615030415110703030e0106180209031507080a11040303170702070e0a020408070506040b0a0503130c030c14040e07140303090303030702010c 79
    0x810b03501480f800c0b4031076039034a648241c1d41c00c4200f0300182c0c074016261554405000ca4040500203401c544c0c0381d1000b450300c46540102180c0b41c134491044200302c4020380790705128852082c00300174190311210000d11603100513039201901c00d580c900c5114250070320702160340c01441c05017403c0b032074903540d150a1410001c0c110b07000d2480d980c0c11030741044010403a0000d50302036048000307071050006907501c00c00d0001901d002071810610700a14903401c10454510340080311036100f0241c121040c450b620211141008921071800010b001c1400007a844098241090620317500140600440d81c42c2612850410700c48401255100e0030710390001000e002e4030741c1c20300401e802000181d40c010300f842d08181400b101c50041c40310b841d080101c0031000541114500c00c200f41a550811003a002040d104d041460f00c040060280c0c0c04401c1803450310b22903d04140c4582407603120f054001d00611418014100c04812444440b0b40e40b5100c02c1c0552600790703400f1300c025802103815400020710b184031040082c0069071 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 42005229 1250 42003979 42004009
    0x51504120f02100e01080106052b0203010503250b0c030d0f05090f150109050c12090c1e0108040b070c050102030901060501020706020307030203070b06042904110405030c0904020d021c02 82
    0x1080c1391411440e40c001d0412810b50b0721600b030035615441100800c0b03041e850b1600c3c03440c03004807002282150160595000b10b0580e00180c058801e08020f1101003d441680ba8900260545100f0001c001800110000e071103400382031000e07240b811404e03461110541310a1440c0c1c0c000305540e2000d01c55946d4003085460801d000c410094100c06103411400129520144a0407e4140d03c400000e2910a15181100c0c80030ba00e03601ca01341c0b5400c0a0403030503920744a43e0300907406500b458100c0c2c2e001c1c0c000102c941d020b4400580d07900c0180d030b0741e0342c0e20098558000390854044c800d0a5282500141c03080c0090351080c0020400058100c1c0350500083c42c3c40001d50001c801d40d0020040c440c0841da000c0100c47d00c1c15040091252146c4624010900911b000034003000301c3c40300302581607018280341e0743c00c21300c0e500d0440c2c00344181800396241c071a09101e540b140d107515a02c042000203c50502821959100d80010701c44401e0420f660041949400b4640b03040c0124103a680070a030071880d0503443c8100101c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 42006479 1250 42005229 42005237
    0x1b031d0c0d0b090705030604030206041727040f0603081314061b1903050a020c010518010c020f040204030b0a05090606060d0b120708030901080112030801051504120f0210 75
    0x1165000407500100d5080c0700074085280d0a40000c616500801141009200280445001c1c1c42c0c6420000c1d16954140e800304d8101e445109442c0e50034000005072038604400260303100300440c1d0940c4941c0d440e40240601e540150712030035440c020149502c0b6103001980a160f030769940740380380810f88402e49002d8014489401c6040d40c581c5542d280c0c9015a0749102d400c500700b846501c4194801494a000c0c0e0201d50011003000100d80101070b4001e01810004640d5000c64011400910064a0601a854401c42e8190104604030140d40c842c80482180500240640c5000a41c01012905a0384550070960700f152103038040c406070131018850030385e00500010143c905400c05000103103540c8600640f8406180d2070385144981a42da524400d0300b1800f28400f2600007a560304440342d1241c1054600f01e010071002000051074903025402e2058035503140d0f50741c81c4113038202010051400c000802408400b0018800400d0b064500d0007040c1c081c502808040c00040402d1040041c10501050ba100800c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 42007729 1250 42006479 42006493
    0x2010e01050919060908030a02070201030b0109030b07050721020a02120706050306060c240a0b0d120f021e1f0b0f040c02240708010501050301030c0e0601031b031d 72
    0xb65070224092440940a0080c0c800d003075114205038020308605880900315007800414040240003590040c04214400e07201403001c441e00300d005460f0190b440c480502200100da00050b600c0303120358002d1000754030919001030703902c901d03100461034030f050706884001503807150a00300e003546001070210000d07562000060100505000e8000c2c090700000c0c1600f40588400f140b0520402c90178000c101752a03000c10145e03200903280303140c00c00020342d051b101139108030b140111200190030b0591040d0344407a000310708103201c5074002a00f01d0300a070b0000480c1e011401000b81c0b180d0440500d02c0c80d4841101410300800d403900c5592000101a10a680040810381c0760807800c00f030039128105501c02c0440112400038912529103016400d128812504000c80c0c00304807030740c01b00c4c140e107c1c0b0b1039030103090700d5514048c41daa280c40054074035100a00001d804030014400800845e00a80d606903403044040c500440d800f400070082a551007880c01c00840403e46402d20040c4014110b40c020407950030000c000e00c11 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 42008979 1250 42007729 42007741
    0x20d090c0501090e09030a1407020405131704060206061c0b1905010501030c0c0201140f0f040e010608040803010e060310060308120610050703031d0708070614030106090501110708060903070302010e0105 89
    0x524440c44c000e80c0d0030300c8144560007180c4002301c81650705194024000b07200620b030051112141d0f6010000072501c500701070784e00341c4401c0e240300250380903201c16400030302107074460f4802c100741000b00c460303500402c0c200307140d0440002c2e0000255074011044001134902041130540d2650a4500c141c01c40760415160010802c4415407103000080b5951302801c142c1c92120300000c0d00344442c401e00100303000316100000ea44071006101001402142d0340c581071035a06980b1040111f9182c51b0540d4040c006020600050041c1d41414204a42209004046800c694225104001692942c4d0b00940d0550700128400c101280c2e82c42d40b440d03100f0000c89585021208640014185004648000d4100342e556030030302c3c80c01200303409440003e00c00d240454502c50380c1c40d803145a40c0d180c5070280314001100c41c101c0c04800d0b0003079000e0300d069900c19210882140d00745001141c02c3d80c0100381d641d02078400c2001c00941c040b0203011407401400003a000d5907540c001c6050190a640f800c906906850780340c1010484 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 42010229 1250 42008979 42008983
    0x305040807060f060e072007050105071506120308090c0102060907060e0f0607080a0f0305010812031f09200304050613030210020a12050a090b01030213020d090c0501090e09 76
    0x9040d5480000043ca116035092804001c0299401ca500c0042a00040c060041e80200100e4900000e04109404c0c1aa8085c50b41d916060984510f40c08114188418000200e40c00d020481c108044000059030b15a20200c5800380c2d00541401e50104102070184800c0e104244150105400d080c00200f10500f010019039070ba17007c240c800c900400012076015203070b9665a4880b00c03006800108681c1e200c1e240f5042403840da0303100d0000380e00420120311a44007d507020340201130403100e45402403e503002c0d00d480f1810311540300400707090f42c001490005800c9650718030398a07400b629280c8000925000d01d02000314101d03101e250076500b400001d00030040000c03000a19a540071507a0310703031280400000c0c6400d80c50a07546451103c05140040b58401301c03164420300c1903086203040c12043c0705603200d02d1a880125058020040c2a0158040060025092078003e40280f01404500145000e060303403402c07000c4600480086481c0c4440c103400304290b6a0010380c42c0091301c2140602a1a81040800d42c1d0b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 42011479 1250 42010229 42010237
    0x6010f0f0309020a0801020c06060306070512130204050f04110d05210c0706020606030c060a050315010509040204080601090e06100612111605010f02090a06030509010605041d0d03050408 82
    0x9820481048505008244030390002c490040d40900002c04a83d25034041d00e01030341205030000810300c204400120703e03240000310300b809204951510342c5440410041c51031010f070020110f107064a031490098006031a1446a03d04c2290140c40c1c00006003020f01d000041600c1d6400414130034940c5405841c0414004100c0f0610444c0108415a10104c0d8000e40343c006c2c000d0f2074044125000e002400036240360003146032842182e08409842d0b0f8110303610100403642c040d805245001550030300c00100d84020b0f5040c8005d4480050402c581021113030340014003079900540201c00c3c280c0117030380100911840350241e50410603940014080c140303000e25025107103840720f1044600300009078001e0100d864140d031201a0701c906001c5860360340c1e9203051001da082c0e0600030b011603c07986080070751214880144261107120380300812a08000385401c0003100034040c0940000e00556a03200000751070795862040450555224a0403401850101031240c01c00710682c0c605000c0c542803104100c00240201d00315 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 42012729 1250 42011479 42011507
    0x20316080d110f0d0e010906090305120f0408030a0507120f0e0c040e0307020904060b040606030603140a050304060e01021c0c15050103020907050a0203120103050303060321030c071502040605040e010e0601 90
    0x503175080d1020005015104c980c40c058030143c40c05002600b070507480001080b10140300b802c0080c103521442e5480d81009021640a050b10f241800441c840100311b4001a0b0013042d00d1921600041d130300301801040f211080b5258400036643d80805480d00018405594150382c21142004002c0c02c0da528203850344203500c802032264441c00c0c0043e0410026500c089054480900100481611050080e005120350701003034500c00d240551b0552858400618283e00c0303039000d00a181003a10b40380f81a00c90a0200c207040341903000c0e2002400c01020b030b0000321445000f00da038a15500c104c0b01c0c1081401c02900c01e01250380f050402c8010b00140c1c03074070441c09420882900d005542c640e150714040f811030203090181104104c141d000042404000405140954011001e42c1d00070201e115103580030400c51020030303880f45800d0001172400050b0b10050681c2a00990002c2059071034403504008030b80c0141c0202000c01e402050510044841c1068540941880754102e541800d250002030000c00d045602 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 42013979 1250 42012729 42012731
    0x3010311040b0604240e030604020307091107020607110405060a120f0c030b09010b1509031903020f03030a020c0c0103020a0c150605100509040c1e050a020316080d110f0d 75
    0x1115407140c540008803030003401034421709801c2403c0d480b08a52840da828141100103504c00a0050071854003092050045a0003030081196624040800c00985070400c0c201944490a12407840541c0310200100385880c812101d412609040208000440d1005001c00b4001e41818105126110103a44166810b541102c150030f030071412072810056050b0310b82c0009000f580c0c40c0044c49400d840540040b140841d0455041881501d420841c003201c0c015240c2c2c0c2603060f845020000c04294a050090380300601910507214080d82c482d81d12407440d0302c160b0700c03203440650004001440ca8002d00550003003031003d28041d0300c2c00049000c0100000c80d100005440b230030b00300b1941810303540b041d030009009200140001d2400150a035010704181c02c00081076014600740f0001a107034900c100303050302600c0310411300c1c8107105803901022901504071100c080254801000b0076540c50031700c0400c1c40c1510381b09a407002d48d00d4400a0241d03042d225201c00700c1c01600c0050051070b41e10070000f0305460f07240ea80070350 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 42015229 1250 42013979 42013991
    0xf03010308220803030f0a18030e040905010204060c050c0102030406050d05060d0204060b04142707052205120c0102030d0e070e0c210106050906070501091208070e04020301031104 79
    0x508100c50044002e00c041000b036495030300240364032020014500ca45800d00c80004136035285282e24095801d04910015145c82c50140600000e0051030341c107400d070310701a02c0051602456960703682284d100390041004210600c2d40301040200c10000285130040030f02c0034609145c54000c000c0c0490160070315840a480e15a070000d00152241520280c0b41d5030010410300084c0d595507003120b0755038481e0090404450404a00044509006c04d01300c464400380031103201004002881c1c9008490050840000c00c4410801c002d014442d00441700360f40180940c1c11005d60307141400b00840c801800c400c0b5015600880440000c1d03a030041306481280b0f50400000c5425400c42c403500741005c649801c00200085080240b1080c0c504a201501441000c1c1c02c605030704c040c41c01d440e0b0108240900c1b40800084003081178200d2405d10901420300103220380008102c00e950340e5124038004410303201c0070001170303000d03000c018082d80e00400b00410034005450031417a55055458000010326109903e60096480740 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 42016479 1250 42015229 42015247
    0x2010e030a050604060209121504031809020a02010606110115060813050708030a0e0604031101050d1d0610050103060503060a0213081009020901061403060d05071203030204030605010b0f03010308 86
    0x2221885a46030300c002900d43c1480c05251241c001d4001c03410f800e0003000c0343c0b980e170301ca5410006941c00c0c00c5d002c041114511030380d855900b02e4071009088041840715902442c0015808002d00151243e018271b5000410603900344032000f018800350810b00880c0342e050140312400131079010b0302d6209540c1d480c901b60259648410713513600380b8058041c00801500c101e03600011250408009841c0c0a1030f5030340d46080b4003920800304001802140009002c512100740201050342c080c40042c0301c001d4940d24081901e0300701c10781d10306c1c10340e15442c4000540d0300140100681400d1202c91400a0442403c08220b80c1e400d1001103952a10014144d105560b0300103004250300500c03001a00c01808200100c0d89000300310705206000d0410311030100d0042c6804000403403410300075664180700b100308019a42c03c0d96290020000b160340d410800f50f540d4020b040001c50300c540981c28040029010380c07805a511480c1d0b00e041d8040b580164026641401c050101c0e400000200084904503900700a40035142e40500b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 42017729 1250 42016479 42016483
    0x203040b041101140a0c050705030604030f03050403090320010e120307020105090a090501030804090608030313060209190f081e0604020d03091d090f0703080d020c0c0a090207050d05130302010e03 86
    0x903040c40d40c40d50340801c05d0703840c982d4050f484088084c402da06032074100c2c0e86c3d802030654860040d07078010302081c541600700503040d10075804540e200e802403600300b041c940c3ea526a042ea00d03009035941aa016a5075684008558100c0200030300c00000f41e0385040e494400703622090b260300450700000c6c100080020700280c07075514018420013425903420204515650307450801500e41c410310450b014142048000038284001100b036a12135104000320140701ca1155942c803009600c15110b00e54400040d028070050040c026003003101520b8401c034110419800c10002c1442c1100300c4020a807560324044804901d0740340801c0e009c1d00aa03040da00c50007285020300c0d05807000f2140d50030440ca903200e407401d01c1d03509250400070a806074a80c041920766005407070300b6494546826020103814407038200400200d1120ba54003c0010000d4481078403241c0b0119400194002e45035800035400071b401060903028484d0034030040311800040c0c00c00d943307814000c001e14500700d00207203c040e0620a004121050640701 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 42018979 1250 42017729 42017747
    0x210021804020412050d030917030414100617071203080910090308040c090e1f390c0c1206020d020c0f0c030c01080a0c090b0415120203040b041101 65
    0x1030082d034403a51074241d45020380c1140c20b07054a2502c904002031240c68028407440d0110350b000031004082d0039500302c503d00c6550004e0030442d1803410300f6400000d2006c062200341508501414007140c00d07445e280c2149007098031102803644c2500700040c104010308520301c02c145030903494104010f1903076442d00079078100206560504000c0d400c2110400401d54032200580c82a8805e4134020703035060b1506248401c4448100042c0056071210324038415084031004018070f140c0c0d9020000c0303203440d2071802862100c4020707000f90000f01c03101e1188812140980c0703c8400d201140d8603140e8070080c19070b100e40009440c1ea2040e1403a84c10310700203202c188166501250b006000c420001e540d503400c044074a51b500d11505041c1e400d5401441c00c0f88246140200301103101c0c0f10165a60034035034650103081401009000c00c1c407020b11030300e09030004121020700d000c0c0c0001c200156030490050607210000e0709014a0702c03001e110140c4104100b10014414072015a005500281d00400d0138030300000603104109 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 42020229 1250 42018979 42019027
    0xe04060608030406030f141302010c020f030a0b0105130b010801030303020a020a0206040e06041512060203130b09070305010c0305010302012106030c09020702150a0203091005040308040b0306030d0e01021002 91
    0xb004074900d81c0641080c58003005041d000c000180704041b4061681c2c2c7c0680341151700c40c03000500380e80550711841000045d280002c214941d0541c9288c0000c0c1350075a0346008403501c2c44030a00400180c9000152809000b00005c01827250740b95020000b0181001404020245980800c010241c0c61007003210000c9594040c08041c1d560b5116001e22004c80411a41c82c0c2c40b9a040182c05803541c40f80b1102e1004554441103031104070302e183d640d0b5402940009102c44d00b444150008040864a805185401060310390b0113490312a0442c1803083c02c0d103a07903401403414507013003900400060b640510703420f442c041d00c024004542902050410041c103019400607180c802c0840002c104055242e000f8514503208880c0805c0c040800c13000c200582c0580300506000d170b0801d0007a000e0314104450002101422031900c0d038030341503c96039105482c2d002a084070507003403808010421203007810043c0302c0c510303540b604111503243d2105000035600d03c0b00034582240c50b0703000305504079141e0307101c890803980704 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 42021479 1250 42020229 42020233
    0x180e0a0201140f043606030c0501030e1c0305070206130f020918010e030a110a020a050f010903080f040504051807150203040f090b01140f090d150216030207060302040b040e04060608 80
    0x403000d091070740c005030786480085141d0a04000d00c20040b0051b8401d01044036413296555810310300e400019402032500710b0500005018012861b0320b0240e80d9019040100320640300010035080c10480240340400040c2803039100d0403401c284a0115001d80210f0174041d80c12161079450f035036120000030706040114180745d1150708028910f194504084003400d444a0286c0d1000c00c1006142c140560f00d5001c0c46001e504200041014056800c0c0131032401c0788180c060600c440b403542e8a59030300d4003582c412160564021000b00d824041482c25000311500900c04000d001c0341070403014181a02e66502d4030481c1d0300390400520008415000384140c500410300d12403055052039803011400040c1c140c002701940010540003d4403c0c2c560300c8003e0b20fa4004c5000495070501703034250180003843c922041b00745e80813619480d5155913060140020712480110094001e07100d140c516001e41342c403805c1d07006102458014841400030303a01120aa0741111240381002903ea211410f060004020342d401c084528 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 42022729 1250 42021479 42021509
    0x12040308032509030308070f0e0609121005060f01030606020c100306050d030305010e010911181804051b03011112060d020301020c070f0506070c1214010501180e0a0201140f04 77
    0x1440d000007143c0110f0340039840d0b003411603985040444886c44441d030301e4004075a500f060740e03e80c1d08000c409000450009001107010b81e1107a0b0090785403501c0c055003000c00f65181d200f04021030802144002c0510750030b00b4240045820800081c0d142d180c640c0303509005400b61045100e840340301c0c0c0c101400802d000f801c0350801d1a0b55050080203028240940300408c50030303400020300c03401c5600c11030344120080720501d0b05094012120b1000c2007415000103602c6031503007103500c01c684152a5560f000300d01c80c20003482d203070210803521405c280e0003105940c400d03454200809107000b81c034804c45403000007034580e01d4910380e60480015510151088040d4240d0320109452503083c2000450a007070341e80401c00258510b0781d50702000001e1082c0c0d0b034000e0103d01104810010b01e9421a89100c030144500151904c0d1100d00e07001c84e003150002d92000a80d58090104c403244294984528a60001c04c0d0020702048882500068183c0091804048040b10002f41c10781c124a4900240c40243c0700c022a01145 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 42023979 1250 42022729 42022801
    0x20409080301140103060806040f0b090304050303040b04080124050d08190f080f0601050a030507020c04090303021312050601050603070c0b0709050906010503070914060403140a0308091204030803 86
    0x50703c1d80000d140440c0c074016010421510000b48944180c0c0e001e41c043d10304a90032f41d00c4040c1e00c800940068860301c03003440040392b00d40d42800a03002400480b210745840e68900300c805030030340c1c000031100c140705110710070b0550081c69180440001e85600340e42c040000e640600d007039149481242d1421700c0c2034440440b120b10310baa100b10802442c14841c0e4a1758030689940d401c0703c120460a8540c140030840800c100b81c02d56002e90481c130342c8100c0c80e0064409a26904010030161120010100c002a0340003074103101d01c82c8104001c0000c0c0042070a101048001503541d10380d05d0106000b00340c402c800200002d400b80f4410456182e840358081c0b003160103030406004c09450b6910034042d042c4551506000074040354881c0d0141c0380708441d103a9070442e109180c0109013203800080440741c2c0c4c00013002c0001002142050354200741c1e140395003008185610a900380100751120141015074590401c41b82c8041e0f06801d00f0070f8070145d035041449941e4980b00c540380355615080680018002e40340c50049684 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 42025229 1250 42023979 42023999
    0x109021b06040f0c061d010810052205130305040b07050111040b030f01050d0203031902031905090a08070b030406111c200a0c0b060303040b031006020f061003030804020409080301 79
    0x100c3d091142e454014a03d0316900c042d10300c1c3c6a514100c0224411041120006600c501c1843d600a5a28502104100c0d1150b0109035505810010403c60400920820102c2c01c018404c19a011003401e40515054144d40d070028164440c51180003202440814a801401420740c032a110391036280d03e00d1550f13680d0310000054144c10890f540da212548000c0000b81c98204402d5015089034020055440c02e40e40b1740c84861352034035007100c07601144024441510400a40c00c10f40007501d180d030b240c1030748130070b8510100064404103820a2200323801540b410041000725000b82ca405c540d00c06004214070424044801440c041c0f41c240380c0100202c1c68000c5c0e21045150310100a40c4489580d00c1c0c01d00034841c407010701c10f100b0741c4518400640103061200208161130021a04010010140d034545a95032001c03a4a6170026650a42c0b080401a0f0800c0015010007040340c0705003044001d080e00386821001260440003d21014061050300780c005004c40d85c0380c3c0e1098009a40c8006d9841c0c49585800d1030003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 42026479 1250 42025229 42025253
    0x17040c0b0304140c010306060801210b09010905062a0307260405060a062303030705101413120e030a02150a0318020306150a09060803070c09140109021b0604 69
    0x20340f074061038a844800d0752081c0282c034169442c50711106840c1e46054008404000c6440c0008445881c00d01400c000800d060241c038001c9164000118800310a42000f81c1002005856082075520902000342180c0c0105a03641940510755210360b00c0e6514082c058a40d031041d4540080c0f500800044d43e52448160901c4a000728010001c80e1115642c01d0000b9040f2503450098400359480280c2d220b444889610340001c81d404040c00f9a41440c0c01c0e661458504140641501700d12512017100c1c6845a841a800c241e00441002c40c00c4090f03003080d2101c2001400752504942007003a000c1d1000c180c1c1c7c40401040c801745a01030001c0444409010010f003858000039001000203041840c42018011071951007840550020007515080c3c46010050405000450419401c1020880001805003c42c80307550001c0a10002071641c6149130701d4964101c10881e040500c0c01450250342405a0005124030f5055905418005a030b0707803112450078400a408050100091140008000030018691015 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 42027729 1250 42026479 42026513
    0x120309060b0301020c0a12120213030605130f03080c12090d110703050c0609010e0901121b1401300e010b030607020a08131208070b060f0117040c0b0304 67
    0x1c004452481c02007500740d21501100c89860b03809421404040341455002400054140c00c1c400b000c2e500154400f801e917040348151005140d07503910208180300c0f0500581e0343c4401e9080d0aa410710241d65540b04d00b020710844058104040000090302494100c000c5601c600420044401103246c45007404d13a07281c4940e02d0000018a070700d01d070150103210014071002a81c3d0300501a000400e074580a103c40c40e0808030031a030401507030400004d000d0301d440d079505010309030050200340100f1403810a80251184c000c070203c000c2c0c070708850410041030ba000c8603080200c0e0910300390700454000c002051300c0854141100d003c0207045204e00010712866840f0743c001c00b004100034001105c03041c08140e110326045458030b0141e00704d01d1412002800d000c00600700c0c0380040c01a42006138441c00b11010010400200300d80081d00000c80605109010083c6580320390100c171241d51400421000070000408a04071030f11140c4000007260400c403c4e15441c80250440180d900e880b0301d400e0401443c14200c0c8580 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 42028979 1250 42027729 42027731
    0xa051009140a0615050a080a09021f0807050702060a1b0b01080a0b0c0a09120f150c080603010902030304090f1b02071701020c03160204090b100f21030c0c0312030906 73
    0x2036004441c5040700700d0754040d601d0300c1c1d06040c6c20ba03409076809607000b001d60300030b5556500d42d0703c01651201d50440440755000480090010440e80160200760007600d00400e00030203105003030042c0d841c0f40c104d030300d80d000c04d00e840c003e0000c05407025421081d00d144001d003440c40213030021480d1400041d08900705401151862100d85402e03903281c4c1030344103d002180000744c902a051040c0c4451740155080c0512074064034806400540301c00e00802c0b8203001a20f24107840d140d80e010721660000840e40c04c144101c0c000c00009085900003a40d0b40b0030f500c21004440d807500b1f543d03070500b02c41c1d42c040b01c003511032644040701c500c0030240001c0d03c50581c2e006003181c5401903494010000d1052095940d490740350750096141484140c1c4181c00701c003148100700c0c0d002e80c0303c4403104000741d4001c01d03060249034001d80c000816804c02d000c0000946590708161206c1c5941c01003540d08200c910030340d41183c2d8150400a8500203141012098002a900040d1218441c0224001c4507585684100c1c901c07806000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 42030229 1250 42028979 42028991
    0x20c1509030d0503060a05010c08040b04150815010e040b01140c15071107060e04230a110703050f07020307032405010f030302030316020f011d060702060408030a051009140a 76
    0xa050f5424082940c1c00c0f40c22401d0100d05000c194021510000402c0c00b85480138141036507032028211716481500301034003413030381100078080302908045441c0e000158108200c03071124110000070200e295824019111f59115010b19400d40d018420003081e0000d195940355889501070041070740c070006c4c0071422068811300e50002d12468032a88c0c00030380064441c0054000c0342d15001040b1403464140820b2030b48950345207102c0003442c1405441220701503d007001c4008501d40790b50000103c03001d0580e895a001401c000c0030000035440000c442c48095130b10205610760000b4000b103460894142c000915510030000b29030031441400d1700c00d0b0289802034078148150b03a01d80503444203130f0305070780310040160f170080c0046801650280ea008007072004c54412100640c100039070700742c01c2d0b82c1e801c00004003074403515041b00304010040c0700d0658800003a000410242c203155462001e103110003030040320303c5a03071000454888042c6a01e42d0000b03082148007800800c0d8040c0b000d52100c90251000700308945018 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 42031479 1250 42030229 42030253
    0x80d0507110f03071a0606030c070203010b0a0602010507080109020c150a0b030706081014220b0307060903061b09050111030712050c0105060a030b06010302090d1202010203041208150d03020c150903 87
    0x5d0521442040b0140c0030b01d0664032440d40c03204d56500320880890703241d500d1341019402601c6400302030008000d03540c00400c96040524000d0b011581c187c0055403c907004003d0030395506c40000b0b01a001e000d03007089070b076126943c1400e094003c2094103100395060180550025040c0e030f0040d6824090520341c00320021070781e030b01e00341022800761040c542034101102e807451a02900398201040a6040700715008900d120a810019060003181d070000070204101010030710074002284a2002c1d4807c02064504412454005c080d260414522482c0c3c100449062184984031091007500c113425440265501711400084015010384c03c9500961039661034031001500500e0541c5604d003c89070481140d40d059243e500c0114080d40c81780418582002c2180c0c2d21000186a4030b406c040888250f03400140c0720300703241c5004140e003e2241c0381e0360200850082801880745070703100c40b0300b076011080b1400d1144030310500c2c0a0341040c280030284c603400800d181022600d88810402004090821416229240300c90 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 42032729 1250 42031479 42031523
    0x230901170601090506120f01020a02010b0301020414060309030d05070905010f020c0d15020c060a0207020a0f0f091a100906080105030102120402040906020405030d0504060813080d0507110f0307 85
    0x400c00d000300c0d031100c030040002841c0c0c0c0d40001d030060806410f004045400001040c03800000d00c2c18032030745030b41c00038140180560a125501c4074110480007585441e142008a40c40c06889058045c0b19000000109540c1c15081048903a000b0b00640e05000c60b14107220301510b400d5561240d00c0c0400c9480c990003e4403031001c502c00122040003805803020761f2035921181281441187d01e400a02e5081014107004002007042e1449844c0000001d65105804d105122000d1810361007000140d102d0b40e802d0020441070180e10050799601d00000403800d010b0811825030904002103941c0080d2016040c4255a90100a580c240c0780c01d03490341e041c0d81c0d0b61001414206d119000c7e405000300c0700280800c0061610b60007440c410343c0034100260419490307100090034002a031a5180c00700700d00007410050141c002030141d900c01000121000303c0c007090303240d002c0288035400490701b145030743d030b80020b0143d030169200740500e60b13a1104907244032540d11007060740d80e07209000a0322503842d0912a003e404481c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 42033979 1250 42032729 42032759
    0x6010f030606200316060506040f02030603060c07050109020a030b040308070234150c0c05040504080f09030f0708030d0f09080708030a0f050c09120105070f0c0c230901 74
    0x1564a40880f0240d010000c078000100f035640c0c00d003900003049000906500e243c0942022030094400003a94180076041208075203540c4c0c0c049000600500400195507404141c080d84841c1c0201c3c017650b1a40340707141c000d0041c03181e10301c006c0d84014149808014032802d0724555210743c0c0301351540c40c0d454440c1c07034080e82c0d524080303101e01c60323400c444c01c0d210407000e0440b0307580313405601c003040c25808059125183d200d0300303600105642000580a216182c02c2c02400071a02001304410396007000182040d84a100072440341070311221070502c0c00600d0f411103072030800c83c00120510755070a03030b2901e5844444a6407294070142525090508264411001c844c651089200b0076912440d801e240908070390701c0103027a4200810401c10345503103500800208800d40105403113102218904e554541c0c0110401c82100b0401c1d0102e003441c2e2405040110703c0781c00c5440c1c1c1c0020354040c2800302c00c4901034030340b40640c0f003900d4000042401d41221120a0740842c04000000d40d10704898000d016a00d4441030701034910 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 42035229 1250 42033979 42033989
    0xa05040b132301020c0118051b06070605150a03050c01030c0e03030d05090f06040c0f0e040f020f0604050d0c0807080303070f030506010c050102070b0603060105040204030f020609010203071a06010f0306 89
    0x810181801c06103280803848800c00b8000400250034884000c5c189400c50b121819410482210342d0040b004001043c801300442c0e00c1d0084061034804203240108009000b4044010090b60340d51001c9540a502c02c9007006a185004103160303405074681ca0820b803980d202000c0e89000c40d040c1070351220740d540240800400104054029030070a0144090036007d002e0241c08c080880c0914028440030400c240907103031180d03000e002d6480440b4a05207501c0300703a0340c0300e90003004561081c1080c44001115103001c0c1100136011140040f001550000080062189500c06a8400050328203d400c000d03140000e8000c0301d8202d8180e4040c15038501e11161680b204a4103107001640310042c1d001000c1c06a40300e6a0070080c10303d840c034404c505998947c1e003241e00c0488207580321803030002080b1052401b0407019004d00402d54007903042c54510b640760511041220002482101c010819520760f074420030642e15265000170242c4001c54100c035090720f003241c09440450004a01400350105580a40109001c0724 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 42036479 1250 42035229 42035243
    0x1401240b03060d060b0a080a02010f03020f031906050402040306060f0e07120f0b060a080a0501050406080c12010209220e01020f03270f0d08011508070c0c05090a05040b13 75
    0x50b403520700300000e61410407400c5a15a503200280c0e44951503440d146c2c00035183d2240103000c885110300002d40380c11104507600c001c15004000121034405001c0942c1d4110105400040c0304805401440703001d07107816000305d03801610206001007485000e800203011203802d9440701c02c007280c50744014041c4031000c82d04d00700410410104203c03140304980c0100919840c203680060103249083c00502d0303075070004010800190300b03441484441d6a4a2251a006000403101003100528060803640c4a00f03084c00740c1c0d440399994102001d04408290102c030b0801500410030842d0000110701e81080e040b007540300003009460b1401c540000301051088602d100d613803242d40c80c10350355011040090b6002d000401c180c20a5142c6039880c50a00410020b9491074a020260502c0d0300c0c034038001400c40805a10540850b1442c484a00d50701350041c02940d041480c624242d22170030090b080601440c10305902c81500f21181104204203075a450b03008601481c80351210359141d450300c00d4807040c1c807442420050455 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 42037729 1250 42036479 42036481
    0x9020310061206031a090c030a030906030e030c01150314010506150723060105100c0b1b0c0304090623030c060901020c03010501030b011511060f040201030204031401240b03 76
    0x55001d19412a4600701d80240403c116407250340c0d445000540c4041e4400c40300f03100e0709110240906109610100c4815001445180110784004201d4420361041e41c1c140340e62222101412038040c0200d828075030303000000303000d504a00301310252a25124802a1900454000103540c109010700403140a070400902c2039250408c01c024000307503640509021280241c1c1011014007080d281e51814402030f0a1101509036580b4001c1072000c0d14414444076820004210030740000540c64a5526410007400e05990138083c10004410a40384110201c6900d00e01c408100040d91000036041441038401d00c1225007812040f280c041c45919014521807a8943c020800d00c02850500c50003601c00d400052044409400403240400d0840d002a0000d668001581c030050010001304511401900210300e4003001c10f078104c1c0c41c1c568807000043c0c811201081024045019a8440d80549019581280082c2407d008030985203000300586102d40e034048002850050161100626000072a4403400c3c01600d1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 42038979 1250 42037729 42037739
    0xb030108010c02030c0c010f05070609031d010c020607080d0905030c0703110105030115030c030b0607050109230304170703200906011107090504080c0d080a11040522110a02030d0609020310 83
    0x7046c81203110b51010001b0030720070b40c8081412f6006000c001c9010740c0301c0c40360401c1518540300e030707640b20741d81c140c1d062100d2a803e01e80140c035028104c901c1103070020141c0383c40700b040030903150181c8600e0380042c11612000c02c0c1d4440d03041011a100342260710840d102641c41203800010356440c002480703904c500d10804c4000e4007540d4003a80040c84ea90b03105280000300180d017540015140e0700030840c1900d00e41e568403811010842404804003e11450040764000030303024980c066a80d10460252456165080b050702054550130014003003d113600015156030708000c00e00c2205040200200548540181000700d061940a11081250610041e0140108a05080e03484014050103401107603c21400c100c0c50f000b1207420700c125a581ea83d107594501160402841c03810940c0d211411595a00b00104810001c50342d81a220303014035048101803801d400344452004c002401d80d9294030001b0301c0002076003014264044001c10503218030b400b00700b25442d1202400c0c4100e000031079188050306c1580700c060007 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 42040229 1250 42038979 42038987
    0xa0c0903021915030f06080c0916140703080f0609010303081f0506070803070f17010905040609020901081c02010603230a0f060903080c0c1e0106030c0b030108010c02030c0c01 77
    0xc0c040070b440320304010036980ca880304038410000d030303283c4002aaa40001d89403008640a0100100300c1342d0000c0006e103048000040d40600d01800d240c3c1024007001d00751183e00d00448082511000300102030343c41e000d25041c040c0888004807241c1158019450005115180c0800140e042c2c0b5050382c2c03409419680c681c2c1c00c11860b200301441594041c4012030000c0d60380ea400004080c0c0620460341c0544030b0410010103411346c4941c140c032405201c1062001c100d5481c25444d054111303100e40e10042620f45960070006c006100d0304c80c0103500039540100102c0d0003403002840585101c400394801803a40000503040f070803039400703000007410780c510301080c50b440081098103103400c1409401620400b1242d82d43c0d40e034004203c107074100d400c0d6407201200420700d07070091069980171408601c841c4c540f4604070084c5440e106d5444c041018101900e19200e030410095008502860744000e42d5680e094032000441080e400900c00c000e50345d070034003280c030034082d1010040c1e40404414a008044044035040151 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 42041479 1250 42040229 42040249
    0x30307050a0305210a06090608030315010c080d18051011030609060612090708010f02090603060d08041a0306040e0102040609060f030906420306020d02040b070b0f0a0c090302 77
    0x84003900d5801501301540e40d030014964000c0c0b60603a0009a04c41c900181d100c00c0d035030325600c04806c581040c0100044140d4005100203201c8d02441c220240720110720304203020340030380703600a43c0c100d10f81000034001414001038125044c3c01a011614043e100d09110010707204442c10182d00c01c0310900100c0c3c0d00b4109048a903400040040c400303410041d200c2895001000121502c10142d4032105003081100020b100e500001c81000340c0c150b1130071070980e0100e8407500c0003030940b9010b01c408032942c00510480c0400d42d009420000060f421910316080181e44540050314024855072502c040d5212440c0140308940c11600c464848014240c9064800da400c0300e05109010180341d02d41404d4400600c0c54404c51044015080d00e140c4000d40b003024411844206c0304800711000c0d91044d00e105103142001c1d4140407254000300159503100d03005002c1c0c4c0680604d500081a004000c95a0400c0020f014000ba2160a4a101c003007115030352202c201040d140c12040d98000300c1c00100c800e1015080962200c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 42042729 1250 42041479 42041497
    0x3010501210c080d02070617010609060e01020106091a1914090702010e060412080a0c050315031501030f150207020a050909030c0a081903020408070519080304030606030b0105030307050a0305 84
    0x681001a990b100c3c1d02c0c200300790640848016001110140706982d003080c409211707909980f50f00e078615070402c40081e241402074040d1350b091124020121089038400d41011001d8035102c001840410726070042d80302901c600980061265800d28009004440e950000904940681c110041100d4140060060010001c0c1821046541300e104058508204200e40c41c050343c030a076000d02140e0724403580180010400341a00d40454200f511241625078801c050325001095811080c10310b40000000a2074030380e88406200340e18103080000401d0240700401980b01d5802100c1e000d9061960520000403172040b044001d5108000403000c0c80142800e00c8910ba011400d0402c40b490100c0c071210780b5140a034604011181c508000801400f40081000030700030040103400d080d400c00781000415078640c040340c043c00303000710201161f40310320403032211a14000704040b601f580c0d90340c0d403070342440800b0349454003040d10344408800000803a0f00b0000308407092365801c80301502d000542a81c0441b01d81c4e2200b40c2c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 42043979 1250 42042729 42042743
    0xe03010b03031b10060305060103150c090618030b010e0a0c0c0503030c13030209090f010e0106050306060d020105120108030304020307050a06081f0b0a0203070c0503060108150901020d0203240301050121 89
    0x96644d001c03070588101c101440c09200188007561651034003104000403107021032400d43c1407289204031b82d034011511006440745400c0c400702c0f4032000b013050038000c0310562020f050455404000100780068010941c02044180002d0011312017401d002d440300780403d0001440c540c02000040c2c00200d8030340c0500700c00f040102000c00804d940c0d8001800a1009803900d40940c2c21103860841d1159091180c400c1c5c803a98a8001e1252a00d000f00007034580c01c0003001c803405419942000021684030380200d404581403005e42880711350719242c0c1c0590305c0e0003c50b4102d00922070380d000070400c0e280c40b5444070111015a42c81c0030041d5100c04525034120315010301140700e5013000c18081000040701004d008040140d038010340e25007070740b41071801e80d0600d21b511407800780e001800144407607003001c20386401c01c000b0102b0300304261300d07031900e00c0780288a40500c2801780c503c007005002e004441c000b20118001751a22592b4486030300d13002010700b00d805c2031180c204030284014032420510042e02d0f00411841c001c10b8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 42045229 1250 42043979 42043993
    0x5100b0a0b070303050a0506090603190809041407090b07080306120a06060b0702090c041401050703020705030a0b0a0f0506060406030b030304050603070c050d090501020607110a0c150e03010b03031b 87
    0xc030301c0e0240c0c1120000328042074030f407410008481c0103881103136446942181c00d0796013410610007003030301c0d80f105030074010180c0c030401c0c00340d02400a540300701c40d01c2540140040011200d01c542c080020442500d4400001d848400c0000d0300c580c062080c0c071502070b000f01c095869510380074100300d07818000c80c4840c4094042c07060410003103071051080e400104061140309075203c0852040100c170a00043c102d50502106020600110080f1104140188420f0030600c1e0750300010704050340303441281c0e80542c0d03141c4510710014042142050089002d81c0003054184014405101004140c0c0c000301c0d40c0c030b504070f0300c240020031420348660080d1181d400090140ca29064848000c90540d902c125102c00105a1290303a14082207800c007d412400c0e4168507140310301d941007200003500c8200c017410000400c414490310f9907100d0424400c149042f980404800c1d0300300d41d00c04410310300343e500c28010008156000e480f1015803c06008214124400a015516020302d0f07540021106010180d91604c078401d9203 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 42046479 1250 42045229 42045239
    0xc2c0601020c09190c03020c0304030f020109181a0126060628090602030304051504080d0905010c030606030b0a03080a0302040b0319180b0a05090c063405100b0a 71
    0x40103103030085203032424100c60303800c10528003801d0b03811511a41701054410080764880300d5022003510241c0740d0004080a1810351800120b0f01107400c0d0b0008402044a0500d1030442d02e019070080b0407402c0d000c1040c1151100b441f0064800900d042d080922424004481602d2202c0340c0c100710341d100750001e21039400c0c00040310200341101150301511240e07034000c1b00c0d181040740d00700300d0140040045100a518515060707a55549030a5858504140d1446510106040011000903201c058103050b808018400007400c042d4041c01d400006040440c0c544003000c070f089882401104110300c4041e1141e405c0078610341c1c4011302c6a000034681000c02d07a0a002c00704911181000a6008102d519610b648440c00c0c009036008545005130010590240d880c050340002d0001c13000707135074000040740e000074059030307121070460901140d1480f00c2d610440018043d2078156010012410030f14038210b4103807050343d0300420b0586038078440c44042c4c00b590051001c00c0006689800928000e0307005008242c1103a0381d0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 42047729 1250 42046479 42046489
    0x90f030403050105040c080a0503040e0402040b0405150a050405070f08040609060e1e03031003080a030f020a20070305030f0a110d0f030c0c08040b130f03050303040c2c0601020c 78
    0x41d08101c600ba5158424402402603c0c80c0d040098422400a0f02402e6001d680c2d81e50780388075074441d2660b40201500040c055603101e5120241001e0701038400d00003881d00d0503500809040c03107103480380315a5039000d020076181081d11401e0710030030780740e01c1c1d03102c6690f1800d41c1602d09000050080354525140c10041002402e940160242151401d005044d407135400421400798a07035103040c3c0e00040d4014810006410365030203580f41100d030480c015641d14420143d08502a01c40890180402030000404e404025803141100e24550305030740321110398013004515161900c00740e20001d0641d0b80144040c1c040404088001e040c007905a0911400d42d800f5200c01504010b6440c1d40e050225544440c0611540e4050007451581c1c00705140130425410340f036445201a019500414800a9005c150070b4641039880c0c4c40c0380090080c50585048480ea0382c58601c3d41c80e0b0084808580200c040a0009124680c3c1294000391120520070b0381d1a007600d00044080b481801000700b4114030a8010b80d29907a221 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 42048979 1250 42047729 42047737
    0x501020a03050f07030203041101050702060c071e05010504030c0603110c07080d090510140a020304090608010b030708030403030804020f060d15141002030301090b03030918010e0703140a05090f03 86
    0x5614082001d1038543d4440e060900700804642c103140c01002044000781d1031a6012040007024207111ba11790842d80081030310703030041c82a080703000d210703031840854640244900d40c001d805a40451003030700f070b80b50001103034140500d00c0000d00c01c411802c414445980250860011907c8445016003271842042210b80b81c005207501450380c5410885044181c10b034001e4056000e00000c0d03a58034003440000740b001f00044400400603040c0000071441180307103882401100d0040081800620046032201e981a000304000d40c0303603510078031407004000349110003c4160360849405440f4002aa030300d580901c08808607200e8400e500032410070403042c191641d44243c2400030058102003c2190070400400081034500015038410741310000c04814007580002180d0540341184d00210343d07008018086450350140031100760b0300000400d0901c0309604611030550480da0f0281c804416615102420390403194618070a00c400510b0600041218109411068101c0621401c0301c51075150b0441850840d00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 42050229 1250 42048979 42048997
    0x1005030406060906140f060c07180c0806061902030f0a110706030216031101090807030807080a060f03030c030c0206130305060a05090a1424012c0a0f09050102 70
    0x4040103200c2030002900c107900180843c041c040094030b0400250f007032600309809070544540402d0700550501d45424050b10001120002203901e095103510402804e220000d801c102214680140440c00314400c8421038090340010b0442464401081030600402a02c0710100b425440108001d10940309010000c000e0101940d4030030f100c04860f070340d2060071311000d136001a080500500028100025101880841d5541410054800000b5041150141c130082c0d201601000c1701103941d01c14144c016860f04e200c1d4a5694490000e41c0d1101c189004417141c6001c0c0e90b040048485040c00001e000e4204c00d1081781c06810045600b00e03060340000c2555009000850640c0e04a800420070010300b0000e00c0e030012410b0205018920300f920701950355900c551405815400c0403491444242010300c800e114a200c1d118030760041303011000c105400300750284203074829410304a11a100c2130321800c0e140b05507000072410222030754031000d0b140c801411000801e20065680c807600040010300034401841698 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 42051479 1250 42050229 42050237
    0x403080d020a031d06150a090204030b100806090c0105031e0403110c0105040b0904050709090c020606090f060d0803100f08010504050c06040305150408070210020a12032003090a0210 80
    0x640702d500b000301554103000000c00e10f4030207030103481006040410421382c01000c641e80700829040b82d50014400145590003844414800a0044140003030120510f05ca40684000c0c91016980d50150903510101102c00b10056080400400c2d12580b04d040190741045c1c440350f032052004040003900103956029a07084001c10b02c0850905108101401012803070a02402c00170300700340c90701500c08018441c010f242442540d48500141c04280184884009000513070030130803007516802c4020350380d02c030306a40d264030610300c400c0010742e003020324890241710b110060034224a4001c1990f480785581c101400500140805080c040341a00a24008200078104000086014200350800c1420702c00f9000015020b007404000c1800425000543c3c0c5e642d0004810100100390b503581011901341c0100c002c0258403007040f50024a5055001441d0481701d0b01400d0400d01e0780103120003d9003100d0304654907140c074440602c022000c686d83c00c80a1617010009106659200200f580080c481142c40580c20f8041 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 42052729 1250 42051479 42051487
    0x10801050c0f030c07081317070b090105160c050d05071508070207061209082205030105061008040807060908030115020102070f02102003040602011a0f0112020403080d02 75
    0x10442401400d400a489005140c0340000c0001d00030b02c20f00c002001c0c8002083c00044a500b08070020040b1070b04071040301401c0041c543c41b034080c00b100c034008450301c5110b481802c80101c2d035000407000f21801c0420507184e40d8a405682c803c40c0c44480d900c04420740c0c01e004400000209602e03200d4410307007564414030140540c60304110800e0448401149800308003e0342c0800c1142d8035800217151401c1e00c2060070440344104000c3c40034000b42c00d058100034440840425200d166900071040040412403201200e8256504d400a05080b540103c407820f038004070040203e4480d501540c0c3c03e5403c140aa81c2c498501201b50b25650700360351015004592035a030000c01001140300f61400007203100000d200a6207070111507280c040f2316400c0b90801912401c3d06d03104a03074a203405100f0b820302504c4155403142c00c4034452541c1e281c0701c7d0002d1084030095400d00500030b103484840c00c1e6444040c2d070010081d0000401d5034004440354281461004170482c1e08200100103d6900c6010301a101e0f0820000360b51 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 42053979 1250 42052729 42052739
    0x6040524040611100c020316151a0405061020030915030f0906090a1101020c1003020c010f0203040b010311031509010606110307150528060504060b0a0507060903050403021801 77
    0xa492540d0302d522030307000d20300192000060f902204845100340c031081c48c4140052070341400401d900810401d1460b040c6001c0040301c4007003600e414040380802c216010002952074005011010004024180000b2500001408030307003280c100f80409041c1000840381401c052001081c01d1001c3c1d06c02c0e503c9020000300402160b100d80c849103da201100300098101030802040c19695911001002018090200e480c107030640d208005800310118001c00c00d0024000403a400341c025444480c2141c880c1d424030300341c0c0301c050640f802240d000d545d0252104a450707113076031100000b25490003526075041c014900c81102c814008202d00340034008410001540707629260024080c09400303070b14409039800034040c01000c620403d910481e9280f03540004a0180da943d0451007103c03c3d60208050b40d01c52140804004581682c082c005880069904002d01900e40850f0105030084c001c034031000850800082c0700050f00c94001c141e005100303003005410a07889034001003a1004042d410300140c6000b80040103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 42055229 1250 42053979 42053983
    0x30040b0603030705120d0902210717150901060b07060501061e050a0c05030c01020406090e0705120106050702060d0501090507170601090302120715050304170906040524040611 77
    0x203003104049000354a0001280c1d9655101c0c1c41c40700b0440e00c2143c0201e96040c4441068000200081c1d004142c1380214146540d9a452003200c4240e41c103543c8250304c000b10341084d13101c80c050302c5038265100038400045442800a103205005041581d60f54075181c0c00603452030640f01400e11070703200308000b04131b940c109a001814022440341440703c20300c2d8003c1000c01a86c228003102e4080020385003c515200345400c00034614031410a621505610000300080c0d41d6602900c0c40041d10020540042191207041089038540500304048510030b0481004200b464040c000521003503102415a90038140c80129110495100740c1c02548400d445504203c401503002c0d64800304031710381e010080c1b02800c2000000703285180c680002030080308103482052481d1420004900148a25a401011034a403000c004101d6041505c08483e4008142c2454511214240948017084c10140040e41064649001c214800407a0003584e00914080703409a200260000000d0000d041c6d1034a480ca048442e0031a458 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 42056479 1250 42055229 42055231
    0x4050307120306050d0609060b1c110315070809010608190209060910060c020301140106020a020108090303070e011b05060406051021080c100c02060a1407020d0530040b 74
    0x20040601d060f0040c03141d5500c81c00300d0000300340c2103600050400040d250210003031241c00010340d0b2110b40f01303070307000101500504038000752480340300680b06c003e502c9820b00d969a42030202e08081d810100d0000740303c9a01c2a0441d40d0702030344440c0086002035880c2190360414030361001494003408401c400d08198101554501d8004006032000302c1d0070325001c03a004801103005e026501c00c0155844031041955000d401025008005020483d420b503542c0d10082d41d82d0b05150001ca000c52a000d0025441c00310100650f8030822240d103401e1032080003040119040743c9c10a0301081e061108264a4000c03503000c0203d64452481454001600d0a0914141c00030700f07030720780c80054030f000c074580b0788020b040000d01e5a25442e40e00c549110b48545001e0ba005003443c0074080d114039410700d060014004964005906809498020000c000e071500760041c030412072788200c4240b800b62f40441d00b4a81103612a900a0000100d400c944034651082441e40100701842d0741c51b0800c8110f200420f100501800c09046 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 42057729 1250 42056479 42056513
    0x30f0b0306150415030c0e10050315160c060e15010f03020102030906071a0a06060e04090201021b0103020f0a050712030c0906030b030a080d020d1a030c0409150504050307 75
    0x10072451502d01a0b030001c1c0304060701618003a94650300401c000d0301c10840132001a540c03112402144584520905008400403a00c0110300d041d2481c0000d50b6041c00b0503207801848000d4201c002c40e540d141c4014015070000e94656041020b0f61b201e102c04110359109110001540308080c00e074806812b00241440a01a0000f0803070b04035030142000141e030000111401400c099441585074842c600b071040500368107140d10030302e003540305040040f001400d60240302901c2858584e00e0501410b1000d100071a82680d500902580c41102c2d84c000068510504036100b0005250241c68030340c0358500112941c00c00300e01d54002c203002261000c03c224031441407104016081c942042080030b2440000d201d080c0324481c1c2014142c1e14402c42410b51000e06c150354000ea00644416a60980b0b1202a0002c3d4021303034817210400c1c070b00850125801e400b1072a240c03048000070003c143c03803a0000101700007024000e100303c94031700800c100c5892865190040c184218018005540c0350b11503400d249400c09039031600 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 42058979 1250 42057729 42057733
    0x50c040f0306050c070f0b040515040b1302150c07060813030806090c0f0f0403141f0c0e0301140402180105010912021305040c0f0e060603040803100b0703030f0b03 72
    0x14450a4030329060042281c0e001007000c5219110a07110005610800402074210354100c0021020b11101a41c941c0c040c5100718111451800e95040b840703c000e50540307004106a102c4030200c0c62050041241c802d44034001041071906c044a00120b038019444014981c15540111300104441508910256800105811043e8181a20b523800a0a1242c01400b8a120303405040101d24071000c0d40042da220071007128a169604d418117000d068898001c1e2100300e90a143e80482c801d290b000c00309030303001034a17000101c2ea503c614600150001030181c1c05030300707402c0060540800302a036801340a052541c0009002000c4d46041c68014010240079441c00400004070710801000a07903031104021003110070102d1984200005440000d201e0f821010002c00c40700d04000a01c814021464407110440c1c400e0f02442c0c100f04e50300d5007400c2115504031103059020303a0520004000c503d1102c015076002c408818130440150b11241044003e0b00515030a90001e0341e05c0e12040c034800018400c041d0303941001c0380 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 42060229 1250 42058979 42058987
    0xe0c0a050402090a030f050f03070507050907050901092303031908090312010b0a050708030a05060f0307030f02060903030f0c0d020c09041e0302120406050c0105060603010b030117070510080604050c 87
    0x408520301068074032004003459070f000461b60074004140450130030031512500750780c1d5403030710350038056910407403409040d1241d01184042030041c3e0040085904d50301d4107859142407a850b180241078210442d4030198a00e10404c01d104041343e609100510b201304080880b417128502c0d00c0401000243d005041e0300041d401040210084103882c80000d044810b03140710305513111103d00d0f088896024840f001003030300001106001c0e81c4142904103e00c81c04060342c1182c155924082010b0750742030b2a10002c0e146d5080c0810400141c2414001000c1d1840003030202d92030036881078581049580701a000c41450b4004c0301d0310300c07031065052003650030354401155020344906180c1c440035240d510100c0c6558011941e045d40004250003030000241e9244a017034400c1d12240d540c0e001510540c040843c0c2d006a5103803c000940d40d20741138060b24141d50164801509607801c0a4000301c40600802c8100101c0c810804006150381e6050503118031a501552550b286040120a2206030f62029244201c2d1150900c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 42061479 1250 42060229 42060247
    0x90f0e01030803040f020102120d050403080603032704020f04060207180504120302030a060510090503060a140402100909020d02071103010b01080703020d0e070b07120207060905040507020c040e0c0a050402 90
    0x202c2600d801c03c2d000b003042c0c52444030f2440180e1a06940d01003030200b4810105003018030400b194032036403141c0d02039150400a075560300101a203a03c03503240c2c4203c40c1c138911650b41c0c541a00f2140302c4000d04802131700040c13402c0e44000011200b504264010300041e40070900c24480300c2100a5001d260b80080c001c28045802d1984d81d900c81e0451406070300040560200001e100e910303207600000002e000251202c0040348002c44000e00410040c0903080c06031103140c0228500310540c1c8902018406260001200340e10b90342c0c00c1265007405207800c102005131540022400c80e0300703440280724451013400c0040c1e84040034038140d01155001c0c1c0e240d9100b649003402c443c19603604892080d03840315081c0740050f5111145594440200148080c441491060700c0011070000f000000400720b00b80030350701940040801180880c1d07580c601d0300030900000c03040380c0108a2410103400c8103412251703900580b813529494001081c00c591813040303882d00c0c030f80c4014420f14481c248800385001404050340e040d4540b00382c00b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 42062729 1250 42061479 42061493
    0xc010203090d2c012a060f0b0315150105130909021002030c0709020309010603140303060f0a0807060f031103040c0f050f0604032d0b01090c090e18030f0406090f0e0103 74
    0x1a03083c0c0d050207002000c588051010300d03150b0850080b4110034001c040000e00b400740c02083c40b910700341c2030107180280c0c081d8103140c002104001941480f0140303005907601442042441d0910303050b5030501c24188a0b0f40854220900448042e20294a0008101c00f243c010003003608410f02138503040d07420130072680301e00e014085092020741d1040303100565281c541644060041c003040e0b1000d4829215011801d202190100007180540030440d40801404c0c04a020001c074160284103e90035940020b104110260182c10642c4040c0028180041c1c00404481510000d80c0102c1e412103290800340014031070304900354403101c00303040c0598042001c2050980420060310850201800706010300c840e04201c0b48541c15040307002140c030107a2108111240c500a80040740a00801c50840d007800c0000b44558480c1409004a8003519030f00e44aa454050a07003c80030381c0f110042140740420003075240249081401440200143d0795030940c694170b0071040c4000f2540305d810810b0f0a90040c00104045042 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 42063979 1250 42062729 42062807
    0xc052a09180c011d2407050105060a0803130608130c080c0102060c13060509030715080405060f070804020d0201090e1806090f0a0b0703020d1505041b0f11030c010203090d 75
    0x1695a02000d94400c0d11034045005c1014403022440b00018020003004019042a4010b084c240c0d8501c4000751244c020703030385038020380e4640048440b4003241005000d00c01c028840c2c11401c201c4446108031b100b40c0724075191208035084501d803640001d50703152441d41d04004055101d100720001e50300300f0303110851240c11591203203d440200b00001ca1b08481c290740500c410760080103106c84c070001c0700400e41c1c00540040700450342078425001e0440005c0c84607000446641c41a2210780d034000280e40c441d401c00c440303604081c6003030741000410000420f0f043c080300a11401541c1c0c00710030440b50440000d0b142e241140003011000c1d10781003011200b00d1144000391b0143c10590182410390f0b5580d030b4003c100d0081c043d20102481a90a14805440003080102c81009940741600c0912026101243d500c112040c2c0d10171903000610011101803685111701190f6400d07842c01c40c03c0da1300c1c1c0341e240300030781d805da030401d03621a0540d404c10300c416035805400c0341d04280c000701072442c8030b010005166940362207064 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 42065229 1250 42063979 42064037
    0x30f200901172a0a06020102070c03020108130b09010b04061e0312110102040306060609090b0f15070b090d030b030a0b0a020904020d090b040c05010c052a09180c01 72
    0x808000366242e10042c0324259501000315840c08440e5440042100351002040342d41d40110800c4002003201c62043c0219442c840e00a014050050703d96401150307201030082c56080701520702c3e407002c4006016030b01c03a1405050440c0002c281c8481400400040b0390791540500110484900c15809035003494020a0860303803c14000d500e4841031200a544443e440c44440c8010351000170040200b14065000500742c0e0310300ea894001140d2611200e0b8200c13a40440c54681c0100300e088c040c0150b2410010084070340600c0c142d02c0e07003454070f103586282041505440b180b9154001c80c19403920280d243c40340018100003100103001a803007540364254200f1000e0030381590190001543e5090340c4507034044808444500d1030400c03a0404505014000c450306440032166042c001d080090503601c60012940c900e504180680f52220780380020802062944903506803a4140111a034860b40d603008402d0301c1101a20108040310808203101420b00d2140c6800b281480b60050380000034007414120210189 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 42066479 1250 42065229 42065249
    0x70302040507030e0d1220090d03110a0606031a0106080c16140a12020304140405060a090e030d24090b0d0b0a020c060a06030308040816060501030f200901 68
    0x148032001c0860207042e001c0303401300b074030702c0f8510328644295030111071840341c0c0203c00410460282c0042022122107903047d1900441c00f41800703400f95500c1c100e607017504000c1c42810045c00c0c40b00c1c0441c0c0f9038200450240c0030740d122a51880204240300d18008102806c0c0701582c24011158100440642450805008020115004640b80d01840d4030001e440301e000d81c00c444010440701c0c261022550741d54058008030f40c0c01401d07919900c03602d030000003502e054504040041042d45120300500004210003000c10b580842c01d41000100000a0b1050454128201c03000c2c55540a03180075060503a5800500030b1030310030701c1c2c50001031000a46607801e0180c50520b072000c0380b0f8040c00c0c1c00055011a01d00c2000d0401306a03035061106800c9941d0050055003c40c1c0c00f42c0d0490350b01c40b05254226400b40c8006000b0038600c0c80060300141d2150000d01404100c007540303030955902a00c400d802c40b1802d810485801d02c10f00c03a2841403100c14540da0700c41004904010382d1000c0304002240944206100301250b034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 42067729 1250 42066479 42066481
    0x6050706060503031611090906061504090c0504080f0712060506061b03220e0705030c0403050a0309030b0609060a030b09150f160206160e01030e19060615020703020405 74
    0x46541c015400506004088a1315108045080b079000c1c024000102d41840d800341c0b00c041103041a55102d4811a20310020306605e56032030041c00007106207440641c9c0c540208000c0880c07803042c5481101000c0301d895641507161410144001e1800704084d006640c0c603880b03002c0c108919156203107075a40c1143e10040120385030b02c41d8808182d0500aa502c10560100700b031041c000044070000182c13000302d91004105090711001400780d120102c40c0d0003880c102e62524800101450700401c000c0d80c0019165100901d459078a4481d2400c0880024003200010001c1904000f409555909103800c400d080b0340b5000d49082c0030002038200c50207413000620702c81001c0001a6090380921004925609081c084452031030003010b80030790350740129271041481070f003100328502da180300050151180d00246051307103402e000e0701e80a0f5540e9468500540c101500d400400c1c040400a020070640a1040781441d44078182030700c4c0450a0f82c1c41c6800c03004030000d150b04185071982d4001803000c101c0ba01600c001900e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 42068979 1250 42067729 42067733
    0x1b060906010311010e0d031106070e060f09011403010312020601090b010f0f030617030904050106050a05040909020a0506040305010b0a090c1b06020705030408030a0806040506100e0409140d0306050409020901060507 94
    0x102400c5e409507140c0c441001c40d4010b007810740000f00d00810703418a40984000c1d603900e00040d0703400c210300c030443e640043c4288100e418000c40c45000300301030340050405c82403442c19404030008a603c26042110754520884d0004041034040292501400f040d40052254580420008000a220f41140810030061a004008107400b07640f00201a00f4000701e00c1810305000d040c02e981e2580110342807400740b0302d0400002200b6106606a0340c0040d943e940e0310b403801c0c0c500320300c25000c5c04902e04140c3c1d20085040c800a0243d840303000500055110768008100031408600708961780d8099400155254102a02c4101059200d0700c1c000c4141d05c103003800ba40c00e032000d041190090052100003015484001000b0580307003c0040540301400c6a6641e2a1190f90f8410034801070355800e8846680145602d401e8041c0240259031010000304050720014070304d5a25140c141d050500c0311036102c0e0715007040c210a0803040d814000c1c5400781c80c05880a00c542012a400304420440501c91582080360100700171003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 42070229 1250 42068979 42068987
    0xd0807060b060c03040302150702090c0706020f0304140f3702030d02010b09010609080601090c02030903010c0807120915020f07120302090a05030d02060a1d0105010b1b06090601031101 81
    0x500098042c0106444030a4195156925401800140e104510000c0040480c0541d8401c48000d00d6015042000686031880c01d20519000501d00300d84076074003441181591400080070b18407403401010040c0800d444014001c1c10100c4080e420076680d0000500f0a1801c280184885400c00c04034000840c58041401200c611003d0010000d5050040c0b14000c0440e40c0e0540054106120843d00804182d0303890714240c6c0c00c00c81d688907001407604014010051010b45030301c030b94541c9070103005503881c0484d0b210000c1e0840700c1c0c4000000c00b00304a0b000340030003180c0c072040388481042c48400810019030503480b140c541140300320442c80c9241e00041c1407106040c503d41503a0540303900004500010400a00240183d0401c4072100c0c0030748003001000030340d440c000410240700103140d0040d104507112115290080e00c2020700858512030001c890224101c1c09200b9203000300469441c00f51a807205103004c1c3c1c04241d500e01a10f090b98401c01c14003904280c082001c60450364404041e0000e00c0d21000142c0b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 42071479 1250 42070229 42070241
    0x105030601020f061f0501020a03020d050702130e010f0c0201090818060c060403050309061308071502040f0314060705030919061b020a060606020f030702090a0209040c1d010306050d080706 83
    0x8092030190038280002c043c20040c4100701c00d00017924000e10603454000481c1e48803000400900181e0016001c03000c20381c041d80c002c0c10440e0010b002003c0d02030b0710656800030f44030f1908640360261b40d24041c40c0f4840d080f5110b180c3c10f890452000b40a8401d00c3d450701080e90003002011005004c08100c50b45507659100d0440c1d03403405a8034140c076850b182a04002c0c0c01508125510051030280500050f5403100030f5080c50082a1700c00907540c2880c01d943c0f91200311110702540d0031985030342040041400c1c0d02201d0050021031080d100c000b40d1044404a20b400c10744040c0416042c40402d00034499400ca002c141c1e40b140c800c90a4226206041034281080500220141c0e5242c80c45080e40280ca15903003c240156403901a280070300480d682c0d150226694000a42400300c0c0b03410601c8900018136000b4003181d00440c40e034401504041075400000c00f00da0300f0001020101e160070480c882ea0000f003c844007004402400c040000524000100d101d19801c031500900c8140001081d00400403241d100c8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 42072729 1250 42071479 42071503
    0x206030910141f0b040608060307180e010b04051611010f0f050105030f060403021228050909090703080405090a09050a110a09020316050f0705030a05030412080f06010503060102 78
    0x5110b404000c02861100c03000549000e028200350a5801110071030b040f581c502100c40c007001551429190507030441c0c0400001d03082550601410b000062052540310300800f40e00d100c030708001080c080341c04110303084036000c0700c425001d50f06100c00c000b0003260041c2c00000700314080c2450180320326060200c600600d50040680c0201d45050b0070030300e040c0c3d210340c000741c1a14ac05508a52030b000c00c20480664036034045070700a005034000f5180025203003006000d4035041d4611760800408021154128206503040c0e1141000a1808a44641c2c2c618000b456507401004e07002c060507856046844a0440c0d10440c041c49016840440110f00c1024445e4001d0702d0300c80d00207090340c0c40b50b0418617000c80c020001d0001184104e04524010170151154400c9038015160600411500d1076440802e0f51a504010607154543c0300c01d0005102180e010703c0100311106950b0b8039180d036071909180c103440461030310441400700044102040001e04020001e1908942e0900303007540c89648500040746015030400300 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 42073979 1250 42072729 42072731
    0x30403060204180606030213031211030f120c1305060901050d050709030302010506100c110a0f14040f0501080a02010309140a030201020d203004050c10020c010504030206030910 78
    0xe01443c080c0c02d031031907210071a9060121944e00d40301102a401000f05a0450340002c88042000509080c40c509070036400e030600010142d1414940ba043da008500707600100c20002030b02010085d00300310302540c41001941091300300031800c0d9004036400240d00071580680c40c00100710b5507503070081007640c0444070810300030b000a180000009141050a1200720003641c200b1010410b5483c044141e00000c2c0c2d025030b02e1607544211500c5c0c00c0c3c20104110390790750704034041c100b01041d440c540413644406090189100850200307002c051208481040406042c6986440c006101c2c01b040410300720f030300540900c0d02213112403071810203021654a03210800428420704400c01e04154064020301030700140324404000f468038411485600d81c0d400c484440e0381c84810000004850410011411400320011942816031410f45080350610f0003900c05403295071003c0366001e6245404010902c07051001c0c4068101082804006000c9000d5400020b204040c040006004001c0401091aa520800780 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 42075229 1250 42073979 42073987
    0xc09010b0d051b0f0a170903091309020402070b0103110303040f05040c021005010807060809010e030a0c290a0507090e0c07080c1006031b08030a030504060905101b080402030a02040e0304030602 85
    0x2041c411a0300070f102c0170000c10130a5604203050221156954454500c460184d464003d032402001091040ca500c031045035943d0300d81c08009a100c0b80701a005c0103100d0b40c044015541513080c208000e0b0042c4010520a40c42000144a207030003e00c010811244151008034800000440c10390400341d00c8410324208600e00000015500c40c0082c408003200d005850360036652300c07860364083c242c90b00300f200c00189034420001c01500a1190101460450040c401114a1155407030b0610b058410903000c858804044800d01000c20070754810150441560305080441c585440003c0d10040d8004092403c986070125844040c4180402103444050f203203030640c0c07040c02d5a011442e0017041207001c10f1b038010700c42001c5807004529034181c90342542d40c210020350030960a840b0440240400900440d81c40340c07500345200c002801040401d40200485401056030409401c401803482c91f5088400104040c0340240300258030b000c641030301416010b440100e52400c500d810305c2e1551003a0303400141002d10000b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 42076479 1250 42075229 42075247
    0x1418090d11030f04060e0a1d0402010f0201090b04080d06170304030507050d080d230f07030e0d0503040f06060f0303020c0108010e010518062b050c09010b0d051b 71
    0x10a80545100320340d2140d000c49410103942070b50b6400b5044038100c5810041000b804018020705000020304001030500303050300d0326036804d20b82c80007003408a5200010b582050000315a003000101c5e02c0b02c102440200028416901c0c0c019441801610141c0070305e0000820780114020358224001030295030076840d1541481150701c0395a41e009202c155401d015413800465545001c02d00485040e4100c5070140c18100c500c60020001e1108031020351000c04070b0400c058005408905003485900927040300d0605140809020b411b4401003000d08956802c0604103041e0f594001c019260040d400680004414840b89070040050495400508428140190000815070b0020380025282400e13a0b5003030a699a48420480c9000d0130b000700c5600c0b104840c0304d15240420700c01c443e130780010000c150711284a8888a4250581c00e4643d603c10341c40702060712a02400420800003032150742c150fa000354550302d070882d83e0017140601d208050f00940c0702c4000ca00b42c000fa5254208100b480400050b0b602c06c492 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 42077729 1250 42076479 42076483
    0x2010e070806010509010801020a170a02070b0a1a06090d030309080903060408030405070b090d02130f0c111203070c031d060f0a0807020109110402130914011a070309141809 76
    0x244580c52040045d0400481c650b10103000703645d1a100b4903115000c02c044404c44440b0701c10801000290041d03400e020100c0494000b8400038040d51503200d00113043c079907012060161101c031041403800b0b003070104814865512030862800e407176900341c40e0008003803441d460249040c0c4111500107034580709000600007030004110044d806103106a00701c1c0c44042d641c91000f00e071406041901940000a4090344001d070a180c1358050003801580c60028541070400009001c03104070040c0d9400090901644508803101003006190142d042c6503ca400d514041000903c80f0404031001010441d065640c1504d0b603c0b019900c5800c04802803451f80c03196111003d088041d00000c5905001038100004260320714018880c20742295007140170340384000406003d01010390b00c6007c800100d200000400215056140b10760905401c4040c0100710a51418861040b100c0e00c00c1014043c55200f003112600080c0c10860080031252200c5261295102c0c0000040d901010b100001204000c001d040018030031700 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 42078979 1250 42077729 42077731
    0x301090c1e061709100614040c09050906040b0a0b190807081b0a0207050301020408011d03040b12041703040303090b070504030c1e03080a05040e07050c061602010e070806 75
    0x1a0302046038801c580c003910107482a0310030200443d00704002e481e10390495003441503124280c1030840d294107000c0700000f02154072550048042400e000134110350f515042c007850400c44068600300c3c030102d040c100007844d90400035250728419552001c1d4101143c4404202100520501d5619904c80b80034645440d030203c4244004800200c4510010b86214090044103001e04107960604408117980f90400310654010320001e4154480d404000545641c00d0008001411502001042011404007060030010020152250581040c8018401c2e11504000d8846042201c004100a612281006051111100c0441d03082c40744c00401c110600d03030075402c01e0340e02c948101303002611503030398400454550055000c01080c5002c2580c04121402044500340301951802c5050000c4540c0c80e41c0b0341129070310105045021900106082040c0240a040306620038901c0c00d0961030013041a94054444200500e458800701c1498040644c441c070035402201d0241001003201c40180e216590340d41c4c2c40308 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 42080229 1250 42078979 42078989
    0xc0b0106051e0313020409060204050a140301050c0406020d030b0607060c05180108010803090d110303030405060405010b01080613020309010b040501090e010f0b030a120c08030103080307030b150405100903020301090c 95
    0xc040380b034003921104200403244580c000c00c46014002000b0303820000641406801964a16024000402c03142c1e15000341c28000c00a10304061204d8409400307141c2907620007450048264814402002a19004a001d841a0b0f01e18540055014941d00014549004646020f000103190103020703052541c100d8001c12500d5070214141111040c12001195100400d010b8003800b900305001140450030410030369000e2a100310032071001d440058010030304c2c40c1c000310b0742590b4543c44103040c04140b16081c0b10761141c2070003e1a00c0c4c0c05514003400840d0340309400005021840c0d1780007001900004003903100c82e9144a0042c000d05c06540c0d44c00310040a010b01d07081a010a51030314400a03400004c0744507001002901802400903001c1c140c50f40c600700600c1001001c140040e5052201c0007445030001180030358800c5d80b0003178a0707003006140102200e51541c110b13402480f00080e241e0f0601c1d4110b080d1400c4840803141d54440364020b842c115403d09155100940540c2440e5414040011740440d09040d00d0f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 42081479 1250 42080229 42080257
    0x70e0c040503010f05190921081e070e01110c0d0c2315030403050d0e06010f060807080a0203130c08070303082508040807050a0605040309060201020a08160c0b010605 73
    0x784a0560b000111703035007641d01c1c000c4041041c44000c00c20300c00340c20034040c2600800102c203034015030300c03c5500941d2642c9440030000d02403030300b00000b01000304240703030b0103020b2048460b54624154a001c0c200080d80d6a440341031100581c070b2001c65a004100000209078090480d0504080900e0540032500032802468280e414420200c81d07030007603084c90171808030801841c203460302080020344445070780090400e50420404000068007200c0303d002c0c10003102d0140d001441650f14000900c084854143c0280302000410428498041e502c440a00d0f00715480f00001650b9440d286003081030100d062400a0118820410001d140d44022405100322802501d50740100e5945a82c494000805c40841161208107094141c290f40d2182d549546c2c0711744100f500a19002c12615101e16041c2002c4049480c1500c400402040603032001d0000d00404c803c2c0003e508050311070314090803688c0c1c020402d4040c540000c40307000c8001d1040c2681000640c00880042c51544c40c0c0000070410750104905007048 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 42082729 1250 42081479 42081491
    0x31b02040c020a03110c030709020a030923010b0909065401060b0a03090501090602030c030403030b090606040303111e0d08090304030305120406091b06030f02041412070e0c04050301 80
    0x145c0000300d03100d4400e5400401911019052101140080d007040f6480c008140d51080309a001840d07048036600c025585003081102401503445071420b40340c00d1120f00d40281c0c800b10500c0128240000d0054000481ea4981d001414081b056032a004c400c80c0d03044500c181080d4081460b190b0584002c441900b0074440c4004641c00c000d9465098403914030699101d1101009000d030311620913407220300c0080c429800440c03150004d0b1119010707a0406d0703541c1a0241d8001081c0030405405120703042d4004002d60b070450b01c51410000241d01d40c051407001070300f40802807402c042120028000344103d1340c40c003281c0e80e0f191441040002d695104000d21030001c80c05107804103503005030000503102101d60583d00c0520f0881e100e0442550580c0c0540121001c0d41c5403030380c0a001440c1c1014400311045d542c0c40c9160758924010009003501d1043e210486a00d1042000b4001d00c0c1070b404402076040c00070f913a01c1e000d096804044ca807409542d68000031200c1000814041c060b00a000108203e0314210001d00807 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 42083979 1250 42082729 42082757
    0xb0901110405100e1306090c02120d11070b09010b01020d020a0506040809010c060c26010e0a02030403050706020d1a040c091806030206070803061504030c03031b02040c020a03 77
    0x225100000c0200d000581804100602c2c0743c00201100001c4043ca00361110b0382003107002c0348001040c40e581c03500042d2150f006001c035804c0c41c482d168030b02e481031006220b403142c02c11034070f9620307c030700c400e0a26481c0c4c58075910034000444000315100f941d0300600c042914500840c510b0300821449091303d0041c068641401511440000c8440c00503811001a001545669840d030b501640a040a507061007410031242000c90340381e1050a01d400425280c00a216403103081c0089075103c50002441d141c039890005101c1d5401440c0056401481020300603a6619682000d4451340102e45004214600009000d030750101d030f80d00800c0703200d07a21400300031114a0348010041600c80703550901002629501003001251641c50f00030380380040b000d000041c1a0b4581d00461100c0d070021005940c1124000140304803401d252443c658402384602c60241460b00b90354840116142900c0090200000d08004401000341500301060285d8010004c10944042c0707000039464031a0300740c0642c08100d4520380425 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 42085229 1250 42083979 42083981
    0x102030f0d0506240a1805030d020114011512050a090804080c0901060305040f0201030b060f040306050f0c090114030402190303021005070516021201090507080304031403040e0604020306030c031002070b0901 91
    0x80d21102c080f84c41410401051012180c0c08000b20030100940100c44000840313071003d020f80382c00340302140c0c0041268807500813259800001139200074894a5609603800d04c1940c1700c1ca43c00108a4020710218042d00e446190501901e845070000c1d00c3c041000500090b601c0c2c0003e030100c2d5114007a101da0b0000e1f0b80e103000136001c4500440c0c01a1a952801040300c0066210741d10901e00c41c00000e03c1507040031004850701c8034a8000d90411600e49a440d800e0000002400801c0d40c0d1010206c1e085602e00003581c0002010300d0592103030170000d02d0b00232003c00c085668154296000c0d4110551100d1007541d070b401e0003036848090070b2080803450b00d0540030595030362181c000c5a550450107003803140b80e0210750342440710410f000b40c1c80000d036541e00c01c1c11707600050040c04641c00500407000111740f00c1d421800c005900d2400103400183c0c81c0e10401080003a41c902d0300c503c40d4004022180180c40e80d0b170b46000700e8100b040d0301e1801e55060140324004550f441956001d01703030850190507090490303501c800c1924 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 42086335 1106 42085229 42085279
    0x20d05060a020a1d061c09120c0210170c0d0207060203090715050304030806040504020102010b0315100906030c090b060403050d0801030b07030b0904110102030f0d0506 74
    0x2010703a40c02072444c2400c4100c02200482e000100c400a0740c6441111225640240c9043d101403d8161950000514980104010020380101c404c02061990481000ca12a48511001d2600d1610441e003e40c082103c0d81d1445c0480d40b1260000c1d82c05401c09100d0740c404a408014a1000a02d0750015600586410009110307850620a0b1280c20481044005040080c14820400407907445030043da0010000d071400038203500c55000403805031104900c030542610850000c01c0c8600e96910445205000c0f0090030f402c401d8444101e00c00341d800d688400341c60154058000e028851050b80b04c070791940740c0181041c1c6040da407030303458508005200000401044481c4010420f00c2141d5480300e6020308107181c00c0203e902c4035070001720480005400508135414240b8000c40703a0b4004c0003116803841030310840075180e008030b030b14440140c00e048420600880880b08203080b00f42d2244400 = true := by decide +kernel

theorem cover : BRFrame.Cov 41906479 42086335 := by
  have h0 := BRFrame.cov_init 41906479
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41906479 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 41906479 ≤ n) (h2 : n < 42086335) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
