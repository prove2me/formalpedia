-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0615
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:44:45.906547+00:00
-- url     : https://prove2.me/submissions/97f85a4b-c8de-4001-93fd-8163cc20dbfd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 110431654 ≤ n < 110611510 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 110432904 1250 110431654 110431661
    0x150801090b1b040f030609020f0a0603200301210f1209030303060503030906090103051305060703020d140103050309010503040521040e2a09030a06020307020f0f060f0103030807020a0212070504 85
    0x603542c21414900f05410718000c05250b6025200040c09076684440c1c4508640f1440c062000560000381a822043d680b80005000780c0210605005022040b241051101c10f2038008d8034182da802000c1071120300c405903134401240d03035400800e44103074003803007110380001e0300d10b030000d81c1d43c0d01d01a030307032241381d2442c41c80d000e8162190790304450712981050041c00c50546030041650410348007440c0200341916298a85407942d000c551000e4528003500c420802030a030160000c1c0001002c101040200c0c2d203d0f8800c060040400303020003002c681041084001300e620901c00795400c03500450a840e09840d42e100449142e80300f64035185075410020a00300700108211aa842c1c0c0303d460020703c10f0750741001e50313102d48240201e640b00741200301011882d800d4a45040011440e11540f222045680f41015070002c0c4d41c51002480d952540d100d540403c500900f00458022f000c3c1300c07901c441e20100e07400d5039001d5030400710040040b01140300b14110707240503a49104022044034842400b0b4042c0c9828541400240d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 110434154 1250 110432904 110432941
    0x4051c0530210109090308070503060d141b12060a0b0a0807030c230a050613091401050301060605041503090f0f0b070e01030902130b0604050a080f06070305040b0406150801090b 78
    0x5041c074144e17000001c41d401030030850b40034100740360081d5a6034400c400910040100040544242c00030b0481c100c041c2800100c0640070003008002080c0f8004540400491030104e05800107160015404200b41c00d10301d420003c04848002c0c4030481054444840c0783ca003440300c6d401600c003840c40d070404000c424100c1d4900c40c076182559442e18a81410b490206802c48414801c0c90b008034000a014071007800550518809002000c00c180114007003942002e401035400c2c0200c620951910000144107406002214211032043d003210950b055002419030080801403000e46051111000c41310000c1e8001d1941c02c8002d03c540c110304000d04052030006c0028036108026410326240c025428050303a100c6004188080b41c00ca004501902d40d80049a503074090746e0b100b50342100005801080500c004900707101810180c90440d082c030350b40e0400480656006440c003034401c2142c100441c010640a402401e80207000c11600400c80e80d0b02c503189421504400c409540390721541d001c4c030140c8040c64489501 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 110435404 1250 110434154 110434169
    0x60604050108070c0510020a050c0d09060c0b06062a150c0715060b0a05070b0a060303050403080d090b090a0209060d030206160903060f0204051c05302101 68
    0x800381800d00107010544041c142909203d0600c04100400c08100b003013240c1601e103180c055482d051109405060703a00102221800d50040310381035001e0340d01c1200d10b0300483d0820340d116402541581c0300c144005034090815600b00c50204420740820103a21140c2400c5240f13200d0040000b10011422420510561a96900f1440400034010f000301000290f0f0306594014030300c030b80420703400802c5100610550f480000799081c04914518019048070240006c0b0703014443c2402c003591164198021264a400000c01290040c0814008940c4101c042c0540382c039075031000200c01d0055220540341010448088081c0e0740400c103400d0840c1061104150801c0e010307036003076074910301d02e039406902c1d034100506290944540a043e4888540710354034010085070490740c1003040c00c0c60000c203507020354018080c40f0f0103041c1c5980b8418a0104800b0320503025508540a8a40740e00070854100348400d00742c00201d8860580b0910710b6040720314030010041c0c0c8407100c0c42c0d41b2081191130700505884c00140e110b020b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 110436654 1250 110435404 110435407
    0x1803031611040506010203030601110c0909070f060201060503060703090812180d020106080d0c1a0115031b0f0806010e0a090203060102061605090f01050d0203190b1207050f0103180b0406050606 85
    0x110591b0008145c3c1d400c50000d007020904119041d0502e4a042d00380e012040c0d20100d407900b4440c2040000c51b0820a44030801c603441390150321000241c5c261840e40c40390a070140d00c6400000c001510039400f8965051164011902e030104d50034018040c248203552001091030020780304150100104032080302e400441c0000d00680d80780c4111252240c100c01ca4400078004007003018401c1050b48180d002ca0058500c180d80c01550b1034040240b645441d0b4841310b0003203450001004000390b040300d00d05404155035507601c10380101c0c0c1c4030b00312125000a0801414090207072207001c1c0039640c140e03602e0041c0001601c016140d1810f04002807038841301078100c402580e0a03441490b64168440f00701c800d42d01d000d5500e0030600c901038004854511038082814485440482031207441070b54049618183c1c0c0f128134051180451800410400c0d80c08070408841d294800340e4204014184a40801d00100050400080c0e44041150082410040010490319800d010003001304000f070728401c02e504403905a4049 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 110437904 1250 110436654 110436661
    0x21809011e0c0c06021e0307030e010c0311071b080d0302210f0f0709090509010507020c03030a12151a0a02010f090b040201051615060302010e030303150618030316110405 75
    0x41c0c51402495009000f0b1a000541000a61b20001c0c40d200d17141c00301d11b603696076481c0c00c1100400034855228205500e500b000340c138402d0f0520902801130061a401025481e025150350340400114204100c03400e502c800c01e0703001900140900034084500820b860150380d5400004040803059107074080800d40461203c00d0181e92800c0544d9558403c9850149520300d0b11668020764038841290300c0b28203141e0511040049030f20040d000107008171200d4003240d0300382d83c1e8901015124003820b032910b400200d480c50541d9002c401034101201514285403a5543e03140c64050001d00d51004032101e0707103003180000c0e003507081c550f091003401c060501c23400c000c10100415640714140c04602501c080c3c10024045031030348007e0780c4445040f03501a40704030310203a0950f80c917403ca03028101134031059011514071492441c0a05000c0b08892144101e018246c40c01d0250310304100d00d9030848000030368000d03d03055040c805078504100408803020090101c0084450929001920301c1c58407071610f01035410482403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 110439154 1250 110437904 110437907
    0x20103150f0e160e010c03030902040510090e1203060d030905030d050703180f030303050619080615011404050d1e05060a06050609010207182004050306060306100e04021809011e0c 79
    0x55041e004e424604040070074005e0908070046c00d12044041d510516010a000207004914034900889820000610036000c14426943d19a80c5400c80607101240410020790705140c2241140f10041c802d0500601d142c0c2c5800101f46046d96006001000c00d40c0041c0d0081410307000303904007034500071082e240705450703013400009801c50a031407000a040c16211004150f442d42d07140020680781c03640c0c00e00714803c950340d581f850381d03298010349068000d0000007031514103d5224800f81907a22610a44c8949020715042c2401035545021805941c80d07001507005410031000314111441c001c1c0104010402e509100c4440c01c00c9030407940c0420f10500d0208001d4200740d801143d80022106e202e08000a00500c2d28402c0000d462185400010070051484c034007040460100580181c41c004d80880c1c01640d9032500b031503030320312040e2607150044403000310070080c03c0110440750b80c0c042d00c0a000080340b0034005d503044a00940603510103040c3d944922921500004440070408102c20092007401100c108050 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 110440404 1250 110439154 110439167
    0x90f040c0603090c05030d0f1101140112020607080c0c010206150d0308100902072103111c09080d090209240108150904030804060506060405010509010c020103150f0e16 74
    0x41d8014035807a03800c924140005506020010040901a80e060405100d0000c0020640754040804030750404030b205c02e0560140318018031a03205040449130b0364204000030046c00c00450f01280d020000708100000180b0302806001c1003c10034000742540b080032070019081c00c000070701d80c91940301100941c0110340d40310480d204c002030305801c0c40100754071282a0041c00001c5500700b031100900006404042042c205100404080500e09040301030351000800c0f415581d007040904940e040521480a00382800202c1140d1443c8810380090b0018031f17135a0701200c58010300611100b41c1d030b40d41c00b05015801c0046006a0254a06a20018002c0e4919110030503c2059403000c0c10810f40c1000502000c0b4104041003011170021b080c880036190503e0002d00c8440100ca003241c00d542040b000c600c00c1e080c15000c0e0340603540161a013a0a1a04020044604000c0701406904250b21942c19892500b14202c00d50003034040800650592030400c00c03035401c51003029240c4514042c0521130140602c0d480720 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 110441654 1250 110440404 110440409
    0x5010206040b040605132405010f0b19051218060a091e03110703080c070807030c09051f090606110a05060c07080f0f070303060501030c020c0906030f0601080c090f040c 74
    0x440000349a06ca40700560b903802031300b10008250001c0031070302050a1041503603030f02a422080030148807903030300c03030704000303115840e910500b20410010f106400c110300720803031147c0e4921303020b01d8440d0404661401003401c054081c1c0d0a102d0881981e940448030360000d00504e68000090807040c061405582e03901c030128a0001e20350f1a888c0c000f0f0b0112000c02d4031405042c3c940742000d10480e14595103030300b000c2e03040d580080161003c5124005001800150200d07425046076007118400c0d02280c0f4102091010303010041210302c2d1b031540c200b09034444c4030b1180b05d010046c1c860f104000a80504109026254041c1000c030807400e035100c1c181e024001500010010f80c028044981241c0f5a00b0b0741c40c0800c40c80c09040e004404e080310200f042c0c40d603545c000014000450090760184410b030340d20401034040b80c00844502005800c00014040350b82031010010360401c2001e0300b2207031924281d042c100d040400a070007120f481c0d002245500210f185c020340b001d4004032807140194440c102903590700d080e03514a1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 110442904 1250 110441654 110441663
    0x3090f040c030e01020315091f06120207060212040303060b090a050607030e0a1e15120507050c01060311040f0c080f060307030b040b0a05010f050a03081b0102040e040b0105010206040b04 82
    0x75102004120701c01d42100c41e8465520b0000c0d501c904108142c02003007158181154003802d007031030001300d080c9a005804802e010303002c208400b1107400c10340c080300d901311044403103030440307808200420002d42680b004042900042241c03802a007002d20707005080e9001c640c00641c010806000e25882c540e1201040c804a40c42210419500c0040d850709079145086c8600c0c041c1d0000010030009100c107800e80802c1803000020301803402290303c440d112008802c02e200f4000010f22080103140c1e001c0500e07404240c116031681409814103816580391f03801d5900c0340d04100d8200200d08680740e024203050291600d0581d80806c140700c0a41240c0c0d00900036507000f0500b81203100110081032040d181072240360041c40c1c1209005500c1e2525090400c200b100c1607984d0003010389002c000140c0b1140100b5440207903280241900304030f030f00c2d503199188150024948204410151043c42000b030070244000c01c01010101080c21084c50507003485c1d84048016403207541550001402c000021728042c20740f65125502 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 110444154 1250 110442904 110442911
    0x30f030901111002030906180a080304020d0512040f0f0506040e040b0a0b13020702090f01050a0513060b0309010606140f030a09050109050f06090106050d0209013f020f010203090f04 80
    0x1e0700d5070180341040003040550304074400001e116030800302140f1540718101341c00403d2400008c0744807580e42d940100700080c0003200140f0102e0014500704106c0480c0a0052084a0107203460300503200690f409907001c1d809403603070141c00304928050604002d0040200701e442e14140f510302859103081c00740080004040c03002040000b01d0035200f40c0d10a10041001502d00b030b0f40b02140c011444001d50089805a10031580b1400040303035044104031281c10381d00c1c05030030b03802c03080d00d003400740700d0604010494001c01540300c240c0450844220400366102d0304080001081c998a04030010b00300f051907500743c0f11025010801051100d0821084035000710410500080303820050902d503005203d1010000c1040c0521046500b51180014007a40260641c071f000b04040760395003040000000d1039004c0250410706400041204c442d6003c40001c80c20070000c40c42d07880c1075504108049080018041902c0d42400124180a41c1880c1070555428002800218586039100000132440a800007523a0b00c601d0710b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 110445404 1250 110444154 110444177
    0xc090e04031107030503070602040f121104050915041b060503040308070c0602091e01081003030212030a0603020a08030a0807050307050d0b010e0d111804021003020a0c020603010305030d0b030f030901 88
    0x20704003c90001550418144da03290b000b01d02d000d00c0651720903c103260b260070710b10700041400340c400361035040215445070070344008490030002d000142c54000c2c800480c07030141485001c1089040207901d07205610404070000703224140714003011741c11081e80200080240500c20040025000000300c0d40004490501c914042914030700500079200c3e0703004054118124108258071541403524810300400700762186503041d540c20307174410300b951114803002c2c00581c04600c061454401038401550403031292400454050b8680d004100003504580c07000c40541d000245980140d54408030240d0801146d29290349141490b0340000c04a000300504100ba50342c0d6450610f4190380030303400a0245500192100152546500b0402c40810380b007494240a210441000c0382200c150003505031040c0c1c5e0080c41c0c2d0007036280c100401c070025000403e26506110044910f0400f5a50740b00165008503c558005d47c0d686e401240c101058400448149000b54013544640c000800c002c010340711890020710b041d03600d140 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 110446654 1250 110445404 110445437
    0x30a090206160323090a0b071b0b04090c0512060603071713060b040c0f140d0204030609030216150513180204081b090606070204021902010608010c090e0403 69
    0x402da02200407900d00c0c0041c000c1c100b50b08441104943c1c0340b10340501380c2c10148400b038488a44034008043d540a404c15205200111010340600201801005070308418034515101207140c41158221106580c0701180c200003101842c00344251620305850001d0600201305050000c3c818041d0070303140303e035501000080040d84220050724441000c26003680b01c5080400c050249007410220503034070281011070081240c04c06019410b040c161964603581e00d1b815227003084500c5510400c4200d0810740c100703c2c3e05041d03103040c000351010b14022403001400150b185006450043c071125211002030342200100101d010010740f510b401100341c01d09903998044108a066034401d650040c920309400604292410003095018105460303a80007103603171002c0f00e0710313102da0082030b1940b1b141d503c000d02000060050a03d03d0242c440f1610140000d410413024025102803000b12405120050390350307407010003c1a41c01d000d42428041c0f01c0c245011500c0c2400907504844100030000b8090010041442ea00007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 110447904 1250 110446654 110446657
    0x71b0506032e03030f14071a0403020f240f060f060a0507060516020f030f040513090209041a1018051302030303100f0501050306030a14010b060d051905060105030a090206 75
    0x140c10104142da01903140d2401501100000c008100001d0502550a241e52540000c803140c46400c5841c403038448a414071003100c1c100b4002e00440840c015003600000030342c000c0010002c1180c2403081e01e00c51000fa404044107042d0b004203145841e5040d1b07806d000c529280c0504900403100700342c1e6141da030392130000c0050b22141302e00380780148500c0c80c080811407940000e482c07442c2c502c0541da00750f5a858030881c0d0030035500d01a03901e0105090400700001c024a1405103c407506088608402041900d044e0b00099100c4504940c203440c1c070840f846036403505500c2d1000c0349a0001c6e0b90180d1b141a01e0610a145911240c1d0140c040303106551800400c1e001200d1100c01d40b101a0b00404407952464504011891f91110b4481d45203001e0211402240a60061094a20900024000b00120003982e100d04500c84121081004995a18142d4030f0782500c0d03200051a004800f0319003c0f0756810111a81d00c8001034160186210526040030710281c1d07030780300b801c81e904910003c4000c00d00107018000900039 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 110449154 1250 110447904 110447971
    0x30305030a090c170309030d0c030801181d0d02070e070c2015070501060e06060304060f11030108070e09060606041e080d03090203010e0a05060c1c060b071b050603 72
    0x40702410302c0308222084c00000415140304260161462035440c0f2a054648540c4224001d0100d02c0c07200c0188100e520317480c00130060b0494900c0101c2c1b0b5680030790f00c0100040036400400400e400108140b84090340400108006145030b101c07041d024a86030000a000300d0000500404c154500c444e01001d07464502c601002a40b4001c050050520f098480c1ca03030140e12040c030880e195403c1c081e0010302d440c1c00c081c081d4450f90015008a1450790f9a0b9a0320380200212101c144a071030303642691001030b0000201950103010b101c07000704404c0341004404500d030701009181d0390b2164051000c0100c40e85806080c2c8003103803041e8803000904402c1049948405903e500003600a00c1a04102d48036103500d60040d4100500940003000740620007101c05444100100001c2c0503a4070031401302d0030a80002d0001e20101060121006044900700b10000591780141d004c207550450101d4100f040c40300d0013007000d1241c8000400b07020300c0340c43c2030040341080c08000c041e070041c00407200b072092002c5100d1515014 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 110450404 1250 110449154 110449169
    0xd0209120304081e15270d0513080304180b15070303020915070201020615030f0a08070507211e060e010608060a0905060a050601050c07090501090f06030305030a090c 73
    0x1101d40c1c0b43c04415a031504041d810f0900c2c4101400c4524420307101061000029070341202c81485071340d401501014000c820080d9a0729210340e0401101000414000701d941c1c0005552030b00ea0380d01110203003900610094110b10040d8008210800840b440341603e03d00d9004584004100403903c0000540030140c42d130035029900d01f00192410801d9451341c001d01c01420112180460b1800301c04080005000d450b00003409a448078011450754103024070300ca09044001012514207a549460150420044c1c16046510f000045480300400030280040001f03040701c0b20003400c0c07240b45880e4203000e14070780c1c01c8080c18004c5082500307240303400d40e0720360315110070b801260a00c1920f404801c031500030481c5100700c203240d000d401c0c01700b464803d0b680904400703076400000070b10705526a48281c0f4010714011304154144a81000389404c0c02c001404510000c0841c1d43d80080c003985814100026038118221540c07010389852400d00020f5042000d403608600c03480d900090984043c500040c22400c3d40c0c0211a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 110451654 1250 110450404 110450407
    0xa080708030903011506050913020903010c021b0301050402010c03050304050c0402190314010501090b0c0f0f0609071d01060f09090e030a17010308310f03030e090c0d02091203 77
    0x114030000000410b041c41d0207070020400c1240a0781c0c80980d1513a5406030b200050420040c1d90540d02d0301e4007000407062165000140b912009400007421224125220005a0041242c03040c00f02502140d0744c01ea5401900240014174103540000e10314210510002d06201002c00444c0900c50304000312411100050b10031950741410502c5041c0c0c0070300104110700013900303000c40c9040d00003030170030028100d91040e110040c0a50403c00d05041c15040740540d0207103842498484030705a10204000c0000e04be101d00505103500341032036484d05000c020b401801c0050204028800c0c2a00070010240c111142450030340384800501800b01c0c0c40d0101c681c48110342c1030401607903446004001c03000302200c80e00342e29003199600303072014143c00d44402440041d0218401f072150b11030a04c86a061960003001c140302800c4a910240c82c402c00480d050740180e8500300d0300c03200a00400d034029445240104003290303022061b1a20b40b224210303034031031904e14415058010500084a0b2104500442c0340061101680d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 110452904 1250 110451654 110451659
    0x4021203041e0510020c1e03120403031e0c0201020606040c031404120e010306030218040f0b0c04030204050105010c120f0e040e06070318050c190308180f101d0a0807 73
    0x400300b410490007104d00c69040c130743c004d04820303000140900e0100005000600490200400c1c0d0080c0d00d52aa400c03609809401011410280d18100034009507202e900c1c0e1f04d080c08100d02140c0700c1c0d544440341041c01d000107400001e0140c0e80008402c0c0d48143d044902280b1074982510440c00703496004110111321480005000c2000711800400d100602c4c1c42c2d81c1d000000c0128001181a03a04070b22019400510341e5a00c4480003107050302c1d2607801402a242810644400d83d2510201801140c101061820200d024800c514240c0a0b0600610702481c0802954005465408140b540c0c0d0308007009022603c008181e07801c0c0110120341451070000d03c100141c4070301ca4512500d51200b144c2e85c8001034985001410307035003811281c85000c113400400800007445002c05010f000300704440c01501c4081c03038160002c000b03008200209400110b404400540c1d41c0c500c07050144800c3c00601d05881081e44030581e84210307901900c4a0380740c4010081031400c0c00044804a424094180c00100c20b070300655202 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 110454154 1250 110452904 110452949
    0x3030307030e060a0b1f02070b0a11150402010516020a0803180a060203031b0a0e0d050f0105070e0d02041107020307030c142706031c0f03050105030303010308030402120304 76
    0xc10b0200d07520001c0e142c0c19039503190b08008854210b001c40e42d0000380300700c480207258100081d28070614244d004440342c290b01c43c42e40c5015504a4204a40080c0341c41c140e42c1c1c0840000d00205503440068120076078035090030713800038281e4081c440400900303000201d114030541d594014480300a2003110152507880d001c0500d210071450300b0841683c05400341d40000100c41e403000003140d11410796044030b1100c11081065111540d03001d083c204040002401174440240e40d01c0d03580c180d4061094005002207181000d1060a64030b0080c1407400f40141600c0c003802c40c1d1205491b06500365412035000515640c00e0a0b094018050318901a415200700c81c40441041100242102a0342c0d261412858200b00304042010811090360511404900d00524650100c040780600e9005940103090b1f515604e40c3e50801c919901410810034006103104200411761034051003094094007054014500d150b04544590100d440301a0000340541c05d005102004203a040c42030320003911001d038600b401c200d054640c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 110455404 1250 110454154 110454161
    0xa030b03010e03040602030f070314030a020a030b0f060a030207050313030f0510050c070b040201020a1a1005011706101107060503010303080901020306031b062a0d09030515150303030703 82
    0x5024081d40c80c1044031000c8000000544003250415801035261221240c58500c0c0d40d00a000f084007481007007200300c800045d104018503c20302d81540016140e1041007401819a0000782d0264024860307281c40c40c18030345480d0107c41e0341513043d080240c3d80c0c00c2149402072951040c0308803801c8440c0315240c088104502c0e0080b11050600420131100b848503100094070032035000380c0d5250b0450900700000c2e00014452440d49a003c0d0050066943c8403156440d020742000c00c0c02c211035070400390001006130000003456250094102864181510108140d038100c0700b400180107a80300701310030700420f0481d910078824565550a40c4d001e1399645549c0c1c04000d0501c0e0400c0c042100415041740000c1c0c15a94140700740ea105801c0100280300012111460150310900302101d103803c01000c100d0400d02400c0c40e07140e100c400384000320165550a0142009003030600240201d400c208210030100082000003455150070401440002502e8861003a4105509041c50700260140408002c0145042d095407 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 110456654 1250 110455404 110455421
    0x1f03240801020a0e030d0903020f010509090901060314030c12030a060f090f111801120222050907080106080a05060303040504140f010e010f060513030204050c030a060920090a09020a03 81
    0x8907001c3c44c1c1e6801400f01901c0c0c00c0711103880310000315101c04c10801340c0b4102c1f1188450f20302c18105540303049202c80c042048943c040b21504001d0303440303510400402100a081a0104a5550103507040c0130105201075140c0c65040600610044d0200203d140020070380c0c0a01d0041c40c9060400b014140d1341c040c0c24000e8044030340b014402c40d281c007090320001180b00341101e02905803140e80c5d100782e88196005540002c0d00e010603102e0103600348854103160044003203409101d040d1000c5a030155140c0410800122002800b4604120180380100501350308a0110381d0010f28010b4086500d41c0c451011901d180100ea0003240d1180c00d0090807640c4040e080451030080f501040108016031300e926480010090030322070700c80c0260072030404000c0c242c414009064140910001007d18039035a8001a0603907000b03036500c9140c42000002d00040c0c44103403103000d0003490000e50901215550310841c0204a00079070142803200c00004401c0590b9841031450005051001310454071032840d00b60040c01400104e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 110457904 1250 110456654 110456657
    0x260a12050105040504080a0c0c0509090703020a0b0a020303011a1606050f070309030503070c030908060124020d0f050a17150a061e050702120a0807020f1f03240801020a 74
    0x440040b94500b002e00400c0e1046400ca44030f90318191035054110b4070f8008950b81510040b90103000802c042ea80c1c0040d42c3d014200340c100030301e2032038110300400941c1312056022041d440020440d54410070303000701c02c0e281164910349945081800c241c5640c0140d12440c14040d61001c00d0400080400c505588018050703008509030711a140c0e20b602081d403c59854400203004201c4c01e20000700c2c0e4900c2400104020382c8689000690513a0f501c41181c907018080c2c0045d900c0b40110341a00240340c00a0300d032850300c3e00c03040c801404c00200514001d014421030340c84c03007002c010001036a031003804c2c000d5001080c10000c5100c1d5804503c0e00e000380c0c189081d6810960340c1b1840c51120005042c901c50703800303956503210518160001410303440c1c0c11707140c80c1d101590481c3c2222a4401d5244c0480080c4001401140100741740c2e5564081031040044d02e1091003402407080441c41042c41d1020b011414041c0c1c0a04c25090000e41040d07480d80d540b03025802c541d11181c2c11710030928007003505881900a011104e07210b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 110459154 1250 110457904 110457911
    0x307090b070203070324020f03090d090b031909020d05060105010e040c05030a0c0c0506010b0d05100305060a05060406083903060a0b01030902090c120c0405010c260a12 74
    0x4848040e12107208400c4040d5065010315418008144012526031904141c40071401048519219400c1a81c10071040300b1071007040071040010b401c0060081308001f0182c0c0c500b04050a02348400d03e06540070117840c0d0b01b208001c420b103e01903080740707070300c00000c81d034000744200e14905e55490103035a140024014140002c2001a00f810181020302a9140442c44c40e02e8850070f56a070794441e480104104441402001f00e05811b41c00419800d0020170301030800724803007941c1e4401c659611025a0b80c00f5040c811412400d10b0200040382010030181c0d04000c4c040000b1400c0d40724070380020080c04864200c07a00c00c3c028841250f1880c041c244d4850000200344040d40c0344003040020f8840103810603032045170940c100320005007010700b0a0b0301c01d640183d01414009107504031078010624840d42151030b02d00c246030000d40c103c0d043c444c040050b54001d21040c0700a10f03280c2450002064049250802005692220a141002201c0d10b11005c50b1009a21130305484004400004000301900c0c40428402882c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 110460404 1250 110459154 110459159
    0x10216120204060801020a0c1b170601060f09030c030602070f060f0608060906071b08210a0e010c020d050c010207060507032703020c09071b061a0405010f0b030c040305060c030709 79
    0x241802604c0c844035031074540070f41d00d2385c40c0d031a4224100c032001d60f0350081d805009404618038144070005110603229100820156040c10341c094208a0000000c0e01805046802000001e85551500d4203480d0f004901680b00e020764640501c0c00441000c00078402800d25038074254801d255401201240c44050450341c076038a80300803aa4a41e00d09440400000d298022090480d007010390300381c1e40041c40740501c00e01c0c00c040c440b6030315510078802038081e003440182001c0c02080d010324010a020509514020011032420302d001a54038940c00340440280319001c02e08003122007080d0705640e82140c1158040c0100e241c0200004c005101481d1420807020f01c16a0070a1041c8040c041e01d03d13920307030580007841d164440301c040003142c4400800e000d040003011540b0180c09800c01c003811401610803240400e400e03d401982d40c1c400002022400d00407450480100304c40b18800014900720b40c0340398500c95aa0315114115400c0b44140c1d00080c180d48030b450140140d60f14000d00541c480d500d159520300c0c0294 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 110461654 1250 110460404 110460419
    0x1060b0a030f140f04031103031e0109020315011206080613061d06010b0906070f03080a06060302090105090f0d0218040b0c0316080a1b0507050601060e01020a1101021612020406 78
    0x10701184550303c9085070200002e21081070322002540060290405405140074030814a05e51382c030860b001041e50480031006414448101462030150514074403d44c154600500404002c84030fa01352181002110b00c0e1003a0984002d6201d00080c000f14815913042e49040401200d803140f4075582111301034a4244541d0b0902c2c03030400b000c10844402c10180c18680d01e401000707011038002e0114281c0c407040c2000410001030241020403222442616a40001c3c980350030041d0031991030754807003c14180108a0840241e83c08402c684607a04111007502c0d4070344002004c9404c0c403160001c029040b1200b08038080d010132290140701d02c218403a80c801000760ba00c42800c03241c0d42c0000d440c09444c1729444070401801e80d0142c5449580a40006c10008148000204443e42c1d200c0008014011540c0080d0074014031209100e028090042418805200303a90900000c2d070307516044070b01401d07800340e80e000292503038401e0106400c0501c0f518890202907890b00d4000514810708030b01288a24a000c00029540 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 110462904 1250 110461654 110461661
    0x110c06160303020322050607080705030702190c0305030a021c020a030e0609040e07060518090906190f1b030b0405240a08160f080c0d03031a0301060b0a030f 69
    0x4a8240c8034445100c001560258080e41028000b0380500381c0d0103075800303d610f45001d03980d42d4043c000c0d00105001d0900c044041d100c2c440113019103003001410402c0105c8a81c00050301903031701c0c5154010308140c08590400049101007908002c080340800220901415400110810350910a581c104a4606000030590b9240c40c4a10010041504100c41e2042d502e00b903000f804583d98082d01c089014565501031070b0501055800c950086100800d024998100800050944110540e5500b6040c10945c00d81c5a8a6400420b0322180d01707681c2e5006500a0b180c8d070419180003403080e2083c400c5007455a46003903402500c188050002c1c1ca40100003c0301d20781405a60301581c8a8400f1900029030038103800300c9116421030041e0405511f140c0066030490810082d21100300004503034100c0c40c20320f9030f0328941c5070480d844504c0f1580406801c03500b69036210448140203515090008000c51403d0403030813008a62002c0c16070552070000b000807085032900c010034440d10950307010043c504140341c4a4085 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 110464154 1250 110462904 110462917
    0x15020d050408060a0209010201020903120318150609060109090c0203030412020607270806040b04020f060304110f1c0b04050124030b0c040e0901021809090307120915110c06 76
    0x10f035022002183d002c0030240e000f400510300620003d40341c00603200210346410712001d904606a02c0c000100050700c00030f28001c4070140c5122001c2e064000c040c01946943c0c02c005010244184030b07030804540700768001c00081008000840e401d00c18a401140080d4898008a4054070750349500d1881000c664800306901e0f00c00c40142d00da45000c0807405000e5175008001e8500d0440000060300b0102e0102d43c1082410b1242d440380d00c80109515251062060f031002c2c20513400c1c05034006005000015210f04031307244800710292903082c1c84a0742280021001c14141c42c0440d4640000801c034410b00200d8000280705c0d900403030007030040000c1010014640140f103240c1076070380c0c8500c11007400010307090710b0140d070480200400e185c1405c0d1620b1005540130300595a07402c1340c2c3e41c0011502c411511101580c056000d08460103074007840c201c09115144c0c0b10703021004102e40e9204070903a81d0f0310b0054a41c0d4000d4540f140b4569443d00c010385000e000c54003900e0428550f4030440e20002c1d05458810100d448 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 110465404 1250 110464154 110464169
    0x402131d060126040f05030f2a01020403030219020406030b0408071a060f0108150603070519140304140a050609010b04050c03040c1a0702030d050d050a0501051c080f0415020d0504 79
    0xf00c90b6150344588105140a00c01203032180001c001e0038110b00a100c0c080e0204013100341504d950740d0960340003d455041906038600007a4011b11080010903008030740c88040030500d000390321149030b81c1d1000800419081c2c10044c11507540c9802e204c10f0202d0540a0080365110b0b617a105100c00806260002618080701d01d168408620b08000c88594800d110039904440c074444120549041100060400d400455501c00040d9001ca01511125007544a1b840a0005818111424084051072000e6031100500c050802080c0e0403c882c0d60364410041480d0742d58006081d030313150b42410300d2900d001c1d00d40035501c5445141031502003140305881c80704584c0642d502884086110786451504941c0943d94143d4030031040e020b005660150700c05000100f0902c4071a0340d44d9942d01980465141180c10190000046900e00386c0141314035101c42c0700680007008007a5181c804110380d45040d071654030a0061003202c0020110700040c001400e02000380800c1c03499008e881c10308450b0801203440b070149114400c03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 110466654 1250 110465404 110465477
    0x151014040905060601031d0109110a0b0c030d18020307060503060310051303080601090305071503061e0b13031403040812281418120a02010e0402131d0601 68
    0x8401790702941c030001c00300d40a030015405041414203141c1c215408910140d55080001220310024500282c0c844060960459130b03500701100140c03070940d2402a900c00c641841d03a9905000c078412a40c81c40c0910304c50f80107040301c18007903c81e032009041e60426101e041c040c1c4902e8194201242c40c60050314401c59888151307038491101740e28101c0b44010050006070602c6111000400821000d00c8414007034002c001e03581801c0e00c4001d0008045610720b910007130149030072848503805a50110000c000302c48201070120303100c0340c486020342500d400070f40c002411a4041d064402c041d000200241040740c080388180d0f4120500c105100078244102501881c01c84041403441c01031702c0f010449a0b6a209140c030380030303a503c400301064404580c0600b5411400710311201c01c0b03c0c510315203280410240100d90000c2c0160095540c006429000c3e00c2c0121407040390003042040f006509032591a00610545400741c2034000c000303030717108200072050311050f001540c141d0003451141000220f000400e1b145290700c1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 110467904 1250 110466654 110466661
    0x20a050a020402031b0708070221061315091a091906050c09060d0506030c0111030403230a0b0f07050f1206180106210608030405060a0215101404090506 67
    0xb00095000410601021150710454601d55403448080e04d0351500c11000c06607103507018010009941002e4407403a02240e80504054085800410629085800d41042e00c10b0400b06140c9005001040107007400d5080c9400c480070240840000c50540b0755132801800721080c0c075082d4003107403200d1200100c00100764550102100044e600c0d4030280d03015004141d0305041030701c0c0740c00050b103d074021240002c05545a00034080e151606121506015009003020105003046070b594075100d00862002410b00c0302040760750b03200c4007203c20450800da0074207802d40d01e818240d464000000710043e40c021011046410016858501a40446182c001452031203801c0c40f00034081810101c0004002582002d4900f24001d5422000881c41f4081c1c2030b141c5540e04211100034605000e2031a1110010025061a000b0032910360040220b80603a001614825a0317032907001c01c1a458883e0321035040c004450524100040014842407041c00c0d200e000d107540c2c440001d10400c00040c0d9940300740141c4240c0001010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 110469154 1250 110467904 110467909
    0x80c090f0d080d090b0a050609060f01030f0b0616030906020304081e01020702090901020915070b0f091204090f050105271b07050a0201020d050c0703080901030204150c050c01020a050a02 82
    0x7a5000d442400761902d8040000e200205803120194111010713030b20b400c14000b90800c18003446901103010b545075240c52500400203100f4000d01c5108605150350b628000d2465521504070070400301e000382c481c6541d90181021304180284c4000b0950010b909000046900361000c01150200c1c2e00160040a891041d200c01650420300c2010740f070400c0d1760070000600180c40e402940ca11030846400010780f910050000d100c044040c40242414000c010800a000640380e101e001d41c011518200f5084150740c1d10003c0c0f483c0c40042d0b100317031068290210f400100c0481903040381d203030340b414080188200c1e60703100b0a000790a80e44030000ea00504514018026211100c100c0300da0081145805030b00600d000701d000c000aa0040c90141c1e09900819186025542c0400c2415a90492480c02616200c1c686204036200c1155010040c00b401000804441c280c3c842d40680d00a0807041c0e048040c0f6200b0707013402500c2080f00c103800315903074060115800010340c0003243c500704083e003040180615404d076508 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 110470404 1250 110469154 110469169
    0x610050702210a1209051009030b0601030b0904060f060e0601050714120705370f060b090a0507081b09060708120103121106010609050907030f051501080c090f 70
    0x400b101c01a08400c680c1901c4041000003840b10360045040c0003000c01e64000003010409960031140c0151041e03442c042505621400304001c0300d0308221504520780318600101c0c007a1038410072866120014a040c80184215580065403c003d000020840c036640d03407508010081d800c0b00d83c5e501044040c010360340410040c0301200304002c414401da4080904003522403881d50081001902c0c554044050114002080c03e80e001c02050302060024200300103034030701002803555140040c02441030041200810045c1d0b04800c01c00e0100400888082c5000c0240c040140001c0318428001a07608001c02c1d03000c000c4510490040240e011014644405941405020350100303100b02c50194040040c00b840e002c00d8000140a5485040300c51072809400c00018023694180c5207103041e50700000e004100d81901f201c0c148045076419120710507241c8d180801a80184490203420010506020400211105051440e031b5108000d80341d01c82d150315174800d060f160b070181d0050306420001c00e014490040ca003401 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 110471654 1250 110470404 110470429
    0xc0e10020c03032a010902030715020328030506010c05071a070c17071508060103090204020706060602011b03020313020105161202010902100c0b01031b030b010e070201050610050702 80
    0x100c0d001c200c1d41034003207407a6500c0103036588810090344800490401c012000142003900c1c000c02440300c1221038001079260959403294050f071034440d845500c1014024010b80e00301050140440d6000001f05050b43d402096081d000b40000e07140600240845d0300614001c110507800c0001403450314186086034000d80b800d90703240304102e042841070600140b00c9405010107450600003441e0711030885009103203012041d03013204410707890407000e000740b05511004196218900740303004100c256060021500074456800094845410060007040c11038054110241c4403030b80c1001103203201d40c148805c408034042a582110704058501e942c4000d584104041c0c881c412401052003042d100c1b5a54105040c62007a01c4440540d46030304017442940303050803070051907842d5410b1000305801d81741d442c105450014080200107492112100503003240180c102c00246610058403100382d6160b1401810300b240c00c9400c88015800c1c0000a001401e191412010000c1142c41d1a424207800c0e80c01c001440700c100 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 110472904 1250 110471654 110471657
    0x40609051b030901110c0a050c010c0f1707050a060b0a12020d0f050f0303010e040b0709031a0411060a05030109050c0903100e031314030d09080a030e0612070801180c0e10 75
    0x41d028034600c0c09170171000380824a0402c000703202c0c1d5030380c6140103414911000742c154103000071509600c010a155006032402194004211900324400001035111801155000340c164401e001e207100410049910040b12940115181c80d8116038900f8039507002081700c0402074001c49800112000908685001c0142c0d03440b60003a1011400d20007891441d54109a01c4140415840e009000a2201300360702c86401c4415443e00c840201d00315100c02006549841c3c100c0c0000c862500003400380094181c04400001c0d0090000d80e5503204031000070003a0300280613103032200740342c08041143e191851f0b02b103071200407000c0e001d8003075844d0b0100c0740c500600f8550140035050108010140644900100c40c00150812480708000e581150307040c54900b92600d01d0350024800c4c3c04006000c0341800040c40320301140d0501d800790340c0c0d0500750042032040c05000c0c1740140e06a50784060084240d040070704c0302d05a0f100626001811181c0030b8402c000e803583c00d5a481c020408038400140345081208480038900910b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 110474154 1250 110472904 110472911
    0xf0106050a0e19090804060306060201090201171008010c0e030f1c20150a050f0702071e0305010c020303160206040b0c030a090b0103050d030e01062115050106030b040609051b030901 80
    0x9209182d040c0c80780c03130b4000c864110780020f080c0036458040c403584000c2c100070b2008000c2c1c0c1105500103002902e204264060800d4244000394500d08600c10020140904400901407102c4402014000b000601c283c20f200b03004040010080740f000040c2c0b561584151915139449105141042d541034100803070300a109145805600700c4108200072101c1c01d541002e20b903d0692604c1c80f01da404941000e005440242124800d00008948c0002d1b0342054942c03943d1001c1d404807010f041115592603d0b44002c01c15400c2c901109031854001c006140715800b0503003454984012030404a032214030844005220240550205403d103451101543e4407030040c03500050454600e84a8041180702640308440a40c001519105415818018040714404c0c620081c4409810700114107800c5072402e10420b801c5044070800000d01c41d8940311000b051510324801c00c40ba5840700d200034040d00303402d80e601c0c1c0694140000025400c880348217942c8a00810804c01c54503c0041003815400c0e40003034140c050543d01e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 110475404 1250 110474154 110474191
    0x80c0d0b011b0c06120509060106030e01020d060e010f050d1e03030605030303090606270604020a2708070b03070509040c02030f120121080f09030a0c06020f0f0106050a0e 75
    0x307103110360700e0280c1c02210058040c1345080381c01004240120519421a4202001d00c0402400050802d0640d101c5050201301c9034518203c03603009004200c51071030b010b420140000f4030000300e0f038441410b07504042203000d10680c4075400d10050500043d00103060000c6d5040c4c0b81e0f6007075581c805146034644a86808a403069a0b040000d140d600140c1c6c0c01b007000c5d08400140241741c0f0b049010001c0410500500010a42c600d4120340c0128034010000340c01135800080e00d000d440d11642c1d02e0a00100c0c09c8408141d501301d9000c0039148580c0601410200d44191080496556035010030350303106002c01c1da5154034280740744003444090a01c404110b8190301c002c1c000c0140b00004180540f0382d074141e01101113207561405401507100480c07034141150f41743c070304552030010030b00d100708841c1c41e104145511b941e29a031050103c0d18202c0301c01c10203404010140804201c0d5980030134415aa1a071200840748000f244011040c2251201d2140c00c0d0302c9085070204024805801d25440e0340001071140c00f490546 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 110476654 1250 110475404 110475437
    0x9050c0f030403020309010f090501020d031e0203010807090509031206060a0309150902130506241e0c1507020c01030906060b0c070302010207090203132d050102040f06080c0d0b01 79
    0x20001d46080300545c001140c8004507507489040c2d2040f139205450440b000514000020792900002584031040544a071081f0881310201c10120182c0d0038100c404640c2c941c0c1d2040e9030750f00c4111038028011500c3c140780100307581010000070307682480c950b554215034644517001080059407001c0d680c002410b41754505480403e5203850000300003e850440480d420190340304210a04050442880510349010180041c0c3d032180d460a604800c6501d081c1d00e0100802d4000018a01804048511054010011007044c1802d2405090700c100b40c50100ca000421111100ba4030f1601103881c00d0040c0d00200d00b0807a01d43c4250401211180a00b000080b0152070ba442c2e0400c0b980107140303240180d4003107403041003103580c10011b40004003c544001c50460501482d03420440d0309021000d00100c003448445084100002c01c1040402040c0e04d0344090541e03030b4a0308030702030f4200b440340b0900c200c200500091014001e80169200c0e0308401c00c0545400181c4013a0720040c0543c5840c281040019102c40c150740 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 110477904 1250 110476654 110476657
    0xc0f040e0402120615030f030705070b0705031603090509180d03050a06080a0f03090611030405130608010f060504050c0a140304061407020f12070807120e0424060807020709050c0f 79
    0xe01c00c51602040481d00c0400341b5103407080105901445500c1000550042640032541e4410740307040c5141a50381d4030725418094503501407500e9070020902040000810503802c803421004a9606850070407090741d500c0c11001c0e0445074041e00c000150003040e1010640c40c400e90000c0d03402014100001007064403103081a02d80a4030701030880c2c2801c7c07416650340c18150001d0000e0000c0c0881d01c0c00c00f0b41050320194003500c038001c0d4403c2c28060031952207034140c034800c03070b40210010b4038548008000c040204441c50010740494030400d8000d0b441c0102043c04801c081003150880e0846d5240c1550f00d00c0d9141c000d030480d41c00108291812a80c0b0400b061446044c10801c82c0900c0059004110104480760582c1c108500d0482480310010100b008000282421094464803900450700002c50490348405a428001c10480203034001e14044203045104641c2500d41400a40310305040d040c2515007506941c458000d0f645500540e00c40c07507040103078903034079044564810f0309004583d0a201030413004e40108d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 110479154 1250 110477904 110477911
    0x306010e060f0703050c0111030108070605070609140604020f060c0304031118070804060501050f010f05071a01060216050f09040803040f0f11120d080c0c0f120703080c0f040e04021206 81
    0x54400110124041e00901174079408d48049081c013461945084003659031044035106034003c1c050003184260a102e03095003d418443e030000c0001070303c0040841d5040c5c076900115000c17071180030075149817141800d1040980c0c1210290320021440d0608544900384010320b08040640e0105048841c1124500440c101c0c80c001c0d805074070340709020f0030540f410300b06a843c147c02c202c2c0100c011448111003030380d05c9045c41040300d80e5030400c20342d50303016420210780e4202e040d2500c13081d00030054000030f00c1c0c0b6030016002c56224040c4050703242c40b1b82c80d0010041200c0c2d42c100c0c002c2d071000d20407001c04c001c1412800210b03081031003140c003a04000340b6644d802c4c1c0c40709111081542c1e000394045c81d00d4083d040210704485081c40300406881065840903001d01500e8020f44880d600190100e412030540a00300084072450500301b00726a0b003032581522245003907214440c1200007400840124405490140c00e64804080ba4003075a0f060a00701480581481001003013607034000d030840c07440c214404051040500 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 110480404 1250 110479154 110479157
    0x1d0409060908131502070312050714060601020d0305010b2b05070804022112130302060f0414010801080307031409060d06091d101a030f010b04051008030306010e060f0703 75
    0x11590702084101e0f0f01c15449900424a040c0d0221a4910190707000c203241083e00e900031034102d4040301000d400c8070755008880e0000c04503011407000715200f00b00020980e01c42c1030240e00b00d5840100c050702c1181960420b101d07544158100f0300c04802c4804140380c00c580c00c00465614082c010200c1c404960070745005640590201d83c070ba0090100b075041c02558484807952140c0d100c07203140c0030f005426580d10454031150f060042d001c03481101c0e912440344018011038006181a40b00e004004980203a60b100e4802c803030b0200f00000c01a4650750048078014102d6060801450405c070700b5840640307102c4541444003003003000421090b501d1360360f040e0103081086249000080e010f801d0020031811229105100c3c2d403803d804401c1041ca19400107404480124545e40126045107070070030024132040520b0250780c0c14020f645a1081036a8154030462440400712014800c98485010f01e01d02d070082c0d03024070121a0005c0000402c50b5003d20300e100d40d0b08401070070301458191039000700741c2c0d00d8111450490 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 110481654 1250 110480404 110480407
    0x2130e1b0102010606110d0806060c12091002060903040b07060b040204090c0306061d040b0a030609050d020c010f08010306020a02100e03070215030c12041104020301140315071d0409060908 83
    0x410381d59092051102401c0203042c926100301c212120580d80b824000d40c07003820400c08078000b0315103071906410389500c00740d10806c89820841e8840107480581150f46800e00031064500c3c00d4a002e0320004215000d03540281c06546880c0c02c2c00c80c0000541d100c50780035106c85440b1005c04081e07231600d00c0140014954004005103191203a28020f059490b2540404204401100040e00a00b51041100c85411303045400081d07041c04080440c40c80035460340040c002c20b1070003a403032080c04004603c060902c5215400e1304c43d0307110340c6c00040d0784501020b2003100002d685000103000042180d0700401c50b0164030f0040300c0f1107448919085040d030f03d81105070b81c240d0300049030407401c42c20169000380b90048146070990071850030b030035500c969002d2540c0c0c05400700150340108092003500c81c00e644064401034070079507403507850f4000300c5000e80200030300e140070740b0429031459a24845504458060005036071030301c08201c03655188090001c02040c10580c000d640d8403a00000030840d114240c800da21410215 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 110482904 1250 110481654 110481703
    0x10050703031505211207140616140304020325060207050303070240140a020a0f11030409150602010608150a0507052703101802130e 58
    0x1401c1e038410603054044208489030a00480d55038501c020010002844c45498403010300d1100340c07408511501003103208400146510900c08506140c8024850304000c8429989802c140110310b04841a03110b0001520848501002e1000c07000031034029000070126030101c10044c1030501d03820803540c5034114a000d200c00800400c0c1c2c042c85500020303e01100a50b0420100c0e8003c140d080a40d14811982058554480d12480c440c00300e032060807500c0700b008c8000110046600c0c40c01895124a0342031011003410001e001d6a82c02d0081701c603038a109564010108a9809094580428000030101c440c00280000714000c0c0710380c8a03c6091002d5a0955010280784c24000303421070395141c01920054203c0004003500d2801980c000350040f8690303000252070f40e240b0390121010b0081c00040810401c810705114083c0140e4800c030001864128265900441d00b84010301c02c60b00200f1041404407200640980580b4001071040d15a0303500d0600410045900c0c21403505010410803030b2440701c8043d03039a0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 110484154 1250 110482904 110482907
    0x90f01050703060b0306210706020a05060f04030e0d020a05060d0f0e06070906050c19080306040c08190221040524070801090903090b13060e03030304030c030c03020c10050703 77
    0x20980c01041c0e0b400c2c10052942041c200343d4062000608943c020f0031081d03400c1710710b00110313041c00784c0e4450702d20f080c0c0d0740c095221800292103040581094400d8400d40c004a201c10648038805030086500d522005040d0718484180049080007402c1070b40d01ca500058001500d40340c0b07100410200540c101c0005a211100c080c08080700c50080d10107a1940c0680200302d01d031340d006007024054491500f44207485a00442209140118020481122031018003c4400300f0810764081d50090300211014841115113a5003113038465412902440e0340c41001c1001c0c6442c041d19402403195000480d415805a0225a10501a0001070b6021160707903000041c180c10725121001005800354041c4901006420940c00041c004039041c02506a41c0340c0d01c600000400d80106000d00040c0500203d01c2e85580000c107020001c0c1100f8460240861412000708000740343c0841142e100300d90685a220540c0c482d51811030b04420510802c5096100701501481c4590304d45521014416031591803a0341d450480c0350 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 110485404 1250 110484154 110484161
    0x902041103010506030c0304170721020a051e0a0c030503070203060c071104050c070204090803060a0501090b180a03080403050106140f0a0510050706060f05100c03021f02070506090f01 81
    0x440a8045030620050200d544e5090072240c0120140000a4a90b02d40d400c1c80d140f0034400c20040320b00032400003100001c0000c4910b0b8682d95003612400302e06030f03c846000c02e1385c5072020800e00070310b941c001032618032803980b888000da481d0100704000c907941102c09030750303030f00c401c1d0b01d1900305030f502d48d001040c510110300d02041104d52145182030700da1b0400c0e113a030759803010100400c00300512540c0ca17400002c0704070b4040000d845d1034a800810500042c0e0075400c0c45c50143c1d0081c0d641c580034680080300800c0b00e5025880d084126030181203004d241c43c01e00e03135101e042c564503007407030b1540522007900c00004a05217402a1010b1801400002002460520200ca140c1803a9003014060704ac4c040c17044116079648a0a081160800d841c040e2840c6031800c402c03180c91203031180042c00c0924003080070035110828500390058a20070ba88a01c00c0c0d00c1104010358200c0c00c9504008c00582c07140b66610b80081d1200034048007407140600150811280d43d41c5c05051450448145500380d0000030304a90500c42400f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 110486654 1250 110485404 110485421
    0x80d0b090a0f200711012a05010c020a0506011502070305070b04140406321e0a0503120a140403020402041401140903030403020f180c0301091b0903060c0c15090204 72
    0x10f440f440e00d400c92400c21400c0c0651200035040b40441c09030340c072181e4010350f00c01ca2500903e03910707403504400303010414265041c1504140c615604e01100c1580035400000c60100349a000001403000781c0c0b80c100104000c0307000901076021802040350010001d641002410003602c0400c0302c4030740390f501780101e901c104510440c0b1144582e081441c02c01c20b13100207400042e400181c810203681111031320085407602903070340b510440d0070036070451240c0710a1420040480c401d0600316810140e00742d0319400c2507541d405044015a00381803c000c0741342054040c00c80013001186522900c0c1c10144d407a00002c040740c00c40c2c0d100310312400060f841c00d802903034022a25000d0b901d030102c0701404d01c40702034042517590089010090007021100c801e010b09d981c5400700c0c2500c0c8440f00c5030041140ca485103a40c43e440c1c000303200d50105113080241c00a040034540c040701d1048401541c0d1b011440d455622004c01910404610b10180040c140e91000841d481c608001c81c03045400402281451044c0305100071116001c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 110487904 1250 110486654 110486681
    0xf100203190f0507080703020c06030a06050103050108030c15100f0902031503010905120f040801150302150403020907120e0708060711030702060a0822151b020a080d0b090a0f 77
    0x140e002c80b42e140c0c0080a4800d901d4000b1030a41e2500c41d6850181c2c80d180c104541030758010004010032000503010740020040d038200380d9091120b6643c818a45940c0e0040c282a00c0751508803c7e600c0f568034401030545c541c00400000d02c00920740d5036203a132001400640c2c00c4012034540000070400040c8544154100c00c1c1001c0e0f0003040a1b452a4440948407001003142c6038101c0c90000c0e4001107a401c1354140c03000f4100100003040300540843c9100406445031100700e0045103010b094a030018401e0040c2e070221ba401403c3e2014503591a50201c607541500343c640c0d03d0850b40c911214041060400c5044040e041080041866003440c80c03010300700494400c00009941e008000c00001600c03146c09844803240b6904220501c1e850301104292102c0741e1180920f1400740c0310489000780580c280c00302c10b020a00c040b0400c4541056008265807100d264404005070703011612200000300c80c00010050910303480d00c005614080710b00002c00c900c800b541c40309500c0741ca039641c000e0111964461340c2034003410b1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 110489154 1250 110487904 110487917
    0x10e0303090901150c0c090209010e0603040b0402040b01030f1a010e0a181104031b03061d060f220503030f070207081f181b0501091409060f10020319 66
    0x12400000d0b07112a0500403030719603041d800002041d1074024030a507084503a11040320803038140c4900040000b504100180307030000c0d5260f034210803141081403c80b8040ea8010040c4003042d55240c09000140003000300c498101a0383c0e205011000c0441d2141442c10419240c0002c206031082000400011a800b10948205458681004030584001144801802040021960004602c1413007000d00450b0b0028002a507840301c0300c084d0154085110042c0c0e842a00304021180e0003901c0e81252602d0281803040c943d200c0c2001ca0070004000a982e40e1001c4140d4810811000861200208a00c8070b00c04071b84035400401071041c0f002107074203056032000c1244024400e8502d0b14118541d2041c0500d03541503440254126170303040300b602d500034001c640c0d00d905119000c1c070200d142044070003d00000402483e0038045001c00c0541c0328698034000c5a1405203040400101002007000c9048090442d650003041483c00010507101c0b01d01030031034020240c02031a01c0c0c1031501201004501a41451b8080101 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 110490404 1250 110489154 110489167
    0xa0f0b03030d09050f070815010b0901090905100302130b01030e0c0a0e04050f071202120c010207091104050901090516080403080403030906020c0a060c02010f270c0b030c09010e0303 80
    0x80c000181ea041421980010450303401a0400c10706100da0800c05c424140191080403401d400c000880c0c80010603c00c070001c09a03030340e4412031103850051000c5680001c01003282003142d061076070000c580180c191071201503450340c0c0e0350004001e000d981c6200000642c452194440941c4c040c450040070200d94000703400d18080040014031094051702620040c6142580803c0901408014906040c001001100e2806440d811b00480000048100300d1040000304003494010b8804a200c50414006070001c20f000c0c0e040207a10400b811641101068900c014040001c0c00d5540f07004150082450743c0e0001340d1030921640c40c510a2182002d9001400100d0b000d00000a9200d80c1e51030f881501032500240360007003031401d0750280c402c0450021072441400140014090503038050105048250001c000c6011006000411b0707803541c0d600c1038044014050b0f02c0080145814000f00000d11462014a80903100c2c4400b10190304140c40c0c00c80b02c48000300b814465540c01182d04200031100724011030900702c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 110491654 1250 110490404 110490409
    0x73f03030507021e1914010509010912051801050f0906040905010518010305060c0310050306040308180c060301030206091c38070f032d0f0605011409180c030a0f0b 72
    0xf0964105030070020174215040280003002152404103400f13100240704a08204941501030a04401c05440b00c0148650002c0c1c00f60242084a45000c4410f5590240401c800015034203504940044000d03140c041220b000240d9841d4004d0001c4c001c004000101c0d541001d051106a006c0e0350a912100c0640034018004123000044641d8071061000320706d9a40c0c3c1d201780c401c0c000c41d1440c0d40000d800d48a000280820550841c2c02e1034824116111001380560b0300c0c40c00a0354541d00315403490b130804030820051015050590090000440241c140000000c030315240881840b12803605540020005c0100d400390b05119150941d002051401c140e950500c0900160070307100050840420720440c0907007003007107600980100c0e42c010a06000040503000740000c655400b249042408030b814a403540f070400c80d0307031203200e0f0000b66001030755242200414541c181c0303803642c4007000c4164007001255038a500040440c44461051502400c2c03141c4034100f100c1100705a6400e0481c41c1004d50415500a60300d4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 110492904 1250 110491654 110491663
    0xa0e01020412150f05240105180f030a0b0108070303090906030b010e060f0a06171303020705060304030e03070312080a09080d0908091305060102070602073f03030507021e 75
    0xb0b5003000c4004144504840305030020030644010300b00e102d0814081144450751000d10641400c07240401c0f1225441d0340c0011034081c400c0c0320601c10704510503502407880b82440a40149007000180071070306060000d80751440150701c26802110180c0c8070b01020710405070b1250199000788500d0400b07000d41d60965030343e80f4094005000b01007038042d04900040b201c3d0f660480b2194a07101c054180c844058440c04000d21185a021240707548528030804078844519000c906ca090b26050f5000c0c2c402c0714201403c000c040d60026105a0800030207107008c0102b9034003802180010751240410001d80424604c0c058280c60004040e85d0440d4a0310703403140040b0f05000210740703205c8a128400031b001403d0785007503d200c0c000e5180064103c0004d000c011030814140c0d00041c040d0340240c00b15030303080340e030303000d04903500d44007030240c5c401296405084100d10a502070325400105036a0a2140404001080c20030520310700e20401c1e00000d840300c09100c2540d4061010380410380109205018210745054416600c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 110494154 1250 110492904 110492939
    0xd0507051b0402120f01140d0206070314130e1819020f01031410030501060803070f060f06030213060320010c0809030a02060301080106051509030606010f0e04090602030a0e010204 79
    0x10040042480c0c021a42d07160b04891101455004400f1107041030381c0e05c201440c8090080401840d8190410032051030644440300c00242e00800140c42c00302c0170303541129061080703026000701850600c440c100c0f52420f16803640140541c10309802151038040355500150014060010740e64011132840b03d016508d030305042001d80d1f0199007095a1210701c00048000300030302036040145240c0b080a00c1004820f594224080b41d00400080c04881e4442035140c0c1c4922030403070000c09400020f050300c0300003081900444000a400c1500041c801c0d030301e4000c00c4940c400740a2000440380c0e544418010804464160303450a82a203200020b109481d50020301070b600c04036405031141c0004902013003150781c100403a0002e1a07000c0d00041e242c1d6500c01100d4040c1c5114000c0502c10000d0306682c00745110381000381c4175002c500034014409903c65000642e01c60203040200c200f0468141174041d495142c81c02103800c1503104110059407890f000d0b22400880300ca0024080140e4010801080350503d4517111958 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 110495404 1250 110494154 110494183
    0x6060a03050c010807110f0c030c100203031302150c03120114010e043c0c031103010302060702030f01050c1806030408071707200f0405010b0f0703050702120705030d050705 76
    0x11a0319490016900641b8614000c0c1c1640300e0750740352485c11203011a141c401d00070113404a5440000c41c800300580150106c0030900140e00030300c00a03a110000702ea4030182180040c01da10f101c0002c02d006109143c3c40071420600fa41c1c0006400b42450310218002801808084080399117200c0c6400000c041c02912072004c0c3c401d64603010b012103081c0480142c0c1c41c81c02c800841402c0505680031071072200c40d0300c50019050007890140800c06c0d0600900405180b802c00300d01582c030b982e0071a802c00a82d9000700c00142e03010304c500e80d000c040c820300920656002e90380079100a41c4488036600c50b1810180c000304003502a0300f0070720034000090701c4071050f80c1c0d045500411504281e1320001418195020b011805002d550402c4030710040e10480f0004100501e0042d00e05440074645c0c80d09210039101c00b849421040e50003040034010303003181b100244c1139980c40307441e003036242915680000e0489060202d0805290b04814410001032608206031a81201d035801c140d81401c00d15250740d5140d4000c080442c8 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 110496654 1250 110495404 110495417
    0x209090d051e160c0f0f050d022b0602130f1203050307140304230a0f060213090e06100e0c030708040c030f0501060504050606040f03020f180703050906060a03050c01 73
    0x2207240d01c0c100030f6541100000300d8000e070510f258102610f21812910840c1e086100b100004a49803400413502000c0d2a40940900c100801c25800d01c4aa0400c50710301450136540700c0381c070411800c1c0b1294030401c503c0c0141c1015840d02046103e24616150303960144149606029040105099102c800c1c020103415003452501c80e541d80409445103108050705e400403480000410080058441c6e08480507138588401100d0071031403215140d5500ea1a8030081d282001309d081d6403001a050f0b0b00200480341596801c2c3d809596039851000035500d502020300442d4200708104100520045504402856203004909003400c01d180d80c0d09a51201800c0d0008101c0640006014403800ca40c4500c0250750100102ea056806414000d000381001d000340c0e80308900b800e0101d1150b20b46501990240e408841000000c1843d650070806100c01c1050203d030424004141c070380841a04200c0c640c826442600c0114440c64040f03000c5091420080026125010010003440815400910350005517004c2c2005c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 110497904 1250 110496654 110496697
    0x605010909020f0403080a020a1a040201020616020c040f0f0b06090a031104020405100507050f06161d0d0c060201051e06010c02180a09140d1e0c0203070e01030209090d05 75
    0x42009100d02c1c0c20160910b0b03000111032a107207600044114282d800f496080340c2c6481d070522b0190b015102070b00c010780181d05c60b40104020350f0040352040d02c40900b40c011034100d52105000700e000e0300e901540d80c0f0400c0c1d5448107011220205400b40c00849407040b901c035454405210f002a0801200340000f414060f901c60350540140c440e5411030b406850002d103c801b0219405400415690007801c0841d118000c0103140f085400c400580385002d2803494051180071490301d68120f6101d1300082000708030060700d03010340d0155141c06100380c031103d004100d44d5001508015000e825100080e21951640f40e41d00d0320f0388210045c001c01140c003c82c0901c0d02220b20790483c00001d9135111900b01141d8189240014442c00707100542c4a407113024411010a456513005107042a11a60815403131000b1800b588041c1001c0e4000c4d0946610300304050500040c10481900800d24001c919000352548a004000500541c0b40c03a104c8a40d0184603000103141d01640e40100424500800c2800342c0c3c110700007940e8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 110499154 1250 110497904 110497927
    0x10204050d060501090c02070e0a0c09150f0f080907030609111509040c0c0b0a111210060305010902070515060f060c0d03051303090b03070306081b0f0103060501090902 74
    0x4480003003000030000c058150090030514014007081c480c00700d000c4e180c00d403c1045540041007001c2210003c00812000d81e0f01c481d0007401900103a4085000c21820a5021802a0f484030f5030b0301100e0f06950f90116081120b070006049404420b400c0001d1002100821981c01d00020f1084141c07580602c1c0442d900c541c3d0701d002c0700c5103540c056640e540110030403442c29082000388080c00690100f15410b1059855052050302c0c440c0a040000d402e4905160002e80b105500da040032068800c1c540034240f601e80484505c40c44620309039905c00d03085050303050030005144d150207414050074225004524142c8c071b5550f2144d032151003028800f500741d40600003c85569510720901c0510b0005045180d5071499069002d80b5105028143c1e03002c285840007180001101c084015600e55040e00c0f51007003681031420041d070035000205034004050325002c011a220b507003403100c0b900342c0403802c059909944a14080200b00280c042c0f140b81050714100c410844e50785d2003550501202e002c2c61005913102c5039a9031 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 110500404 1250 110499154 110499157
    0xc09050109210314070312051b030402100908060c09010801050901150809101401030204060f120308090309040c020c01110102130501080a0b030f03030f0109021810110f1e030306010c0f050102 84
    0x34800780701213000c2056000c0c0368000c1000d900c0b01000040c1040701e9903502401728148416100e10754180c4000703000240040c107190f640341d20f00c42501e0414080c2160390f0840d49103401340803504502d604002042d110429600650190301426085a0010681d030500042d030083c0501c0c0c0c4803440400660102241800505114201000b15440300034030441c54038a4114071116030a10089010703519207200000c4440445170300c0c8065884180d804551802144c030b0450b0001d01c050658880c80c0410000315900d681c4510840003040c0a5802620921030301300005070140480402804203071340100642c0c1486d44005441c00240c440900340040541c4601e21280300420031980d2440d0035200d812211031038101e0010286110301c80300c4105008507038076000160300764040e20405e070200c3c040408205840d40792108203400c5c01c40705490021256015046a546800c045006248003600102900ea040c01e01d980d00031904020404011841c1d0304107400000c119144560000d0011242c070b0b144c0b4010040c0030340 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 110501654 1250 110500404 110500427
    0xa0b0724060b0d02090a150302040f0503060402010e060304060f14250e0111070b070602090915030d050a030207060507050a02010b0103090f021005070b0903130e040c030b0a09150c090501092103 85
    0x72140c01000b604047c0140013940280240e880f0f490f1040000510b511b000071300380d445244c0c1a541e4003020381805003400507a0308007038800c0720a40d0b01c504000144a00034403a0b0300c01a4076001131401e06090505005c1070040038a0342422004030010204210240c03c80040c003219442880c2c02c0401aa043c00c3c064140301c100e41017840c84410029440081c0080c80d0050a07160300300300c0762000310381c503114601c0030000c0c5010105a01500001003422030325000f0809000311140d01c0c20013520b003505903070f10742c1c0484004450f484086040404c3d00c5071030703076424841c034210f0400c01c0c00d080100000680343c28040c4204190000d21559190301802400c0344540180e0b0450b0b0b40c08622160941030540310140c83e0703000340704582c00f14105948c0014015030035210340d0b8040c07500030488a840505603254112500c0380107150b508860780b240d01c81d000041256580a4041082c03180018a188003c000104841c1c050b03844141000801d8005201341d014881c00c00294080c98801502d01901900e4241c90092800 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 110502904 1250 110501654 110501669
    0x706050405010504230a060b150a0305090706031107020909150103030207032f09040305090a030822050109060503070c12080603070602070807030807020a0b0724060b0d02090a 77
    0x1009010820005412060085103d0b104210603110381001d03c0c121720b09030800f8020280e1280a000000c1100d55100c0c0b411640c002e00b8514416211940014859100c4180480065920f030200301c4042001d00c1100080c0a00d1310b0148010744004441072668012164081d00c104808404038664500070080c4a81030410b84d503440c680c030b681d6401e019440d05c5842c071081c1d54113403c090b9180001d03440b441d002d00c4011a160380a03442d4000349018082c40c1070000b84202d0900c0310400441f03001d50758541800d0f004500c14681166180000c004201b0100c0c0c0250483e041c84800351424020307680c00800c14000d440700c17850407580360340e10044206d4890361b640e007020313004050f4540c2001180754400301c114440c0c50141d040f0782e01d00f03030340e48412a41d0340032500c10341c00e00b500540c0d030510000f11040010501c0780c0c001021303491101e46501c0c4601e010360168008071440a8520f031152201800c60032850344a03c0e21101c20070140b80b42001040c0d00d882000c01c130f1041d1030380c0050700d0784d0695101c620b20401b03050322 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 110504154 1250 110502904 110502911
    0x304090e032a10020f03041e15060603061508060114040906060f0e0109080d050c160603090203070806130b0a090605010e071b081b070801020d2a0c0b09030706 70
    0x680400d00709621041003006a1800395950750050250f07140200c030001550400f620349146d845403500241a40740303801406445000c040007401056009502d08010b130014403001829900d011405412514540d1003840c50b190760a0324074102c25040011241d0024084c281070603c0300b000c0007103600c2031180b6009000c0c1c240c584080407030f03a1548440d0880064200303031203940301c015107a401510241c00520490407554804802032403264810405806150243c4003141c40b07141110041c0403d02c1d800b03800450010740d48800c014190310b82084500010000000a0089402d1090841c0c0512050180184c40c60910307801003001c2d424146e00800c43d19401040410880d40c451030003000c1403d064a00034001904440002501e204040d0000c4845034804603ca14200d5601641305800000d1809182580540c20000450000a0008029000c074000c00000c038030f8408503182290010000484c81328418481c0c00ca0000c5800580400f015504412041500e03514880860b01c0c61080b4500104001e08 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 110505404 1250 110504154 110504197
    0x304030b072123190b01030b030a1103070f06050301050402130305014502090402030a0f0807020108010b091c0c050316030c08030f030f04020414040f030e120304090e03 74
    0x120303a800350010790082d8110200740807800701079480000702504c3c0810760003902c0300700b038500340c0c00c5a2003448506418140480e45a005000107414a078902100362071040c030054040f86107280902101024104032102000d815060040c02003090005024150003140d00041002c4075a6130484c0090080d54060b000b4440c42841107040c0c54109010300410030660217081c0326522450b142c4a02001c030041480d00c05810412039002c10020b0f100283c0103a13003601803504071101165071880d2003000c030340c0205110b0360f4a070b0f901d200041070a103050741700c0041d0403070501100100f03030344140b03c006522203402c2c10300c6016121400d0468071014590b100c1d681c5031081e1042031200c001c64650b1300342180d00a03062040c0403950707158555120702c10315071210940c031001c0000408015003075070381d01c0d08075002400018424115012218a100c01903030300791048190403600740304040c1e1150154615050564400701201072010070281d60380124003840c40e501e9260000046d80704403c10540d0441404c2e8402044d01c0f01 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 110506654 1250 110505404 110505467
    0x5070e060c0c03060105100c1106390303010501090e0a110a02010c020c0a03030c150e0102030406020306034b010603030306230a150318151d0304030b07 67
    0x1401440541d000380030349130000480c2d2030401d44212110a042e158511405415501d50141c10001d10450741e203c1c1061102c080f00700c450041500c41070b80b0207861a41c528041004025032140c0c00755041c2000e81c8200300500c4541d9024102000300d0702e00c03c00104460311446001c0004d0b0070030749010540e0040210301d500c0d01503415001401c240d8201d4094507203c035408014407048114a000c0030f4003190140c06410001420409100c507030946034040001c010030104101826079209407401d403203651300030061100b03034a000c0c001c640155100151100c640141801501600501c084003068800143c2400c040c41d88042286108180310420003003000a45034034000d8000c5c8458001d1204240d43c2c0c8200d030040100c1001d81101415000f091100c2803490083e00c081d02e548503d14241c109910740885d0300c5050500304615000b41d2090881400100003100104111540c0202480b51120900720200c6035a4022003100d0650b41c108100003c41d540d203540565404021041c03050400c0201d8406003400f4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 110507904 1250 110506654 110506663
    0x10807020c030d021c08010b250b0703022a1506040207050f10050c1819080a03110c010203070f060b180709030b010f060f081b0d0905070905070507030305070e060c 72
    0x303010194213846082e2100086900e88003d00404d00c01230300420840c204503188809514240c410500001030040300c640e0303181c070594000e0381c004000c29000b1a452801c0810660341d9035005602c0320311070311142000d21500c0d83d10014401140300e003000302c0002c10380e20b03252030301190b9440d81c02104540074401e006040070b51301ca0070446070342c2c1114546004580b50a80600c00c803003000c00d0600010994190000801060083d0080e6081c140d0070f814200060000003803100061260007500c41c522801e40403c5094207101c801000c95046420030805d050000d1003044500321010b8000070006140590a004a810303041d18194141034442c400080000d46544051198143d910640c8020501d036030302e05500b011000940250008030b210410340c0f0148510030b11005174400500c0c841c103a01512011038180d00b0794050002d000d080e903102e24058050110401819005211101c01080185441da40040041c021500020304041c1c9540118400c541308a46007440304400174569503071804a50482942c4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 110509154 1250 110507904 110507923
    0xe1506030d02070302211501060e03010b06030606160c05030105012705041a0901110c0a1106042105010b030105190b0a03050d030e011b030c08010909080702010807020c030d02 77
    0x41e210764000c80c0c00301440450514101c0382e0141c009072159012010480c015003000701c04024a1151f544801481d01c078055940f402041c1585450321800814030525083d1140700c2c0c003242c041c100401c2403090640f50320044032282111550304011811070303481d0400300402c1c154419035166007004004174045140a43c041c0c61040100901e0005014010290080d81e00c1201c015101010405080f00c1409030148810b0b40091280000264000382902d40702403a0000c0040140c01c0c0e1218401404004100003800000307901181c5481c03c051401c0e60243c28000480b07502445115405408030802200750000549903100800070f02c400c0c508040c407031003c1991a52144142c1d410040c2c0444241051903a420559070400c002d0f00202c040740c801a8098081c000071400c841d940c540703a0b01c0450020726802002c021040e54003180d01120807400402c80c0c981a002111500c0c58200f1107800078a0303020840700c04550a080c40384c8039a13541c0d41c0603410416003002642d0103005201d2070740e961a41c0450320180 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 110510404 1250 110509154 110509159
    0x5160e13032c01110606010503010308090409050a030503010812031308091206040303020306100f020a1b0519030501050c190e0a180506010801060c081210030f03020f190f11040e1506 80
    0x1104c545030a20075540d0790f000c0d941140440d40c100014000b1940c07a02c001d049944000d4004034107440c0640e41c643c0b4007041e40c0007d41c00650048010300c020311040c4034100740c40008503030705415030500041e40b107070482c60803500800300040041c440b04581c4482400a04110701003068417000e04d040c0c2005006580308039a41441601c0e0400b4410009001748002c00d000000f542c01400e40007002d54607460601c2c11500031109200c1404000a0159140d013000300c84481c17071030001c1a803949540b43c103500756007020f0300c0188540f0381480f51210003400001c0c0c1d00c00c001c0c0240f0b09520411b0b003201c041500c4c072017150000f40c1c002d150320b60042159003007500b050b0f008480a0b0b90b00c182903a40c622085a00c004a40300042000000b000340078011928030b01c0154020407800d0317021400710354a43e87d0005120340000118056004200000c0d65210140711038184030701032004641200d034980c0e032159140140000c00404180c0201703c0d0541584541d486080c2c24000c10044034526605410b450a402508450540c07 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 110511654 1250 110510404 110510417
    0x12071b09050a0b04050103050a1b09022106030c030a0624090b031c0c0f020402091f020106080a0c0e0702010b0a0b1c020408120c240405160e13032c01 66
    0x60f05418184501412079400c080075040200055a0744520070955a426004441011a0101b000d0b0070301d10003007008054840c0a070317640c0440403021b10b0310714100400380c92080d04900040f4015840c00301c2c1e43c640041d440710001804032080a840c034503188140e40c442d034400d120328102040c400740550210804c0c880407001c440c442200301040a492440b004e0180f400548480302000000d4642400c45a409100810250601c280100482c00111351a040c1c1942441110b1141141e280c081c82030a01909020002d4052001e00d41c070f4103481c0200070320824000883d4280004c15103032003035015441c81e1800071324142035680c1d550403024403508454501e91451405800b807900c000d81d039100315001c58140fa0060000090074001c1480180c01982c0410054020318003c88440b114458203852142c0300f81e000400e103407c00c0e0421034641a01030f2100f0300c441c020301c0010b00403814061140381d44400362500a0408483c40d26040710070700040c0624400c803510803d0b4040079084505000450300000380e0710072 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 110512904 1250 110511654 110511671
    0xe040614013501140f0709060c02010e0315012903060f040902060708030a02040609090b011e020a051543050f0c0c101112071b09050a 59
    0x29521200c01c0c40781c4030000c04400d8a40901c0c2d00c141c0c2d0105126100a4800c80b41d000d59200520b081d903c184d401e0403480d4102c201004641c40c0f004000d00c2d08403480789090161142082d0029081801c3c010010381404815058070016680401541004090380040c0f1002d07940e64012145110b006203280019030300b25101d504071241120b2041c3ca104181c01054540c18a85090a010003040c0c481c2090743c11a00400299012540d54001540140b4100c0e034010398071803812900818490094020341d60150900504000c184e0740803200340001c0c5001408881c10091600d400c1e4070f04412460002c20f00d0059031410106803103e142c03824030030b000c0c0118620000f030070810900307000c40700d07241c1c08103088494030300030b20909030100c10610801c0c000d82031561400035440e0b44400c06070800c1500721a0355000302d82c10905418100c11030403601c10f050a01446550404684903102c0c042201c505c0c00118021405c0400d021010034016030203140085680c2915440b0440c40700034000c100c411002290400120 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 110514154 1250 110512904 110512931
    0x3030c010507031d0613050c0607150b040204050603150a090c021e0a0c06030b011b0506091209030709020f0d0e0703140312010510030603050313030318030b010501110708070e0406 79
    0x10144c03140d0700203401d250380d4817034007000c000514032015200d5219a412102c0720751140001451801d01a1050020100585d000107041e2101640400d000354011b102c200302603100c0710113076500840c6a0641500341d40010303000c00c025450707991001006070305100d48c4514903a0045040c0c1032041e00a0015042c280d46807070850b90b40c48504800034424101000c0402c1100d02c00ea0020300b6803041490403021148448406111f41807903554140e4158204006215503404d040091070800c04280441505050320311001a0301c0344043d10403081c1084c0c0001340d844070b0b0b00201003203d000e030000401c1045030104400307076550344250a00003140d241407841101d1600507400030964510084400e100001d0f41c0c204410f20281c4400000700c4c90a0546500c0007100003401417018142040071082c02c11111861810020002e18031040001941540ca40c0f017400071484869405041d00c00a080051196281c0140546828100d60006003180580440406c040640b80c641030702850145105100c07020b6104031 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 110515404 1250 110514154 110514191
    0x150c07150216022106071205130507050409110409061d0f06131505070e01020706050f07060209010c050303041212021303030f090b0f0405010f080106091206020903030c01050703 78
    0x805905036a944808005182c0b503c907144034241c001813011401540c400c0554500181580c410011607241d007506400310081d44620b90740441032402032414882d4a854036a04c4040901a450140ea00d404070340081c40021920b6090400c0d015008204440c654203104006162092426404285002000ea03c10900244512001481d0000307412291245c900316265100845801c45e01e110712042c081c1800d001034030030710b03204030352680f15510108001c00c00241032070025041001800b0040c0a1034103002d08520a9404007540040f0050355013400400580e07441c1900314004144d440000200820001240ea04001400c40c0e61100c0c80c004000740030b110240e010f0001114140b06403550100302103842007021400204050900c0100300780c80d240c5000721540841000b52800c40001400c204550303103c0140d00a0303040d81d01d003054040d41000401803180032076114950618034201c1d00602440400e0b8101c03243e61100800b00c0c1e503210081c94980f8041d040403624200400d103015042800380c0e10010 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 110516654 1250 110515404 110515417
    0x60e040f120f050d0906090501020d14100b18012d03050703060e070f14070605060f01091a09011419030b040c021203100e01080f12041214150c071502 66
    0x7203c0b9801c100d01c880c1501300400c440c2806440781c549404850010400a1000303108407254014080341307207407203265000a410800392114200108450301046082c0d2901d06603004461481d00113141144800012103568082c503035184003000705030703200c0384840112409030001c240d59620148040d07516504e0540840e00c3c00e2040d500580300c1d01001618043c0b00c0e804a407005400e034100742080c4681443c2c00c0b9103541005004480f015a220280310852910700000c3e80b10607800d181580c1814240055003110b84800700d000681d280b0041820105c0740c2c040d0b03041c2038640c1001c0f00016202c8080f801e6140b0180e00c680780b0000880c1c9425000d81860405000301d480564107900100302604140d05c000245500042c205485010322407004200c030f0910740e540354000c01029008107102d20f2261a014101064400780f15680b5000f04410462034541010403000ca6030403100b0718209050445083c0c1c103101280407859441e1861204210344808001c7c082c00309103010b903c0d03060300c41484005074400c9100380ca = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 110517904 1250 110516654 110516657
    0xc020105040312020306150c0c0f090402030715110d050d0515010504061815050301080d020a21020a05070905010810090b010504020c030d0c1d030a03080408030a060e040f120f 77
    0x8481c03d0120030380c0d800030341c0c100c000580004196142e80c9450080d61f00f100c060100c168100118440311480e00300b00681050b801100d841c501030410b03030f0000b50788840901c1194003451280704110703100c9005100c0b02a019031004260b074400c4040441c0206194040426a0b003194a040041050700d8108941e803110920181c407214030b064100801540e020003d0602010442da44143c042000b05103c002c1d1a0146104d031500d9032a941014000d500f065000340441045512952880010980116080328a800f610716025100015240224140316070058040e107144152035001a1080059201074100c0c0c9401082d03c1c1100c01e8042c29109803007079130310040c2c11150000c0044c001460141e00504d9442c0b05001124175260020a600050b69066818074010424903800c00b1909144100c01d4008204c00710042c08c000d8001e5036010b4880840a003020745900741c00701c00030342890400c0e031001c3c001e480201180212840c15103030034600c460a441080301e800c60010215035800d40205054021302005 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 110519154 1250 110517904 110517917
    0x6093017060a0302040212040308010e0408030a18050d0f0e030304260a0b1905060406030206030a05060a0801060b0702120102030105011b050109082107051e0c0c190303030c0201050403 81
    0x10050503208030540508840d5014194100000c0183d4030f030702c010070021001c00c1084006282c10304000c0c01c0004164400900c0d400d00d40d00b000300051011040b2944014041400148050005481001811940c80041040c41202c00f030044c902d4004e6139491002c803150b80d5206031102002d09243c0c49010f80d110351141b500c00e0384e44d540c48500301d001b19a40002c00c03a00488400b0311042d1201c42801f281560302440441d00780490340010305181c061b440d8015002c0d2404d0111600e10781c00f0030700c01d11009000d004400e68405c0800c03c0c9994540c044001400140024050075840d02c400c540030381c0c0510380403440b400f81c99071106004074040c001d032412907005844040e2a042108040881c12030b44a0b0115060355892640c40300180542001c1c012080504c180c84044020060400030007502c040c00b11024484180146060146100da500070701010903010941c4030f50103035140034980011200c44680c000c1c03640c500e0208629400592504a900035682808400300e40c0800303a00b203480649025000685 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 110520404 1250 110519154 110519177
    0x5060f010905150d02190801050114090904030c08040801021c140c07060e0709050105030f060103020f060d1b020c030d03050408030112150e0f010f051021060930 71
    0x1014000c80d154440300c071001e41c0c07511800d403031300c0d600326440b030741c2400d00101c2c84007992201b2a51108000d4051301d42803c1000f08801c00695511a601443c400c2c507201c0c400d00b2000908040c441d85040d9061039110500c20340303880e1200d0840b07010f0740241e00c00000c0c0a261a02170f018420300c0c0e0003540c0c9000a03189000c40035803070710b900904c9a540f10a00c1500c40d244c83d8404400c200c4030070003018008103519200000e05504000402d403d014040b1428100360380050010f1000d40e69010100701107000860b412551b034400d400c4658081c200c00c0c4003ca00c030705130400030301c101d51384c02154480344000110161241c4081d0305000b50200c94007035401338000042400107020001c50443c1c900780041c01400d1481380b201c200d900c504140e401c403072045801034208001d801e0a0910174001c05078088030f0800d0a110314030b4403240d000c100556500c03030f84141089054018495400301103025801c0f6030442d8007030291940030700384000072a4503031012101084440f88591401c85012003007100c0d010306c50392000301d60003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 110521654 1250 110520404 110520409
    0x612010303051e13140619080601090506040306140108030403121b02040e07030201120c0e0402070809131a0a03030c06150f060314060f06070312021b1005060f010905 73
    0x2081080d04070701c0350004007070700742840b84064090216942c54440c2c4034005810f024201320017045e506401c50040c50188072440d4545040c0e1031074003600c060361406c81c42d80c4d40c554004841905150b0303c6550402400640401400b04980204440305855002d851403070340c2c4c61380c040d641c912035440090244038111040d486254881d201142400e03420349603a10410f44140c0014007240d808103110b104640c45540100115604841414003a60000f04100403034000001c0c050014091a5a428403c980c00146070041284000688a5000340a085540c40c170020703600f10300c000c008041c2040009205040310309120300c1c2031040c0e901a00d03030541c3c903d6004a035680d0703580064000002c1c90340700b094005001060350b464610155000300041e5034045207004040d6202c0240140240155020701003811645545450340d4080358030280c0d1525000c8001010810079000074010b40c0043c2d100321020a000d06070b800000140a802481120000c018039110b41081103000300104c0c0c003903400b203000361a0803c49403 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 110522904 1250 110521654 110521657
    0x312010b070804150c030e03070515090a1a03011802130605070c030b09030a0801080706020316050f010c050a11010603150902060f07140f0f120a02031b0d02010b061201030305 77
    0x941c0b04402290505803950282e4802d480340429940028401250442c24164040c40e004180c06c0140c000c0c14641f41040007140c0195800303c000800480d0004402c0265144c1d100070400400510f101c001c5072009100061586500c2803080c0341c5922211200d808008807244200d844800304050b00298035454001d00b03403104c0c0c101c001e0903150540f22200c0040407611000103a4400c4906074041c69072a15001d070003074107a52040e0441c8038680e0003283d040c060140c0000880d042c004054050303150016082c54468500b000c124611010395003041c0d40e070302c0d066400c07801034050306030151200000c0314400c0001c2d908032026448050004907014603070a004001640c4500c51690005e41680e00d807a030642d580100661254401311004107036409100d0303041f0001d0006204004901c400381c4401d0100c81040ea41e210f800300440900388100142580e4018020800c95040905401c05048200003940340503845001c03c501c8103000d5401c000d8071040070310b021000c0783d4000143c2d6400d00aa85d00b90388044999 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 110524154 1250 110522904 110522917
    0xe0601110c0907031d0a0f02010509190e041a090615040f050c07110a0e04020f0a0e0403080f0705040f0b09030a020901090903030b01030e030d09080d06030302011d0312010b 76
    0xd00079041da000301ca0b1a01e500c41441842c3c56140429410700042d03c0801072414501d9240803900542c4024000400403800d04c42e0310b0341c091800c0b5466804c07000001380d40451001d5800d2046a08010024007a07555068a9100e00c0c0204e0140d000d50840d0030000ca0007060490315000c061b08080b0005100c0400b101201c1701446d8040d1000809400350b000b0031003103e400742d0f0300700324030400401d49804020000c00c402d1168901502c0882a4520344211100e14020250000f071061907000c034a60701d5501c40307000640081610000040103803c090601a0041c00107490004501c1600000102554010f074121402c542900484100e494500188400039421605080f0f42c94050040d520001da5110b5951501900721804002240b020619028048801c3d910540d41450304200150078001004800d4890300b003007142002c6080071807490090901d200d441c18040010b4600003000c402c1c583c0c15880311058a00725400c02d059000c2c088411079490058040b00500c2034410300043c00b4011205001e4402c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 110525404 1250 110524154 110524187
    0x50a022d0c031303060f0b06070b0a09150f0501150f031a030a03021509060103020f120109080a02010b0108010b121906030c090b0306070c0b06040c020307050f010c080a02040e0601 79
    0x62608041c030035030856001c0340c800303420700340d4803d0180309011881c403c44d0aa00d06420741040a105a040402c900d0300600501070040a01000050102103090304003e02287e4041000d0425001e140c15110080c250301c0311107905285801c0011651268184c0c0a541010490711040b01d40790403410120080c0460001d03884503031281c2862060705450810014010506c65005010862505544007a040b64000c0000a660f8400001040580c0b0f8000322000644001e40c0c0d81312040d03203440c1c4440d002d08241d080050a820000a90502580d41035010f105082801d0384c2c1ca902c0c84e6a40ea4400000e07000341100481c80b00420310100700f280702420309000c2c008001c03101c0401c07416540e44485517520340c0366000745d910b15140c0081a6062800344207107980301d4400d0424a54000310f544a00380d080200400150295030340e1061950008c0c001c00654030311941c8001110200452141c03040e010700398034031594000c60078840104ea10104140203940a441d0000a0704d41d40b0b80d540c0c80116503540700882140c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 110526654 1250 110525404 110525407
    0x1203031a0108150f090c0c0d140a030c020307200301140103021503181c08010501030509070618030b0a0903030c0c0503120403050c0a050606010206060d0c03062307020f01050a022d 79
    0x604d52070304d40306103100e01010120075072615108110941031051203406003082108090358038458600c104281d0b25600805d01e000102002109005c0c0d01d1032050b060041d181648140c1e803040070202003610744210b44407c0d0003c0c04003010b080040c440503002804000d41c4107194080000d070801c007400240d58800c00703006900d0305440c0a101c090b400d10403803010350417024416890061509421906160051100f840c0c100858903040702030039111002e50081c1400c005540142c0d540d0b69100b59141e2010b545c12401009481c1002e01000000300380010044002c2820300007094451030091981241c1c0d6178205d4050b52600404841251209100400442c20b2040a11022145580801900703980c288540b00400d0759081c90703000a03141010041a0500c1140300e0489140025403040b5140c2c1141e40c05040030444000c044480350b0440c80412903084c1b034800c000204901540d000400d2401c4440002c000c21960302c0d41a500c0c401c1c0d01c1030301c4142c3c040d600e0b040220610103074298000781002002c5d0382a10b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 110527904 1250 110526654 110526679
    0x11071418070e010f0905090420060c0703020f010f05030114010519020f0609120a050d0929100f050906030a02033003040309050d031103041203031a010815 68
    0x2026480c4140d07252400201a5200841c1c01c1d60000041050000303d8100b44102c1c502e098002601000014402000c0c0306000b940d2541d546014140c00c02c1d0a4002030105445200400410b6030752103030791200741e1040031100501982e650040842c0003001c15550744562840e0b0819201210100c40c480680d1b042000802601c4030400307000c440d4540c461007542c094004200b07200c00041c54014060300595050b0401c0319132503018409071080700d012503054204076031909030501d40400180203410024003451041d15900c3c1402c03040c9504a543c0c0140316054410790340350104610100d9000c1c4c05442002c00d03100c5814080d51400d00b070002c7d8081001400c4071542902c40e80440d041c0014084071400300750010440d4042d48001a08288007609a81c101e203065184c41c1d02c00816503003041c418640605c1e0107007105800d040c4910351080e451544941220360b695034841241242143c85035040c0c1c0040e02d02034142c0303034000c03009103441103090050b9a248095112400d85e5580e000090010139400305001981 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 110529154 1250 110527904 110527939
    0x703140a0b010f0302090702070e130c05090106030e0d08040201050a0324090501050a05151204080d051f140a060807110a0501050402040e0601060f12061806080706110714 75
    0x71400707407200007441d00c0060300d14414040e4490b4080d0000065400c808000e00541e0703010b8a0700d5034003c0720520301e9202211942410b03003443c1465009160842c1d5107178008100e054158100040404044c2c084038102e060b460021a1804c00545009000900c03c002025409200390030a043c01d13100600c0504002a8081c0c0c0c0c102c4201c00381e48050030240d20741c4010070030b85c0b800ea17000d50003c1406407003188003800d03c0c4601502c5803180c548001407102149010405002805080c1d412210300200d08001c1030401218078030541c0d00c41900081c180c8401000403407029203141034100d040320050582c5030f4040c20501c044d0303a104c1e001000e540811040c1c00244200703000c1086174141c4140030300000256410310740140415200490b03855001c44d0722100041061035441040746110201503e804503400604509143c068000c591158003151071040313200b00300e0070542d48510102c0302541d00315414140c0e56401900e940000c1948052583c0059404101d000e844180c4040035100013408492900c01070401d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 110530404 1250 110529154 110529173
    0x1508100909051c090e06060a03020c0a0804080c010509130515041d010501050105040803030c1809010815061203040605071704060c0c091505010f03061a0903011d0703140a 75
    0x94072107921180e02a10042d0003641c1080c541d83da2807400600c42030074124500c07a00b0381d003d00154000c1da800500030300014420760556040443d1041030325001c2080d401c00c19502c2d001402110b2440c040c003030107420a58001c80032644128009499000b1000c0c0c0c0c1020b00c4001c0c0380040195031b049824002840d06603a0307901c501041c410450904055502c5048082400c407481604824144a000c00003400205400002d59a00c00d14003103150f41e48126800880c11000c11000c042c603040b0b01140004078030140f000c03076407503c4000710005500076607685108005d91559140290300650b0030811080c85654480c600401c1107500950007110007803c2d40086900c00c0d80103501400016980440610810903240030100c02400124802e00c01c20a01e0089003030380d96014403545060103401d07000e04079020702031b40001c0300401041c502482c80da0b40c01c02496030641e0069104920070b520304441400c4050042c0345131410341440300c00410701141103956440b2800e0005c02041c036180300e5500c524001031300880 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 110531654 1250 110530404 110530421
    0x90415061502010e010b102304030f08030402030105060d0804060e0612070206011e030203030a030507030e06101509080a080912060108030d0c030e101d01051501081015081009 77
    0x82c00001d10b5588074250074211aa8001c0d541c0c421410320078061641079101000310318146104c0c00300b5206031400341001c29544a07540c4000d1030076910040400c18041400050340c0704900035802801030341d540a00b00800d000110800800c868000c2c80144030140c411501206044009014145000c0d0f07100c00c4680701103000c4402e42e006074030060040c4218604103611002000c082d444480003241145d000a889020b2846a442015951030000b10014420b4001e08440d41460040d603105080c542d60f81d468002981c0a40b020a120721352210020500c90819107080360040b002809030300e00d450791003034110360100458690046503e05100704c055010b10000d070080ca0b0040056a0b50840407544200351002c0c800b500003418079046000000c40d50200703103da9031807502e00000500c60302c0c803884d00b404009041c002c50711940c81e010403c807031400c100554a80b481000d03200c807281d6030344207000041040c4260003543c400348541844995028019000382d50000340c80e032021107031603440380c12070f004940f0b020 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 110532904 1250 110531654 110531657
    0x30109240e010f0f0c02060f0417091002071e0b0d180203030a0e0307060804200103020c0304090203060906060307140c011d0d140c070b07050313060512150904150615 73
    0x81032000c0c0b40d04285d2080000a450707a0000d440b06103440340b84140740090040002d400c0c4d8110401d0000003519100444000e0341e001003003001c0718003402ea0020b54074071813409502e0f01402142a022070540940034064129015065103030316019030400c11501402a00440390301120400c0e10410041e50144041e04400ca255500c4202c400c144004042c60900e082d400401400310000030b0001051603840c1191040e503809421900e03617589400101c009102d80604084640008a000b20780702c0c0480d0000e500130442211800902d40710001000441d201c242d078500089041c0741d82c503040a40c0010040c1c548020b200c000018042c614480008400b00c1c03150f03080300c4d40c1e00030650000c1c45542011500d10700120f0310100710309041c0e42d402780c6540c0d0f42180c010110040f201003000c5080002c10000c6454007040d44034421100d41d5208005040d58204100b12084410408001251140340000501c40044c00600005994030b81e40c58003142c11814220f07408019444000c08180260803c5101e0f4104146 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 110534154 1250 110532904 110532911
    0x90a0f0c0b210f06010c03080603070509070e03060c0c032205030d0309060f050601140d020c010606110d02011815200910030e0601090c11012405030109240e010f 71
    0x10750550b0303507000c0b008000e01861150741c03051014590788082010107082d4075040101045e20340d1000a86040a2a0f0016500c11400010440d021340d0251007035525004c29000c0729141d8907190f51014950155040c281c010350f009004401041100000c0040402c0040729440d081c40e03100c01c080390030015580403a4000c692145080410030055129400310084002030400c628103100300020007491a1130035020500d48042110101c040483e4112110342a03040b0003008150f0303941d24050103c6c2d00d9004c40070418050041c2c20307a00e40d030040c0100c100c01c1034415240c002ca0409507490842c0104030104070390715603503204001a0030b0390b22404603110300034800240544921a620400c05c8a9025111540801d400e0888080a1410004100d415540758410200382e075142010122100d81e2100445c049a600b000d00c03082003000103010b040e00c00095414002d0015484000349801d98401d80c00042c1508807650300b00d003084410410b40229030340c01c1a00400c401d202000c40c02d00f03440d003001e4004003c569 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 110535404 1250 110534154 110534197
    0x516052103040b1b1903150e2401030209060c0c1f05090d03120e07090e0f03070206030c070b010b0703021b030a2607030302030f0112081b1c021c08090a0f0c0b 70
    0x1f1150313030840244940403004004d031404450005216402001220500d00d50300ea60b500c030350b0301075010307100700c03600250055481c2c103003182c0010b0b900c9030b08540160050f07442d042c454035440034116094101191580301c0b20300d0030000e03a06200141e1a0680c0680400468a407000d031009900d001d54480117403044c005004140c201100c50b021182c50040e500095480340811043d680310202c02c0d949155011510f4a4032032759180760a140d00e00c20400001c021032031031400803508031318107805804240c0c060341c00c0322a00d90025005500480e000030326036900d980494481400145500f064804a0300141d12680310010115031420f0550000b070421408690044101700790711580200207401131061214020080c14142c442c1d02240c031a01a682101d07030034001020403450401c20544c0040701801341e0301c181d1107200c14802134444140e80702071030020b203403412000703000e44c0f29401180c0506a4a00941003081c42d542d94858800903001c021a4190105640001c03c0c0c0e100b00c000d8036500d8410625407045c0c21 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 110536654 1250 110535404 110535431
    0xc020a17060601020106150305060402040803070c031b031a0405160b0d0b03010204050603010b180a060c02030606030105061c0302010e06070e03061012060b010516052103040b1b1903 80
    0x1000b810281160701d0200200a0030301d0140b1840140c90090500103180c2d00d4200104010748660380001c207041c40300260503c03c0002c80c0f2440f200b01c03400742d06030a14062140c4504015800d00303103c0905025031032100c020080c0000075800d60082e1064007120840c0e0548000c05100340416442510422800705e0001c62903011070060300510341d411002140f401c0d00704400035000b4007060041110186020070090541c04005800009100c401024100a60703645d290040464214141c101e011b40914400709225040500800d8016000100035080c001c1030100c60610a80e0101000e804540d00c0d0b140300ba004c10001d100082c0244566030314040403d0b100c00901d80f4140019103201001200c840042200546560800d4445540004045110211800125120300482064012038103036013142000700320b0002030150f1090b4030003207204c44011441c0401d0819000450f0040d200c01d945000051803080c00700d43e01c121b0f250b00950010704082c0d60314500c1000c01c7d0481e68402c0866501d070740900b680e0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 110537904 1250 110536654 110536663
    0xa020a03150906051527180408090111030306030604021306050d0b0402041409280803072706080604180c080d0810060203090d05100f051504020a050a0c02010c020a17 73
    0x120700350000741c6040341c1510349102c11241e140004040c1d0111ba40d43c01100d80d134100302c5130700712400b54680b41018201401d00041603444900d420303001c5200080700c0300042e400031041d039108003001000340509648903001c0c4000003100c4101404069aa44400f081c1e42d036a00d5070440e00e1034082d0300c0301a56417910b441804101c41401e09420190740c2c005c003c01c0070107040054950000020102881d54003405000728450116000100411000e400301c20044240d90065070f4229044c00c802c1c0301e100140c88807105212001c003078020358000803c0c0400048103810035801c201039519841d80300700c4a1540644030080c200200d60417138080341e0002d2415030555540040c449802003080300b4142c1c1100d1902c03a0180d507a201d001001030060602502c0c0c001804018412044d00c18500d5006002c8070344900c0c0d00300020803046511841002031010044418100351098445048843c1c442601d05011814180c40314512110102d04002500c2200390050301c0300c40348100103000e00c0040580b20b000c1740c240c1c181003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 110539154 1250 110537904 110537929
    0xb0405010e06060a030f02010203070602040b03040c0e010b04050f060c0102040806090c0406060e040519050c0403020315100e0c07120c02010e0f09010b0c070b040608010e07030e060a020a0315090605 87
    0x1150300030b4052190994800313078200101e81d4002000c080030a003510041c0e06502030000043d0200d440880c00080300d0300c18030010340c8101d11404034450a140c441a540640c0803080c00b03503800360201440240140e00748240282030142008200031300349906075048a0070380c1d1241c0c1214000790058028004104010807544210a030200d0b400e0144a081010042c9048803201c001c03482140c590000c50303000b100c1c8020058219628207414001441d103403202c016031f680039100480c042d1107000740000310580408030f0140a0800121005911f03464a81c010303400307000203401500c148804001d6540000c10b14020461285081c0d00c40c0c020250460002525120000000d0ba0040d18042d0109015030384200d80c15041d00e21240760252901c0304404001e28000c0c441d08036901c0d0000000e00440c615800a8400b41201e00100215040343d681c0f140032010b840d09000c02c40065400800800c6c503829054028240c40c0016140c001400302c2c1e090707105650402c1c0d03a030012001030350b80c0c1b006004504010141041 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 110540404 1250 110539154 110539181
    0x111010204030503070f110909160e060307030f03170f060901060203090d03081506040909060b011b030509011b060903020106050d030203070b040318031b090b1f050c03070b040501 79
    0x709480c540340c00b07459125280300100184a0346606600300a19907141f0392a0240207000d070070b0b6030714264044a960314040502c011644011140010b038081c803203803850b0b100714000b40142c40814559925400c0d11358a18004405015440359202190350304a41803621030b640d00f200400103810490140301402d903060300104110740081202d00b0454460150ba070b0040d0f6818a1308180e6961000042a501c070411061941c1c01030340003c000460305050703003003282060300880c4100400921072006640003014540d02e06144500c08104001013801000030f40800041810908000d01c0810380c6418044003903142282c030346076034444003014036074240705d8000541000d43e50101001925140a59280a5102c004103049005000030f805c040c4609401e098100700390032110300480d22490805031001c1c41180d10786104180541c0007903401d4003401103180298020300f0f004080b036a0600d4410625031208410020300801700001c2e640044104010040140503070080c5c280ca04181c03a2040c05d603000c0c452001d5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 110541654 1250 110540404 110540407
    0x114090403020618011b0206040506060108060108040303091104110c070828020a050405041406070504050117070e120a0204061409070f110a14100504051e0705090406060501110102 79
    0x70740c0005149410403004140d41d66080d1311400054090300c6440c45c0c489070700c4140e0040340c21482d00000c065004900c21020780e0f0182c1e4410b0300440c0c1c0144100c03070b041c2c0040c81a4002c1030109000f85d0103405498003400e00c1c003000e15906400b090944e412007060010441d00090340081c90034080c00184043e02c4550041c04411a10081c0090310711143c0d003184e0041413000c40441c08554840d2160710060001510034000c51405040c000300c000c000150301400c3c0d020707607070005000f2031103442141c0560303005071514142026901c40849030038400805000510601020b40502e59840458040841094600600d0840704620600095440b09da01c155440700d07405d0b90105041e80e030408003030b0b40043c2600c1c121029079124001160400c800d140e0fa0301440c01b43da42d000d0180850504c03c148800d540d1411180e041000903408001c4520171200175069411031054075041034145842032400b0704250b000c484a60342c807000018000e141c1660101c07105503545004102c1960801c000c1c00ca0116010001c6 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 110542904 1250 110541654 110541661
    0x4060f0f051c0b0a0f0f0e0f0c0c0a0f050607090b03040c030305031b0f03010302040507050a1d01020c150307080705160224070b04020108160c0b0c040b0d0203011409 73
    0x6840750064a03000800706031640c100150565641e03108030407020300107000c01a82552000d803200c5881c4c0314001c1c510040a03815020403038000180940e402945c607402c49400c6565020400d042a4000e60151460f500071a81e071840440d604200440c0c0b070f203005001800080c203000f400074208100d00e03404021404414000c01c00031801e180407400c22241c060400d0780e500c0c1d481104100c0d5144074031600c01903c480100e844214403d103023016505980c400d8030200302d0b40c0c407080ca00352014020003609800164144400c1400c141059400c602c2e51081801210010340280700050b04460709515800aa07080120030000c610750b1090360660040070a003071062500848071404104808103c2c07000c0e004880e01003104044c5804030740d1100041035202015a1644000e107800315000c1001d590a900040f840804104141d001401c95490900c0980b1100c44021440d941c40c421280000d02e9100034003400d000004902c00c41c0e00041030000050f00300140d0329818200480030343c4040e00d0582c3e000c4d10002041 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 110544154 1250 110542904 110542907
    0xf2d0b03030f07060209030f010912030b090a0e070510021005160804060b030c060c0606090604020f09090a090f03021608030307050d020309120a0c14060f130303020403020d0804060f0f 81
    0x8882c0d050340070094080e900c10b0a070420102a105080d9046d4251250000300c24110700c06500011003103104400025500310800390803415110000c0314690300560700c3c004035000a6031a4440420101e442c030a0750502a5039900081c074000c00c080ca00e801681052039100000400740c07150580c07040c5201e03460244d02c0c0c02c0070002401c15800510042009035540c1e404041944e01300302d00c1e90308410040c502a540d816100d8030f1500d6800c140e0b81d003402043c0c003901080d0140381c607000740c031f0164030b550030010308080301c01c0204400648050090012195030360b86140114101031401c040d00f038065001043c100c0090195001a00c14a03400486a50414018800101c2d0b104007210503102c080c450141e104e84a40440d40e0800000c031014081c0340000050100f101c6e90003020741c154640c001e1400e20316000c18040c00d940c9500b030459105481c040f56100042c60141c4689114190301d00919006041c01c0e100d03804a5028100700e201580e602c04086003c00403550301c030066a08200c0c0d14580814844407004e070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 110545404 1250 110544154 110544157
    0x5130f2409021603260103080403030f030603150f11030405030403020a17030412050f0706030b1003061202012703050105040209090a0308191e1a010206011d0a0f2d0b0303 75
    0x400b000380003420480c151413140c4011085203031701120109156524a08125903500c01c1c03000b10041201042c0a18246020f807007080c00b01ca070404103140f00381d14179100303060040116460006c0d4407540c032100c10421031411006140301e248200000c658450a50041108814071070780003c203080c0c20307420740c1c900000d000700c00e403001c0341c10141c85005065800d190003820622491540c6080c0e00c07456000080341580364002c1240d0260660701d0720710f00845000d0450581e546070048dc071001c0080080000194825a03811040c80200015500d003004040121a075034495540b00356030a80d121001d00040d45015003005401c100700800804106d852580c0103054210018401480e0b0300c50b14400040d65507903904a514012030266109110381c401c0140d603001051000140d522120540780c6844040d40005142d505a4000751200040307503607945010300064000902c11201261a40c0300d00d82880c10383d00906848090200624845402d01001e01c00f40c94141c04d403540302c139410961000c030b080e00c000c0b0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 110546654 1250 110545404 110545447
    0xa0b041b09050f0a030812010f051c15060b130608130b060907021207050105010806090105010e1303021603110906090118023403030e01060b030105130f240902 70
    0x54103542d00f490140c002456808803640040c06160000680c081491030814503d41070729038000c0702c00825900d40c070520900699500706c43c8040c41c280084480400c52000c105240c04003110350100c0d071719840f0741003003a2541021180c4050220050424481250024000e80d40004800c2200000142070307213803812543c002415150050010301c010036482031082c8085c9508030b4200082c141c1e2a034042c80c01a009220034420040e00e8041d034000700b0030008040c0104e41c12240c0074058404941c80300c84203c00d100c8203d580817401c0d88034980c120000c0e20f080107132017002540990841065522180c0910801f08802080d00d4070407200382c17005201c62a00b0b1024085a4410071900507201c4400d5490703406003140c440404280c080242d074681c0031400101d00e01040700c1d4400e9400340002d035100c1e10a642681c080b4043d100590700144010301c40d07814441c0d111004081e9040c0c01041101c000702281046030700f40300070207180105841c440fa8150005000040040000c2c001c110710b06102d907000f21111140701b0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 110547904 1250 110546654 110546659
    0xc0518010302130902040b0403050f01050f0615041e05010f17011503150801021c0b0d020f0112050a0b03011d0303060120010c12140f01180e060a0b041b0905 69
    0xf06500d11070003a0200c420380649945001156210784406040d811500f00340300c1100d0b10300c2441190000d185043c001e440c01a1103010743c40540d600c82100300709070301020192035141c0c1c1030180030001c1c2840019001c00320340c80580c1c0ca1903056074104000103140542c4841c684060002c0c510346140010303109039945045820170241c170700601c0101e01085001c0c02c202c0c0c410200364500d80da4041050304066004102503515200305502151800d003200042da100024135940c020740032041e070805400d024180b503490b1041450040c0d001240288280b04a96043d12151403107a070300c01110349903041c244a0340300452064030409030b807003090460207a501d00c0000c004504000e4496540390039103100c140d400084c000e000c40280000410480000c0c12440102c000506071810308941c10680ba0a07485624040c15481c19240031603800d00000c10a0440c81f0400701d26803c2c0d44112058004c04240082c034000c900303040c4041101290181084150b4948032000f525600441103014502608040c801e01111402d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 110549154 1250 110547904 110547907
    0x120a03080703020f0f04030b100609030b0105040f0207120e010e010207030b18010603051506190302010e0d021f020c100305010501020604030e030c041a18130204020315100504090c0518010302 84
    0x350600c413050f0301514104902c00400485c01208000701c0c440441e01c10710303002d80c00204040d6503810440e25181240b0000d420001a0380051050703080c10341002d00c440c1040d07040586480744035a154805a602045498005090039042c07091350340c0d0194044803103900c00d100801090742151581c0d540da40020301020444521008054035541080d0002001503030428159940300c6040c00c03030340c641c0340d00444081c1d1089501440121000740004442d0042c2c2c2d8043e903407100401d141606000703e03000203038070507a40550a40d0440345c0380002c108641c40034074002d50103400c100c0b83c0d80c002d002d9030400c124035402c01e1500707041c0140b10f182d0f030014056602c030b0f8040c0352040810702c2c1c14010a0170010045001508a801c107440303203004240c014442447d4540546040640c05080390100801c400d041e130300d1030182543d100003003002d86426000b40d500308403030b14201010884a00300040c25228140301420110350003240c2001520050700c1001440552410414541140c0384010031629405110841c18940e0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 110550404 1250 110549154 110549167
    0x1201320307080a0b070201050a140609060a0302031209120c10050f0c0d0302071a1006110c06030103050a260f0a03020c101b0c0b01050f010c051002030105120a0308070302 75
    0x30108426002000110240c1d450b5158030f00b40988404011100d54004d58249800302340307506c40500c181042240d4455140110742c444400304802e90001801e9680d001520140100140e9402c0c0003d1030b0f5441e2413100599180b907410280251008034042607038086d0403450780d02c0300e15200c1c0200284102134516142d6503071440c00c110291180a512501725041c800d0070400440d01d50194010540280500c0714a07001c12020701ca0b4180c20001124410800706100c4000c10999020707890960301159101c00359146051140b0100741c1c103400c01d900545155002204400134001d010751800c3c5200c192150020002c4424941d0f0013051041700032000e0610800034081a55511a074181d4004400300d009a6110305482403002015000c40704020101241441d400c40d0381c280620811940b090340081c03140c0c075503860582081b00110505501c0d03410721081d152103100155080c080403000b40a1050010b0b00c0f941404203012004495001d229500c2c1d0000c035140c80820b170443e1249900842d545070150743c461 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 110551654 1250 110550404 110550409
    0x319080906090d080403050d0915140c0c030102030c090906030a051b12060f0f10180b190b0711060301060518040b0d030504180b06070303050403020111030408120132 73
    0x842d001c4d020328000b00340401044804502d008081c00c4642d200c0f1812a1594502c400e0b0b100c140065602080e00503007000d4603041c42d80040d200755a011001e83da500000100402d0a9a1003214a070701d0075400003942c16510f14145045641007202a00100309001c1da590300c0a995443d2151450368545801060710200e0b9941d0702c4803405003d40f00142d4240b41031a00c50b4498064095660311a092200700007c0c004103403c02d0b80c0000c13140c5458544014248a071000707401003180411198108051121070402c1400c40000080208549510309540d02c2040c100011386254180303600b0b114070b10410042003102e40c84001d65140510045020f10b210f4403d600040042c41400c1d41d1542190035500c8480605800c800039200301e0f60041e00c024407017405607000d1310440e0b02c00060b40e684030100780709103c0407904c80d81c00345903c5480303400005071071045a594020789400803101200d502c0e00000c2d00c0007100c40e20090580c01850194100280c40704282d4030040c40030b0314101011110942c000710f022280d03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 110552904 1250 110551654 110551669
    0x60e010b030c070f031106161d03150906150301090b0403111006120b090f030403030807180b04090b010c0c0504091e050c03060903090a0b090409140309031908090609 73
    0x1150b00c541c04000c0303001c1c00c0ca4080c10401500d480d009042c02500005500a1015a084512010f4513628840059803003221071a09510049c00c46070580310f4008441881030600003a14080d5003800300030440c62401102c8035442090300350211b8042c2e4180402800042c0003201915000b56240c20041c2400304080c40c42071609400805414455040c10000200180c1c05030035480b001d8000c54800000382e07140340d030203036807030884420908041e4001c000400c0130911504041d40c009000e450030040c011189101280aa0003940050130800c05c00681005000b00501c01d00d400d9510a00f000c0c0c02e8641c441d219024500305901c10903000b6a00d54981c02c040024002036545c408030002e10402c001c001500700180d9070088149080d01900c40c4201040344040000159044d80000a0040038910700f480029403141d04001c11041d000361b01c440042d40080c2e07000b1320990b120306c03186005503101c01070311081600d07018a8201500d00b05e4245840304010490003c201c911503807040d00c174155107003540c50105502 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 110554154 1250 110552904 110552917
    0xb070507091e06152d0522031b0905070f11030c10090507050901080d0309030e030a05010c0801170c04052206050403080a180f0221030405090109060e010b030c 70
    0x1420b1034540040342c04415250004556032550f50703141d00c403445203002c2460742c00d4010901c4185d191107801d0b240003140b2800c0107002086c204105c500410814040c41141a21641c01c1100d17082242c1c03200044081c005c50310132001b00b0f414441800f40341424407000d0007000c900075542003040840783c60b108480b1401c00c102c078440034806044039180088250070030010b280044086443e8082c002d400513640c6070480b4003e050740c80b024094482030181a030103a00130240d00070200c007808220050307102d0355501880311045181c082d400210b841c000c1075074010300d101030503080b06408960b00429003e04c61030004180300d401400356000211030329801e0b1022440c108248407001203050158a00b020030605400c40f5028520a03140c007605030f00d650000c4000d40d40720030103101c00e60040d0301025010418140541000c00c2c0060040d90300d1403200b17059400410100156140c00d60710006040295080403440c41d401042001001c000c10f5091240c401d286803018450114001c1012000c00d5011038000100c030785 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 110555404 1250 110554154 110554211
    0xc0327010608030a0201020c070b07080d0f0f0f0e100618150902190906090b0f071412090120031b010b180103050d080c031305010905011401050a0b07050709 69
    0xc1394252088001d0103540182c2c881c6501c0d02440ba800281201860b003642c403c954060391440c02c142100035039900030101800034041150310707603001c0005000c1901c07480d694141d98030b501044504502c3c0d0380502d0031900e018031100003480d02104100c1c49101c04c600100c2d0260f03040c004504010900175503c410420742d0080d041e90b9100013950340c0600e00d011464a038030307440ca8440d028074941c0e0300c0c01559000c1042c810070699110410080c02d982c1d400c00000c09040c1d00c50203614010300c04c1190340a290040803000d4500e00480003902c00900c0da004101d11195418a40c203c1803201784113002c1545a0044405c808248040c02d0007030b4108500a4001d01040701000e000186c4400316203040840300e000030f12003a900381c000c000440c2c01003803050001340e10986603020303010300d0f540701c005100c42c2d6080700c26030a0f03645e55621403012000401c00e004554681500c840040c005504080070808014031319413000301841020800c7e00b00203440840d903282140d0a803d00000c503002040c0d0551442100e0510400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 110556654 1250 110555404 110555407
    0xf01030603051203101a04170a15061701020906090d02030a080705060106140c0705011101140a050601111605010c1406071701050d050616051e0a080c032701060803 72
    0x30600c2403d001441c03061805c034081e03048895480458800b000090354880202c5401000288000ea0925544500300e44a100c21140305803101e465404020322080c404000440e15510200a250f11191891501d028104000c41c50000c80c100012043d1040c010b445000303041c03001c81801956010b2009002840e00301c07a8059a841a519210340c8644090060070082610160401c034001c01c403100b6158055444c20061462a00f08401074801040345481c002041d92582e072030040d00c0314815042170041d0200c010210f001d042050000d425002d5842c1d0034090b5610120894000140601d050000c0703420070b007008000e00c3ca044c00d04890410b042c0007807403d103100751414401c44a03440850700e40107a2014406449030390301c49040001184042c200580039500506c0452100c0c00b0300b03101e20f014003100d420401e2071704030188820566184009514044080041040c0030300a400546481e400320703019280300c1c51494000542013440f5039540c4615194455252001440c040940c000310180080308200c9 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 110557904 1250 110556654 110556673
    0x302090406090b150d140c0307031401050604020906041403032a01050714070803060415060f02010f0506130903030e060a090219060906050a1704030c11031501050f0103060305 77
    0x700c0181ca500141103c8000107200050b03000d0802d200d80306000140202103018039003890311503041c030041e02422880503000d21004074000ba9010008c01004601c41c034500448441c40c11000d41c00c4440040c00070b802940100f001c0516aa141c0040b01c06074dd001c03151600c8110f0a080110b85107000d840e0b1401c5121025904240c0555030081c00c44103004d400000034003241d59019000c98047e17011000300e20301c485041c0040340000780414050f40e440380c800750000501209001060416078400d078004008102203031000c15030583c0c28007900c25103602e002c000340300c54203002c030105100c00300e06440400c07203968441600c410180300b81c006061280904044880754204000311500a204080c000c038130440d0819140b60300d241950b81c11901303c3d00c00d134940074107040c90990243d400b40d101038211800c105d02ca54003900050907a83d100c0d0300640c0642c0e00e44001c501240f801d100e01c6401108418881d910452000588200c2040014150f44055400002c403080400059000c0c0803075410062442c00758a0b01d0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 110559154 1250 110557904 110557913
    0x1e060903030f05090106050907050a110706051b0303010302130c0302070f2f03060a05040512030405070f0902190f050d0204030b1e13080a050f0d050702011d060411030703020904 78
    0x39802c14180a908110b1610340302c1c5250300b01c0b0b00500c10a500300421000207030003103000750003070300292556051100440d1980e481c03032410080b407034100e103001c2031002c1600044072480007070034441c4211480c0114038550441c0c000070407640c0303c0d00d160244075481d10f00c2e00c00c806110f6015110455842290107900e0380d8507113080f08401080304c1e036030a140c2c13000c07510310304001c00a0941200d100030301030080c19494075500d030580003604000703109076103d10032011640021711801004505c00e50141c0c01030400542071044401190340a030b842172500e60b005001408200c40c0e0700e40720300c80d0003c45007400091700544840c02e5076103000e041070762860a80301007030000500c0142c4045900c82c0481d109901585010043c40c0c1a400800350340340d40b4501c040701d401c940050751050003004c103003400b070a08509140c011540c20786a0703486400c012805a07103074410b0001e840e40900900903103403a02c0c4144c0040380b030969089551910300400180c40b0f81441e000a01044d2014800c100c00b554002d00001120b00e0716052 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 110560404 1250 110559154 110559161
    0x609150207150b04091e0620040f06050406200c0a0f090f050108030d09050c060a030b031608030f031b0708070b090703030f0c020102100e0a05100b06071e06090303 72
    0x2104942400c100100c400f500d010b100e0200c1069105103200389140c0f04a802d00010400440e04550166807044030841040c82c54244001400c0c203060300d076a0b541c3c1092101901d003802c5038042c3c8144603051000f0700c21150801d081c14401c8820f0880d42103480412010b071031800c81c01d4995240c000044a07401700715808050b69903001d07a00002401e001c3c100001802500301e580034454105070360024080072050f00308070b400200c9881c2c000c00031076101c1300c0070303000148503a4000383c1600c020a07660300942c01c0741d00341801205203040044090800061a281030252244581040559042800000184c1d4031020102d0390f0703124401c58200507251015440c111901c2c2c2c4c440354054480c210a28002035520900140d01d500381c0ea0b00d9034480800c590408010b031042c44001e14224194014001150341e245000d11a500074400b83c10010411034040d82032540c00d220003110341e11002030034900c1000c281c0e103d1030102d500103079020303450484d5411040d52069100b003000360010201818101a04141a4140c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 110561654 1250 110560404 110560433
    0x6030501051005010915020c090c1206180a0c0915020c011e02030a030504020111061014041a0126010b0702011416060203090304090203010e04140d020a0609150207 72
    0x700015128014015005003081c4a2140020500c840c01d121407848411044410022801159001403042c030016020810031907441c940d2210228071807804210300c120f00f41d0445816250841c2020b9447c2216080710301c000d2840340041c0d1101d0641921a120b1501c00d002000101c00382503502c4e0100e00000e4542d400400030328001344990240f5118041c20354011040d00815030002c41c03030003a0030101680600070017001070b41440800c040a103183c200c107110261048404522080303540d0305211041c511240882061400b8910f00016843c44074528008211ba0f1402420700c242190b2000c051140d20b500282c2d200600320704080000a2515a0b1002511000c2d100341c031a4038010000340c030090030314001c0c18000b1000030074400b40c15020540b2a802160040c140d101524601030721181c0c49410781e4000c0e40918040c455030001c0106001d003041e0385120034203e04010304030904100e84025074500d003001004d05040d82c0c50500c04104030350700100c80d180e4020b40303105540722000c0e4100b5061800021 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 110562904 1250 110561654 110561663
    0x405060318070e0f0f0612031c060b0909010b031305150603070510021b040e01060807050a151e0309060e0312090106081207080f030f011a0406050313020d0b09010603 73
    0x10140410300c003050f80b207400d01c181d18070801d20302550703a092604c01d01d00101404446e000140c8401820403914240020301945850f1410401c07a25a039891a00c201c0c0c6a0340e0025250740010b000d681400ea507003074090360464041241c06500c03912100c01403100c80100d020020414460104030101c0c004219002d18820740b0101c4c103941c01c0d00d030f4910034491000f020380c106c0310040c1c01c00320f1106804020000b0060f140b50010b000060000e80452082c0d0841d80c0c1c0e500322a005a0100104200351f18028491102400c0350800c115a41d00c080c40c005000103900b10030741e00010144455643c0e0300f910030b82c4624580c603007002d028040081459005501e95014040c070110008a803c001a08c0100500840c0111a43d140c01040c4110033007281286c950810785084500200402214807082200e001941c000c0301c1a6134104169451f01000805400b000440490141ca06000421225800805803175100d43e0703a8000d9581c0386c0c1588000f0390103c1541c18010f065107862401d0045541d0150300c42c0055905c113 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 110564154 1250 110562904 110562913
    0x9041a0405010806180a0201080402010305180706030e0105060a0e07050a03020903150a0c02060103031e02070e0f16080103170708070c030b1819141c0201090b0723030c0405060318 79
    0x14614006c0e103407112010301a011414180209005504c40d40c08943c0c040c4813542e0b04c1e0703080580d1402550070700855601480000340c036240381c003d03064028860280c100800301c4000d98500d18081005044010080c003180601c1004500200140d0090b01101c15041d401410394902440c5145110802035040d5581610503240440000358070340005070240c107903501621280210425510814030202082d422842180584a030005411203102900e90203032038045040181c034900005980030400c150f03a00742e000c04c00d001c001040441e401b1005603d84104800070150f40720702d40d0400e00340620800c3d0008040601000f000000d0020092025018070000d504031007101500d030300510b586000300800c7d01d42c006108590360b40003540f010407541d0040380b60800d40e00c480044a0b4641e2001d4185040000540d4444d000001048503254100303034090300e6401c089501400480401e0900000341c001180014030000c089100007081070203480003084010049561781c913141f0a400c1d00644848241e144d503205 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 110565404 1250 110564154 110564191
    0xf020319050405280503030907170607050a0e0f06030f07030609020c1018021c1209150e0301061e0f0e1b070c03020603070f0e060405030309041a0405010806 69
    0x5030161600440e0004000d001a89040340613254804400c92101c080c1c0c44a4102d0b4800a00e040c409144948440d0f806090850310304450f030104031840b000b018210b6000001005145034000e8180e03010340b81903250041c225010b84010905940b07410780c01d0740d40410007000304031003940341500541c400c002c155410f21140f40d039960394005a0189400c0d00d001900008801805c00980780c1c461180c1610305042d01c84100d8068010440c1d4020b1440c1420702d02c010f4200c1c04e41409803006003001d40d44402d00c1c0c442e01403484d082204515034000c402140820400c4213168400d03903800d4011501500f074000f083c140d00c01ca041034859071a49680f00d141c3c00b102800000058030b00c440b4030860310803011511040c0c19520b103403412600d1944144405c490340d060405010026803500d42c040e5104450940318000144c1442d6000351416400541043c490740c410031042c40691404800d545007003109480120f04403031101d03005150010071180640c2c02900d00000058100c50010b50b0ba4020b00180b00c0e011384048 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 110566654 1250 110565404 110565451
    0x3201152304021e070c0914040b04110a081608070b070c0314210306131a190b03131205070201080c0a0e0409200d0f030e01050d0f0203 59
    0x160303896940120000140000c454505040e001800c5055010b1160400901202002d02058000c0c1c0d409481000443d0004e001d503041a10890501485920320518149400e0f540c1c046045d1000304028003c5100007210b144584800b010300f03000e45402011b03642403096509030a03000c00e402e032081c458584181c9600040c0d420441003240c0341c881d0031140d29a0318a0968540035080e6104103d0301c4098410303c00d11079051500207001c8184424641c481341d64905006003003108154a035282011036600d421070107017142041c000d030451011016a8040c2d0681c00c1c196000c012010154040c0c00403500002c00c0010081078440c1401100748642140c03480300c0c42851007100e5a024041c0c000b8085414000803984815091015041003003031407030291b020700035180c081800c0e108005030031900c011202104060f0081c0d20360000070a24025210041001c02c103850f041d0303030401c0040004c0c090003102c02001e05907901c03440c11102d280d081c00005000b0240054003d100a40c8201c841080c0504a80c2c40380700b544 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 110567904 1250 110566654 110566679
    0x901060806190807060e06040e01060c061b020606150d060b03010302090903040b031f03150f060506160605060f0909060403120501120209060316030b010806070c030c320115 76
    0xc50f040341c020302075039040580c15108000360180450340300300184000904000c900328141c0c080c001981d00c000c492074041c6041d10035030b10a002212409240c1d1008074501d10350000321160701c004221030700103210300d602c0c0f20140c003403240d680c140c407200d0b080680224490b14000000e40c100d9100343e0740320700195520894036849000d2030040d240b00702010401301e8881c1d20207143c5d0419110444100446490341c80d503894070440d50551100b00e06503101c0100455507045403003280018641583d00c14a80758000b02a00121400d0340801041d80c0c0e80c030408503c29032942c7c50b600700c02c40e1014100d1034039810302c15101503544608131400c40004440110580143c805801098103c40c40c04010360443c04055080000800c0000c0c032064062242c80d146c070a041402d60034150041d030150b0f1000041e54184501641800c0c802480c1d8400d02c250340d546003001aa20109506649801c40426841100e2860b1040100310900500d0404080214001400280103510071404480c5031080c1c40856075a81182d000364 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 110569154 1250 110567904 110567909
    0x5031c02070519030311160c0f060203040603020d0621060c0c0f030309140118030206011a030105090901061505040806071103180102120a030b011d0906040c0e090106080619 76
    0x6030f080302080020740000d030100160070910034100850701218410b800b821580100116801c1c0820420040d001d100342c0c660300001038142c00750341282141c1000406543ca210303a21610b000c05500099540926030140c0c06800030b08200407041c0b1803807a552180602c2061800700580f0395900d040204009180140058004141d001d00c103440c0c1c540301074809034014600a40150340382100c03c0240e41e40c8820030300c1094508001c40b030103c0400502810000c0c40c0541c140c20880200c2071070f0b1502095809003034181c9044070710440e2511090740d11610302c03902400c0d8a901403121069001d00c101e010039085006003090b103031004200d607041c0e0359882c001c8503841e0400c1c21b505142d0308100a0110714401c800c200080300001230041b10606402e500003030419a0100c41000700003503075000341024642e400001070711440d6944143d0300313000e00d81c03a001902c055801380c0381d10700c02c542d640003120350305003e00031410800c980248003003d10741c0e40d0000984010f2044411038440e80301100e00c0601d89101810f0702d001d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 110570404 1250 110569154 110569163
    0x40501120e060a020a02100507080907140d120c0c031511090904080901030e06010906080717070605030417160c0801020f0429070c0f060302090907030504060b060705031c0207 77
    0x810f486945030703800254010062039086020708060007440c5825070041500130706440e900d03001a0724141c2c030f003641003d20b03a8020303404840410a00e00c4484d41d44185983c80c031a08405400050020848152035100c0200c5004260000616000040c098810310b54a103405a541c018000c10030480c0301040d0f60710413550011b0744001031001180110f840500603050440040c140003c0944007101c00e02e1800350b09900c24001240c850006110041e01440a10700800702c40704900f0000d54240c0402d03403641007500400301000000310005040c4068840c1010707031094208601a034130b514101c400c0e420101d03061300688030308003002e10008883d081442102c0b00c00e041005500d0074a418054500c1c00707070302d00c2c1c0098030315054815610400342c0003010080c50158801c80c05000c0032850200c101c482174903141c1c80541450700c10301003698991502500f19030b00000c0d40ca4009a203585e5440d01500801019800c150000004503000c41080b20000080c0540745042c1000c410184c0c0380b401003030681c443c49800030b1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 110571654 1250 110570404 110570413
    0x222061706030d08040524060f01090b04122618100c080f09030312071106040206180111030f07110d17030408090405070917060c041211100203040501120e 68
    0x100782031203102e080390028450030580e04e45020050700c1b002c003a24080c07409003281002c182844001c9c5060040c0d40a61034081c01d150752031618110a00c0740314000c03403048101d8041003a1180b4208006011340700480c80380800c90040b9040546a4289140c02c80d240c0c0070703c40445819140564070f09401515440e20881d524030390340c0b800e2569a20303060380010030303502450322080c40240700c503035400d00282061010380000660b092801410040c1012021a40120240c0129040c0405a100d020484d40560825441c2c032004415040041300c03104c0c0c404888184500002c24140c940c42c1d4200018100c090003001c00c0c550208010741000145140c0e080000c0c0106001e4880c803400b0180c580144d40d00c180613000e124100810303940818142c0d40203ca02000095049209014900c031104444e51040c400c54020065880d00709071064152051340111000b925106010004004030212443c000c0384000c0c22520012001c400301035580c3d0040e02031076000c110038000020300380607240b1415811061140090 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 110572904 1250 110571654 110571673
    0x10608030f071505070804050601060504060e010e0d0213020a121e0b0a030b0c070606080f0606090606070203011a0a05030a05060106030507030905030a02100507030216110103022206170603 83
    0x1c0c4203911601049030426429005112041d80ca8401d4501c1984180c0f900b003181d1409241c070070b040403416002a424854240f1060240032b600920440e0391000a00b8104001000000041c0030845140402548805034281d4845c0312070f00c6401034003c411107500c4289010703404100d80030507142e4034040c4015120081c40d16440c01205034000c21a5000050100c0520a41300d40342c0f00c0c041c0303038100c41c1d203c822480095140100b25041c403551008015010160550001d100328060725420080e014a1044000d100803c2c5031340d88030000c40300c0942d4010300030880d0309c0040244040d0328044409083c030510980d03000080e141000f180701c4103010b901101800c60381e0b08200302680140360160055040507650801000060780170401811040f001760000c080901500c0fa1400c1590b50050100c0c0c00c240c018051130071304095002c2010741e034035444901000d900c219000100d00a002e00043c0d100c92040581400a0004035500403c082d0382c1c0950b528002604030704c00100003c50705580107a00350380300f121a03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 110574154 1250 110572904 110572927
    0x315030b1311061908340201110d15050306010503120a05040b0408030309070b090d060e10020301030b07080a0504030f0c150c0e09010f031106130e0408030103120201060803 76
    0x24414415072114072290200c5010943d19004005031304440380101c540350358803d4011320703201e40c03102d0a2202c0341c030b1304241c0141024002254240300e0310001c0030f0359032401145000790048200d55000108854940d144200440080d001460151150040729040490300d402c002c20f8070342c1a0307040640140010802c9034030b118140e84c422814541000400d01c408549200035500810041400380021a241d0402040150400310654801e1a10b000208448001e5440305652014a25000b00c000100c4942e200b5040d0300f40900c98100b1858a44000004810001c0340003006000b800340e9607492010b0380d40c062a8104841c401e46002d008140003c2c00240a2441802d07040010b503c900203044450942e082e2031015198000350380c0010500f104400c8040b030070a10469170045c045010072041841c61351712144c0e03c0f502c000c41c0c0c05019000000308000d111188000080050441e04000841444c01d402c184e02141c2081c04119621191101c9a502c290b00c140608425540501e01440c9070403130200e003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 110575404 1250 110574154 110574181
    0x210603061d030a050d090f0f15051902090d08030a050702060a05090705040b0609191a090a03030e15070302030406030b03031201060e030f0f010b041b02030702060f12090a02010315030b 81
    0x2a17142468a40c8108400203907424240c1c14442e201c1c2a03000e80030711484c50700709841c100b90300302281554500404c00a151003410440e0700c0d800c02103000181c2d18902c00c07000c207c0359207070000c002c3c141150000c14040d95035496803007244604665800e0f01c8040d1200c0443d01d06481c41a541c109069203c00b800380150b113000d034002d59007000002c2c1481d25184880e804203200c800060180d603002c49052208205c800440d009850a889141140c107240030010320008010015501001d420014040140e40c0c0a407240c0c410310780d2441200155a0303c94002d450020744c0d0764014000c00c80041c1c20b00e14100d10300c2c1000010359146a00395200341310242e081c40d03400c507103038103c0b512101d80c90b210b25185420040c2062050300044c040580000c2042e00c2c1c41c4040c0000e8504590315075182d924140b20100d0802d9012060b030306025412079815984002401030300800303015041d074424960703200e4810322000a00c0010000034840c800c1e2001c2c80b03044506020f2a64907503940c0b10252010b003c400c00034141400031031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 110576654 1250 110575404 110575417
    0x103140d05030403091e090509070303111f110705030f18060405180a0f06080105040b1006050d09170c0102030a1505100c080c190510050c1801210603061d030a05 71
    0x40000c141d61f4500d081c0302a18020740f100704540c2c0104c00248203040e030010f103010b03000071442c0051181613981c3c031417012078808100103003034095540c070761401070001070742d0446031410b03001021079841d01101184201260300498042913070340f4180042c10100e00b44030007510304a032002030a0b540c5115a400310f06548241c000c010380e01081c2d54411202e1034100c2889080c0c0a021200f00000d0f071464076140c0031b08900e0f8040e081600b101c0c0c1443c000c002055002d030840b4490280540c0225010000740342c4040c80307504440b50510000d05c0401d000f20300c084158060341c030840c030034001848a020341402965103c0e0140c0541d60700a12228130802041d030155281d0310142d4400c000f001c1c5403000d4822000d0031f0608210510001c2c0b2042c3c0c02d00c41c1400310400017091a01048202000a820500c145034040d101d220300d62000882d8041909046038001d000d81340c2c405512071200001e04000c0741101c0010f007118001101c02c01d00e013110014000d03a580d000300f070920000c080114581075004c0c070262243d42148 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 110577904 1250 110576654 110576699
    0x190201050c28061d06180c13050712090213020912010c0201050f0a05071d060c01051801060b070f020607050f120d240506030a060e0103140d0503040309 67
    0x182c8107103016254660a19000282c0010308022a401e182207401d4a412030341c0f605080b09800e031044030311a0003107031440c1c04c206c041400701120302c450255681002500019141e020f070030301c01240d01154007034001c41d104414550f01c440101d00e54000c0a004c4901400e4065000001851010b209a2850b0700804904e1001001d0511105104d16007900b907a05001c0c0045c0142d46076402e000344001494082c1e9001140300c4000d100514107007130024505140c91058807400440d080710034141c0c0c0c5409045403441124807000380564030f802040d00140c0c5c03c001414003469860820002800d2030f11106a800e02a40070183c148480710540800042c0d0b04600d8041d1607500503030b07103070301c0001c1810040ca0003c00c413050390003502c07182180c444904882060104142040d03030040b04007400fa82403541102a92812140140c481c1c40c1c00c0c48880c0144159040840042130280001c030170300c006800c0381c11400352100121440d6888406044489000036240200440c038000818440384004a08020a01044 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 110579154 1250 110577904 110577913
    0xc170904150807030204050c0c0a0809061c0624020c040f020906070c060909051302010807110d0203041505040e0109090317010e060901050a1805060415080d020105060102190201050c 80
    0x446401c2105224180c0c000a42580b10340401c1085060500549501c4500794114908008016100c203440d031f0451140102246000511401150ba450341960590895600441c60710110540b800c0b0007480c40d40121a16080388000400008401000c0c510541c180c5d6405040300e0744562050001410926a51200560702030103c4800c0e0b49a99018100050203005400082da00c3c002001d400ea00b4181c000d8001d00b4202002c00c10400292250000055828070b4294929a94880101c580400c049070078800340c0200e404507a5217643c0000a40b0603134203880000f070341701c0302c4004c0e065845109a1040360f80305000b0700c0c01041541c1240d070018051038042d0030041e02d02c0d8030b815140109200260410034000f115030342840f42e40e0034000552809400c1c2a20102c21450a00407910003110000000084480d2a10001003a9442e203400038003001d8088503082240c02d859103003080d01c4d03801000c0080c00540c6021b00180e125031001031466102d1000308002d980d141a903400460702a4410400445540b06 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 110580404 1250 110579154 110579171
    0x10e0f0402191e0e0906010c08041401170106020718060b12040302100b0609060904020903011a1804020d0312021308030a020c0105070b01140307080604080405100c170904 75
    0x140c41c002040710407120a0b09035640d591100001e01501c24448680b034002c24400e182288683d04000900140182101c849566549150048030300302010000184007480100e00003a4060050b14600030789802625a141d40341084000d80725407442c244158401a40141804c001c94440303000018082c0520384004640f180e2103155844241d4041404203958418282c00c1005050781070040d441084404001400101c0322030000548502801d084039104160005846070380b80c2e2290b040322802400500280130041e039414040500340d0170084424003030400e0030501140c035664101c0d0b803445158000e11a28000e5080d0702c0071250008200d0655035225400c2201465140c000f860050050002c18000c559a0302071840080c10440c5e107500301814070005000540001c0c0c8108405815030782c0c520340c820301503004200064a402503d62000041c1c2c01074805000900031031710024011780340161782c0c01315540d41040c0d086070444802d0302c0c06020442241c00401c80340984d080100850480207001042210 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 110581654 1250 110580404 110580409
    0x6090504021305250e0f1e04020a02030d11030109050906190203100302040509060103061b050306121603061b0914090405010b030f0609120304230703080304110a0b0c0c010e0f 77
    0x30900d14980042140800440c2e66450310703221b040ca000005440c0103107042c45400c1101d00040200104034890340d004a04000428070810542d490058410028889006025540b5055610a000729400315040c80002441b85400091060150843e0240301c000206100003400003500040c2444480f001240303c0080944d032036004180c05000704102400d030651451500c2d508481c06039082d07c5082101414018000e0703000416a5842002540c0240d40b000c07041c8802ca0405418881130401016180700c00b00500c1072a2b8082004c40f4100e8103158240c6103807040036911141c50340300d1030004510107085c1c001141000900d180d007080c41403001151424600000074103210034440f109140e81d0004040101c24001041060f007040300c074000c0d8505e141442c0c0c55041c0c614241d403540c00c400111110203641c08090421240009541165446440b0b0070b180c6071008a8154210096118040c0000c0104a00072250300b2562020f85820040219901d91070054860400d2500526844a040c014207207298 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 110582904 1250 110581654 110581711
    0x3050a030f0912050d082d0901020706020a02100609180609060920031504110904050f01050103030c0312060b09040e120703030506011d090103080f0c0d030501050406090504021305 79
    0x4510801c05070102a0001400400c00c445c02000c40c0784008a060085c01030b2407140c02c510340c11044012030b441d1f040d0340e2003451030b0280c4a03403c0b004090030320000d014240b00d40d000c10f03103c80450015a05006c96070343d0303951500c140c0f03423000c01c24013228180a00c4071000680340d41c407407490213100e0080803d0181081e1502d856591803440c00800fa1105a89481403d01d8248585414903000d130320300c1151130403c0c0d1905041c100591110324050581180410180b10302001086921200030009021568592900800140340041c04401080c00704040d0824446180034100c1503481c800b801c41d00f409800010440134020711400581c050141600038080031034110002c0580500039100807605013800c0d4001460403001c41d00000c2d0008141d1005102665a04051070440e80c001d400c85031143c142c2004849a4410449402c51507c1000e03402d0790703038a070945c200b2030480d60222820401213665019200c00e41c3d2081320000d41c810700301c6500c00d0004071303a50300c8240c2084100100624114460b030601e102c5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 110584154 1250 110582904 110582939
    0xe0708010203100b0408030336030714010b0904020f0f031b0f0102120a0302070c0b070c0e0603070b120a0b060414090610020c010f02101d0c060403050a030f09 70
    0x941d400004001e5109a41ca0004000b00080c003020381c5040d11300418540c803030102130242107122180d103079291981c6402440c03400d0459000d00700880180b00e07041308181d9a5210310360031100c070054011f4009a91106224880040070090b0800c9d0442d0380d242d003081fa000700070100b4036030710010007038100d044c80c3c03010480d40d105807601380e805010322000401004003841d00300d4180c2d41154002c0030f8001054041006541c18241d081c18050b84403080381ca410102442c282c0c100301e0103004003098260511455100100454806460f0000c150301e03031205060300ca400600445241510030003030f0300c560b00c5040006582c042019880020400011800203080d5070255002c00b00b21000f400f40894070346031a149698100c0320482e9446494001c3d880003940320303042506001e0500c0f030140c00c00310701e142c001c0c82005509102c03101e0130803501d0f01d41320b8a2140d503a000d0380301c1086445a1601040c031070030b00c0b80841342070300c0d04640203006010640c2d8084510440901c0d50301d0801c00d00700c80c0001c581003031240c625030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 110585404 1250 110584154 110584169
    0x804020d050102130f18020a1704060902150a0f0207060203040501141b07080f03040509060609040f180b0903160b090f0d0e030d081603231806010902040308040611010e07 75
    0x409030b103000240441041b0030041a0b00103441000101d07040c5400034403440811701c3c40d100700341641e901c605240005190b40c403000780d0010503600780c601e100280c07400100410750150729160507907140c464080b651102203000340b50140e40204010300c240e41c001c5418250704400344500b54606803141004c102c0d440403903e00c1c0c0740d03264482c00c002d01440f0801d011802d94228028000c42c102807070180014050400507101038002c0500040302d40381c540710307504110718100d81d8a00034080f282d111141da0f015000075440075580080c41e0350200d0f02080d4044103c40300131500350b4401c8242a0b0b55143d0101c1500e001c1c00c0c2030f056218514002e00604024010749180002a480c2c0001002c8800e083c5402e0460102080080002c035008210202c0e491450007050647c880c40c0000d02403c61901001c11a000e03500100325140003203042042114030109202202030010301582c4c040d99848107800282d000e03d002c0100742d07003010b003c1884441d02c51409103c00407108400801d81c1c603007004c0380c1820604036803c44c12 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 110586654 1250 110585404 110585429
    0xc0804050f0105060f010e040e0607120b01050309060402040c110d1e050c1b03031c060f06170106081905040b010603061502030f13050a0905010303021c0804020d05010213 75
    0x2845000d0001c1226800040d000b0310251070f00c0030026050501300344880e07052001d07040321100d0585443d4410348100b03002c5c0c0c0c115071440c103041402900b40c800022b1010500c3d414400d014009510a1003542d008890420041400f82c98070f500f0400075046c40d441075000c00038000b11800c1103010070407808a20802035162400380150352003090090902c060500d4040c828104010070300000c0000300c00005a06c5107189480303034461280000e04510581111205101c0d4002c0c00c014130200f19800b8108503200d0200c1824900d0355040c1c05c0e6240d00400104403021040c0c50010029031340155a001d600400303061840002d101c0c00c0c200a401c80701c0a840a0340c031003202c0001030100603003602c81c05001c0c20507165851034002044100958a2207007011803501d00c00049915070000220115040242a0081549581d180c035a82c181c401001c0910094005200301c0c20046410a101a0002c40c00c00041c0d07204606591280c0070b01c03400750403900044405650030800c0710050310300b03248004040c1101082c1e00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 110587904 1250 110586654 110586661
    0xf0c030315030d0e180a02040b04180606030c080f060a030209040303020304020306181209040603060903020318010e0619020a0c080d120204140d050102090d0c03060e070b0a0c020301020d0c08 84
    0x5440c21260180c00350070311860360007410260751001c1900011040105c0d000d400350b5191401c1c01c02a001e16030014943d01000715001c03c800c190b03600d02d40c510501041d020400990340e08030803800d41c1da041c1611004036004201003803138941b480d101c481c0c0c40040a0318844a45980764082910100304840660002ea4048103010451500780301e00c90f00310409444287c003081c401c61070f1f07a888411b1581d01300c009440c0014694200c3d1200c0e0400c20041d500100d0400082e030072420040c0d240d41c00f000d4841ca07500d181d0120010150302600c5440b2003560054001400c00d404190308846c0c001c0302c0300e010300552281d01c1806001924801e4600c02406618026040001403008090040c02c9603158075000b05006000500c114001d82c18081140c0104880d42e104141441c00c4c4140203200c4c10400f55004510f0390481002c0c0015003800108807031040404100e140d0b0804200d54942801e40903080c00311000b04a502002446028541c80b41400200014a0440c030001020101d0b140b0b21107600200b0074080c00c2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 110589154 1250 110587904 110587909
    0x11e030e150402100c110607020102120403060603050f0d21090f050d02010b031c0315090c08010630020306040f0911010806010906210e0d031a010c0302030f0f0c030315 74
    0x130f100310b51060601c1c503d004603e60b0703224549000d0f0f2600c0c6010348008142c42003568030800c0000441420070b623030192390390b46038149000585181c2c04181c40511886c2d0b0f810b122940e00103440180104141c1d14040e20898084a4807440d8801c0192406803948896180340417030010410b04045522850092a0001021f400a400e5a0402e03420300d1003a00100510380c0300d038138000b58500350760300c0c00c1c580003400c2d40c0c40341c00092000c085500800e514074584001e4400f2039400100d001d068421948841a4140643e1104401e03460181e00074482644401d0400748800f8080e0050b58100800603c0031800c5406c041908044543c0c5e25415a918044010019841d5801c0f0854981000080c80d20585aa040c07820144c4411002060781c00740c030780c042c20340d8500c81100c0d5200c1901c0303140c0042940c5080c141280014084c1c40c80b0146041d813400322440e075903030381d40c091806065010340c55006942040e101c84051103e5030042003106259034010401c0710380302c58007400110b11071000981448503004a4905 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 110590404 1250 110589154 110589169
    0x3140a06050f04180206070c1e060e0604030503120a11070302010b040b0405090604030804050a12030b03160f0b070f020904051e19080d0e071508090606011e030e150402 74
    0x10042d00440c942103003900313140780703d40c1002c0a144c1c066501941e28030742440d03c4041c5205c41e40c400311140041c041e2100d4046800c184060440c0ca143cbd03100100e400310390041240612480c40f006006502c00c01800941142c4000c1d011380c00201c01c44000359203603540150075920703440018214010f075594111401035103003510400c011414165801c0100b03141800d0100e5032140042c02c00780900c410708000904114007009415060355100038bc10240000700030707004e40030300400444c4511034002c4142d03079000b08805644108c11150001075003d0810725254203114680d1000105036840b0640c028611b0150700e4101000d40202c0c8104018102207410944128001102d002d980d400740c1c0000f01c00003500300d0a84851031506410142c0650b4900c007440140c002000303d1217081c98580603050000900c10985c0c00308080e100e0854540320059502c0414250302c0d084115222804106001d00c890440d03005031540c18160302d280c0c100011011210050340b407402a88800503030b0003190341020042107087c00c00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 110591654 1250 110590404 110590429
    0x102040303120c0e131104030b0610080c031302010c050102070803250504030308070e040e010b0102100603020a030b1801020408010c1b02150c0a020405090606180f0606030703140a0605 81
    0xb04001c1c1c103c00c0d801c01450030100444c01072046401030240200d04003154440141800300302400d139500c990b03a01d0490348003d0100d03241481181e88107140380300540205070340351240e03581c0316003640745558101c046c00e0034800e03450050b0704001c00200c1e01400504244010201d242c0142900342d100d190601c900400407003515807903c03109458051401400d0b401c8001c1d13400381d1740d05061112107030380d0b200800c480034401040065445420a05030b03c0c2c1144043d4403aa501440a03030a0b07c50001c42810020b0036180d0b10700c030080d0400e034000c04c00c0007c01e40403400307140c10900e40a4248111202c2001172420b9030810f412840450f5580c41440d40e4103500821024154408110498030403102a0001207804101c400075408000c000249100b001005000065001e54000c20820032410160b84450395003504030354a501034001520a100e29007444d0200030b100310311000c0c2880c4507655043c05d0041c0c1c3d40000d020503040c56142d00d100e40f60b03201d0f11b00b00709200b18589400040d05516140401c90240c03040e2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 110592904 1250 110591654 110591687
    0x109060501091a091f2307110607020105090d0506060a0e041a04020a0b04030f1e0507170c04050c0706050c040506042309041505011a1207031401080102040303 70
    0x1c800c100002c3d2002c03000e12115660000d2502e0300d4881040208440d910700f80c5a6003c42c00d0b40240c0c1d91162504102c210302c40c01e5502d0340002400c0501c60b1045481d114a61003c0c102d07562010008480385042401171206520600d085403c0108800110b6000680084112a0360f0400ca0400401d07081c02c0d440c40c002824042003544113810170f9194a1030a080408000600702410000030b4195124003414000400130300699558440c1e803805c140348602001134044564850a510520f102821020300483c200d8024029102036450308000740f260500350070100b45a40103501020700305668a10603c2e00c10f61402110950b6601d580c81c24030200d51000b45403d49032a400d2000340102e8450b20203171000c0d034440e840660f201d000c04080c1c40c0c004040d0a51610790000e0b01e00100030410020162071131002c44c604ea81440382c1d0362107108089040c80e400112000010092002c42a9031022401d165000803c5050004001c5004407460a000000340c10518042e900068204109644026500c040c50710030f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 110594154 1250 110592904 110592917
    0x30c1710050f060f0d05031c0e0703020108270607030c0f080106020d0f020a060e030c100501052d031b0f0f060d05071403042301020702010c02091504090602030109060501 75
    0x34070700c118048101410720f0340121418980e00400c0d80700c104030342e03004903004011030381c56000320380c18008801c1036400c585104c5418400c0005200100146107815aa4141c507121141e40d40d0708201044402c070381c070304800c3c0d40e06000150244100306010ba0780c080c2065940200b06200c045001a2044030b0514150702080090401009510b60100310321100e810b1515000910003101c400c101d15062081002400c164904840207641d150004014011054424161400300440d4030014048900074415240c201c014034144203c2c00485a03850343c000100d055140c0003d8650300080f0340341042c611000700c1500c0d4060085031f454a40242804503e1800b1164090820f64940c040341440c0100b4640383e1b00b540d00d6101040c9901c2c0100391202d00d2203125261551a883d140c200115481e18082c0c0e640d200300241c170840710381c204040c000ca0311565010784443c24503400b541e091050f0410000d00902014461100340b4609640c4c6020b04a02940142000768880d4103095070101284d13400d0713000c036050022 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 110595404 1250 110594154 110594161
    0x11515230715050c070c0608061201050a05040c081605040506040e0d030603061a010c11030a0b160305010e091906060801020a0309020f0604060206040602090f06030a0c020c150d0203040c030c171005 87
    0xa040b809010740340623190642880d2181000b050b03e40e4031b80800310655500706070030040f0900180e4081407103680a100844c1c46542d94002c01526840c540a080800c0c843c041814000381c14590000303a00400d01510000300c01c100c0581050400c00d11480d004000794884208105002c068098100700c510340b0140c000d159100e04c40003810071340340032034000e107007110000c0743d011240e6040c403100807080e07048060806513240071031804200820003c85000841c1c588400490700015420250307103c1e41c900c00041131900000c13800481030040c015021a00d0301d0722014040359181c000e00151680003019100455040e11601c100304100c004002100d0107800140810040f40c2c3d400a000d80e0040d82041d00166540c4030240812886100d28400e25008500001070140701c40c1d0581c456025105d1a41c265081480c0c03910803c20195403004608180e00c0051202071005c45046e030003142c1182c8100e040c41e4a556903a40d076410411070395809044400f0851050a008032021710640541c0031081400304820329 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 110596654 1250 110595404 110595413
    0x1020607020c0109090908070203030a091719020603060a0801060b09030f0a030206040f050f190204050f010b030105100221040515132102040e0708011515230715050c07 74
    0x70b07041e00c00c034045591a0315001b414404400110344241d03402505995032480080805881140309101d6444054501c00c4a5466030501150055103014442c2807545000742c540c0070020f09030030240c5096440a02007100040c00b04003449404028031505407141d8480c14084105070404201c0c0c1134071081c5400801814000070b902181c11179015a00c5440115407010a0400514100103545500801d2103030100c0c2410400000b100303403a80d01e10860307081c80203076120581c1043c0c1480070302c01d520300d80d02e007840103110604d0300c4d00300c07140d178012944100c480d030758410781d50844509009041a4100d00300000d0920150500e00e100981ca000c06504017807405000c01100b101d400b81900c00c6040001b0711031100f000b0034641801111036150001d00500c03035000c107445400d07241c012174441d1a05642c40c081c030700308032000901001c80c11140d40459841c0c2640d400d210076200b42c810b082d403280c110a030111418a84041d02da01411855024001468406032851490811218050594035040c0414010700c030015 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 110597904 1250 110596654 110596667
    0x1903050c040203040f0b0c03010f080307030c11010255020f150d0e060a0908090415080a050706030614031b01030209060c0309040c030c02060a0b0307032001020607020c01 75
    0x51405841c0140c2e80da0b180d00344a0001e014070070b00200145607071424488000c1514002e14103030b60101118010302c9a55030038050b664850444d004010420850303481d40455854140100d06d0300040c0103803003003140107200f201403036507000c603080f00910411614504e88101c0c9494540c1c51350b0959140420500203114560921914800024070400d01c9254040282c0c0f9105000340103d964a4981d41d26014144880741c00b030005c4000300405441a8030000d40e55001c14014810a45d81008000b0f18108201c01800084d11030380000d140e00441d8000000748e02502004145051340c0100702600849060402c0181950350340d51102102c02c21050003a40543c0d004184550140c201b0100400c50104a0300140c1c0603009103400d19910840c0410550b01140010004107141c000484c0d04014040d90488150103d40300000d07046c006078000c100241903004183d1201b402d140005040340e141303583d82c1d076030b02c00c840940000d01c0c012150488038500d40ea50301000002c2e00300c030749400504074050300400000e101 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 110599154 1250 110597904 110597923
    0x50a0c0c11060d0c020615041505040506180f04050606010c0308061311040603060816060801030b070e100504080d300906060806040b07050414040b1201060602010605190305 76
    0x920700050000090b42c1c2d940e000c039102850014020700070780380400300c0a51609007c69071040c100c01c0c070826505c104d2809104420360003a0384c002c0701c2c8000341080e060000402005090507000400340101c0c924000d214100c0512442040652001c036207424508142019405040f03503050112503200100000d4126040d9540a2001d032240030004510710301c001c1c041c00b00030f02c5400d21182c000501117440d5071b043d004882921505812a48142465070041d002500780c2e1068000280c8a01e0050000800620303889810501c2c1b40340c1809040c0510300003411020000744000c1c0840d0000500f0001c0e01004e0044983e5009103090400c0c10907014030302c1107404684c00200b02c3d0600703a0300007155460b0900d40c1c480f0304141d4101c1020481c07551501e1342c1d96902c19059130f040d9100003001001450b081e00c0f03001241c050b20481941c2d03040d20300310701e17052101a03e01080c0e81c2e680081200d03580f4440200901c25080100301c0c50340007103440391800e0180a51451442101d6040c144101804d001040001952150 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 110600404 1250 110599154 110599163
    0x60e0c0304051603030207050102010e06130210020a0b070504051002030307020a0602030711030f0406030509210904090602120105010e04090206070b0403090302130c0801052d010e180a050a0c0c 85
    0x80e60340d0346150840c1800800e5460560349031035180040305241d4009550070548400380c0003000070302c0060800d80e5468004941d01405843d140380c0310390044c00c0401f43e40c04100c4090045402441103a40c404c0d41c040c4c011120b09001034000700e01000140350140301d05443d000d0341d0010350b145041c0140025260000c003080580025000804503800901c1900c0281c005a00841582d84456900060700000e9000d44075400029040001280740c407200805d05480610854a00011030002c445500d10940c0144000b076a125907200100c1c0d000c1400c600041042c507180c3e003075100307066052400140c42804000f48090040303107010034510040c3c49a004680402d43c006880c200c00381c1c0e0313a05e8125101300f5150002500000701d100d40c00080c89071a044840d001e48941c880c0d0b04d2581c0c864060104002140324615000003030700c031101c0301c049480150400402010301d002d2072040d1940300800c03080280368070318031460115601008207506c0750348074242d04482c4000d020f100c040048000144107400c1c1803401341 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 110601654 1250 110600404 110600407
    0x60a0504020a1206050a0b09010b0a0c050304050d051f020a0507081b011404030f1b030e0109030204060803040306050105060708030118091e0506060409080412020105040801020328060e0c 82
    0x2000d540d41c56030b1400003821200c0840002905501d032010107004250780e074071009414036541842510704105264140c402c101182402c159925804903600c044445050b511070208000104081c3c03510301040000c940510020301c2200e4a180d0419410000c000d84501030501c144400001030b9030100c1191801600142d03115122529050195101041015050301a6280c5404502c0300c980041e00c01e84218086d44400c0d0007141c0140040c0c80c040d175612207032046078041203c8240062300880103091146030615050702c1c16500c130390105003240c0164200d00b459a00204080007000298054a800f42c40d0a0311500c0c2080070390303551001d207408103005040ca0340364810224440c040150b40000c1c000c0d5009814000b90080300321101c094840101402e5130395000c0e8200107120303410b02e07014841d182544400104d250900d022420750442080800481c1001420032002070682c500340040c40c0136030920070425090300f104c0b09001624050343c0d0041044203041810070440305a02002056002d1044140c56 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 110602904 1250 110601654 110601661
    0x708011214060a140708040203060703051302090405061b1309020c150f0610080601091a13030804090b0111030301031104020903010903031d0a0b0c0d060e01180f0905060a05 76
    0x40e11054a074507030710300345441944108040c41e03040b0340200e1030000007a03024010f90380711038600720362583c0101d4020f5010303480b05010440b240d1090380b1080d8010100c9506005ea200d0b154001840400c2c10396055440f5848141403102094103061081c0307081c0e55683d4201d1030100e0250700760b10b8209451081d41e0354039501280810702d81034284000311100181c1c0d02c1a0411303280880d00342c254040250b448a0161000407a40440203001d11101e0380035a005031100020145840035040c1400a200c0c590201c403c0280107060030803d01480c42006107118020301500c4908081031441115800c0800e5810400d140780440505080802101d055a030801b00458426120070003040203032082000194241d860145150181039055005200d0002c0400030103c2d0070752440f4100d6031310f801e40100a800e9071464000700d802d00c9440401403150314140350021444a46d2200310009030002607205440078111181d5071100140725101d805d4070007440d0401004400c2c09522000e551f501d004041107031556403078011 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 110604154 1250 110602904 110602913
    0x50f0c010306033809030a091505070b0403200a050c01050909010e060f0a0905191a0607060b06030f04030f170f0403030b03030d090605010f05062223031507080112 72
    0x1244c41c4450704e100310b0314681400003000d69668400740408001902c00c0070041500d590700320825610704096654035003005141d496a034102440540104c05005801302044441550003c040025070114005071503100c406040483c02c0c12100d0244604100c410042e80e1075907036582000605403074001c520a075aa6441002040c0f00082032107103142e004070350810000329101942c00c000d10503010340c041d5610400c4070300703500e00541305140040d40d00c188104a0b02c3c003039170601c080030f001001d0003214041150701451010070b50651099501d4119001c01c4001c02003495008020b00452a0383d1707107010140041949141d16600001400c02c511070b44892002c5400d151094200703160104000b02601d6a80c50915516401446540c2c0c04949150410000080900c14074803041c0884401400306864000040d40c42c100000d40611900c4100342e5410000c200840b00c0e181003400e810103412103556420200781094034007003240c800048580b103403200b000070413540103080c5811550380900b041c041d00e0300c6240 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 110605404 1250 110604154 110604233
    0x103170c0c090109020315010c05031e0409020304050c0a17060a090812090c040b030c090705220b07062403170d2f04030c0e04020f0409050f0c01030603 67
    0x507420381c060014000492280032070360045024103a281200f54110601800540f44903014201c00380c8076800600c0820300400e0902c18051032440a86840c52800e83c650442d03c042b42c2003a6000c0c3c4840c0d002a40f00320b11802d0201c0c94034064480000b094552403004034031661307140c1004012081032620360b5800c030108211182551150903181d1607001452a1849074141d80e65800c4209501c690b003018410a03030760074041850f80c95090f005e00b515604d40e88002099809903c091500e10080c1c407038540a00b80d0384103111480d800342c102864425903c6445080840c152a0075681e00e003285803e502404c07401944029103001240d034021546104070700d0201e0400114003134003440209683c200b0b965a26074203190350f040031100c0001c0f00d02d0030360000c8003103a01030035001d00d000040c407004910400344917030035000506582c4180300070040300d406801a0041002d0b10160003040300c1942c00b400040031441018000346004e00b000b8641000f01d180755466030201040702c4200f00c015110081c0403100c0705220b022 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 110606654 1250 110605404 110605423
    0xe07300305071a091c05030412260403080f06030303040b04080d06061106011502030f1e07030e0f040510050607020402090306070507060c03060b07080a02070905100512060103170c 79
    0x211124492103000d8100b09141c5045130031803524001c040b03001d440007120f0000448030115030741d2454199503c1d513481c59900e0340716500d14024030191113982c88400d400c0ba2000c4c488010100d4200906040a00d03000c3c003040c001401e06141c050000307040123019200002925030003034000c00100b8894540742410035540c40b034130b020010b00a041c4070022943e0303030704100d032012514071000032034200382ea2710030040390b04030080da19600068008220309101000071002070030640390034903e0614190000150103605074088401200801d43e00c0d5081c003000c2ca4101015402c3c032009403000c0c0058501100401a5440d25002e050302c40d500c041150030070344d2155410b41d00d01c90800fa0489a83e400c019070003800c0c94100c0700303085405504151070058498428000c43c0203d6001016403401c0000c9942ca40700242c1280c050030b0210b100e07100e80010300f0501030040c1c030f000e1043c64980480782410407040c06106007801c1c0c0700d020705600840c0104000f80300030401402c6001480165911540703540c00e90350400c116031 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 110607904 1250 110606654 110606663
    0x100f09030b090703110f210f03030a0b030c03010c08070507080702210d03020c0a1401090510061703030402060906130902030108011a030a02090624030a0e0730030507 73
    0x94200251100000740c5030041d40c5c0036003001c0c0c8590008504110010b8030785103109070003800e4034103105402c040000c4203032011100c0c441540e09010000c001a403558008032030286410fa00d40c03c0301110303820240000c018808050b0300900c1040c040b108060304141c800f0300140d00f005400582e1505000141c0b003903400e11341d0f000340a8290484201c01c000c1202914804185160140e104442c00050181c803c4401740d400e00030141a9648440d140e096030500d8410081c40c40703549590017040007407028420401c180245882c00107180e400d207500300c0300c410b601405101341680100301380300140e5218001e0384c0480d007040340e84c7c6640d1580d851201818089030b501c41042c460000c00003088a14040d00030100300c1c0c07200135403060404904410981c0d1820720080180d04440f1290124501d8203206440540c20b0790f9426131031400d0105904075500c40d9008541414217a551820f0450002d44180502d50003024100b840d84003040388a610809060100203644a1031400c138506003007094001c03810344040b690003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 110609154 1250 110607904 110607923
    0x71107030501051608010305120d0b0621010b0a080f040311060106050319111c0b030d0801050901090501080d03020903100204031a0a1b0c0203010e060709030c14100f0903 75
    0xd901c0c055010f460700355031050043e400e410341c83c0406442004c4a40c12250840300400c070440300301c40c80801e60f80c00100e00c00340b8641c0351071010200b03407901401405040ca0004003500c5802000c80070900d54041a0000c501100081003055800c175805900c02d0b030001104e0801c25400e48030f5160070303200d140068800e00c85601801e800080d4090b040009144240185400d40c44a20f00c0c076100031085802041205400702414411104e0b00a0341d000c14040c229001100041c0e80c83c82074002901c2c1050582d80940011140f80c014081424010039480c010441d4000500203541882e000b203031507040d001c010004155010455900b0b9603010072040b10480b8019404650341c5c0c4e03d03414003003480c002d40f852003120f9544200100d0320700d04803841040d1092260840700d0f03441105210046035840a03000d0241d0f810340d01d4401e03c03141d2910500c0301c6030040c0003a48807009107e26500e041510454280c1c000c50020500241d444829210b1032469031030000786240c08180000c040b101510040d41070380015041c450b9 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 110610404 1250 110609154 110609159
    0x1009080d0b0118030b0603210c010f11030c0306130e031b0d081303020a06061401170402030601090e0a0209010603140907050a03030807020f01060f1806140d020604170102030105040612020a060503071107 89
    0x1544401009d136180240d00030300507401d20516030400d5510016856040303e900700001f0b02c1710017a407000303160081c400800c50018640a107072218180c400e8035080301995040005c0d8010b42602281c15280d0f483d84600250518420200c000f501d6940014540c03a400080781b0702e44810103200b880689051540700404000c0c09495405000a007100141401c0c04290760481c3c0c000034000d0b5802c0d051059600800a2506a0a054900b00a810030042c2c03807260b0320a203640c110042e91441d03200c1d0f000c2c207155940022786682108202806100181451215400800003408030340c640154500a80c0e405003084001522080c4003203240820845c8484542c0d4a800004030b191004034050004070b4418112010740303140080030000031150f8621a1003c80103451040d2080c5051012078070a08a00042c40700e81800d0340c034000c400204110120160890f5800001403001d0700e401e11810300940803030781441c011a80e0a074041440d6030300c00d00031041409008000503250074030612003203007082e14003000e480c207003907 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 110611510 1106 110610404 110610463
    0x10e16031503150c03050c070c0302010c1419020405010b0406050d0c050705070311091b3c0304060e0d020706080402031009080d0b0118030b0603 64
    0x19407200000c080b60303901031440b20525540b02c0c0810f0a11003001c00804a03500200110b100d11014400300d40410076041019055990a08160008003034906000380400c0085171131506c1c6201d00754200c190b00000b0f03004502e459100351014403240e601c0d80c48900d1940142d024400010703105206500342130f1040c1d00103c10784151405c01074601141a02c0301410700c0403540095500c1d42286c00f05401d1810301c090102d034006102e14030210300740c00560381c00f005441201d440800010031641041040100303218420603000003c0c480c218040c50300c117070b03003030161700125070071f80e611482c2c02d00a030914800456101c0c050569a4058090305061020136284400301420a982520a1307444042c80f00249100c1c404009014079812034903411800a4082071b01c840c208100c0c10448880d41c1c0c94601120286090f05480e40803900300b14660b5280b010925002145500007290180303031030360340380c0d05 = true := by decide +kernel

theorem cover : BRFrame.Cov 110431654 110611510 := by
  have h0 := BRFrame.cov_init 110431654
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110431654 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 110431654 ≤ n) (h2 : n < 110611510) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
