-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4501
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:49:35.555206+00:00
-- url     : https://prove2.me/submissions/88267c3a-dca8-4804-a6ca-a1468689e1cc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 809352517 ≤ n < 809532374 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 809353767 1250 809352517 809352547
    0x3061401180905060c090d0203060c04051309051e031e03090f0606060d0510030f030c0c0e060d0303020c12070f0302010c030b0a03140a0b09100501050609330f040326 73
    0x251603139400910b100d92a80041c3c1c1c0032b04c8080e01c110001d034007281c0c8560a00043c0800182040d00b045100c074908400880854000034881c54001d140440d400b110982c1600360a0840c081c0c41d0729144103c0c450030048034161120f40c081d6105050b402c04a600c040851402c0b41c0d682c00003952070341d070442410408261815044e410040d40201260703449c0c2d0090356030740e0740c0800a03154154140e0000d1280907a210402505002d004003c02500300c6465942c201000084c19911440354014145580043c40b0380a1031303000c0c080b000d070781011803455a4807a803240c00d110702d03c0c001e0140118010751a01f20480a014001d21407101d01d070364094070182d5180d045990341d01030341c841d000c00702d6164407804900c0000980249001c5100b101c469014207030000e54111240c0c266036041e0060380c851517080c003036100fa40e2104541803c28140c00701500c00e590b5611601084440d070341480c0c4d5402c1000008240e8480c01c5008010f00c122071007442d094013201400040700280103080c09000c169242d00300040c1114020030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 809355017 1250 809353767 809353777
    0x3061b041a041a0304031b0302030405060a18030323030f06040b03030c0d030b041503021c0309120f0b15031027050d020c01050a02030d0c0903061401180905060c 71
    0x502415450b298a41d000f003a030815107290500800400042000f0030190302c480110302000003064010681001a9000b0303442e03014900a19000c1c1ea004184041d00c0f912900c0002e42c2000c8e280031051441d038403405c0040c5100700c100c08100c440180b46050300c81c443c401d002200d01c14154081c582440da1101010407025040c11403000d80e06200034402c0035074850f001d004500300c0741e6442c0c90002d02481d109050000391464072150800034055505d003000980c03111007001041d0141038062400d01d20441c54151010081074100c2c01546c914100c0650411416071104400b00303005001c2046c1540c0c0d520b04c103031b80c4030000c0c1e40c1da250550042c3d401c0f10b01d03210440c0c000c031500c2c000300b001074016040f10061140c828943d486041d00e065000303c01e1050710070b40500880c44149401e00c0c201d881c003a5101c001969a2045c041c20220450f52529402c1d421440f8180d16809154040d40c01d03c480382000c0d0006a0b052003e0141010b0101600d0841c002d00d4030768410303881c40b01d43c044081c011640c2c2c0d00c41c24480035000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 809356267 1250 809355017 809355059
    0x60618040b0c040b030703050615042607150e03011a21120c0a14010b0105030f0405010914060a0b0613063615090e010909061d07030203061b04 63
    0x3d101c003061401c42c10300a180b00c1c10306030790001580c2c609001000041d02c461204d040b0610070400081c04490011449041c480d1402e40b28a900d40c0c0002d07020034039021980d802000300704500c0d10030300c41840e070000100304418000c41c000d01c00107121003141000e07040354000a6a01102800344d031715010503038040389030189031b04e441500c00030700c21003601800300d500a0411a01d10f400140404040210306010409107018020003045010b568031300182c403520000d4903078800c00007590300041c100642500202d003550b6210a40d141002d070055811542c40c40103032449040c1604026a20f101030030114151940c1d603079842c460320905482c001041d508010045d9541c05640458070f0000008200d1003007010b144085c440b00f040d511454009580c62070b1a16a1003801004070907442001200e2885074618195210002c1c002941c0620323140c03850082c4583e184001d12030300d600d01c4034004400040f03201003c0364001c0e02514030551750b030028104860003650301341e14541d0341070000b80040ca4082104103d9048 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 809357517 1250 809356267 809356291
    0xb0a05030a05070905120a050114060d0201050d111206180403080a180c06020a0510110405220509010209040b0108040503041203140c0309010906030b0a2d1403060618040b 75
    0x140702d0740446c081c401c856096440750b9001d00e00c42002c00001344103a400389000305001108500f01a000146407074802e480181c100031000ca43e032894501e460f8062500408000c49465450748405901002e0441c11284244600046103410340320181c8444514400c030740c9a9211050b5548004900005110004a0a00c241039034064800002d440d181c0181c003621450b0000c00d0b60001038507203a86800154080042d210b42001d801c1c0e0215218070007a1816290100c5085229842400c8607240359400d0105110026041c401400304802041d8020401403005680a0008100b00300064070711881c00c0c1d600401d9984200001c0003c84000380702202603a100b850414024220309003095003a030003c0c01c880803180c000042e12001c42da0801d0203180244440d04080c08000b000b5000249090118840c00c448110310700c220751f10780303a00c1c3d5088400030645075214402003500c42980c0c00d50b40501c0c900d800d010307204440102d45203280072840000d00881000c0d0129003503030fa507138600302e07182c00281140764841 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 809358767 1250 809357517 809357519
    0x70506041b030f06050a0c02150103060c0516060b030c010e011b0c08030a090e01050d0b190e0a08040e01120215070f06090501050906010f0602032209020316090b0a05030a050709 78
    0xe003c2c5074441c00c118000c00c0080366504114110800b11044401c240b000d65100d0518004200c0040049504680e00b045000070540503076002a1110700c0b9482c1c100b0b06982c1030724172890801c42154007100204000390101c420140302e000054800c60004a1941d02107580751161980c07400d11b2010080001c1c2c401c0c1e006000280ea02d81e00603241da001040e00b840400d0065205200461003d0103d43c010541114450768098082d01c60001c2d080001d4800344002e00c203940082003c00c09500a0003100d84107100310b44400d509801c00c1aa6030f00140603c545865444000003000c110501d4101022038001741442d400203502850040b5aa200f0003049031803408100d00240401e50503c40c80d2282c0f8081e4001280c0c500d842c0011a08002050700700101101201c882800620781c004140c41e903010403000a500c45c155103c01041401682d5444210170328000001c01c80c0042e109000b11404080944a140750103855440c20789460042c444407600003201800014070709240c40c1c101c150412060300703100e040c1c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 809360017 1250 809358767 809358773
    0x31608040807180b2709070b031e0619051215042001020a0506150d060608030a020709020910200f0708120304050c0607031e08040314070506041b03 65
    0x50311661108040516880e0b80802608050040051340c020803203000e00c2e00412404011425181e4020060103212030f4400200d811208002030390180441e1003000f5101d03d8010281c50030346502a2a00ca500349598000c85c4c55400c00500d4011800380310b40c80c140c0154241410310150000b00556514184158070b0040d03c4840043c1080e030149014000e05152521150b8025148103210b80c600703030455200403980004604049110b0b604900711101072a16841500c4c0010190b60064201070111460080f00281d41c0b1400001802b50700c41355001d07561130700e986687d20000c901401a1080c0c01141c60054101c18922a0080c080001108440c2d00b060f05101c1c400d1503c0c8c034200703450307e160691044c2428001c81104112441c3e004461010303441c070798505544c41a07124004540e01e41d016500c0403912008041c0507040210a030b03081c0640c41400204140e50091a080060390281c0c082131600c907542d203180340328100b03d0360310913002401001c1d03036140c2c0e03a0303206040301501414807000e4204640c04400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 809361267 1250 809360017 809360023
    0x60b0708220305031e030402131104090218040c020d1d01030207080706090201030f1e1d10050f0703052401031d25051f090e01080d1e020316080408 65
    0x10b90300800003180c580d006484009411032081d0402500075206004200069960100d00e0030101210388010a403140f0b071060310544c1d40a81c0d0401042a800400da855501082e1030b480e4400d80021901030115101252044e1303101c121108036140080c10480b0351b42260307241c04203d401081d20600d0700516150050711041916080b8000455246407144800703429507070316004074900004c079441e08224004812050050400c1c2c560405021340362943c0d40380800100e10b4070810340d00800101079a014400348540780c6c00a00c8119002c20005696601140e0020701c40e11410303104030b2a954048000850510510025030f05109102d8105900d5103010040f1040c2540c0d4040e000d1000700086c04012582038500702604901d85d03030b07281c660001d920100801d41d03401c1018600d4038108d800840109941c8a0100c0741c41140d40c01c0181d4440700a800001e060750001580c200101042e690300a41d4803000b0310800080032245c55010046e8020710440c1d410304c480c44003400f520391185100d20300d440e0ba1983d050382 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 809362517 1250 809361267 809361269
    0xa0e100302030a270623090709180320070801020c0c09090c0303031f0308070c0510030c02120f0c0f0c010906110646060801060b070822 60
    0x40000c0c0c022050040c3c03550705004140c100c0d911031500b868400c3c030550802d40300c104135400190245842d80e201e07442c642032020312507960344191032440c8407526142800d140e940002c2d00c600c05400b454090459414542d281160100c0d42c0c2c140d031250062141b002042d044c0074510740c807110144c0100702001512440c01d2000b00f21030312085002e4864120401d08010204170001c00144441d001508040e05690b004400c8980c4108410317400701601c09540380d505c0c04040c0f00c3d04000d200410001d8414140140d2040c0700f4100c81c4122511007010004007012400e581010300c0b240d0141e03018079007542061101790013500f240c20140518a0408c0911000a4a0031500e510000d106410400b04040c080d60b004003c00c010742218100349d00c40010302246107a8603a0000d090520524403550411a80d039101041c120364a0512a45075515400c071901a80f03451426584030007145103400c000040211b410f0040b1000c45141c80707045400d044842d01c8030091a070180b4681e030000260b84041d03841c05182100004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 809363767 1250 809362517 809362549
    0x90418030f03110408071a041806030b06061323030304030b1510090605070221010506040b100e090901140106170a1e0e010f060308180d0b0c0a0e 64
    0x1107a41d880045000d0300f143c05286103141143e0302080103020728000041c4040803074601141400d400c40c10030401e0001c900481e0004030000700a1031000010410942115061364014130a21000c0c0c0c81c0d035030800403d4410702d1414007000400810422040c68007000085040502c0796402444c0c24a80b000241503901c41c0e04120f4074500300c00144074000f2000003c190622209031a54480940111805003810140d440781c03070200240090404115254288801c060f1800f0514412400c0d1084140a0181008580c41801a860320713040c030560703180502240381c000d40c0300e40340e98155040130740c10310011b90801020141da940d00d60081c00000d85850303c000b030003004d0301c1e41c6042c2195555105007003030250142c80d01c1815400c0064400d81515504400c0b0302c29070b0300b44000940700e00c00340102405080c030181d81001152500c3d02c0001803020030703002440b044030440d10048000302c01340200f10010880c048042c00f0502c1c01030008681d030215034010704000100d400d00c20142c1881000042026141171450b0f = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 809365017 1250 809363767 809363777
    0x20c0910050d08190302070b0411130f021b0c06040605030c040b03010609080d02061509070c1e140106060e0d05010b0901060c050f073506090a0c0b030c070809041803 73
    0x10301c4e070740120000742000710851803400703500d0440300e07858454201720082e00c06009198482403003541555240030f230200c0801e94030000c2c407420404010000080d0421078090503511409a0b9610000d00007186006605034010002410582005001c850603000100381d0b0b55020000c2001041014408001c1d50007080c50b591860919070601031454209001c02d2501c505540c020014040504068114241c640c0320a940407102035030754039000c07540088402c90142282010f00b44111124049410318407105004001009054800c1d582060880309680b0075080000c0004040c5000783c80c2400d1900c03046030182001082c01c206001c0081c1682100307030b200307001003070580b05440c04015081c4594280b401e2550f0243c0388183c54004000c2e11041c01c00d4500603030104c0c0000100b4220042c8a181c410443c0440c221907051030301240031070f42d5180040082d220030174803d40002d4112081d0003268072503446190801d080c40b40680c1c070390216420004825500c20f071202c1544d8110001c14900141090003a07480b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 809366267 1250 809365017 809365027
    0x2030912070519080a030c0201050909070e101e05070206120c0706050a020c0d20011814070f060507020406030209070c0c06050708221a030108060c0307020c0910050d08 74
    0x4200070f402580d48191001c5018100811058a0210f1040210380d0103007007905002d215440101d42d903204095501741c5c01142c1c141441f210b954400c00340704040c1025541603000c1541d01c038094889610302c03691060f0a01407003c5c049009480703403019000d01c51001d022941002c4619001d02c0e10650126001c24611a01040c00c0e01407045030b000b00e03500880551000c5140034001c42e40e050322900d0104a02061103644441a860b070341a02d140c61549020660080102c6c000d180b400701004840d55070b040d02d1810311207108140040001c40c24000311906001d0201d800e0b454010300342d45d142c00c02e0100381da105a55210002c05621100036003071050000380d6130000c1d10a107030700e0003401c03030015600141c0070008144016000101000700319000240e1000c14040300380c80450814001d1405c43c0c20050300c0066600d02480304464070b00180d4141c1c3c280d85e065a14540e1345003030360ba119000c12582c150050303000400d08880c078144001c071340341c022001c50600c8044640f52408120ba880304440212454180014 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 809367517 1250 809366267 809366269
    0x21f020307022413030504080f070302040b0609010801060c06090b150102210a03050c07050d050706050708061c2f150405010e060a02010e01050411040e12030106050a020309120705 79
    0x494810110442c2002c050070858596210704031540c0144410101c1c5513100c0c00360103040c01003060b50010080081100c24000e00800300d281c40d2181480101d01841c1094540c110901d0030406030ac01141c010317916001180c2c40c20364211040341c10094251910341d9500c01c02e5020030007000c0050721514100901c0b100024441000a107082d00704507490b8445802807103582c40d807118240031210203081d546030110380368854240c0030702140304014000f881840392107142088941c025000d00441809007100304180d5403040070076201e01d0b100310740c01544817445a498125003840e8800031a04030380196001d0f622401c409401c0c101d65410030056414400c502c0342c03203194524050100c0103614400b060090300301490640060040c13290046041d01c01c2001041ea044207034401d40c450000007c4da03100070701135410f090505001001590b9070050165080c051042ca07075502c006007a40c0042c500c412201c0c41c5a03e4000201d03203c0d00182c3c0d00400f140030401c51482d4a80c1d81e80340b0100c1008148000d00520ba250070 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 809368767 1250 809367517 809367523
    0x7050a0b0c2710030e0c060c0705030708010504020a08030f0403080a0c0b010b030a061410270b03061206090a03081b030408030a0c021c0e0607150501090c0e0916021f02030702 77
    0x2180a10802d420071102ea40700e541c000c5050300d8104c0d400e0710408d8039110500f4049040800541040e5018840c1c3c200010b00c0404c15041140941d000765440c10315180c440301000d840c2e101d68811074060100c01c10081000820700c10080043e40e0680c5032009039074142e5951010100300a07480700f51036031000300032300c04004003600c01c0d500208040304a000036034110340045090f04040e01002002e01c03000c0460000c131503600c82c82d9201111070f160842c03040152640d9000390396030015a41c0138042c24040b2124500703100001100e50080401000402e4580840e0781c084a1081c801031940b40300403500402e00300c0c581042c4010714052031103079041d2510b034a003a9800404031002d041e003d5086600c502402e611501c0040201000c4034180d1030b0211045e4000c80105880d481218401030121002060010811485900603816039081c032405010380519500110b88485030700b4800e562002101e0b020509121030f5010880b480d0072580107032104450010402030a07401808507031a411600041040075155042c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 809370017 1250 809368767 809368789
    0x5131d060f13030c11010908030d150e13020409020a090906050402030c030106180e15040f020f013018030513120b04080d09060606050c07090207050a0b0c27 69
    0x900042c86140c2c0321920014603600c0c445038050150581012566107036407007050f011020b082d822045998034589282c01c1401400c0d00c00100c40b10100e0340138003054458250710924045c2d522600002c8942807545c080000030043c400040761710905d43c05000900c600c4034041e800f5424026080058030b4a040e00502d4108801c49020b10310a1745030410a203c07400c0c228102c04090150b01c02c0005085080031034442c5052080445208080750341030030041000032421050035028400da4000c8906203044005641d1018000c0401d01c0c142d500c25840050450105241527040702c507014041801d4034041c2c41152000c00d0503500b0343c00070700c001440d601c42440644103040240011502104102900d07200d0715403151002e070008000400000359a000c9000700e82012910a401941c10000142c0d68400581550b0003116400c1d040c1c001c0503000200e5162920984168a8004016012041d801c0c1e0360010004001892000041010700c454070070800e803030320200c1500744440c031a1402c0d0b40224042244926103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 809371267 1250 809370017 809370031
    0x100609140103030c050a0221010f05010f27020714070609080a11010c0203070618120f030e1329040c0207060e0a08010e01050f01050d03080105131d060f 67
    0x600c03000398041810505140c1c11250545048100e840051400b5070401038070380c00c0650f001c02c0c0214a41c0044054420fa40c4a48903020020001401e041004130103449092003110304010203c8010032005840303035024820b1040c0869601a8003403000c0c0a2400c9801010042d10203281003a019100094200502000f070005814010001890823494540da82c461250003813588150174071081e2180d004042420a496000f01a603001d03607103460008000300001500b484481e41403610028204480c0d1800300c42c00340c0c20001188506109440c103940301004404941e40200b02e10745040e1702c88025220b58003a0141c0c0e14819003510810000000c070501410324220310491400206680d0030b0340000d031040440710340d400d207041d4100b190b8000070758401295000d0f80b143c4d420709020011402042d4412449400051810707201a600c41d8203002c141c254502000327000c02d0a400c0140080d18102811070550380100c403002c5070b403808000c482420b150200301451001e0b4082810b01c02c0d0b0f016040c000d2980310503 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 809372517 1250 809371267 809371271
    0x203040e01140f01090e04060207060207020603072703030212031f03050d0801230906060f0d0f0606020d020d18050a12060c1412040812040f0b070206042001020705040509100609 78
    0x1c11b00407031a000d80d0010b0002010030307500056103000c00055805540c0d41c13075001000f6540380e207007020000d07090500310024211b003249001042c54008415003018400c1d0703074044e80101084080d182141c1d038242d0000e0101707000320184020800404a95540680140d880340c0c000d07001d641a254805060800d040e0400c01e410340d6206400020340300144c5083c914250120307100e041c03548507080442c0c1795202c0c004050640c031a000943c204402002e030082042e1101c540020401a80d4440c000c80c9c9400800c103c0c00c0050b04503105070800c00c1c0c0b280b50400d05100f21400542c1e00c06540e200010b880c068540e001e012480503040070f2a0502c0343c0c0703100b400c48a54881c10407012148011650781e180e4801c24002c3c1c40c040c8145000700302407010800070b640000080c200801002d00741070802e05c10091510904940161031240080d568503c045641030051b0b5002c40c1030f14000c08451500e03540740903001c02c05c6046104020f8000b40c00d41d83c60080500800c84072019092a442900c0d00b10b0540e031064000b00c940c98 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 809373767 1250 809372517 809372519
    0xf1e030c03091508070c150f060512010204150c1b240c031b05031c051602030906090103241502010c09050a030201080612060115080f04021f0203040e01140f0109 71
    0x140c00c01c54082c5d011441d45801455074459140c845c044601080001f88080c0c603242103c100d800c510b6100d541940d03c22a0540d120982100106090340700328064680d5014039112400f40301d6024612000131244074500c281a500f854815a1400c507202d0f0b44445050128010140e094024a9201ba800b42d100e070700d0311010301c4050791800360003140d8407072141e020540d8813641c3d04140402481900c407400e12401e9071002c078084450941c00548415078025981540d0721004115080c000022141405400351031141095104c01c0190010804240040704c020780304803804084614082206015041c80740d6034010b0392003c403500900b1909450b842070b09100710040203000070381e102940f090840c0d0b0f0910b03000e1001e0340d480c0040b98034082d00c59106940340c07103101c2c00071443c0c4045603d001c1a044090b9540c2c8596901e002509141d81400d45000e0f410240814140c44408001c0d4900140105680112460240d4441e48880700d041c2c02d91085610004681610100340381c28042c0d11050082480c01d940e800b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 809375017 1250 809373767 809373809
    0xf060109050103050f011a130b1e070b0402040903030b190e070e13050703020426060a06120611160507050f04021207050d0f020a030c0311030c04030f1e030c0309 71
    0x85060086e0b218541c03070300c42e5540807504000c003101c4203041c40000700076100782e48096090390f40d001810922b501041610180340b00c2c6010805992400c2d030030201030045500c0d6502440010012600d080d1b08050301d452800303140b510740d00505000c0440c1e20000000040c54180742d14001c0c0750160045080000c100a40304403691601050120322144240008040c0c896070410750013880b581c1d204030080c0f023034420030389101d4000d035113030903d441808400e5845660341d80c2c40203011a03409008084414000d22a4000452003691001d44011102882e040c44c0407401142503190302c0848900700c80f1584000424061814004c4a2204101041e03a00b0350404103e8621140310000080030281042808260318011920704c0e041041490034040d411503840d42c400f800107000c0c3c1800c01c0706801203410000c241c4840100b001c220380c414035200c5440c07420b1900b541c2d00c90341351b100d01600544400c1006102d200d03441403a8250315007254403030b4840b07444c502102e140150a0122550205c10318000344108510a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 809376267 1250 809375017 809375041
    0x10090606050702010513050918190c03080306012106090f0e0a200a03060b2823030709020a020f0708060118020d0c0e0a0812070303150306050f06010905010305 70
    0x2441d42400c5c601d840d80d00f020000c501c3e01d400307580441d40c040f00350030600120130003c403041054903400741d09503441808400b560140c0074150001c010a000d903c00d0301080032030a180c0c051034100c1c00c14944030b8084084d010074205000c0c0d80b541c25800c00c0d903507103508000442880c8102984c04940010a111040c80042c0c01911003607043d5000c4c0091010b080ba809582e2013060074007580d85002420a461951a030a06d00003d0003c512264021075203404900501ca442c40070014842840302d0380079034070a06054540180388032100b083c101000740481d080419075414012400544410840142c9800001c0e030700030724102d0101201d071203c2e00440000d00681340c01088840c15561440804480809142e0f0303000c00030b02c21103400f010068904000520059440003032a01d20b6242180e52807040382d00e4a188640343c4050704041101244200b1150300042c2c001d800c10400c48114030b47e294000d594a403120020f8550403130350b41c40c801420034100280c0c0c2d03821240351805450203183c100b00c0340c0742c01100079803 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 809377517 1250 809376267 809376277
    0x1090b040b1518130e010510050f0d030f0c020303040e1f0311040b0d080a0c053a11060903040608250809031b030306030601081501060f0311030f1009060605 69
    0x35021080c1c1d82d48031181c0d00c0e0064114209901c8220412000d0902c580d1756000f001c0076110032584d064011030000b49450b000710342140c2e5210051900c03155039040d42c2c0585501c0000a401001c2c0108080b010001d43c0d000d00181000742050803220070756191040030307034400050704904060000f030102d9050000c640c0360300720030030010ba00340d0340041c02c0d1110900049400b5003603440207200400000301c2003501940f000c182030030b4034481e070f00301c405002070340000f0b4146185c604d044a581c8980303e084445400e2219142504141c558140b10640b504034201c0e40c0d04103802218042d8039a070000400304401b551007070025902c11511025415050422031900702600300c2d0300600c0041040d401d003c9890a6804d100302e510703640c60300100c0d200c440c20340e85446449400031105144203010300400055800704c0810445c0c4501c00440340c0c203201da800c20b5021745c1d01d0a50203424000b015030706c0d90200501d0391610019070003a0500315802d1660b240131a00560251941e8200c00302c05820620100480d80d040019a9 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 809378767 1250 809377517 809377537
    0x1030c06080c2b02040b0a031103060f0f0f09070504060e0f0109030b040c05100210050a05100513110a03021b0f1009060b03071202010206010e0709090207050f010501090b040b15 78
    0x11000c05400502e448500701d00c4070f2030300030880c0f00081c00900603403c000102128401d986040c014042948044440c43c001100d08c3c0303070030403010451201586007000301440403090050080584400840c08034076043e8084400c20302003030780043c052210b6a0400903140d0421011900d0018004d00680001d25240152000501036480c0380003080421000c041220f000c2e21025080701c0c0785105040000395109043c24408003194a000003103024000346002d000d10460050540b41400c901c1c002c24012103450034048408141c2e6030b460310160026048004101c45240c0340d9002da21250b401d110810f407802101204c45540d800200ca481380c1c1c0d01c011a90700441e003c1c4040c001111161800c114002e410040c120a9040c0030304480840c49903400043c80940724001e81c201c1701c1d00ea880e0100b54100c100156100e0300403581c2d102041260f45003940080c078074540310b642920004c20380c0c00c1a02e030940d5000e030000c402e850b80304c01c489040c50034144501d00001c10b0441c0d000100800342110003115100300c041c10 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 809380017 1250 809378767 809378797
    0x3051507021f1b1803080c12032809050c040c050c0604290106050403021306031a0a0c170105040c03090203031c110c0309010f140a050301030c06080c 66
    0x14540324028003902e03401c1d034005104624400c64110305040207262159002800c000d60914a0000380d03ca243e18051811646002020340390664543e8481a040b030300341e1328001c0c0f180b0b8032842c002184d014040d500440b010954108070b04107a62108084110155501c501c0794600071499000c20f0f40060307040003235801500d000865011280f0211080e100301c0c0314440c030b2780c45100248801c000704580c0782e0000712918074030801e450850038000c2d00010004e104140000b442800705002620740b1442039001411139000024041d41c0d60354907120f0b100c0741e15140001340c03100f00c02008a030610390300a400d010300e2246812800e0030030b40030380603858403810300916004503a43d11010000d01c0c080d90003042425001012a03448c0d404083c030711440000701450101000c2c2c00c0995514100000d842601c0c1203108520265080031703034000044400710b0003080c040702040160b106040c003990861000f001d030741d50a650f480342d50b9810f500704801d12203001d910400403c05c42c8020420394211b40b00503529002054041 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 809381267 1250 809380017 809380021
    0x10f02070b06190812120106030b010906120209040e0c091f120f05010510030c0b3402132304050a0b0907050a1410090605030c0d06030b091e0304030515 67
    0x141d410048600c0d005000c1c00d11891505d03140ba04404005016440c440710000980ba03a00c91904405864010365500d011070100d4000303022a50144000f000f0f001d414440c01814034403540001002e03200384002c5050b05410400c0e1000c405c0c1401a07015a120040c005490085d0000b40400c500a50080c0716800c0d82c540c034040c501c410440034482102c4c82c1d6401c100207014500b040300c0011149655031201321044d5025a500203034a10410058880444076103140b0408042c0449040d8001c81952a80a002144030800300b8016501c94240d1790340c000b09000000748880725a90300314440702901200c0c0740680c0b25041000300040c1c00180c9504015031103002005561101000e003032034420380c1e4000b1540301421380740200c0c1c45500c1f800c04020401c0100d030356030114410070106031014480d500480300040d1003003000400c2d15102034010008258124000182a641c0f030302c03000005041078919400036000324580101e42d00c1c0e4a8010140c58410001641c5003a255568041e90755080501480302a42ea03040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 809382517 1250 809381267 809381299
    0x2093f010e06010f05030d030903080a0e030c011103060a0b030609012705070f0f0e030a110f0d060b03010e060903070308070309020d0c170c061c090f050a05010f02070b06 75
    0x41e81c90500c4007421501c60356107030303003c040042003540a114040e101e603072800104503120340542c030758181d00b548903082551104200407001d0400b20343c1a030b190b4030082111500940c1c0910400d211484045100c40e01c138100303013041080d410b0081d80140302c3d400f4140140503a80e543c1000070350440790706e00590110400d0140c0c02c4c24088000c1c0300e4541c04a4544403c105207980c0080100075a00500c0d610402d0000c08058241c5a1184000009805601010310300c00040c0c0d04240e00c0030b920301c0041070200c1c58201003000a0b8100614241205d00301d842e19100841c0c1c0c01c0c24095000181500300c080d10440c6420603800d540e134000c66001070b0801405402191068ac000da0040034410740150010783c00f480d00d800c00d4000c0703004a110746685602c0c0401140b120342c10100391004610401010b40e46421040442d00004d100417040e03040c4981e9841c483c003000181d454048020051045029012803c0603080203821200c001e4082109030b40100040d4001400303620350a81e00080443d02030981002000c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 809383767 1250 809382517 809382521
    0x1003060506090f2e030b060a1e030f060b04140a050114130306020309030304020315071704050709020325050307080c0a0201091e0c050a0303082a0a0302093f01 70
    0x880c80c1440e5000e484110444e00903005040d044101644080c0b00081068062044501c10300500d0b01c005440ca504400c540000c0c0d0b107580391012002d14021810b1695001e001d412614a6441291800d000241c100008601054426803040007211091303d40d0f480d080000e0070b007451101440e403901000141e88051040309008070409980c10260864481c500404001d40d29842503a09074442d21606c000f5964440100c0180c0e413045031145d54054200f115038881d511400000303031045132540900c14002c21094444d10103035210381c00090300d074800a1440c0000d28803000002441608100c2e0420030050304e41c0d000911f40360009000440c45a880c202d120040f8010401c1241c018400d0001c407815900b40720700c44d54001c0215025030400494184d0705d5040040082c207921005010500303c2c00042c0020a4400300d156441105181d6000004103990612a6650017503604c3c3c0042503000c190814a41402c01c0c0c0d031030302d425003203c80700302041d44a05030001c98001501250600078180703590429484080d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 809385017 1250 809383767 809383789
    0x71a0f0f040f0311030c01021f020c0d05130602010b0307050607060b0904081b030403050a03200d0c11040b011d01020703020a0b0d1404030f0e060c0d02010b1003060506090f 76
    0xc2602545441c2c50380711603a1103a040c0e1000703581c181c501c802d954016140200703284041100503001003c2c003240380345500c4512900503501d00c0580f9400d110703031501507101b0300c030300104803200340e45880d918400841146142c0b402600110110ba01d444854505074500141c1d0000307507182281d1036a2105200c1c500b10780500401c409658001c0700520600c010041c032140a40703581584040d00b00300e100c00c4071070241c1d07a030b011b907101c06003d607071000c2d10b8540800e00030902d61100c1704052082035000d00400b0030852070f107008030300410002050104a802809400900d550308244d040380c0038880341180c400001c004400000040030594440c0055441d1070b802041071800030760f8040d201a5085546855580e40c54200f0000031290904003260f00807507800003000d0903c41d6905480780b422110b07104604860502c0d00300a203a800103001c004250380120b082060300c007a5855a4004170301240a40b003444013001d85031001034149400c0c03401c240141c0d500c80003074401010080d10081132030380c02c0030001242c142032 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 809386267 1250 809385017 809385037
    0x5100e01140d1506180c0806040f0204230925080705040f030f0215070c090f020904110315060c07181d060a0b01090b030601270906080f071a0f 63
    0x15a0100c2d0303090003864104c00c08640c2040400c142600e0445208019101043c0c0120000380706400050703140d2810fa444400380d0078410b0030041c106501e902481112040901a039188461401d03005015460013250141d408114903003645012901e04480142d0b159136066500d05001c2000c2c0003500340c0d445102594014a412443d19100a6503401c00c480207c003240c90690040c10790301e1320607120079912022078641d60f903c030304290300492a00500900514400c007003403952076000c01c201000e03640c0b90b000d104808110b007000160745c0e047c00d1000d001d50a004840542c080d24041c040075228440c00304000f0222a81c02a4540c42200c041031988001c040c02d80030f02c0c00c0c041c02c3c00c60002c500d507400200c01c4d20601c2d000300100800e441d180e0065448581600c9a14038a0404000058140d4030031360503070301400c00b20004103038a14400c010030300180c01280c015105c256501d01041100d180e0070481d03002e00c1108030300601400c50404c010162482403e507444a0706e903200203500001442c2d01ca0480d101908 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 809387517 1250 809386267 809386283
    0x31605010e1f09091b05160501090804060908010f0606120e0f030f04060206010e130210020a0b010305061009111213050d0801050103060b09030604150902040204140405100e01140d 79
    0x41c0e8001803c000640c0c0501410107141000030040c84a00800c040c041c032915488050419140c4034401c107400d080100116290754a80314101e00007414800600007400d01c0c2d49078184a681010611800c64494004100c2054248078081184541002c4100e09c80d000341030f0b0100702600c010440360300d007440400003151203200008035503034410400805041905d1469080d100c40f80d0b070301e50000388080c00685404206500d1820700400500d0a00204144007000d4019200d5107000351316030000f94030003603000352800c1d0003901c20400f4156501d049440030380700d00c0c40200300342035600304940700c107001e0286030396142c1184501054900001c80c9241003c158081c04480100070a218010a41ca01c00e01c28140800d0070200049141c42d007400a40d5011840038000b00000d546603140c0900c0d4120132962201c0c007681c0c5402420240c0c681f800148041d0480b024800e0b000c202c4c2800780021104028201030040b401c612040c414121054482411600c44110501c00010407a0010340b28a200d590018204c02e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 809388767 1250 809387517 809387569
    0x14070b0109021201061e0c06180f020901050d110f04110f0705010c080c070308070504050a080105010503060c070b0c0f0d0903020c0a0504060605040905150301020403150b031605010e 80
    0x10620b400401038503c00d50382c2c0c41500e9903604e0341924600d09201100c15a407024006405015110340400709120703000d04c1c0c01090442e00c2008030035003d810040c080e1001040d4513004400c3d4203040c00042d004010541c0e041180c4451a1101e0700d03903c01c4402164850351b0302c2800c10bc400d80d1503411103400c021620301c0301580d464001c00c55120591203050125810350800301a00c64003409442c240d841000814600b46c5171200e981d4046a0f0060024400e44c207114080c0b0000c031b20b50301e0780a00c100241000b40c00000f107950420b02014a0164010000002103000b0405c50380001c000c01c04180d00030600c5000f041c1c40e0380c1ca881c541d94560142240341d103591860b2030301c080b0a160780000d42603018501a100d4481d040d44230380512003556400d0051101158082004106000c000d0703004030740c0090610070304044503951500083c2a40c5c0180e0040d140703407059100600c10007083d4030481c00c2c90361048004045036409c1d44001d00c4402c030148070f1141844401070080700c9a44030034006070b000209646140f17040d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 809390017 1250 809388767 809388779
    0x40b0a0e0406081504110102030a0512070903170a0201061502031c060b03040803181b0d0f0b150108070302070c0b070201050702030f0106080d0e0a03170c03030a09030314041214070b01 81
    0x1300c141260151a14400082d1768076031940040101c5c0e8001e02c856039080c2c600003c8031444c9075143e501400900c10404c012030000b02084440c0c0080c81c0030240345100c86d41e510221600282540c2c542c0d0000501000904126526240c0000032a507510410340b001c01c14104000c0c1c07201c00180310580c000d00916100004005c1013015020046100322a05048600004008450710342d81b11002010480800e40100200d481440c0003110b4020080c40342d002c90b0044441583c5041101000740c070b40c3e100003140c0e44000e110542c2c00110a0ba44510b0500d0210305180c02d5840e41e41c1610014400c20300c41c244000340c64000e59100c0c2c03040b03803071040c0c0140c01c413400721804051080c000d2400d44602403c90140180f008003691144880844114004003003264807800d6454282440c0c1c20044031b161341c00402c010740603640f00d01303101441c415801c031080000c0303445890030043c0c02d032036503803039003041144418007003000284002548007443c0b411407820025981000884481c548101c0c400580210082e400000f10 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 809391267 1250 809390017 809390053
    0x30c07060210060b160615050d120206061815040906180201020c040b0307091d1c020606010804150914101e0501030201140f09151e040b0a0e040608 65
    0x142a54001c1000704540d60150f00b00d4501a0030b0707505885d204400d003080d01040181c0c00540c4805202c413588603605548500181c501c84410b602240e0b503030707081000565640e4061014952201c0181c8610b44070f101a43c40c00c51b519800105034503144003624050400c2e80c1c685500649015601207401c1000082c440041d04412034140790880c018404c01884603d0741c00c040c01a1032074034401030000c103001d504004181001e00366801d210f6031104154410700d658043d0400c41c58425034002d41003892005c1c40044001e081c1440184168103000c01c2e0707820302c070004261401000d880400010700040590b2603103403004d40f2000d952116109480b401c265500e10103000e130b101040400d55000112551625a43c944d0300b0b65509110190114581c2d014100103c1c90b550001e0649020641c03440340341100d0790300040c0d141e0f03121044006103031501061002024184149080040701e401ca01513061a04c0c1c03152401080c410402c00b20200706030900d01c00c0c059101c030382204020301141d1040d160202803100e81100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 809392517 1250 809391267 809391283
    0x6030f1504020f0f03090a0b1602071401120b01020c100315051009062105040305030f0901060807051504092a090e0a0908070203010603350403020d0302030c070602 72
    0x240200c05014100a0789014800c41d00400c598950f02130610440d6404100c190704010000826802203524a000082c02681c41a03c202c11f800300706511403600510003403402100b0340080c10100400c0e01800d0742c40ea00100d004045540c00d80c8003065114000004078140a40c41508030b42101280c010481c2c0a0341541000840300c0c00c0e800720346890341c1d8030f804201030100c0300b02c2444045801d005060100f00d01c20200c800e8002c02481d42c105184008107100c0d0200c0f042154164001040030041c042d031846060382c0b03583c100018000030301003103051030715240e142d8119214051181c4241221180d90307408403010b4500a2840c00d07802c002845481c003401840c0c011601c0903089510f502401c20104501030303c1d040058880405030880d443c2c0c0c034485200b0090211110596060800744402801a902409088040c521884040c0300c45d22162070505604500703105410140e115500c0b8201d80e09070301c0e0080c1c60440e501200e0071600740e4a5410142e00710300c582302c01040c0c203020358907000c9246500010050303 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 809393767 1250 809392517 809392531
    0xd12050316020712080a0908030c1501090e2a041812090e061507020306090703030806060a0203091302070c0f06180501020303130201030231080a020105031f030206030f 74
    0x101c8000c40e52000301c0c0c0702c010030700682440c04100c0c1c00704400700b41000c0140c4401d025034107180800d9911008085e00d90b030454070708207130b0784d0b1f120590300b01910b0948100140142039010041c172000007015140364660342400d20008008820b80100076442e902032104c0005034401400c10007000d80c4d0b141d20007003480b2681c0d2007600c0d00c1c0e8020151140042c805c008220440b0302104c0a8001900c59908006820034100e40c4100840c3c810300c08030002d0781e070070f01001c1d0150103003030001c0c01a07610398500a01040c2000300301c684130300303000c1c4a842d18079034012080b2030440000322070320403080400f0f29411000b4081c505c0d02030700240041c000031a0080320f1201c55020380341c02e40c40725402c3d002a6401065003a1050140d940180c2007440480e41b1181c01251044209105040140c1000d400e011511503c1e035900c555211f501d841b640c4000c15240c0030346000e80150403464040c02c200c039403a0700003030264800642101d03034003040610790000081d0359001c42d101459008140594034289031401c0d0400e040195028 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 809395017 1250 809393767 809393791
    0x9190602030f0f0408030a0c020a12050901020c22090807210806030c15033102041a011403100b0406080609090706080105100905030d03020429180d120503 68
    0x1044543c2c14a00c82c0c140300d290b0200030306180d0755a0030408006403030580a1002540724070030b504c00004010310304950402580d0381d1042d03152400c1d10b000914080c1401000c44c000e84160980059402009000b280510900980800c01c050701d031900c590644503030034029002450200503620400345141082c809040c095445e04141e07110002015240e5540f554050b0380844885c26a01c0e00251003405542d104240c50640022240e602d030140308007981070000c0764100456031207079204510300741c89814130142c42150799402d8048414006007056540d105034030014280032002401c4941031007009000b034502d0780b450700d80701d80d83c41001420a0900340c500b644101c3c1d588001644c07207240092403600320f4071309559204080e4a00343c01e0108214070f01c1d06000c2000604075000c030300c0c1c3d24200040455845144c1d00180c0d11460039003060085134100e580d00d12481c503286840a1901d00c41b009840165100110060006a42c4400185c0484540e180285a02580c201c10700581da0086c010354412920000300c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 809396267 1250 809395017 809395021
    0x15090114031c091e050d020906130f052a0f0903070b0d06090f0b030a140c18041703070804080a03241a0403150504140a05010903090b03061809190602030f 68
    0x305038400828001d081c0c112040641040c01741c0f80c00703236540340c1003403016005030500c100994070903082e1342481d58080c230260784030014007040810544c11503040c1600c4ea0000c40e020450424100583c0c8120101d421000d0300c00700300503102d03550901002d0020607100b5003641d603c0080105038405002035102d0055a1460440024418180390081810300e41c401005000242c005c0ea94203c04c001031142603ca19210702c040c0c0b40810f0311403001844242c0300d00111300001d440e2514110403aaa18a100d98846100900910030000d401291250700103510001041c2c8403420234904400401c09504124000400801141c07142c48040700c81c2825204009040001c654520307403900020702c26440000e11502c4000c1c030b140880707440c47d4011600281301e8214150084e0700e0001661030200000000e8501da5910506101010380142400f402494071542260030751030304400041034091404491380112040701b000440c1e00006001000d02c10107030110301c8590034060b0030188000c0d041118080740300c00c181c0c00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 809397517 1250 809396267 809396309
    0xb06041d090c040b030d0c06020408010c080906090d082208040605070312020a0c0807150903120c03110a120b03030a02030a030f020405061c090b0a0f0515090114031c09 74
    0x5884c0c2161016000b0040700b602000c049460000e881c0064411319030a100c0445c41c5002801072080440c0955600f0489081c1486254101080130340380c61000d40c030105401d080180c200d0600c3c4d60102100e44c1c0d2120641402d158007442811300c00c0c0083c0030000006000c01c91075000005028101c1c040d555070103142d1010102d0b44200c5c811042a840400c81320f11203030b0001504d050050010b2440380b9a0080e03000c00c1661002c0036100207200880100c1c40302420043e4440d038511400070012120703d0244040c400e500a400360078840c01d10000100048840c5542e02c1c01e205412291200310041c080b02d0307071050140350017901e98210070f500310006030521850224104080c000e58064480c020952858002d00051801e100403451841007107960300d80079103902091902900c2480385c1d90b1802c000c2030081035090f45200720b54000f0042ca04d018111400b40300d0f1500d8000071241505c2418000954400b48200020720b4291407003c1c2d09021410420520000c540c031010090880b14405030030001d2280c2d40c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 809398767 1250 809397517 809397521
    0x1e041a060a0f090b01120608010606080c180909010207050a03180f240c05012f03040f020609040b0603010b07060507050c03090118030b160f140702040b06041d090c04 73
    0x1104003030855003004014401c3d107441c0d901c00e48180005051040d100000d14416030151404c5512450282c0d6650000f004401e030402d0300c00b54846503003200c6510f46107600e8991003034810704082c918000d0312031400043c000502541202d640781d400c00101c40032a0b4807860010600d0015268800c1a42407c00c000141c40c40050700307520580704842d1901c503681042c0c8410414600d810143c4804102c003980844c8081103017031003201589100d0740c8d031003c01003925104542141c405c6510340d14902d40e0410400c0081401040040b6500b40e045032455990080040010040d0900740342d66680a00000000503c480c1400014010144038020500c160703903807280203039605d00410207031140300c0e002006500d0280d845510041c04007009a0b28988040d5100d44500c2c80c1000101c45210158000000c410701c510f810440070340c0544d61500c0c1030003404110098000660240000c001d0080340c42d806941034950303c2005031005041001001c000c1c450b641c40c0d000301c6880058036250514040e130304010615050034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 809400017 1250 809398767 809398769
    0xc120316082d030a06050907020c01030e010f0c120b0109030507060309150204090e0606030d09170a0219090b15040e0702070810150906030203151e041a060a 69
    0x91400c1100d44001615400002c0d8050300c1504081c1d000314006890707076075064000824061420040d5522481c2880b00700c8102c800b541c004d28854154001005003481e80080c4201400c0000c1c80e01041d8141004401800b600850800340d00c91401c000c00c03d6801503000640b00390441352400d09000b455294401514445950700015040740c214220600036240032744c002c60f11307451140d11071543c03140405096000301e07003190f081045996210703402810f00ca60200103603a000364045019048003c0a480c029141d00003e20a44030000c42140c10100107403001d000d003a403001e8010f00b42c1040c6210046021a51210074042d4414040c42c0882e41241824061007240c0c0c4181007000b154076090030800c410a103207030001e080d20114402e016011405078418418480180680080440d8142c0a0300841c0e140840f5600b202100300d152407070400250b0740010384071001480c2d44104c070406440e40c0e5a075810f00d10141ca030710a40035011009000400c000103189114003c031a05501034162149010003036036081d9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 809401267 1250 809400017 809400037
    0xc1214060603130506040309050316080606010c05070323120f030712090f230102160b0403090e0103210203091f020f160f0602070b030a0c0302040302120c1203 70
    0x40005640340c101080115004070b0801d14000c09000c099491070b14298045600f2000503094010030406424100191100c90200c941c2e890001400c0950141d0340b00300c014a201d040089400c2d00300140300c1c0c1800f6034000380d500407007400d170744c001e46020f411085054a1031456448c4120241184043e068005445505516020035851034039281d000f21185420141420311855940003402c001410313111602c0151882404c1c103c840d400a4580c1e11549200c102c040300c0c40e640108881e094410103000c401100075800024100c0c00e80f0b403801c040b241c803819600145e400003190303000441840f4030511260003c00b075400b9500718060008004076228020035000e250072007030101c088151622805815a8003800900c1140c1c10360350344039004c03407902d0700d10700c540c01c609112400284915560b107a00702005e0480b50005141c51803903c0400591480f00610130144103a440c0c4800c1019442501154020364009000c6002e00f680c0795406507c031206020054401d102d1030403610b00c5200080151408002 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 809402517 1250 809401267 809401301
    0x912070f0504091719030506100801090e030906070510050a1406040f1803030209030111030c040603151701020a020d030e19020d060e060103050d141b1f0c12 69
    0x116103018480a0003482c84100c03030010302c0c1c0040031650303010180685a00c04003a17000741c0745002014030142c2103a0020b03210900900000305030040031a04800b040b4112440b500d0f0002e03007030740346104440c294055040d60139481a00052810103008c0c000810b06c2e4110700d0803d00700490344071001c0e0002121801007210381c18809810014000d880c0c06e0b0711286001400f03a0020a00c05030400700c20905868100048011130380c041000c0c000707401c0034452001104265882289141400c00a847c42400345101d90410542c9031240340301003030b001c80c202000038810100d40362208820140468040e411003100000103114a07810181c40314800e0141c11400300341400070303110074041002c0d03a8005500b03011050340c0207900c81c4142c000007841072182d41e0428918a02a021075415450001d0420315001c0074607040000800411208144c1c4808840488140c2c1d0b09400482d0003207403000d1b081a140c4441d8450080301e44481d1301c51503100c1d40211001e010283c3e1104401c001d0340c108070341202d41d8020071901b440 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 809403767 1250 809402517 809402519
    0xc080a0c210b01020f010f09060e032a0c090a050403020105070903031e0504180e1209091602100c0201020c0c1801140d0b070e180417030a0618020912070f 68
    0x215075948400e6000b181841030b0340c0c0b1000d280c0da00038256480351603001486a910100c540622070700740f0402c0040c481e4500618a08075005d0700c49180041a0002c010544503d8100341e608803a08210540a0410146c890351551070311007280801010100e80036401744d401c050001d40002d100b80d500a00380c0c0ea00d0744520104003502c00044000300c0a4624500900c41c041001141030311010705228140015038202140078003031003142504210303a0800c2c11341c80070400d21150400350f4031a05640e170f000302003404200c980f44805000320300d084119420450042d2411942c60020f942c19002410000c15000891b110070070320205100d4007054401030241d0a03404c3c5001882580302405140e42009002401120319002c2c1d80c0b5241c5074003034242c0322a4042010a8404425414154600d03d02d0740880065506946441d48070400000c442c1d062210580030300000042000e4440da00000260446e090049807a02101502c08025802141e44900c03903400c46069030381e1010001044400e40e803110350007484032 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 809405017 1250 809403767 809403827
    0x30911030c010c06150e0a1505090c0d0902060f07030926030403140c031516090302180a290306010e040519020409020d0303020711030331090c080a0c 66
    0x2400d512101610005c104c0d880094407901c14032803d8000c0d203410300e0000304200801d0500100c42110350000c2d01500c108000c0010101c42c070800d80b46031501030040411301d10050301c0041c84600c0f641e0701c0040d850901082460606910001100075034903038400d550404e11041c0742c0303401c21100744524089660f20801c414000a01c4240080c110313400c440048401e4501c2410000782000d141c9802c565440e4280300800c0391a600d1008406101d540340d0420055860540e00460401600340c00003216403044080810380c3c001e15503102c2001000c04082440c502141c5c1e0030000c0440d600c07402c8240c880e1251100104030007505d162024080e40c3c2c81401054a0700d5082c0c11a1007560705100c1c1a644140e4803540480544c940701c110404403442540d0040e6501024903007120307070061080600740a0361051204417001c40c522013803403a0f44400030b003031805046459010b040082041d03401c010307020b5040c004a5481b41c0d0b0450303c42801400500c20a00c03941316044c408545040d042400c2003141100716042c0340e05 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 809406267 1250 809405017 809405021
    0x51503060c0a030e0a020a1508010f060e010c02010e153402010804140d0e04050a0606141c0e010606020607020312060d08120108330f09030d0507030911030c010c06 72
    0x84d00302a081d00c00100303ea400088500d8900c0d441400182c41c101500c00c905540030f00d015014014070200c001c0c0c1107042c80401001c03008002080c9050041120a5030f0640e802040034542100e8001c04c40041d008401d0031034103080d080b80c418045100880594080d0202405030110806c1404107501c0442c203c2d550011035000d080948261083c2000000c5075150344400d20038200202c034076807161031074424034a0038002111801030549180501c1c3c282c0501ca42544122000c6052035241d811540761000240c40200f604c408000020040740307170040004282c44190081c104546103a002c3d2000703a5a0008240c0c0c0740d2144440894103904242e0000d01d4900d0720150100751280940006402c2c62454544210704000a17000031485501210607404280c01d21501d40d4401d24070956286119650311582e60b030440c2020b01002d1441c4211000111703503100130819240e000302500c905100504200d500a03008000050317041c2c902c2c600014070103009050000c0d51101010043c0d5907040391511948600e40 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 809407517 1250 809406267 809406281
    0xc190302090c1308030a0c0b090604030f0305060f0301181b18200a0c0c1509050d14030a0906090b03060d0b060609150c01050703050708040609020f13051503060c0a03 73
    0xe24003000f050701250180007000680345c45280768486100c045568100041820b03801007080726a54004010480041c1d4004002c240345152030070040703915154100091054924005205e401d50b00c0c2046107408042c1d00700302c40301e03030601580c0348091310004402c0e0050110442d000b1000302010702d03008900196082e17403144040c0d1310242480301d4052001e0320080490f6200400160004003109802020301078000564002484002e025001d08000c484000d00410f810f07120b82842048101c100d141440103a40c51715840e010f600b0162075907140b24180c040e215942c80c0c061840044d0819401103004000d0008813800741800078101980d40b005c0c2c2e0344015842000808964000303d0522003601d003902c504610740c402c4415070009503114000c5104180c210f560090007001010304000c14822215040003000d50805c0d08414041005001030000c035089804c1c2d100e00740c2d0003602441e455441034190340d1080b8000d0400700b00c04100030780d0002c109944c1d102c4c01d41e050090440200301c02c1503068002e80c0042 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 809408767 1250 809407517 809407537
    0x90d120212040f020906010f022104120302031201080a11061e0c0705040f1b080703200405040f090507051c02030a050a1a0709030818120c190302090c 66
    0x35240070005088240c41c101c06503800c40d05a1603403146032003146480c45a05600c03080a2a040b40c05c0858664000d41e03410404000302c1c030541142c24054403400344001201c02402d02d4030320003c00600c0d945002956a031280248845040810001103071f2100046401101c1d03076000541ca6150007a0402040119445039903100801e040011707911034218803242c041e0030110325580140070789928040500c800d03540c2c26186403244038502142040c4440c601c10f82100001c5041c58400a19961448243c00a01c1801203048a5100139040000100c1c40ca900030416518142c03828410f00e41c0c240c4002c0b055400d9100d000b4210303001058180282d04000e214400207040d2040744d0000e1480303a401280c02d201b581c20040d03070640c204005107814045c50000d60386c058826401e985580d403130001e000900400490000425031980000c00c85060890074440910381c0f6070040c4010183e02c0790365040c84d80c0b1080040c105014004a0390b0441000024441150450360094104001e43d50381d461590f08691000300c0e51 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 809410017 1250 809408767 809408771
    0x4091a100e180c28051210090213060e10062105072d0e060406023a0f121103010504090606030f0605010302030c1005090d050f1f0b010305090d12 64
    0x2403c655901c1c4d040710801e248582d0074240d0b0201c0b1124110780451120740103140203c104c100c0c445801d8200103125603d212240c0000254156030f807000444101d4a0545401030744c0c00d10501099404e4800d48040c051841030243d08a07580d41d400c001c0e62900d280091100c00c082020380c0109034a4415000168840014034003e120b100e4817450f140d60281d070364104014107a440010503449a07810640a00c1d1180d0215426030a09140c03e41c02940c503103038541c115091175498021003240e0425110360301c0314502c00c40021030405144030001030180c80b140d03c4c4400003c80d01701c0d1050740e034643c230700c40d08405070080304800e882d50b800c0c101407101500503940f003120420b90ba2007000001c1003022003032910052090602099075455401010b10b0b1a802c01444e61080b81055002c0c1011a0882c0460301d4841054519030b07221801828000e00f0801085840784040c0244101303188510505400b500020016040c100f000d010b50b40b004400f29801191241800d03884550304045450180c2d80100415080183c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 809411267 1250 809410017 809410033
    0xd050c040f080618011506050a03060e04030c051203060d0311030c01151a0307080a0e0705060a03020a17010e0105150d020d0c02010b01230703090504091a100e18 71
    0x1400001c54107690040d12250001c0052000e442034196858044804900091182c4402802154941040c44c070412052042c00506800c009029400200c000c005094442000d407800e8200580303c0355000e03c0407601401441c0c00c03400c0d026903140649000f044003a01e1b1a00c02c011695056800201d80417003a0002d00c810701048a200400b4041e05902003019106c01000c0d514140c0d944080103840010801a41c8080c010044d2a0380c0c030254040c0d00028035500070034912240000181402c525400250308004001459800250150018181211f06642c0d05420004000414400250070300560202541000042251340703007595102290b512141e07503081c0340040c24902c0c0b408990040307842444903030302c0701e40400e0f91640a00c109120240203003003d4440c010340000c40c0c02800380f0a9110b000000000c40c5907414103110361041d00160601820400c80c91107039081195840c0c01400001748200d00f1000010103110320784404404071042100c444035280c03511038444110813020140d4010600c50501 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 809412517 1250 809411267 809411279
    0x61812030c180306060617040b06010309060207020a060914030a0206030604240e0708070809061b07020303130905013303140a1407030c02070311030a140d0305070f050d050c04 77
    0x70403a0003d40c4103400002d0401d1a050000d0f21000c0640046049500072608000100701c0140800d83e000e0f40920340090504040d1070288028026030b9006500442c0c135000108040d50080d4041c816144080c151018280001d410199900f40c070b40c40003504101d082c00400c465080680000460781c40e00004d83c401000d502074903c07a07261031765010080e1300701000305028096411400041c0c100c24503203010b61355031510030002c5540c1e04001e491085005da20504020040e81e000044d1249254000c040da90b8072000c0403000c070301c691854029000f410707140030700018040c800800d5004aa8400524510401203411a66400541810018001e048e25851564907841c50400098445d24403010001030301901c0442c06451004000d1940c41032500c0c008150803600c2d0006000d50440e0b901c21001ca4050081001203410854070403001052100c02e01880020890041030034400580ca0303545c10029a950340404548140352050400c1c0030400c01c020203600c105954100039880303007080d0421450156164 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 809413767 1250 809412517 809412557
    0x90711030a270e04030804020325031101030b0a0e090114161d150c030904050103030f0f02030403021c0609050313030c0506040302062502060d050103061812030c 71
    0x150040c00020502c4800c0c034601c2550a80700e150b001c20750011541070038104004804003000242000d42880720f0500050112740e410408551000c1503034040500c0c0a1b103072100c0240c046020b00044410603900411b0142e5944a80304071001c000c1c5c01800d03131100b0340c03030601254550300d030283c080340d0b2954039030351601c1001107408a014040c5c03101342c5195042005480c00200720741000f80540d1380c5048520f0054071070765036041d08100d406200040a07a9100c10380315525103184682601c09820900f040000030506400c000502d000c00d0300c6840e151680003051404076128812400000d500041261410201c4014141110030043c070410002540b000142c0352189140c004159031140425820780c11b00401200300001c4008040c00c3c2d42007400d20f82181d0000740d640c0148201801550034a0f0100000400d04106031210756030003030a00e0395552602c0ca804005082d09020039901141040003105107402550302d103140c1030350000c403204455010010100c0191036141c3d00e40d800c010b14030a00400741d518107 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 809415017 1250 809413767 809413777
    0xf1e0f0708060a03260c010c050304120305061c060e121b01050103050a0305032208070b0f07020d0e0105040b030c0301060818030a03090201051605070509180c09071103 74
    0x84008065686032a4100a10311200100518040c240140c010800504020303804e803205001091070716110b01c03400c0203455140c0a8213403840541c3d07007000b0310410500d07006001140103070700036070000c0ea00c004000e0041e002d580058814a4120710b0207502094154491032131542c144c0c2c40b410000c10031081301564140340c0820b010122080c420001902c3d500c00c16402c02c0c541600107810001d006961654807403e8980301c84030805011b0100c0040007820501d0610000c22860700340381072070414a440750502000e107400c580c17021a41c0411401c0858500480548514030840709940241340c0c82585050403100002010030450511600344402701d000311001d405148541800c02840340c49601d41503001700422400340041408a04400300404160008021204c40c9005410007058100d480e10040360316106250381c071417480c10001e80040812401180c1d240494204075003541d041d4503110a44001c03120100700f607030f40e2648454208942070401d103a24a80c04001424072010340080126550300790f500c4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 809416267 1250 809415017 809415031
    0x5070305040b12100906081e15040503090117010b0714071a22030819090b030702010e0609060108101d15040b01120209060f0d14010b1203120f1e 64
    0xc400c003085aa020785264030307030050044420a01c0700e1440d041f0482d484803205002c0715013490340d40400240445007080901074075880d03845950401e14050034003646175081803200030f00250b6082082106042840340060607240380a001a250518070b46d070f004801c0c00000b110040c140145140012403103021446451044c89194015949845816600c3d40c02c0c10419203000d0b01c103070418024008130712014140e6158210211101d950301c030040340141c4a55290303901c500110384000003000141c56064104402c0d901d070442c115015501c0b002e8501e0f03200c403802d000d070001039440070359840c01030141a0008203101044804548a801300000480e042001c2c800682d5001c030f40c00c00600c400c0080e0b8400c928014a40c00300005802142903000514030355000d00060310403c5200300c883c0c001d41c0d40c00b1000602e00e0348824120030407003100040b58044c2c200c554200c1d1141c80003e401e14502da070003004550f04141c0a09126145584a01010b051001c000d0030200c004900c041c82d00170141d002030491802032034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 809417517 1250 809416267 809416297
    0x50c0a03050c04150507030201140a090b07140a030207061b1110051b072f03010e0f07060309051f06091b090e0c07020901030b0603060f01140105070305040b 69
    0x22418102030255500a80624200c440801040046125400b4504000a0149411680c0d4521800d08a02415158040001c0c21850740b0a00203124041d500c0003072014403035030000707015607038414043e2140e510211040e42a40380400030507102c207101c0d034000c0c44240c1c0708480005044070680061b40e00402d40b1800440850301511400d040e01c00c0401c807000c0b0708c2200c0b410511091618005000d0607602c062001e08000344045290b03020001404441da02c2401200d1441c503001c5681c064400c851400318422500952070100820b110040c00304038403086511450003081c20600e003800480040c0071100080d211400303103c1c524200003801045540070802051340200c1c08070700b03101d201d200b100e0940324443e07507000d02c1c0c441c06030079550440398120842d2880341c2c4400c1d965032100074141d818811060000c4d8080841d0001108200418194038010302081d000c0340c4455407141d0081c06014801e01a0703241c01803e0000841e502d41c8140c0051400c5171080c1743c800e0402ea92401e00030000c0e000b0070900c2c11010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 809418767 1250 809417517 809417527
    0xa060e0f07080f07210608010e0c0a05040c080624070b0a0b01051207032c0a17070b2e12020f01030c0e010302071110080106110703020f010305040203010e01050c 71
    0x1648402c0305600102408200c480500308940050510031205810541490000002080741c40165020100600c0300000900c6400302502c52280c4900c840003020344641d1058902107814101407280e039031860710301c0e1164107180c0c0320700042206150781c0030740c0da030b60108006000929045440c0007a1030040d10940c0c04009900b0071000c0d0301e050350113011038ac40c10040c09018401d904003840094a030401810301b0001038a551122175000e1260811030810004019041e50701d000c20340000385903a41d980a8078000005100c451000c200394810040003418070080c03c03021401d0f9480455003480c8c45500c1403840c946c01c68610900b0206140140c2c070000188080303004081c250b09000072241410507007440c00700324031110180003400b42c540c0d11654a041650100f0100c0410402c581851706038900100364040c144100300c0000c01c04102402010000350203108098800e500000f241c03415654001d214403c80c18080c0e00460003014024000e0740c4c15900c4000d590071540082c80398602500c40d81c2c420740d43c5c0d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 809420017 1250 809418767 809418781
    0xa0609021c080414091b0a140a0c0b0c0c150c090a0f080d0e2b060204032105040b0a030b041811030c0a050d0308091011040302100807090e0a060e0f 65
    0xb1104c1c259190140c1005c0040001c1502e40c2e074020628124001320f101e44074a5058022076022000455103000141c000403a21000c0f6001050004142e1168003042003507035918aa0721028082c98403207805035072000d2a045006a0922000741d4003001d181c289508214001c0d0000301269070070f45c07108011022500050014841c10701c40c0d0b2440c070080782081c6d4811020640419140c0c4041c80da601d908140061800d11030080441032001c4442e080341040d521181c80381090300f44050303d04010308241050350400c00074030380520151070444141000150070500316a500b175003e8032088004540c49942e59040704406124094102c0c90a0b006001c0441600e208c14145480c01c12004101e501c03030311300b4000821240d40da5510503105940d05142c01000b13510740c40704140c0b628800c4401040720340c2c14480c504181d0521030000c1c1048078001c4481c130440307014906098541920684880001644000c0c040c8281c6511940c107941058071000c00141255603804000fa926005540b03003199104000d0502c030341 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 809421267 1250 809420017 809420039
    0x140604020f1306031406100804020907020708010213140306090a030503131e0c051c0609020102010b03030c01090b0124031d100204091a100e040f0507020c09180a0609021c0804 77
    0x12061b0103a403480c40002480f6005410010300400085c4918140000110014400c1c0801002030401034025901c1e807001c0280300105017041d0050080d003098200c03124900d442c0006505000348060809444d00308030702d450441343e903800200080322086409080200290010f1041c0220707001181d211003246100d4581102102c00d2603114600c25180034010890b80680009101ca415600c0b030400100071540380f0043c0e0160442d01100c87e80350102003200350903107034190040c002c014400d0b91611020f03a200c9803504142c210450403182e01d40b012000d078034003040c06a400300454448994240d4403e4010911441c540090303008218203003031b0046070801210b001801a20820300e480d80190a814a8071030200700c1c1168403684000c1003040010340d407200e5484036400000da176035046405000c14603061074040d590f0a0030b5549540a4482c1800084609074015240c0180d41483d00151000c034809840b03078806042e0300070050307074000702c0c8400031450b00c0700c106402100248540380841d1940d18100302501 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 809422517 1250 809421267 809421271
    0xb060c011b090f120501090c0f09060911030708070905060a050a0e0411161a13031e0918230105031507020a06110c0a0803060f0301140604020f13060314 67
    0x244015680c0a01c00c1d078542a0b90041507404403044400300b4444d6042550141500d01000340c03040103490400f24407044180580c0701600c800003410320407259203803000b0007110703c00c5200d00c01d540000d201090380c00b4810b040554004e1094600014503d4854001a840340e0080c0c800e40c01259000507010880e40d001074510f00100400c950801860782800f50b07000442c4240c0588035284642c18003083d01300890b04103090301031900c5005c402d94030700e858080c0000728034050750160040341c40e42e010810b00740603800c032a1558511035564800c845160803001d6207003400c0c800c492844da50300c03404815148800c09003c05603011446150310001d500d0002410306103070340301d51303015550f900040c1000719507500080d101d0788043c1e110200190340081d01d004011540101c0c20604d500c0d0042903046414014003502540c00b0708001c440c6801c01c4103240c01003500325401d09140c0f5180e81201c4001452928165001c2c00141c1080c402c03592600c90901c521801d100c81a0300034001003a138904010440121040030b00e6 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 809423767 1250 809422517 809422571
    0x40203100c02011a12100b01050c03270603060f060307051b06011a0703080c07080702130b0f041e15030b04030908010507090501020303062115190605180a0b060c01 72
    0x2c0010540754180581b1080c0000501c0c062940b91120b02000b64440c004072002030042c40b054039150b4810380c901211070303602101254403031544c458204900d40b07010b80c02c82e07004600040c50043d1081151041c4045070304020404000d106050162020f1a44200c082001400b0701c2805040a036042108003c0c1d2014a01c240a10300300045c000400003d80003001140c000800e5141e01e600c400c00782c07516110510650800075004070b81d60800280c1d44495401c44107a0381400c680e1007190044c0c06081c04215003049a5580b10f607c0005408440d0b414103901c083c851810315011800c6070317a2039072100e030b071b40040540d4224000380d186503042040d43d100707119241c4c2010f0305140041d03001d80b41c000000e650303010141609209486400c62148000004003c2e000700e50b03104030695000c8981c40440568451080341c1511602d003030304052400d400c1c00e0740b10304419100d00426030040182030f2036280403070744030060206400301d94601e00345043e540d07950003600c04204d070000003048141c002d0031041c1003e0414a011 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 809425017 1250 809423767 809423779
    0xf0308090a0608130314090a080d2a0f0602090301090c17030702090403080711070b0711040219080411130f0b0f1c0606090f06081203041703040203100c02011a 70
    0xc06012582d0340400341d1400c0d011b10345890300f181180002540c0340320b4002e6043d0b00c02c1e010400020316000101e814403e00d5110344442200750b4861407000c0900c11051140030412100c5202040024510140100260f01800d001420700c0350900209007100d18043c0c040d91800e210440400400000d14440c100070320703a01d07026508203522903022828100f006417008007400380740000a000280f103908051f11840c283d5040b01c2c04d40b6a1140311401d80d602c89a429180380078041c071800c41a06090080b2249103465a01d8103525854840d4100d030302c2c1d0405041241c540c00c12003804c03100d5940700325035031081606d103407800a4400d9440401908070381c40910014080c0802d00c61300c2403250b40303010580382654510100c0d0b04548069207031240090405030000c00c4482d1904a46074420802c6612920a9030f01d001d00f00c905400c946581c0c840c46002c203c80042ca00d41a03403800c100906407200185402c5840034048035161400706600a003512809000c140050f95196420b41103540d070361100c1c4d00c011500740c0346 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 809426267 1250 809425017 809425021
    0xc0309151803050c0a0b07180b030f0612150c0a03050a090b0c13030c080d021e060402130618050a0f090b0a0c110a080c07060e061c060f0308090a0608 66
    0x30000c01d403540380e000e400d01c580450800703807000b02800039a05140e4041a040681d00d000800600300038078030020400101032401c80403440c04400b1084078002e04954403050703407da031043c08004418000710140540f501034124180c02c800107040181e806000b25094158450100030340040031510001c0401031500e04000e0705d0804603490116445e003240701e032611035a40300d5070520119115000c9520082c640045440700140c1c00c240400d84400101d401e6083c7c0d130f0f521240300c0140d544076010a5640945420060101d001450040754600001080840228002e13a0b40d100c1d9907038504040142e078000303e03182c50400900d0115481196010f6040010400109541d601d80100040740242148051656800d5025085001c2d41d100064081e0340401c4030348904507460721200c56042044041060700ca040e902040c1e00c2d0050b41c07005000301d0080d0440b801c00b02016100d40c9a80d01c0d4240d2607001ca942c4080100702410303da09641d0195004103103481c2d0317580c0c0040a0004020480d80310104001b400b1003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 809427517 1250 809426267 809426291
    0x61404090213150f030503041401020c0108010b070201020a08030703050403180f0e04140f030c240f040c0e150108130305040524070c060806030d0906050c010f0c030915 74
    0x2c24000300a003501c20018090400000c041400b084581101e04660401a0b00004100e0008014020b03120001041c220034410700005a80c0d40d0302c0d4411481c0815442001400103c420380b016000c20b41c01481110500302050b10f5007160f0364010b650710000203403500c08110a040e00010710058001412612200107446c12070340001c018500d0084030f5000c1800c10114040c000b0740119100311244a00c02d45812010007138060b5900e40c007114404595000b20007800894120032032403000b025140c54640010790f0744040c2480d41d00c0000400803a480900781c1400307d810001d12070014450382c0040304c10202d44d800507001600100d40182004210440c41c0502e80c0081d0b03106055404070b42046d00c0c0e50311300800d80c11452003c6030400289402143d40803c1d40414080908802c02c11103c807070f00c4820321a180c040516803a0b1030740540a034081400440100f02140c4100e009224000720000000340a200c030b185944141e80c4215a1030001940390218101882804c00580f0307010203400908124900180b6 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 809428767 1250 809427517 809427529
    0x20d090f1415060d030215010801050f010e010302030d0507260a0215060d260a2a020d02010806010e09011d070504082109060d0501082a0f0d050703060614040902 71
    0x10700780350240c0c1d13040140b0420180208102c244d0000105480041e56844002c5180240700403114242c50b84960800010050100c032440b5060740d40203000740140c010b2066058031258401002216130613056924000c07803807800e41d40340c0420100041070b20394580d40d4800003450301e8403d02000c004c20180f8028054640c0e2a4a1000344d5079038444040202d60400c08106115142421940c4060400c0002d40c2d110603988500c0b00901008501e014041405e000341c0356282da6100380354029000346449100002541c05840394550009052400c405c414210401090b48100281d01020b1000385501751b01c0b506501e070348041d07980040145815410300d480c2880440d50b40c2600c030585840d18215915420890703100e1400c807010820090b00c21984c4130180c40e1100c004060908c903200c0507003c1d54007080a04600c40714800c0d0700045009400314080c40fa00c0820030700e0400e60340c0c0954801040724520303000450902c42000258000c001c0003400504d0b080000002070314007014288107615298543c0010b030b8a007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 809430017 1250 809428767 809428771
    0x60f030d020a110114030c210708130611040902070203190305040306091a041203150617060409060c08090106080303250c0606090b030c12060601080901020d090f1415 73
    0x103681c3e00d1640f80820068840400c1014914058440001003003550340300fa100501e020500e94200d80107004206600000c0540b00b40d4506000403c00004a103450f4502c400302945a8083e000005020418a50510096200b6404081855000704800e0190318091100c4418002c0c031844100c9007030220381e4010020b06c5180030003003000350b803080d03610240427501250000d2050107045080090805040c0398010b4000d1481080009003001001000074a280001d00100e43c82c07503c1e441c4600e04100842002210024822034015070348084140101c1c0c994000c40600c1c041d1520b80700444d080c2502d1481c01c1d607086030003030311443c2d01c10001c1c0800340e4141100b021a03502480505030b00c021003000110744e810390031100501151b042840114280805510400781944214201d603541c1b02441c0c00d000c0444010100e1106075000400051060350040c04041c0e806201200018600b1510081090440350018000e80d00080c0520760f203400c10403010b01680000311044000c1143d98441035501140b4000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 809431267 1250 809430017 809430023
    0x31a06160f050c0d0b060316150f02120708090a0e0f060609011106040507061206031106070804031a0a050f0f010302012a0b09061008030403081c020d05060f030d020a 73
    0x1422454100340b00b024000c5003c44240100b9000040006040003504800280c805c24402c1c0240b01d0b089613041503806401c42100d0136a46c1e440300c1d0f150148001d03a0401400f00311201075000da11240103a500500d401083c20710301ca002001d880e400303e81c05100b40682c582c0c00640d541c2d01180c081c050f01004a1144175070202c011249160394000810040340c5051110130340c0c60172032081d0014001040804281e16003030741c01517551248903c00d0b804950040e900c0503c00900005407012503500541804001811401c6c0a1080c0720714096403641c400072056102e40f90807d82c0049002841862015800b5580e0040e021060341250f40c149581c401006600c10b2000a040c45003110701c5110b81417100c46d14101805200d240014225000d003403407002b9200c2111542e10b40c0c0103000004841d030041143c07080039210088011820141503030b030360305201d40c0000891a400d9414000d404452030150009001072030300180c01080310b003080c10a011004141a506500ca60081d5401c241115400200014100d030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 809432517 1250 809431267 809431283
    0x1171209090a06120b07030e01111603140c010f0f092013020c060108150705040326070818040204180f020702030304232202071a0106031a0616 63
    0x15144103602c020101c590008107844c86003440f040030301c0031000b2090b10528150b1000e00031541c0b01c6c000c0c5400c0342d62041e0f5200703240d5014031000b00951307248021404224881d00301410743e10204e052040294000c08440052603449180d21101d541035070050007010062400e05109425131560ba408041c6010842c843c0391081010007034411303a40d9007000300c807210140d04046540e401000c9516450344400d000b605043d1103101c00c07156101590500d498460480365507101e003044d0866690601d030b44445240582c52241c24894403004d1176a540c01040c02d20b201e419200d81d01c14071258203804070321444620900c104c1c4188010814442c0c80c0341610b8408800321800104648a0382c2d00c44002c1c01502d4010390580f10101e00420800f4903104801103c1d506611a044515407050801626541c0c00f2544900040c04581161190159801502c1900d100c1c6244228201000c03d031407281c41c0c000d9110900083e01c900c00c0c4a04109174110341d51017804141d8110707180c0340060b07203042c65101740254000c2c501c3c1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 809433767 1250 809432517 809432521
    0x1020f0906071a0c070b13020105031807181d0d050a03090c0306090f051005040305040e0402010e0907030b011b05070e1f0801021207020303060102070515120901050117120909 77
    0x8140f5200401408000d0768600c11203090001c2d01d81c10b2908030740800c41d4800780c41004260521415140e149480703605035100c61450b40c40120b2980041c208562640192003071800200d50110b003c0090044807103904400180d4991004030030b201218440310100c02a0000e282c1c0c1b0038494dd0060485a52004504010844080c103103031410005030300d83e0001e400d01d4609048c040804c460808051000d07030080040303d48981d114100c10040351015580103020030000c00c001c1041c4130916213003d900c00c0c0141403202d80c1e1303408000815a07882c0d0440340c20f00041d43e60b240b00403246d030308070917080720903490080340c240181c1580d030b01d2941d41c0c80c0c40d0143d0040c00a00c10002081c035001952620360240003140ca90807140d5544600034041d4208080c0c2d804a86003d00c0007410040c400401e5078400d410507401040c40700d251801b808440096000c070b107501072a08210541c0f40d2005144214040c00f4107600015466240c682d002d162501c1e688800070040d0407201d0061010340c100c074203464001c10110f41002e056 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 809435017 1250 809433767 809433773
    0x1120b0a03231603020103110f160807050d08010302010216081b040b100905030601050d121d030d08100b0304120806011b050102030f16091202120f0d030c0201020f090607 75
    0x30001085000b0228455103003a504055003078090071080764800e0300c05000501d103422607500c1c81d005541c661001510140492060381c01c000340c0c0110010f000d0010a0300d000d609444140c103007071440384100041040382004100b15641004003180c00088000002082414450720641b60b950303146210031490360203500d1805a0b82d4030f40c0520303400c000050a5075151001d11102400c04034091240038801c0c0621000000d03181420000d428006a00c07456440800003010801e50f0410b9604000588164030072800e200f1580b0201b1041c00300d4112a20380f40001d00e00111000000300060300100032824092003800300040b46091400b40300c80b11420125001e03070301c1d9801210002c04810341603600400c6d026100e402e104040d4011401885003a042a0f143e079a0007602d15014012509103600080aa035410404403602018106101c1d100600c4075115006810000340303841d40c8030250850540243e050700c20342c960580304800b01d1412600080d070802010240390301c030502032440085d016000c009680ea0070 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 809436267 1250 809435017 809435063
    0x306180613150509013816260909060d051908070c03150c36051009080f071514070615140609090711120703030b01120b0a03 55
    0x50840644441c14940e5034003070072100340782c24018450b0000464132600c0715030303103c0000d001001c1d0034040080380f407e005607a5488640b85001d4050b504084400440c4500e5441d61000740144c0380543c0c3c08980394001c00041000381c000141a40c0d07c17034003607603103044001200456200140d0035500c0c04804084241d082c801d880340304901d00200354455803d0044200300c0052211a0302082c411000c00c407a00c19803030280e40344510854100e9504003200c107100e0300d40c0340d551075081400d0181450041305070765400c081811b0182c07408000d40410740122041c81400e00401510031407810100081002030700d08010440d0030b84990320340070104200407841004007021001100e03011a400b40003006070b8280c0c0c600f07450380c131007007070081026000020301c80040918040e81900d1100e48000d03c03070340050b15008000c0d0f5a0b401c80c061499818060070f206042c41c1100440a002e262b4000c2e01d001c00c0b105000000104100d00c02c0c04c0c400020b628100b44d03040c40c0d448554030002921362110001c8003085588062042e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 809437517 1250 809436267 809436269
    0xf0c0b1803041706010905090a02130506030c0d2027130f0b040201020601080d090b03060a0f060210050a05090607080a020c0109050c0406060908030a0c0323030618061315 75
    0x3651509030201c0b83d00c150030014406049424801041105c1d031070304140180c442c45402c101a5100441c4002c0360100c0207a80e10881d0086801005c40b02c541c10a2808100300305001c60040e680204074412002c00310715140420b00280000316080c00b840b050440c810b1040c00c0a1040b010901c9000900007100884800003408880750000001e465510321498074809903041110103c0c0140a000000100c1000000d002c1c2e041b5699626105511400c210100b405904010000c641c81102071000003610740601c3c8236900a00b00d00c0c3d004e8030b034820076000c6a0040d2000640001c000b81c0c5020100702c10684003240554204050f403074080116241d5070a2540030703029280200c1019481d0080100400c00c00203100440d03142d054606020040d40c41d074082d82d5208082c49915450f4000f0850006201c0c412045400703110310a0500c4048100185081202c151200385002d030b41034000000c0c0901807030110959819024020488081c9181c00f10210300503103210341c03110107003d44940d0045039104010541030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 809438767 1250 809437517 809437529
    0x3070902090d06091209080111040e0c1b060a180b010312121a0306090a020d0b0912040b0c011d0705010e06090d08070308010905060108010308030a0b041b0f0c0b180304 74
    0x400132a041d82410304e13140315600d401070081031001c040025a444c1c180258011403e007124000d04043c03030149440d4001c1c0c4002c0102005913410800c201e04021200304c2940000c59070001400c45180014140c0704452501d0703061150030401500241c0040c05000000381580c0d4003020070700d6803404500007610f14648015060f00c00700d0411200b88006524a0b5601d07080076407c0b4120303001511080307010b0f9110304c06410065003040c46013848502080b00c0311003041d004005102120705000c402c031401041500542c00400c13030840001b580042c003590074040c0401100504808038000b601e80d050040d034424440c4515818000011b8199045527201c80a41c2d08458006e021114003182e94503018060380d10402c030071400700d040b680011542c00c18601c5031a1007040107840e03260301a4216101d039a41c03034100504044000d5280c40b04000262140d0084203a6441c440c99488950782c042c8002400e6040d0140007801000700c08401e010101c0c0d2a180110b400003103d0700c5450115606500450461007280c00038 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 809440017 1250 809438767 809438771
    0x1c030906060602010f0b0109030b010e07050c06130210020627030403080c07061403072c04090b0106200309040e07080d0c05160501080f0a060510080a05070504030203070902090d06 79
    0x841030f03019003109880403141c1804220140b40341005440c1601c0f2030101030000180d120060011a81c90f2400c0303034101140d41411030508480f58203040c902003046a142d0749840407910030340d0840c10b01c0c2c0030b525561845030019001030314151181c01009481c47c082820701120782c03070302e580c940304050044a01540d0407801e1184e540c4600300409654000c07034030407480051965000300364131100310004c0e640200040c3d69142d59180e840d058062540508941c1b82c0e4051407000002c1c00195250310030b00d07440d14401e8a05150070f61500381e01900c1490100c2c00b030f81c0e0b08413101a00340c003840408400c03200019000ca81c0002c0e60079800300064900511038026581c9449011101e0040c9070b000308106428070311803021103026406010b84001c013031141c0d1003414086950b42c008113404800d0603d807158400050038000613a01e0380c0d10006024183d20700f1018020501c00c1e001e2000c15080c2d400b950b984010b5a041c046d1610345160302003a40e4285034070031907a9841d40405e00060a642d1754a030650410b4103c601 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 809441267 1250 809440017 809440019
    0xf0d09080412050f06010501020111030f070909050a0b030c0102070f06051c060f090c050a0c0b06030a150b010801050d02030a0201080a021903020c01050f061c030203091315171c03090606 82
    0x743e5196101c460102d894445c032000000c056105026075040c807100800d42504648030241d03804c45195002c4c0c2502c0510401c8031000c48e9485080c4140c0b4840d000e0000049005403c0105040c00c21400c03154071411500001c4040c0030840a00c2c8146040756220320700301f640d40c4205440441c000c494117900d030000d10308040f000114504118541c0c002e03110020700411910701200001e43e071500c102400301e03001c52040d0b0741901c04a8006003c03540c2c0601c0140a07511120700303d0365150a49890b020742e440b03981e641d40da444a12540d100d804580503210035620502455400c1e00083e40c3c070821281c0c000c2c10403100500144c0703005a2034054901001c00b00c20450034580d03180001074081d4000c407400c0c201c15840c01d00001c2d0b540c4801500103000f000e015000401601e0310b0240c0081440c01070744160300b988030801110b441034462a841ca01e81c0341c4030103000594541000e20207a40c03146654424042c009880c1c1641501c4075011540f441910754407a020000c2e00d0000304180d000c3d000b0a003003c0c08035031034500 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 809442517 1250 809441267 809441273
    0x180f04021201060f110705040216020a0b0d060503060f180a321b01030b06120a020d0509120a030b0f0d030915260a0b0607060608120f0d09080412 64
    0x30005041c1c0300c41d9104d4200c460000d0b80b040f1100702d850240c00405074810340d000c0129042c564014178151401c070b00d03800349040480c2c011a02040c1c2c07560240a0343d0800107003616401005108900c0541800c0740a041030307007004814401c150b400a89105a40d440c040c0d0f040400101c10022420791544c001c0c03a070010311407180710300303144920f001018440450b0403100022401e00c010500c05000400709002c00040c040c598011802040303420200741d04078000704100ca861448079081d070383c42a000f1a001680d641e0518000c9819524007801400040c0e0114001007074200c1c0320419100200c0441c680040e03144840342c0098602d948600a203500003030542c0e1200d050590240040c40bd4404142c0445201d020903013088030294030003c1800c0e040240322110302c0d80814041c030703442d4100c1c09144001c11600350800008441e584909d0086545941d1018208181c400500c140c94240e100c100308142845e00c641ca00d03425603c07035945007400c0f041c0d480701101d007000880d4094a000d020706072182e580b0044685 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 809443767 1250 809442517 809442547
    0x170f0c2d0a151101050a0504020315090f01330b03040b0a18082101060509090c1201080a0312020307050d0e10021305090c0a020d0f0c1e0b0f0c180f0402 67
    0x3d2407008503542403100141245495008079405107901600600d0301d611415080078102d000680840344502078424aa01000024019215520f118542c5040b042a0758890603859060403210000d0786400d4078400c0090100c56030542c0e5000760403000a41c515038625040400600404640c41c580450300c0c00410240814107015240c215440c03040e42400d0002c82c500c90130301c05001d100c2e0b200050810803481c4124100000055042000342d80500c2c1000c442070b0b48a81030a501b60054051544492075400c18981c0c401c0000c4407907400b44e1411491070420607801056845200321865200d500c40e400d0f140e461030b0800640020001407041191034607501090039400c01b03454812203200e02d200c80d0202e1410b003d80e00c03c0b00c000da051600100240702e0010415111032500701c492600380980002c0582c0402c91290340011211340c0340e0b03441c17200010702d85000b50701c00c1320107042083c49140354000c20a00f00c040a00b1500503582005008442101340800a00f095040c403c10503007050012664504581d600 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 809445017 1250 809443767 809443787
    0x70c032c0111060615090a08010e2b050a0f17040c1404050c220e070201090b01090213061b1e0309060f02060402040b0a170f0c2d0a15 59
    0xd0b030341d10460079400c9403030981d03484090f03440c2d66100d00304070440c800542c0040002d0404280181409070281d655245080c2181d521000c100e4031504000560700d401c0e00092006200104942c036908030f000705010700100300b401005103440500c0090482c890038517008000051003058044240041d40c50030349008150001e40303106031450038000b800f031a49a071616000d80ca10580c0300c070402c1d90030031200046802c9003001090850942070304d200130115064181100c010f00c1141142c0000c03809088904d00380c0081d010503481940321b0303441480381c0f0031a02c27500c01c55002299118a441484290507000e8009c0aa444800c014031911100c080b60106000092205000c40e020762100b42e00320b55078540507601001c0b0f4036030110060300020006801440d090340218443c03500a896501700035110719103003a1808401c400030f00d282e40724428049400004101d0284020401c0e24446404841c03c0150340500c4001440e000f402200f107902c030412600e800500328010725030309400c80b404912008000e80040a1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 809446267 1250 809445017 809445019
    0xa0f020709020c03030f040c0308070302010905100b13090311010603030c0501050615040306021323030111090102101a0402070b04120c12030914072309010e070c032c 73
    0x1503100e000034090328030310944500820320000f43d4950fa55080b40c0e40307608040140201d4900f02072010200114840701d0151800521a4000245603812410140c1ca03202150b100509081d0801c0755040541d2201c844002c420302e0015000320311a226450b05aa00500480d0020394661800e8000018141e1260001e800d00d4050301c002c2110740c86a2041c4404070b01d0b0250040c0480904100402c00911143e00401508910401c41c01c1859196000c81e0300390b00c424401c1c3c0541c0030340508286043c0c0b600784103284100f0110341810781341680540000c0c1d103441d0070b07000062250703a0302c58209407007001034680c0c0004031700010000c550303a500c45c1c0341c01c190381003050f901602d603d41001d17943c01a480c003400f080040a90401c0c0308040d10100050100c0c090700c0c0600701154054a0401d505c1401001048110050038601400c108004001c40c09940b41ca240448800d100f5051340e03004008401100c0d04c0507420044d40e107446610007086045c02c6e01d07480540d031200d8128040b401c00b1001c050942c0a055000c10320 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 809447517 1250 809446267 809446273
    0x60209010e10171b07031107030501050c03011d0106020d05250b040c0f14040f09140c030c0423070507080304080405011409090f18011406040e0604050c060f07080a0f02 74
    0xca24400c1303081028403e80d007544030001004100c0100c1d000b0580c2484c0e40300c0b800226400e154480e0707903040c00e40b0403e03a42c0701c001d400003000500030003501c4c0c22003400e1407481d40000d2840390300d40f810080d034408a0480040070b114001411240c205034405040f031008511801590314610709141102001c4000c0320165a22044100d01207501c1c86551844411130701c4240c2003d13996001d45c0200001400d54400c2c240c0210381c0e401d940790000e40da61036411441e03a001405880c01d00032030001d0505118440b000148100d1130324941901042440b1043c8608400700c4e249020540c0c0d0300c040655552165810241446402000700020050b0260040080e0f9800b82e81c1d00e541301c009070404d244180140da8065500c07000c3d002c0042d40c0002078045540d485101161100c281c216000c03160707030845480c1c10505603500101400c00445081500a950120080c40020801440d01d0307201d554490001c0d840a512038907001502001409049099421060700703c0071541e0307a8804c0c903001070201d10f00c480300d80d40540 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 809448767 1250 809447517 809447521
    0xb07031106070804120e0d0c060e0f130203090703050312011d0405061b091203030f0709181a06042904061d03030c010c0507140a0f060209010e1017 65
    0x35201182103802a001c0c0e49456070705807540e83c2d4040c48403003008210010021014024003040c1d0320041d00c8040c103800703903000e00c5245040c0200100291406000e00340905c4094550b003020b6107840c101c0c1c040300c07c102c0f9401610b0341c131078044003418000144c0c8090700c1c80c8008517503803200b4200381021504884d8201200d41e0008400181c0300c0c0d1070b00040310040c0c06d9402241c00110040c001c0c02840c40302020b03042c40c0318030300000301d40003641c045140141e070145c075070000c81000301c03105010300c1780c82e0001200e043c5030314140e10780000300354400082418002c5494441405000c0401c0545030500b900304014421074440da105c4404442555540b4032009230000003a65810f44900003500300d6043d5001c503903c2032100e0542000012012900e5020b86030107100c10040780400701004e104800c0c8410055031100d59418541c240030b42c024058081d0150160020780f119800503006140e46500700c1d074401809a294581080181c90b0030b42c007004040d0304600781402c00800c0551022111011040080070070b4256 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 809450017 1250 809448767 809448797
    0x90b010e010522021b060a06030b060d330f0209040f09050d0309020d020a0b040f1509121e1101021b0f01180b040e0402010e010201090302070303110f070b0703 70
    0x211410a840c0b4a201c03149503e550f1610543e400500b001c0508048a012000f90700800742d10703103001282c64022450340c485050040100d80c40c8215000a030031100010300e40415200c0074884c9030900040401d8800b10395180f1107030f1400c154101c1111a844504022450300f070416074020307500c49429203100c0c910301102c3c1c40d5191349030311032695115000001803480b44c005c0d0a060f00181100041a039100c200c1c560580c005075070300168400609101d0f401d01d9241c61900120205040e4240c0000811070b80e042c11078000c0c10b501c0242c510454403401d4000181c0900f43c20b190190b500d04d00c9001140510503c000814000386010701c0c1e5200c2800c0e400c0b1444400c03207804c805050000d00f8000d542c01868410000c08030342c801e500c641d602e411b1044240b0720099131403107041010b80c09540041d010022072000c200666030800130580001e802030000340600c010a94000b910b54070340f400f0007001e006600010302991203042048408022400044907441911340341d83e0381842d04103007811000100d0140240d112 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 809451267 1250 809450017 809450029
    0xa1b020625020705060d02040f060906020d0305060a05190608010603020405030c121204150212180d06020409060905012c0a02032a0703020615030a11030a0204090b010e0105 76
    0x3290310341e4000c20001039810701d680501c1003289014803003188100c22000c201a42e034200144640100014010b0f80e030351404444242c600700c5580240c052201c511001c00080740c0204d00012505400d00d000070703050f038410001039103800b44c1c3c7e08840c0e00120b1150007481c0d04401d00308034205407401a11500081c0e0303079803403048042e44518011075400d03801440d07200d01542407034803601c0d040649032001e8a41c0085402603040701a0440e074405c1c0070644107560784502c05a0140846001c41d0b0420611510f4201104030384820342e40c1c454012400703510304002e030506001055040d60081c010350340090041d50340d5018244007401c002c0c081d08154116450004422401c988031071700f4104014440081a41d40302c03030308039000307400050501d2404030704001c0805c84507000c0705a198841140c0c0c2c0340e25482e1305203818001d2900900900281102e86860b1016516a90003e01140c0c4c065100c02d02811409401c0d021032309103218800000e41240c01c1502c55810820b46a501c01e050350f20010050380c0d640ea840b010804 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 809452517 1250 809451267 809451271
    0x70e0f030c061806070f0c1d2205030d0606030e01181205190f0807170c071a010807230a0603050604091203052707150909050a1b0206 59
    0x5815804a03141e40342500704080078100e14140416207107250310b811000702d080d9038040c2004403002030048244104000031001540003401f1200d10b000301f0228142c100701c5420740c008e0a038134102c40c4100329010002408401540003150b00c681541e840f40035881c2c241026000c1c038081e00d030120341415051580c903001441a0f6290030f031820402c01080c0b480342c4400c800c3c0c0e003040c0321510801c0030420240c06c0c1c842200801c001c07010b24540d20703024600c0025200070f058800c040c18410400000000c0c0705190000100b84c00d0b00b190185485e071769070f8055880c185030001c4031170009000028415000140d006004500042250354050000381d6800b04004101c10030740e000b00a056210100903010700a40d4441d51185070710590281002541c184552621720380d182e008070030000040c1e1500c2c1003041c0c150302c041e00a65001d00300c41c00110180840c0302500e48418140c016810f990f0282320260035220300c503d081800030400302e02c04001e28105950018041d00104011203161501c4031362004269100150b118 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 809453767 1250 809452517 809452519
    0xb030402090c0307051303050304092a03020c0a05060a1d0f06070810050405150a080c0d1118090a0c0f05091311060424051204030c1b030308070e0f 65
    0x1a265030350b2403006240d4201a28a004119051001d0002810703102018800345002d000119100d5280c103030000161042e0040c038411201c11407d0802c1e40c0a10348603204034078003e0703080158991000841061501401031405060b510034002404000741142d030200307000041c0004c00c0441541690401662100090800c000982c00b007000120740034402d241c01608454044500201139940b040000c05683c0203482202c0c1d0000038403000c1e070741d61805100d024000d103995400b504040409800084241002e0040501030000c121300400036a5520f412820007680da2070488011070820b0140281d5941010384100d07007108442e600800c0a00c2e040300d9620440c2c40c01810000143e8640d030070402074a0dd145412a40141c00c20106030003542c8580281015040ac5d5005004286201031001900304100601d101402010451010104650743c03900398081d0701820f192451036464603000d1007010341246046d00c541c28080e400304c10164441c42203401595185e0ba00003185100b4010491032682480401d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 809455017 1250 809453767 809453779
    0xe0603010303110a1202030306010e0f01020312101208070515012301020f03040801020c150103170c070b2107090e0a11120406020913020403080301120519110103060b030402 76
    0x10400240300b010414070903460f05043d03501071200356544600e0000310300c0341c09015030404010020343d968440040d080103042250020072000d00e020001c0d441e13101d105040308184501800040340140300341c40c034400405e40342c1c1c2c220b1020001c900340441a50088801150b071070155462a100460903820014141c92443c0e200f07c2c0020600101e06107076140e03c42e0b04d41d0540c000c0007011001110144050401040c80c00000359813090190310035410304400031120444c11400500500201742140005042610f1038081d0aa841784c001030180d1500490f68002e1204100014600c100c0c61100031040d425841da562a0701419202d4100070344c0c8a01d80c0380140e41d803400350f20380010319010060b0400500050b107071100c41d143c0700740060202000d030700403242990351540000380d50300d01d42080d80b21210250001c01d070450400b400e5541d0041588010300c07a580c40d60007842c00f60f000303100091122181c20703510240034075501121403070400d0000d000c4e6221580030078501880018900e02c0c076401c4a11a55005000c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 809456267 1250 809455017 809455019
    0xb061f11190308013b18101d0a08180303040e0a0f0e061e0c130305062a07020114041508010e0601020118020913020d0c150e031905010b060d0203010f060e060301 71
    0x15611817440001d0000c1030005041c1440e40c0004010b0010030805c0b10342c03010124500702c4020403032460500da4400041c499200d0f6540c500480c40c3d600689041d80c0e0341c203032082c910b00c0000000034030710b00450300450b5140c604181444000040b56228507480e004da50014800c03040344e8600705031149802c0360408412004081e4154101d10503214840e845280c0c2d182c40e031b0070035008080103881042540c00440b241d6001c041400f4030320300d5918581b00c8850300c01c0d046482800c045800c801c807074099100002d0501c40b0359020340140c05c081c1d0050302d0141044405103404000c4155008200c60028460115a566440f0105090b948103000c1d03041900300c10840e070124032060b5030911103180130091100807c0d01c1e4440c0700c140140d8a030f00349007030528000e07100400050309100e940e50f1070700751016822080c420801c00c000200d4501285443c080d5032247d01024101105050450140522100c1c0d554400000a0360f202c80d810b0316809907041e00d8a405c00035084540f2108151202800748030303c0c4c0c1e4040c3c01400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 809457517 1250 809456267 809456369
    0xc03020c1003060f030b010e060d031b053c01021303020f030123040308070804110d1a100f0915052205070c0b061f1119030801 56
    0x840c0c401c09411480c002440c0303941e03204c0900c40d0410b10b8104445240b075450040040c0e0030f00c1803086400040446112008400c1564058490303500001413203030b843c0c4251100b5050010501010010306e07048030000c03c0d076100740d0b10803803040c1da010009a444400b80c035a2070a00c015051090304e607200b904018218540b800c517001c0103002003c1100c00c66240d921400c0c1218480090345080b02c400114070300030401c0382040d15024102082c000c0004082100f44810440032800102904810310401e54031141d00e0265814006084516070509450f24042c03d8144001403851206440c200d90740d1001c25450300c0d444c4c01c010300c140c1c0d0562000101c03200310001c2c14042e9240c00c3c9030544200c44103500062030b25010603482020f8810440d80c040c0440c0b01d1035203010521140d40d85682d1304c40d008403507003400200142d20740800c50b2590207030481000668009100d443c1ca042060084a0b1400540d01448040b9807800500e240403d0050584086111a880e05401a0342107620200482e0450030012800c60720 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 809458767 1250 809457517 809457529
    0x703060e0711100c02030403020909011104090203190e0c0a0906050904140304080d0305011a19110f071502010e0f0a1b0902120708311406250c03020c 66
    0x510407a0b01480c1c0f03020b0016503640c4140c40e41313001c154016549031865401044280c2c3c000929a40442c0d04100e0303008008100002114240d4030a01e0b8010384a40f5441a01e0346988501e20741580018075005040f03c151600150550317100e902100d4102800e80ca0318203140076604903100e0260042030690100300068003e0041c0b00c3c0b00729051003100d04140e614060586082e044010000200b40c0c2c5000500503403003030820204040d88500c207504d10b4441c02e50a0b9000418003984140d0030080f5103100344500f5401840411170010741581254071740340d00c1d8110225011441d4040501640c41d00c0c0d01c80305920004582a2400401d140140a600ca4181c0f6a02007440d034800700c0001103142e5200102d490400b602c094400b8081b050307804c002c58684000d019009110161012003600a40b804680c0c14291310f4141c800c01c0001018079003415403042c5041c410446110942e250b042c01104200030f0710500000c442c83c8078100b19020f100031080120801d4480310003844000c3c005801007041104642049 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 809460017 1250 809458767 809458787
    0x20d080c40090c0518060d0c08100801060303020a03030f02040b070302011a19030215071a4c030213060f05090c090904050c0405040303140703060e07 66
    0x507400c6400c0541a00014910020300030022040e0304241c10359104940e01c1594220040e040c8020104a040c615a10280c80360040f080c00c140406a01072031030003207807211802d07200241c20010301800720001d95640941080003c070303104002c80250280c0007450b9041401203400b1a074140d00944501003c54500300c0c040d166900490078034980800c00014101528002003a83d180254000581c3e02c50719184000300d082400d0b03400c3c2c4261005449101703540c00b01c11941c000c895046900700c10f031010351002444d40d030080000140c55a040000409500c0c1c4089981d5440b0740600294215840082c01c01108140703038071740300020f8103880128a9880990030107030b099000e26182c05030303150b50b035600e9001440751221503054080a6480f91400c2252100c1c22040e000540ad0443d500d07001883c03c281d141c0030314000e90000c80d21034019a0041401c3c000e0502c402002ca001c017400c18040c80ca82414060081c1030541d40c003101181c600c07070005148034428880c500543e10030360342c61402c0d522403060071510f406c84 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 809461267 1250 809460017 809460037
    0x110a03420f030803040201180b0f0c070504091103060109020a020a030c0f0b0a0f0614100f231e030708041b08061609170303130305090909100b01020d080c 68
    0x100c000401c10014954141c001584246452966854144001040c81c214600300048001500c02c061045103448801c1e42c1d03401440503202d9844020303501a10f484e00342940e1200d600641351600d0a0140016160a0091000d0a90840c5d826990380c1d28144100c0c803403002080016041841c070007000038803c0126030603090090301403040c0c15110b502c411603036030420f07a00d8011081c0d4601403c80708120034015000101281100c0356501e105141c0071410514681c000c8104004500c1d80a2000710700500c00c41c5a441c41c0311501140058541040701c03104c2d07010343c188001407000c0500b90103c00d07158504507803040d5500d6541c944a5101c07582e40d4103200c540310b1030000203042100d401164040c01040194030030820b0400c034950038020380001520340211358200c095100c0e60741e0800c02d6900d90000850b500070380c580150824480a40c00c084030603001c1c505119a00021003003c2c89030030301000501c0c00101c46103450401c1885544401a0313602c220b0108407101207508500042d201d203149030090220020 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 809462517 1250 809461267 809461391
    0x90501081902090d022215052112070c0305100908190210020d0222030807080c01110c1b0f18040f020619111b090a090501110a03 57
    0x321130f50006084d1614004552089000101d0b41e2003401c255001e001640c8444507e240c00403814074001c81c0200d9040c041582c0c03e10105030b4503540314a42001144500038183d49d07699242e0109140c48400082d03103100581b5148150083c00c0c645581e18400d102d016540480820b1800f40c2030395111900b102c050000d1801c0d405580560320140d40140002c20010503a41e50040e50345082c2500940c100084602d00c09034880348030030901c000b561801c122110700341c0100e180c540305e00249481501400044c0703250582100003242c0803d2031100020160844201a07111101ca203002d41c0a0180e00b2041180c07881e4070600d45403840c2070503050409400e4000e07000300701c03500400546c5d8000c243d1580c00340b08000d840c0208004182001a8452000c2e14000d10040103058241c4101800d0080700400c651030034890706000010520000042e442034100903409002407000b07082a2781d0540c0781d500001207c00200703003004840e10040d1501d0303850064094040b1076098203d048000300425140f540c0c448449000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 809463767 1250 809462517 809462539
    0x807050d051204110f1908010e07081203101827030f0516020d080403120212090111150a0b010201060501020c031005270a0215070209070509190e040309050108190209 73
    0x24a0700c40189031000886c4086900c04c03890103c44900311820000107100c16009010180040f003000f1030015017240b140000b494a90702c90321044201c0d414140e10a44007644000b41204c24410f0a81001c0c0590381d9a00015849600c80c8050b000d4880000c03000400040840076000040c0b401800903055003541c1015004110260303a0108600c043c0c40503040d03039814400300782041008190020711200810910103002c10b5911910900101d00882d00f804e070610400301040d007034140c030401c0040344141204405c2700e00d6007004500000207001c240c410500650170541d0100e0154000a81d0043c403c001400400d100c82d007a28890000b414040c00340c00820741c400103514403c0a81d649858605103102000d81416003851040048130501d44204503d21482800003002580c0c5501b0241d034401c1060410954681c9810000b0341c2c4e000c00a80a0700e41e031003065401144050120b0398192049102e03888070b05607140c46400645004034200d410780c100c40c43c0d01008003804003954016003440500500886210 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 809465017 1250 809463767 809463769
    0x603100e04050c0f0d08340309080706050f1e070512090f0d080702040e01230610050309030f0c071a1210080a0b0402030a0f0807050d051204110f 64
    0x2034109950580351070740580f401c242d0b2403a00c02049480c101085030030183d2242d866071524082c0c0141c40b2070314000580f034820b1202d5950300d03a0004d1454000c4040e1640300940519010b01807081c43d014150b40703480b4010b80441e40c1c601880444055041080b201d50030318030b1182120010801c04e81c40164014807d020b004009002008100f03524032001d400309072141417500074007200b120080840c80c4079090030790070203003c52500f030119062141c05580c0821000c02e4070a0700b90252201240d031014548001035005c10302c034070b45030303510303006240884d100004804c044c4000c403000e0100b580c00070829002040002c05009100b401410180401410741d00c1c502da44000031001210700511000b9881c0000035600c1d900311078500d1203540411404010b990003414120050303034a031180c1900908034882800450103640d81009036150703440c0c1c82420126440142e1a1059458106403400c607102d00c18142d5503075909015000f41c030015614a18120025502c9481e0300d0500711914901e20b13003000d40d0400400035 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 809466267 1250 809465017 809465039
    0x6172a0f190605070314030103030f0c02012007090f050f01121704171908041a0d050405010605090a23040201230306190503060f0612060405011d010c080402060310 72
    0x80802c2d403a010307210911800c2c00b5000c030030034100d00c07404024108010b2000071742081441e4201c00d001e01c0d0040c0418081e03c010385a00284080c06014140440038410600740c00280803002e8904144091203a11180d86880c01514000e4038294001483e8200601004501000d100e0555003e00c01c4070b10380c0d069481050303007203500036004440203604081890149140800c86d006c4118200b80000322035004544449841d40503d00480700e80824211b03803d84c07004010382c10344508202124082040c1d041a11300030f0700800c16440b61600601d100400100c0d00e01c050300c03d01900c840210751202081520b004034500041004000b241480040101641e1080c1070840580b40f441201c120356541c0c0c02c2920800c9807580e44035262460300951108140803d0b107000c60301a40288010144211903110440002c820030301910b20140c052007030004000900205402600c40300c20310f0486032942850482c0360b50709a640c024141c002251004001c40d0040c04c1460003550301000050729902500e07259000684 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 809467517 1250 809466267 809466269
    0x40e1005090d03141003060c091a0c0606121005040201031112042114130b03150a0b210603031603200d021908070606172a0f19 56
    0x441d4403502c52094895054442e03030034034001e084083e04c242d240144501028000c2804014074a540b50075100c034915001c1e0f6110f8014080303e0104c40c07a040c248601e0300031207401182c1500694440c01c00404e0306800e22881c030582d10010000075103012040402c0401c058100900100d04043c1d0350a0103038411501c3c40b020f44420340f0030300703242d040b40d04203802c115110386144440784c6803150100e82541e0702146c1001d0f03240703c4241400501a201d030245d001028010300c0f242c2c4111601d030303000001c01584048494001c450000c08403540f55840c3c1e240c3d4070340340140c020010300842c0d2a10300e50509405140445810341e010b040101140d2421216181154048811400c103c01261808103d40296980c2c40c801c0948425040c0081c880844109030007540e4860552950302c038000d2810031031040c000c0d01e0084a0f151074000b0414090180e4a07025084800c0c1c1c0440d8002060041036400401c2e441c0080704203035086140300b60308010781040000c220325280400c05c560b44c4000740710380e031141d14450302603414 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 809468767 1250 809467517 809467531
    0x4020309031306030203390309151003020603010b13051507060f020315091008030a0e040f0e0d1b021203031e01080303010611161e0906030f02040e1005 67
    0x140e01c2c2e06006091082e02503894100340d09150042c000c00c21100c400d500c034035000100d150341041806400c5802e00d2000080d51001d1000184000700704051500d000031115041005c0f00c88000c0c03540d4403011107a10328030980c00001d610074410001048528003030b002511a012145962454040d0b4440015409030103103201d0244518010480300184009442103121101c0e052405500e0362410041c0220443c420312503580c030a02244e000306000c6040205034070003921801e0100d070754556255101408490071181c941788035a06200d403a0028000354050403540140207401030201880c11613081d101c13142c0f01009403041312050410280940e0305ca4800e80c48845030700340a0f5549007401c0c07952080388005800002c0d160041440100030005000085a045039101c0c50031604110b8002402070420f001c015408102d410200c801081241802c0350054101150101028459940d43c800c4425190386200152049025400010140c10990402c503032880712641901ca030350020240410484a094802d1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 809470017 1250 809468767 809468773
    0xc0627030e03070b0906092b0308010e06030109050c100e090c0a1e05070201030908070b04051c02010b09150d0507060806030c0108010b0910090807061805090601020d05160204020309 80
    0x80c6400341000d1011002810301103114031700c0c0c0204e043c049030480c03095808503400303824080038031041c40c20024249008000124200c544074081130600500703141c401e0180042640c050320100e0440d150500c645107105500c000602a80016401041489903030350340088203010b10380d010505241e80d0305000a20540c001601c10307403104c0d68008000c044074080c0c8004140c0b15600126101115041402d0743c440590910b80441c8003052842c2c144083e000c0c204006192110510900042080204102003440e04044005a08184400b0200c2c00d9403600c04445821041c0100030888103d03151103e0800d899000d421380144841c03a548040c07400440d40e01c075100203070600f810b0000d649001e0003203940c100401d103029262941001d51303a0303082c0d200b00d8000600c18440c1281050000340126184070050080005942181d40d8031300c00a480b82d0075144200300c404084260105540c6460800140a26810f900a240c111f141034015242a4804084040d210060144520040ea40c500046201d5100000a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 809471267 1250 809470017 809470037
    0xb0a05060d0e16120b0604020f1603020f0303060f210f1c030b060f21090c0f0d0b2a0403030509120c01140a0e1f0216060c062703 57
    0x18642080300f10002c1800f0b6a2043c1c204005951103505820071003074024805141603100e17500054000e12030b01c1c646500962001c40c040e01c02e04000040c04502078061340a03203a491f500d66010544070b10046070000e0380b1403c084081141418454440104e0f03491500b0320441e03180590080524150705074030801e400ba40032402c60035207104240c0e0305012245241c1030500c0440c20001c000340d1540035103808020314034808035405600140b100b081c08192103580810780503504102e0245c68503100c0c403400440c0035120050b0004814207200b0341c810040c40d00400d00742113940320548000118032540c41a005402c4030880056a10983c0c02d000b000194420b80300c0c103585060000a0103241c00903240880e81c29004101d0b40c1c406d90740c02c040e52489080001c41c010b07548068569042d1070380d130b201100c0b40d0380015140c45242440f582c24010342105004076000c49010b14407140015800c030000d801030f8800a40101000030000b0666000410f02e201b01c0509040c6040701c14a07000764030940d9920580000d001130701 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 809472517 1250 809471267 809471291
    0x20f1818070f12140903040501180e13030c050d020a0c06030e0c04020a121409120403120f091203200a020f100507020904060c031a0f040b0a05060d 65
    0x110501400e401108034918600d003414020b4070308102031a0003020720010000080c01200b10790712022544240030a6080141000c52072a0b03580d8006004003030100700b103101e01e43c4048084106001c00c0762009107600551350b0315009501200060007108605000240e5000400218103001710b00c0032641c194020401a025401c004944c0001907005109262a1400b0070741344244c08518a5003a500607100542d8030301c20020221303481440044002041481c1048170a1320909466550b03014038028400c55030b00d80c0440411120b80d00c01c52000070207482034442810540b9001d00002003448019082001034a80c0c0c48448a0101d10b5410f403c0b800100144a01c1d1041138002c0b10b8034400b0b110140083c8542a016070214140d803080304403062041d44a01005100c42d44260111030141d54080c003081e070581058a46240648507900e804408039003001898003e500b20a0541c100445d0700510503840c01c6090707410701c0000c20888c038100f038126500202c0428a40c07112402418500e41c0103c0c0000c900725056 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 809473767 1250 809472517 809472529
    0x40b100c0209130308070806240705010e12030403030e03090d05031903060617040c0801060b12090a112202030c07050705061615060f03030504051309050304060e0301020f18 76
    0x1400884442c4504100b00003080d4021710b0309900c06564101009151500b0740044c81d03402100c036010920410119100102a9084000d003842c2c80c80f40703000b03000d074802440f0b103107480f10a0050000d1501a003800041c002c42e01c1b0760410b101c005000d1061700d10305408100070070203203030741d10328143e03801d0b40001080414982900c1020003240020f160800c0070f14209100204270071807044811440041c0c10010505010300550b0480050a20703000800405545d481501d100340c201c0045420551850b030006448900d021803240074090340912680c894084031380411103007192102041705c903480320a0106540c02c1141c4002c0d400b440f800000207845102c1480c155103452503680146029120510030f94190740c00741d0708101d5036154407942c04c001c107000d0003050000a060070b901c41009041d00c04000010302d0f8000e4000d205031349050300c0a09003004030706281c0c42601c0e0425001000c03035104001c02c1096910441d10b5010b00300008001500c0d02c2d80c44c412112454100700c40c07503d80d06242c1048201145444 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 809475017 1250 809473767 809473771
    0x30f04080904050a021810020304050402070302102d180303090f1b140402090d0237090509010510030308060301090c0312020606010f0206150d020402072a030c03020f040b100c0209 79
    0x11143c8602021f20020000d44a00542c0716081c05541c0200f0410100740c02440b010180d10125001005036200c0c05401d0881841d0b0340c180d030b091100d00f0306d08103012140280600c0501d55459140440d0032204c5903011001000d0181c1c043d2142049841840f0003e990f40e201565076044121009a0582c24640030500e04108015428402c61040102c84100e46a02050348519a01280c146c920381c1c038888444998200c010302c0c6404803858891400317a054203c0c01d6050152084ca030301c01c003d1b90703031041803031801c942003034501541c030001c982d4040000a100d0f5a01c1da90050307014001050b2002c440d5910f1402e6080354004840080c800d886c10100282e04000d01c50748903409103040321402c80f5002001e519a400a401d0000800200d0154886515010040d008071580540115030750505400c0c081050303602c20b07018402c5100760074442c1e0815884081522305072500b114003098a2450341c0d00300507400d142c0044036504107407078060803400e60b034500c2c050010036041034882c800c42449a01c10488007101c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 809476267 1250 809475017 809475019
    0x6080c2104140c090105040504020d0503161101110a06110d0f0b040e030a090b030a2d0c0e010909021605030a120f050c0a0507051608070e0c030705030f04080904050a0218 75
    0x1e0003080c140b030381c84c840300c41e046680036140003406032a01c0c004038a8401981101416601c4005210704c071081040f2070344002c0c140180260303815800c842c07004541c40307404c0003410b1515601414224010420710b41c0110f07910344205000b1450030a50f20841d5080c0c0d030700262000701e00e940e2001c20010038205401601070420704900618070f03200344200301030001c03a410f01030364604643c00310018811090b40d40c02440f01002601d5a080d180c2c00d4080190046d82000034010422424045691440340c001c1d00002e4038250141c403044e008600b04080c070070080d0405020880302074110380110f004280207000a050540140c1d80d1007040240b005550010356032410103800b6250b1501c0b0410a82c8a505400e842c21100136103002030350f071110f90600361b203420800840c1c2403010f08070500c0001c401000145090440341421010a00c2e941c5005c8108145e01088540f9800b1410801c00500412801c0038502d901c5481881c0181c24049810042004c5501c00c523241100745600040b15074500d551000840d0403070324 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 809477517 1250 809476267 809476273
    0x203060d061b02160b07150209040203151c120c110909030a0207080a080d050705130806061018060305100f08030a1409030a060f0908030406060306111306080c210414 73
    0x1c98024980e05c40e1196080103020803580b03201c501d8202c03445404032003c1800c010700944d140e081040709081c008820341c0d6418403416100b0100d02440301c0041c4018910b541028150465910089003590303d0854a02e08860347c40c1d0000508400e595545002400303100600011504d84da03190340f0103460940603410100c003950020607a000020000b03012244004090000400c00d502c40c0035041e0740a0042d4088824454100e030300c04500740d1000540184102d004503031040407200300e00b07001e5520040c0c1c0c0d80e04801c246144070081c01920f0003600a503401881c164194400203a03036054215815180c1c3d04990820782000480e511015441035140000010f21103090740381010050002c2d586481204004040c1511001283c03040002903200c2c040070398101d80003503178901d041e15100005141b1800101c0f1543d140458504e071051904e41560b19440c0e2109200003810b003411b0080d919600300603c3c1520b8172070200900114070511a401c98011840d14a03540354608081c5804207890f070303026030500c1ea00d40c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 809478767 1250 809477517 809477519
    0xf0a02040606140706150801051f0b0f07021c0516090c050307081603020c1209150304082b09050a0218270304080f100f140a0203060d061b0216 63
    0x14000f034045a4085030300050000320342c45210707650060103400382d00c241c98075440d000400c41807407500d482d940440d0680c014410681600c0d500054000c0c0210031383e441c0451010301881006050900302e91407800c9606120b00301c0407000c4c0e901c140c40d02c0c504000035510300d654031004215101d410b0155020042c0d42d42821410351a1140b8000c01c042c00c020000d18030b4003014480007801d20300a40c12219003030219030503224500c0c40ca40e04020786521000c9840e01504904083c0c14000303425005680c06a6400b480d182e15140c410128030388004454804035914142245040c1001c04141c418040c106110f00b01800c01521039004000c0301c000280890b00c8181050410040500d5092002c0010700c0c124801540010341809800c900d140038540001c081d0f48103601d030346981181c0010b00300100005a050a000e0780c490510100f040d00c0e40d600400038503403d0382000c25038402490b0041c40d40100c0c0608041c03000202ca445003410384100d100102e00c280300350b0300445010755050100700700311320064403504009 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 809480017 1250 809478767 809478797
    0xc04240801060303080415140901020705061006050a0c05070f140924041e0608010b130207020102070b0901120f0c020d02071a0304030c05010c0201022a06010e180f0a02040606 77
    0x201c0104002c4c0101c187d10600081c075001580503040303070b052034240140640b0380090054001e512108040c1c5403445080006192940540342020541d8000ea603102d080c260a80b005070356103601605c08907054000e0302c4000c01c4102c00d0903002e500a00c03a501000403146042c0082c0071071000080c0c0043c100300d8240b6074040f485040c105043c05a00b5050b81c0002d961070a101c4180c83c089200c20b840003846040c05000910030405421400030680100c41d04103180704145c000034203e10401d44000e002d60000b040801c13130340c07a00402402810f0010b040905030441d0210004003102d45840d019101240e86080201146504100010344001c907800105844d5051081d0710803410f0800a002462180000c00641094031400f9480d2080b5808402031081c0c0781195006800317500b00740c004801400030100401c1c1e044d0303030340a810080c21181401422042e428502c1070b60144000608050004190050303407a01e95004115042c40c40d00010094203940b00c8034070400c42a030b112540003004100b2011000c0307101c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 809481267 1250 809480017 809480027
    0x60f0e010c080c030a0e060a02030a0606020327060d140714070506010302040203060f0a060c03141801120b2809110a0f17090c01030e0708031b0c04240801060303 71
    0xc00caa041c040d03a1031740e90b19042207000d07111320643c1503a2805080140702c1b0700540d41c0c001d14055031440000b805181c0c0c8554040340d80380644812229200e010155102c0030416907010311040820140c5114540300651940b90241d821100780103d14410541c204401c040c2e104130305900f038601c400b4131303a840d000c8541c03a0559a031006000c0a44100da00001003001582c0e0010444481200a803d129130982c0e03c0d031024008007603a400c1079022a807412032504e1a403001c24102c07407440c0c0c902e024103480c0544c007200440715120100d00e40b51400c1e0740d03041c8a0445039103216100b040200c9580542074041c0040c05100100c00c80e07036111030002030a00140300f144400d10350907260480c9481c035090380c0700c0c40c21032801c030b402150b801c04924800800302c0603c002c0d1040803d10642d41007082c0c800b80710b0500120500c50303490748907100324100b82e0002c0c07029491441c1e10071a44071001c1400c4049550740ba0120000600b201c030807240000180c0c03080e03c801c0002d01d0700d040900000f8407514000300581c52440d03c02030300d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 809482517 1250 809481267 809481271
    0x601050f06181c2915150717180103050f0412021203270c030d050703050409020301090221071d0604090e01020903100b060702010e120714040f06050d0609080c0307060f0e010c08 78
    0x111901c2c03604c603020200e1b0806030580e0030068100301c00d02560850301c04082c800d0790100a5080c1506408802c1600c2035002e4051207005400550300d20381c2e15521a250600e103094a010400300714010048003030100070315800a1409400c100c0d20b04211048080c140403050910440030601d04c1e0081d0342d1400c042ea43c00300785500400c2d03007400c00f581e4500851608403500d01c52030b0052481e0510100c0003046c1074070641c1c040c4c0f074104d0080c41c1001222200400b140541c80c004c684440009043350081c2818405101c0000303664100580302c0c44c04c040d11800c0d40425100c600750b0110302c581d404140030070b075491301708034528902100650420802c0106400310304580300300302000c2c0c1400f1242e41c2c442495100d0300940900559500c040d01c4209449406440d101e103490f42c540c911540c10020007415200c8903200b040c04a0314001c1140034103800310343c0c0c1d0700090810042c02356500038041c44a01d030f065409000400380c0500c204800594002c007144c80e6001c60b40c100c80081410780c5440c0144449a0b008003a0356 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 809483767 1250 809482517 809482519
    0x10e04151508011a0f071e11040e071401260603150906010e0601050d090501061a0f03060d030302070c0f06020d0311031305120d020304050601050f06181c2915 70
    0x30f83d844040c06201800c5e0300c5a41e40c01098001405c0c0da41d0208458101003d18031403151320980044003000c2d0801094913036401b910441a0480407040200581180140711801030604040c0d403800d00c500d89680b0100344c2060000c1d070a000000030480700d441e041c454103142401c0110444d0349070409800e6503644541c140207103802e00d42420041005a070084041e6a00c010005909200444480c40d1481c0a0a014400c0318404881201c4684103c1c0c10401600c042d00015040227003195205001c00002400906041c0c0a050f420008800407a04400016000c0d2000d02c910142151402c8402880e00c00303000200805c1526105614028411100c2141d801c00d11a10002c40042c0190178202d05102110350b001001d0a800a400340000042c2e8000d548943c0c028001e55001e607903254144900d140b6800545544038074104615042c0800c1503001c054440e03806011041c41c4028180c0f600c02484026000348c803040e2070140c41c46030501410081c0815901c400b052061a41440703480700c4600c1450140e15 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 809485017 1250 809483767 809483819
    0x10b1903050c120106021c1b020603060402070b07050a18050a12051005010602070f150215090c1e090603160521070909030813150b010e0415150801 65
    0x1241a00c120081a41c0c1d0320402c02280c070320f255030f40e034002950b01d1100c1c2c0c02001002c0140400d40e1141ca001d02400310008502c0410b081819065500f04013072a400184540d500560078801710002c10084001c00780304110548916543e001381d55005005200d000c100c250b416107912030705000b01c0d200d0344541d0301100d40000d0041c0340303940c0c40c0c07070140d0920407001c0f91030200a03d010000221641c1c0000c00c841201e1902c1c401a0a4a80316a1301b8802c1d50307546c109000c0541e00c188603100c40e0b0301c00111103503842801c042c03d68000e1403913807000401440c4104280904110900403008651905070b100e01e07007055045004201510241c150b421803817040d4032030746101b0400c1040760600b001c44060414000c041c05c40507148881d8403400c015005104800342540020301c00000168004801e1007881e81c0315030070480c01d11380641c0b00d04102000c0c04007481c0003030401c11518078220490711240242841d140c080c2c0640d484050030425a00d10285400c1070000c201702082d80100705819610003801100300c203180131 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 809486267 1250 809485017 809485021
    0x80a120302120a0b0a05040509061303050c0a0c06080901140c1b160f170c060d060902161403040b0d0f0605060712080105010c1a0a0618020c06010b190305 68
    0x65000380250b40080c0d0300c1070030b500200103590125902544e001c800c200c41c1889003a8440c406d001c111101110f90070110351102c4081441c3c942500c60206280e0301c03d1a20500c0c000300c0002142c1403034894803040703e0820032004180841da40029071301b94015034240080100264090b04110201d90140c0700c904d0400c00000c80300c50320444010014551340164040f1001f00703c84c414002400303942031140d202070f0524404045070001d1032a00020500b21000d006150300113034082000712540c0a48000f910650340c410300091141058001f40403004000180d040d800810341c2041c1c42d20604800c0132001c90b4108010a2110a000c00c09030361454105040000303040c0c42024510004100c2504100e42c4443d021030407004114800881e80052142c0303946001299a0f078000540f091045801d004000008103c07070b0030000c1c0d41c1c2900680d4400809400800d0050340d640003500c001040386480c21200343c0015484801d6801080464014200705100700c2c503002e06407503c42110603080720f0b0742c1c0406850f400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 809487517 1250 809486267 809486303
    0x6160605101203120b0612010e0618010b0a090803190509180903031509060f0103020c120a0c020405010e010501050304021207150503010e18031c0906090b0603120301080a 75
    0x1140780c0903100248122058510070704000d010a9100d04951500c00e04100180d90642030220917601225461140740c1c1e82a401c0180e40c514603070300140480e4001c402c80b0500807240e8070300402d00e8002d00f00c1c8980e15503600c41c81ca0004010400030303001940781398010000d080018107030140180c60400c003442d0541e12004150700152154950700d03400f910380c111040600c500c406022000714001d140d0280514107031115031003844160071040341d24940c08103640d4003041d5070394069001082d54a2111054564445c00c00d40798003981c1c1c101c0003082c8005100d415014003182041c0c40f4850240220f518101015850000001c101e8400108001e000e8861032035613154407075040100801404151003c070407040000c21004000d90070074400d0010034000321000c10003125403103440c2c10002c4603440255143c80c00f60120380b6030a180360f18000c107150750789502d0380b40440c4852040c10700c441c1c4503891840035401c000d01010b2400302c13000054029402d080004004032100001c03c0c0344000da010940c15000d02080b2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 809488767 1250 809487517 809487541
    0x303010909060e0703050c090f0108060708250906090b03060a1715130b060f0f120718020304210c02040b0105070f05070503010f090b041b08070305010506090606160605 74
    0x10080388118450704d280401080030114100028000030344240d00e080d076940005407820038080c820301e9030503005040401c24852103000c5907588070508144a000220001c0040d050342c40203a1029000202d031345100f0300021703502c007100c4d000074009840c2d00c07429801c0140c0040d9000540b80306018128503011018080c0104c14440744800c002d08100800591074410240c03900003c91042c02c48803403018000240841c904003140418819001d054405810b03840e0050103407044840114541610403110000340024840040084a860711200580c5030300700b0f46072081d40c0c441c0e00900358400b21035220720700110550200e10389070000e40488001c41d418103680010307152032240c018007401003000c0295250a010002844a0841c1d1307040d40200542010400c800c412203d0000d00102010b103801c01050105203004541c882c0e070940c2c0001200001c1e0b41e000c0092419005500444069444400300079480c0f0303055004030341c4032105480b454900480c01c2c0f40049052701d01103004040c50fa40e600841e400c000c4ca4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 809490017 1250 809488767 809488781
    0x31b0a08100f14040b0415060b0f07050705010c120503150a061107090227041409070306180b0a020a0e04061d010f05060301030f05030d050a0509060702070305030301090906 76
    0x20a05a5041c0c0301180c50340400340c42c0341c0d10032000803401c040c194103000e0400d4101d01c3c03040d42c015591401644585d91040d0704941c1c6002c50000c1c640c1c68810105003640488000c02e6481400507030b0568500451400f0341c1080d00a03130009042c40f0012490030007250203408505c4030b039641860016501e9441807150a00061085603090300070030a46004550250800c9080305d0f100003071000c0700c0440d40e035442d08000340d114002203a111011140d05ca03080c0d41d00c0c0e041101441c0c1600031300100c0c1c0140320074005004c0c0030b0102e5201071035510501c130810500c1064442e0010034492000d41c4209880c05440d404044a405002d140f80305500083c0341149030701c91132a294503a9001402402680d1b03a0302110740042000e40d5041c1d011103c1d100c0005540800d441c00340007120406400380342981c0c070b141c03221107150140d070350156440d000070000600594094800d40d4490000800c00040714104410024a0f01400901000039036000e4503041c4081000001640c2c1150481c42e00411070140918010014003c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 809491267 1250 809490017 809490029
    0x1050417160608010816060905040b0d170304021807020c06070609230c120a26070c171b09070e03012906070f0204020703030626100209031b0a 63
    0x2103000702180083e84003820038100c50441088076104140e0304102c900800e217600c03e040110f01c4000c01000b4034101a0040315a1144c02858000d00c400c444c3c0320103d201d000e2801510151400004000c00c502e0840c0074180c40d420400c0880b10b0601d0aa032029640303130340130322105208100c00304e990785c03c201c400c1d0003403410305034003820680c0071100c1c41701d404c0ca40014885400390140a0b0b180c4004050620165081d41080030200030705054004e0380310b61820034181070030000d030140c0c90144e0301d9210000700002d100c4984101c0c0d0341e100d03040c6010464105501c602c0d01050441c3c20010582d0301480b003181655840550071200e0401d0342c0c4515400750350420503d21400e03055401c02a011100111510070074501a1084914030f203065800c00820540e40b0072500000d01121882e02107002504281d0f020b4885244a070400051641d15072054031030201c140c1d07520b0310032075a071036005d07252291040c800544001e4110030300390300307200c19a000a911100c03101d0100d03990f545252512119903444440c01d1000f04a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 809492517 1250 809491267 809491303
    0x60b1302160b0a0b060906070c080a05030c0606040501050d110120010e0606010206040b15040b040216061d19060b0414100501230d0905030a030b040f090201050417 72
    0x1209400d12684a08181c0055031146240000108414640d000f100c0a0740001000c491400602c8401c00015405c52581540c0f45101c220700030500c11020010200714a000e00000c688800c0b06680c01c0d858102d005000d20f000d41d0610004014644418406059031544040c0440c3d040c010940100d5140c0d9500d54010401c000d40c3c0c01e103001c0684198010f82c40d40090105440c829600ca000584c0d540c1e60035074008103840101800184200880c1240500e203401c01000821040e0603540060306076080b03e452808a9920b074071604003080700320301c240d41e140c16040403407c0540c42102c200503143c139100c44030380c41c101c0048a40c080070450168040300807d080203200b045058050101c84203517a50407144000104802c0e10040360769802000d084000b0f404207031800071151003001c0c28131520740118580803a00b070b4940310501c00091051000d02551265681c0000e41c06e4011010042a140a224041c000301e20b0a0400c002613680581110292b5850f80050614074203100d45030352501d2907080310315400311 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 809493767 1250 809492517 809492527
    0x1140717030114130902030a0b1e0708090d0305040c0b0d06030f05030901020d032c1009080904060918080f0f0c1b0105031014150f0a020f0706050304060b1302 70
    0xa0802c00075000c1c0c1401c0e60180d25149034102c0329002ca64805d01d01a60541c001c0c0d07101400504d61002c10350380300c0802da041082010802c15074800c035600542d0006c01040c2001d0401025160400c080c0b81e00403a0741c0360038042c60415482e11108141a030082d902c440740005600c4454940340e400c103000a55020f01c030410703065039908005850740c1100e0002401400b6088a02e420144a0300929686441800004103003130b5035031046041c07804070b418103c4420301540e6003030078400401d486031560a6020b050780d40c0d075520084007044115082500300100e40c520302a01c0000d6100e40c114800f40f00755024a40e640d4422004510340b90710b0213030104030611038400180030b140801c408607040c0031410303240302142d00000b400d00044d10300c1c0c0000c5641c074800410142c000c10010903420680070203039002601d42643c8540030079031444641e000c45030118901c503000420030481c590402c1150700c641d000070003400500c1d08040b0010300070300c406403022f02210f407a410181c180c0d9846008900208075809800c44da59 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 809495017 1250 809493767 809493779
    0x12030c1403010b072108010b1305041a0f0a030308041202030c16140d021c060f060f08160e0a050a1b0804021201051b0319060b07051b011407170301 65
    0xc0d5100320313401c40c1d0000030450309140b16502c0d84816100d6080580354101d01c2c1e03003440807102254100301407400c6019000c0e440000d844c0c0b00c034480c1c41070710707850f00d029012910040014005907003003c211041c029642e4160400c0441d500c440303056001039010b0300c05902110812412480d6002c0c0b0001507209021750302c03400000b444114040741c22241e00502c01c81c003800e000301c1040080d0801060284d00711003407031403101d0901e4110301c0301084140b040c580003c000040c0b00f80360003207030241e4101c0c4000c0400904203028010040000400d0103001150a0b43e40e2800c001c4100010070014280f50a4a510703403000c01c014140030341000c0741d800300790b660758450b00c034000c10018038512040c1c5082e8000d40303140d00b40405829043c09114802c8400d442030442000c0740c0340340284e03e90301c01884040011340a248842c0b5035200d03801020010092500da0f41d80f5804141005410480c2e6100038501d00c074901d9114200d80d98100c98101d20600c0c4e4003060a80780e01c44d90034a001191a00386081d059904000b0002c546 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 809496267 1250 809495017 809495039
    0xd05180a0b0a0e0301020403080a0806031e03040806090f190c0b0d0c030f140c0711090109051e0402010905010809100f0e01290d17031e0601020a12030c140301 70
    0x2507003d60b074142e1200407030010300d805c03841a400041c016000400004920500900303c403a04a08007408503030b1456541401e000701c00c0f45042c03400c9207036000014200045801041000d42040000d4007510800c08502c245e01c2d80d070040301640c0040642021680e5007444401762002c4010711480e01a142d82d04050b9030407200601210b500c900c04a803030403244180f100002d20904031488040c110650140e1141041c4401503005004215107000c6c0d241c00205091f1600301e04507008000740e020124480c288500c400150700e10783c11104015142402c104005030384c0c801480f00c00c9800a08040d02d40c2d840e400e810505040901c20089961402d14a080002023520342c0080719030b0b1001030080054003914014489030803540c45402840c0d000090000046141000341c005e000c9114100280c0c20041000c040f0065802c1112084000b450034966803c109651042041c1d00034401d10251006840d0b036601c402680c40c44101050405584044201000c2d01811507005024400391407a5101e6a48001001c0c0b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 809497517 1250 809496267 809496277
    0xb0901050d290f070507030807081003060603060606091e27090f0510150506030a020403050d09050a05040b060a030f0b030f0a0c0801020f0d0b04180807020a0f080d05180a0b 76
    0x3c03030241d083c00951401d10520035a9141035041d5100c00990b00e81702d004460445010b8540e4640c40c00320741c4000005480380c41420f004600c07c070f502280180c81c0510240c07029040d50310035800a07840458080d80c43c02e20094030000ea44418507011190050308104411228011007080d80d0a46010000c00c28890328010303502081c0c3c0318900b10f890429000305018107a904507050141c91145ea11024000c178544400510341c024070f26800142441d5494840b180782c4202c9450200114551703100070710030b0b410b0010742d110262409031000e101082d05000890039500c80e50920001b0182e9451000e501e0b810b49400200300c03c50010304803101c800003c40e0480d1100c0ca100e400311860302c1d0444000079401010b0080c1e4045141d00c45810303043c8440c0601070009002e10080309507010359030f104d002148a03910701250380004d006041c5103407100c543d0f02c18803083c004260000a4002c0203004200000c50001501c030700008c407207140c031030b4551401080010115403a01020350780103800740008100e409920010301 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 809498767 1250 809497517 809497531
    0x11010f021216050a020d111014090115030218040213060b090405060904030206010302102606031b100e03031201080a020102100605090115020f01051008100b0901050d29 74
    0xb0401811042c400d5400784295a07200000d0381081c040201001c1c020820090201c2c040c80c243c81c903854a01006c0000c580c9520b141c0c0001500c18410301c00e90400910907031f150b444a003c800d510b05410742e0002580201c0f0764121102c0c0c15150b030002811511880b1820900044400051000d961120b1040304503230007800130304d405a841c1000042052074960803180c040c070b0301a0054002c590850b000d00800344a8568000c090000a0f18000002c20303045081c10103010504d80800c216007844010181845c43d082490042684001c0d00710540341ea9040c8241e40190007800c1550002c1d001c4804079045005440c2003252456010300002013060021906684091003603003a00d1081200102c0030080311007500405802000b408014411280000300a100c2c43c0410300450780e2a809460b0b0250035100212640f00e0b0382407620f2070400c68400e0800580416034500b45050105070020004590500c505200b0548607884944030342c0103026141a1044520036a00d0010070301d040004c1d80300204d030a007030300c81d0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 809500017 1250 809498767 809498791
    0x30d050723030732090105120a150902032e080303090307060e06102112112404120e031e0c0f01020c0f0a05030a15110a020d11010f0212 60
    0x72070290360300f0040c104100da50848801325103070f1001d00340780000d0b008208140d05200c010407100280c000340081c900c1c400c4001440c0410800900303c0070f48000c011035400620704a0041c0103000b60009500d40b070303d518640071091100041c51844101984000b07550100722a40000003e0000c0d60034040003c0c1140c40c06002c044c80010f81d04401d15681e20011584000d04241448007400b0000500c03140028806851622108903441c03034907980c030301c1c1080a8081d0045015004220010082803285a204400410254404d102e50b40b6507042c00140c028402010201041c529040b03113405034003480303071410000d0120762441d1207100143c041d01748068681c05161141d0610384e6140d18203000c420600403810ba0190000b42010024011425550f0742c4c503903440b403010840070030940ca0170000700a045002c0c045a400112040c0c030343c00100c0724403080c1d2955038034003000300e4001a0340008214030701201d0351500d0141c500f21031150300d0040c200c400342c2c040168000070300c01d13880c03c0c000e524050080d180b1a6207 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 809501267 1250 809500017 809500037
    0x18220b01150e0105040b130e011205100b0d030c14010606050432190b0307030b04060e060f0d03050c010207030c03030f0c12020703020a0803040c1a040305030d0507230307 75
    0x7095079020102140b150010b4001c100c14403100d00c2c0100948403201369200b060b04629141c10f10042141e100b41c0180c0b03051b141c1d003000c00d400e10800300464021060402d1007000401c25040128886e20b200d400080d05212188a00b0300230000140b503c841d02108030703802000070607100c00d4001c3c10703a80148101c0324070924074501000e41101d80d8000c02080c2d0070150a06006003101403c0c0301d41d020b071018041c100a00e0030b1308002642c1015400071441071840e80e4001074030780d4146040008480e07894005407131005c821003c109407034442c110303010b9946a0446880000300c0c1546812144d510030400b0312200e550001c82c0d00700c1096080b484005041d40300e0344013030150315100030034401160b100c1175060300000d9588411445e40c0800341d000300715450091064425541c0642c03075000c3c40344d0003501c00316061040072100f009400701c10380e600c000840e00106541e140916540300e040d82e80c0150303c04440c1d059030340c40105546600420076503130180040f03449858001e005500b100440e420486882d0042010390700 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 809502517 1250 809501267 809501309
    0xd06060e010f0206070509130216080d140103050a0f08130605270109170703021c0204110a080a2d0504030f0302211f08030405040c050918220b01 64
    0x1e0807070303c220584d580b21b41c105660a01003110380c1c86941c8691141e10750801940d030740d040c030465542c1901d601502005a4418070100c1d02c8040350190040d500b92082c0242c0103000081c1c012902e074015541040140350000c116090400c682d108031700d8078000400e07040c440000e0303503a00040078040d101c21a241494411100040b2070058107001c50105001644240060054404100da10519040010200c075451a126804900d04507504440130400e1000c20089008600c1c0034050000c44030a4800c3c8181011300800c4060710850010b0b281480181d2a56485020110100b10003c400d0741c0081040704d170400303c1505180201000d4909400051040c035103401e000e4002e0080725400f4048901810011008942d075015244c8090042130200c03001c000901000c0b20f40d648954041d212000140d5130300c1c1c2c0f42004120403500140c42c0e40c0107202080c0104d003400e80c1d030b207244c5c1c421075254445460030719a28602c0302c18000320301c12601d0b03c2c1002507401c0c46090001c3d151400e4140e820a80340f40d556191101 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 809503767 1250 809502517 809502523
    0x10507030504050c090a0204170718060f03060f090c090e0610081e070803210603160b0304050705190518060a06121b030e061311010309080d06060e010f02 68
    0x682c060103030b92100020300c100e0b041c00c41556a000841030720060a09445094030301400d400b40c088240c050780001d006120810314161640d01030b20b0301d900b081100340d151508035803080d5110700c00540041e0f0703250910242e081090b0071024046a0180b81c1c001599240e9854800a00601002c50007521440c00022906040d501800d02a0782d42e0000400c0e0481c4e82880d019805154204100d05a000314880040c80e22010006461190405181d03500344011001c1004008100102031034401c2d44583d404000220072100c41e107007a1b520b084d248550360742d01c07418403d103084840e51106402c0b8046070250000c0080d500209000d5070b80850765000c04216168030080c17480c10603181c503540680b80071003c1244034040c0e040e034601e072000c014000c916190541c0b90444054a808400340c0031035218001d100341c040c02408056400001e001d560107600710941c40740680c96140390002418503596100403070502840c0c005641c4c1c003000404080c00002e48070302000300010220305425021488000d18001658004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 809505017 1250 809503767 809503771
    0x20d09080d180c0b0d060e0106091d01060801090e0a0f031805040e190f050303010f150c050a0b130b0a0b18040b04060b120615190303021f0b061b0105070305 69
    0x1a03d055001420410031041c0c075480b00c9084500b144e0b89910001d501c1c2c2d40107001a0081c00203441c2c21854903c0c2854a455403066500f40032686180600103100440c1c001c04003505541e203c450005060300c1c080070003480d02d40445c0c0702406503041400d008042607840135000e440403c50707440410341550344009100035035040c1192074001d5004440a080400c2a54580e2030743d19000c2c911b58052009162500c5007540c3c0203810a07419504844420b0200c202441d0400b18040c2c03241c6801e6001c0c90041d20b840b81c40750344807000206080009000b1802402d07844041101d140d80140707011a072418001d103548010400c180615010300045203c03007003828000c940300ca200c3c0f504103403000c0095580e6910b00e001800c070200301940c0306e400e107100007503111810048544600403019000d4820400f08080120052600341005103041e6078420500000754041032031400f59012421142108822410b010050040300b01801d40040011950301e0341400358414108010b10340c1e01c001c000c2500c502200b1002c0e5041 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 809506267 1250 809505017 809505023
    0x6040b030a11040504080f0a03020d06060807020a0b1021170a14070203010f0207050d02010b03060606180a0801180b0f0421020c030714030f0f061306020d09080d18 72
    0x359400042e00c2e410301380c2000d40c0c01441000941c1c5054034525041c01c25800c401d220f0800030740d0108a0b900b003100030741302d004098221802e060f0600e141c8994000e541d0000c13250000d00030034030744001c2074a504560740713020003420064101c1c600c050020101400010b19510b01a90780390340c0402004100b407181000c0742c1c598034a03952804618034011581c908268030074541207805660364008c80c0c204600f54406460854895000752960180c0440e0080c20f44589521792403081d08260140300c03150352403104840f0250242e0341810003200c010000584d83c1e0807103610a0009500385001c80114002c0209410065841130385481d01503254000b018400ba81d08030307001000700b442d41403031483c2a010098003820072010349c0704441d4840400000f090604070590300007103245010801040007031405000ba104d021604000510f030741032074290381c03030703550000034015812490b0310300f0726001840744680407550007d800c68401d100c17060051610b005c003640070600e1118a40d1030207000030040456aa080031800e60 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 809507517 1250 809506267 809506283
    0x9031e052506180b03010e011409070e0111011508160f08070320150d0b06090a030209040f0f0c0e0c13050906040e0f0c120304060c0813031a06040b030a 67
    0x10402500b070368044582e0031083d0761100ca20000141040d0400002d5020307001d104461801c40d49800020a080e807040710100b82301e580c060f41005091544124002107001d000d10b000418012129425070040c01c9a044040c51803992181c00b01c0c11140000f9992548002c810040840351b40ea46820650300d1380d98007400710140c010030010000b241010240c0c203848407a600e00e0281c40100500052a00d940400350a101c1120105644d40100d00a10030380300b4421090790107030b10308209100050a48032444c000248517040d0800402d0070702c50800020f102056100255943d007680c0e509004990b41c409100f040e201841490005000c4090181610300c0f40052040b42c00d031207810041000030b510001448542c20a95400c0d6003000c0f08402c12100c1d04020084000e425032440d01424000300380c44462004590368070811003000b0165004c4020f15026030896142d82c6c842c90440c000c2c000c001c21980c00070340b83d1080240c60280b03007442e0b010031501601040350700700400d80f80f16091645546100d003000d07052034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 809508767 1250 809507517 809507519
    0x12c06010f030227070c0209010f032103090b0403090e060a0608040b0714040e0a0f15150507061a191a070c030f121413120309031e0525 60
    0x410194480190000b1400301d22040706485640c4201c40c0e002110003070005070046e0f0b00c4805505111100b90301401804050340c0c102402c54552601408098000741003003a540604070301214800c1d80809503c0c0d0348250101c51505013814014503140d4140552040b604c1241c001c107265180250030076003116090386503400c481d9120344524100480081c80102441215406990029007003030060001d0328801c001070351141452041c10301241c5180340c0350380200e40360440403012244400000c408865400b0f9616003507610411048410703000703511005010a0400ca40454513082c5101c9001d80c200d07042e40e0040a002c560100300704004a28850031074422000d05140c1c5407852644c00610285000c0c0420000456076556440d61b4654001c0c01928581a20703036806c48202da111195500003000c00e01e216041a03080d2090040e204070178440d203004a10301420313001c00c140c0502010002560400340d144003103090241c804082e40c02d003c20403181d600680200f004029100000400c1e40e000c014124a101 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 809510017 1250 809508767 809508769
    0x2c13060207050f0d020d170907120507090216030305071404050d1406070e0108070c02030c0d020103140c0919140108040206040312030b1302120c0f0903012c06010f0302 74
    0xa41c000c0710203580324001e05440d50560303401000300814030000703a4001c00300138100c65401440e505200c041c114420318008280a0017803400070788041503e0a84500c0861100a4940113150404583c041740003e030020401484584182201d000402e000362810f01c07256413820401c4664074400d032000d00d000c10701404103005074240150520340d800d1080c1c146010700d00c0c0c0d00364101c0c03410303004499400000d44d0320071140359139507800400746400c1001e9050a00010340716500003501c520480312541d000340c540b00c4404066a229810028035501c000031100107905110348a84520752041c08404e0050900d40c9030785e01984110594102101c0031104000301140411004588a080c050400d1703a001c20284004004644a42c12014800e2040c0c2c0303000540103040424070510b01090070312150301b1441031000710019020038288a40c8523000c010307420b985401211030318a40d070080c402c1e01d54040d0700c0c10130013030000f40b01400628050820a00150015120950103641d40c2000340a007005818106d0740403c01 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 809511267 1250 809510017 809510021
    0x30441040b09131518120e0904051216020607050601081204050d060507020a0b1005091003080328060b120a02030103030903060509100e251202010e0409020a2c1306 72
    0x2062000d000049100c2d5001242d0617145880c14205403960311600b8440541c841e000b0320842c0203080c040d1654211498580c032100d45030619568412084400000c0e01d800072100070141005680d070060645403940c1850030841d603180000d010300e4100340b14010009207424000743c02d0f2011144000d041b40c54108240d038903c0c1c0606400340c100c1055125550303d40d80002c00e1044050310991000c10040d030b1080c500801c004c0c010101404000b1040f024500c1170000c41e01c500112035000d104103581d150721030079000101584104800e80c4559051a144c00400c01c15100d0006100140c580e0700c42c0f854a44070380c88004101e1000b0701c0000c01050041c0e030101f00049668000d40e0b030040c1c0440903580200444082101075805012118900781c20010300e81c0c030b08035003911802503103a010302c2032540340c207051000303101000d00002c1000e0f050080556200701248e81e1034104507401c5601406c0801c0e220380c0d4881c01280c40440141c01e22060240c4042d254518010340742d090700c5100001140d5600d0f0308541c4540d00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 809512517 1250 809511267 809511293
    0x5090a03030b0f0d150c0e100813080f0406030501050a0f05151e07031d01021e1e06040c0b0304050606061b0d11010c020f030441040b0913 61
    0x1400c4030540c01c1d03c2d41d5641d540700f049080e50303005008800ea5810800010300407108a030102000340568038100e8030041c2c840040003000e0b06c0450a0900ca00c0d01c501c1b4000c0704000040c000188a4000010024a6040b119001e00200d5410380c809001507600c0e08104034035209a4040c038620101e80210030015885c10b183c1708101680c0314009640b030110401001d1407285441d0840c541d0007040019a9020554085480b612050b140800ca614a461180000b500c80f0040e1718040d0b448020102d0200c0d4210741800f0007890b403901601e0000c0340c81a0106800d4032103601b200d084c0d038078642e1514001039040400d01182c2c03185500c00c002d00990b0369460b00f000360907004011950205400d400a0f0403010340308001007011030000340c8131081c581c001c07131000a094511075102c03402150803040003100c01000000c20340c2c0540b24085c130040344204000005030751804209222038544001c000c52410540e882e01c200c1e00500c001614217001503400c07403050051056083c0c03500520f484680c0050800b050048503102 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 809513767 1250 809512517 809512519
    0xc12012702150a27030c0b03100b0f090a0f03020a080604170f0f07061d01060305070509071b080a031401261c030209180402091801060b0a0f02060a05090a03030b 71
    0x141a40201e0b40c81800c940b0003600341301d041c840805009005200d08000400002c00406100c203256191180a0266540841c40703007050b89078010402e05250f2281100b5600090381c0a450020595603800d41202501d40724402130740140301c2c3d4140403500c2e2001044c51842075800048140007008011240b80d040c0d4003000f405040b0a00c180140d90b280701308a0f006021b483e00444000c0782100070711403c44050890075203501070302d0303140c203a041002607400702d4240100ca20840c0d200440d561800c5040d20600c81c40c0d032580e03480f8880044100300b0031655602030441c1e1425543c2c10000c1d07100c0c1c50340e441007144081c0640c401d484000044000c0010850059207005440c0c001a18080405000003113440302c1101800c0020a40100b080720090606900c43c80d00032206014103112803d040c0c0214241c040041c04841400114102d0040c0600c2e00750040c4009059011400b0356401d04c0c0035005020034040e584110042c05102d011810b81c1000c0e001e11405003d080010340054489580d0a03001820980389035 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 809515017 1250 809513767 809513777
    0x4030f0e0a0303050c0d05091302030a0b0907020a031d31020a0203041706011a0c12040b03061f1b14060a15120305030a0c020c12012702150a 62
    0x6880380c0d803100caa40303070001c5209498940c0c8400c501c0d5060780c1000b0207910f500007000014011454142c2c0c4044403941402e103096001a504d86844018070050301c0c49400f0190881117840500c40842c0d07000031469000340c02a43c424410168980240444103902d00c02154003101c0480441c95100c40d0700400f032000e02c0d89000a92584481c82c03040802d03070b0031900e54000941c0000c2010025a03032090541030070102c424010f00f805604200341d40c5c280004001c5030003004403002c951000122410040c1e84000400b050085480766501c4107241d6440d442100e4640c003c10f00c00201003c12852018101c00b014082d4942d2101e0744062042540141d0340a0420382c0c0d2030110401e002c0c482001800001e026420035240441c9006992402121080440d885800200550300040010a9000060320b4210b44004d00c0072801004109003280340034aa010340c183d03c0110040400c214400c1580034801050750381000c00e04400050018020445030b1842c040d4020480352441ca4000444500404881d0a41d00f00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 809516267 1250 809515017 809515037
    0xb0d0902030709050601090807210302070e01080304030201110c130203060d0c120b0106090b0403031b082802070302031507021c030e1504110108060114120a060b070302030304030f 79
    0x10b45460096485601d00c01e07990701c188802c55a118107500e019108090040c05140d01d4901d01c05440c0d05d0040807018018610b110b080c040501c2440344070b0080803040e0031101156103a0060540302c1c2c0c8144000c0f80480e02d9901541803440c1c0100e483c035403400008140d80070041c4450f10f01006580700a00c0181c1c0203000c0b440e0031000a0340444400007901c1c003440303480042190707841c6c81e104250042c1c00c09810700000702000c1000c1d188980468041c1e90303240c903101e002240d000440480c10a640c0c00c005000340000b0500c0880380c1000c0355010380f018003444408180c00c1d8000c4041e0b071501c1039400040c4d016041440c83c100d140020300d4034036800170000e20444a4401c8803028030283c3c441c040b40c01c80c0c00a40c441040e842d46540400c64000d2280c04403044103410700340f0b030303032681040c1d0042070016060100100000d042c603801503441d03130030150100504690b00d205411008100140844440110501d00400451010103003001e540b00542c1c150011895501c49407002d17100c0421000c0900208034000701 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 809517517 1250 809516267 809516269
    0x201030c11010c030b09070e032104090204120c0b040503121b0f0a03031425031104061809020901140f0c1b03010c020c01020601090e0f010603080301050a090504020a0b0d0902 77
    0x40783c4600075000e554005a10038480c410082c00e11406001c4504020080d0001e01b81caa40103c5c10700ac825001482030031081d220b0f11503100c181d00030703503014440c0584040f4000998111000700b4000302032103800d151047c1070702d030007075454103004900500d41c15501880700c000075624488010407422004800000e00703103184d40d81e16494401c0e00c444901e00c50700902e048104140d0180214003081400f281c00030380629210481c2c3c03031000c054030b0402e913007103003040380080055000782d200303000301c089003840503a44680300d8001402c1d0840b0100540408801079100250111700e5200b5a101110142e40c4d4a0280b40403c0320b25091b0740105d401d03401c08842c10001c102d0315540c10040c10250995104002d1142d0300c03410704160031034050700d444800b550001500c06009a901050003415119105030006204000940d4107140c0344143c0c05121042d07103458004000d00010030055812030300101d032100400e50700d4034082016128140c2c1d000f904060035180902c86082c40c00047e04010340440000201810301d50 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 809518767 1250 809517517 809517521
    0xf052b1112010b09090c070f170c0d1809091410151d0f090a0b041a0c0c1009020d021804140109020102191103060c2d070201030c1101 59
    0x20550010512002966086501d6144102401000b44075285400e184554010940c3d4260080c0109103510340007a5800802240401000703103a070704581e070149141038002d002c08440d8040b000c00c04d4584103188542101c0f0b8424400c003400105844d120f0b2401078038202031171014202418080380d203031b081005440403c0780d0810a45500321010140446c1d104000107104420100030b0700940d88849520864401d0440312400c1541c01c018010200b6025a60706940301303043c80c50900b0300600546e07200302400700f4405411300c80074806010b40c800300d5841c0c54901284100d885519003103210f0740c02c0145070202d5149180d0004034031500281c40c908205945500180c2e42c210a05225004461003105000c05c1c0003880d80f20484900f40f52008018062003a00042d6603142904100c44c0c4010900503042c017040302d4203000000904018044450170300304190311407003d8005c03201c540300b09441842e0510040c000a6100300d449000394442600d8184141c0046010703114294103182400010180419440824 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 809520017 1250 809518767 809518781
    0x50906120d0e04061a03060111190308090f0115060f023307031a060915030702060403080903040302060301030b090708030c0132060d14060a0e0c010f052b 68
    0x7580d2441c950319088010042114016081404d0b84002410a0700411140350100e0b43c102000342012403c0000c8010110314060b5088514511030800c804400105a0130a200d54010104102900e10990010400b20300320703204080200501c40041404110103030007000e0100f1104a03c0c070654400c01c0000700c1e11070a18010100008121491400c0d1441c16100505581e410440350300c1e0903c60040c000c2c6100400f07910180410b44910700024504030103030f5500c004102c0e0341500c00525526860720a8001c0e4441a00b00c0301a000b2aa140e00051803003d004000c03101501e5004000a0541e425500c03120703407401004100b03000c03500c180d07040842c0d4480d0400190154503103410010818161141c20b6880c03122401000310b00e8036044000a43c56240030b0043d0660040040d00c8008200c030b440d050003100d44112540d01c540c0350041005000700b004454003e404170868850448248450000044844c2280140803100054040c82080d00c500e5035100c492224070711202d2540280560f4403c100704440303103 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 809521267 1250 809520017 809520043
    0x9011206080715082818050d110f0a0b0406050a1805030a1103130b0304080f07060f051e01230415092009210a060f1a0a05090612 57
    0x40c007400e0f03602e42c1c4802c0d21544003091115041503280d183c9001601d621141260210045e1104104403038243c0c44022000055040b60072940400b00c0e104000e07024040d85000110350380a0b500c421407040c0070005018000a40c031800c2800c5c203a0311a10740c0001803101038601c5000c10303120503142800e88001001e03a80901c3c010009117a80e00304c0520044c060094140c0041604e03041880280d40800d030701080941103a84003000b995581d40d603842d001c0c2803403003503040710381c9440c0000c40c40c0d8051052070b0f40000482c01705400200110b0700c81d9031581a8040d007156400c0e1440c10f840005000c0e981e206170b40840c1c4803803640f00204210314444c001406035030710b0341c204060441c565441048581428000c40c070202c541868400d01c64032540100004512400348070b80c0c0031341c10300340c195540488006502d10210034100705880c8000918030701640900f69628201620301d0819600fa5840c42c0044013103103803510003c100103481c5281c882403010703060000700707580e0380310304048250030010400344030140415078 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 809522517 1250 809521267 809521289
    0x4020604080a112716030e030d0b0405010914040f14030d0203040506010605030601090e2805090c0a21060e060f0117060408030c07020a05030106121a0c090112060807 73
    0x2c030350350130b000007007440080036107001c040802c0720103016030040788443e0085240300041892902501042e0068550380780166118400000c07980c0002e01a0b5022800024040b50280450390381d5006c0d500c141c400007402c241100d0040d50118000800c60390f0300c0b000c2648900b129071031000130340c54501e0450b00020302c001c05a079000400c12041081c00d10510b40901601c0c1085403e504240700000e140c2c02080c010f020a20a1310804505c01b01c504402941c011103805c12503c1542044001d50302c003600f02942e9145091140403030300c658034645009117009543d01c4842c4540c0c80201c00c4074520820301c07074400607500325036103c0c014100e101707050007003512400d00c00c08001035079403400101c2d034504003103055044800d40101c8140b01c00120b0f5503040303c0d001a811580d60340c0ba40081d000148500c5059880f0f25032540c80c103040010428942540d154580d40200c20100c0503020410340e022020b40101c9980c1856142003051114641c001c801144000002c50700015503c2d842c0c03005c0a11b0074246070420000c0350707 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 809523767 1250 809522517 809522543
    0x2070e1503010e0a0b04020607031103070c031401051b090109050402040e1b03040309170c03070305070816050631060203041401110d050a020111162306010e04020604080a 75
    0x20400b4003c44001d40c101c04002c001169403504c62046100015000a00c0f46400040390820b01d481984c1d506190780c96607090320742c3c40301d50740303440b509601c601e12040760001611815a84581c406102d0184a142030001c41010507822010078000b580c42a030f212414010085400b04242d103441c806013000e00b8a48491130045d0810340051210000e5503100070141a50400c10800040e81c481074520440c3e695880e1100c22408051001e400c000d03400080300d0300352050a400006003e80000d00030211120030f81aa5100c0d11028016505007510340030b01034009a081204111104424500810312070026041c1a651546180c0c82c0a500c500c2d41d2001c0d0040e48003140030b001c40529451300032070595003402c00783d00e2180a06d09030f0342c44540800002e014048007181c80d2011078000e400401541107100f43d02951a003076424000102200310406480414002c0c8100c040d9624005601d2580301919006091a178a07108445540341402801241c0202084c0000502184100541c211186c840c0070818894 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 809525017 1250 809523767 809523769
    0xd0f0809071a0918150609040e03030901050708101d06030a15020d0c0c0f0b0601050c010905071502160e0907030b0406050712050c0f210106080a06080c0f01050a02070e15 75
    0x30018809040d04400101440084c0c1c4d9a0110481004426601c1944402c4101c001800401009e40c1c101e00340d01002042082c04001907010030b00c070711100e0711901010b13120240d0741d8a01c02c0990103141d0088084003030768000e0205201d012640034000034100d41e01c1e102d059441036011108141c80c03008240d008650740011643c5030080b0300000929140111001003103440310030110144481c041c015100347d01c049102648280f0841d038440766004001d2080580c1840c3c2650341d000c403071003501c82c441403104203124918030108201c40b01c5070070800200ea8450030482d001e08403410181c02e10150344121040000051809082c103403107180940800202031803c040090140f02103603001c1d1121500e042c08001032685c01d017040e034820090401f21651508984149112900d903254516144004000300000301245c1c000020752084081c00400d02265039902d06680d40e82c1d50070061103a104d081c5098503081d0754801c6004c1c0101d6401803044a8945aa80308042c0b48c50b001528200c0d199400300180c0c0fa01 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 809526267 1250 809525017 809525029
    0xd140f0c01020a0c1202030106030b131106070b1605120f0106020105090f0304150908010e0303180f06012c09010203070f050903030f030c0c010509100c020d0f0809071a09 75
    0x140300d0280081c00811005580e0300d960360700d203400307842c0c6035122558880c419910258000070107580c3c4021200e105041850074507104c403c02d124100c94400c4141c104040905006c8180e13600704d0307401941510f003603c8081f60300d00e4048000c8200e204120301480020310401408190500400480410801c6541400b030000d083d6400200903000d2644200c2d080c054070900003049608131807515041000c80d488401c012542c000c032540c0050030b55030809070809920320010005502403005d0359081030588030183d201544486400554074070a400400042280c002404103101c151811b28404519050440c10101000c00d400e441c1240540e6012040140b01ca0f0045044016400103041690400c44a9030019580307104400030301410100c0070001c01e001c250f00030241c1c0c0380103413218002d022602c0e1221203070313079150014064000c407942800200c001c00350000c078481c800ca5005039500032095140d42c0040d21501005040180300c2d2044400000c0c013070211001d400e002c0c01c110840b4554510110080180c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 809527517 1250 809526267 809526283
    0xd03270302040605030303130809040e0f06060f0901120f02010e034815190201050a0609050c0732060405010f05060108221703063303060d140f 63
    0x3019501c2042804940030021008c3c3c603032154042400e503615030509000c034002c1d00040c01317005454030031a508003001d4840030459612414050702c0107444060f4550400a42e60401c0c0314102c0240700820814000c215030100a1901c280181049902a001071003c130307191000b42c84440240d045541400003060044514105140172800ca20791042c0490403003030003001242d00d402620071103040741400a01d030314000c20344207858108800405503850300c1c84041d000e048104c400c0c040d084c1c0f6160000c55504824401c03d8011044c3c1100b66060034540e030346d00c0d0410b0030458028940881341e6020401c59212424072694402c9081c0e01608007400c0a140c10350079208000f00204005041008000480c0d9000301000d038080742c1c14180c540300b003040780c84000644100000141c0010001c00301c0c0c450140040000f140a080141d8100c1c0d42c2d41583c85100d010549011030100181982801810f500001c0c240510340005005016081100340ca90b03410b80028a0040003180580280741c0d01115610203100c600 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 809528767 1250 809527517 809527519
    0x90d020615060d09020d0501020c0d1803030f0c0f06050a0c18080613061b091d09030a0e12010c1701060906211d0f2404020d03270302040605 62
    0x9031901503040001200c50050521060000381e8a034131040070b555074500c13042d9505801030000c558414000c0c030055107843c250700d07202c0c01045040d00c41d035280e89401c03511030089039010b50703c613040182c649204443c9441010340942c0c950752115982c00118884d8800c082c084c6600b00c44c0094000751b0040c0c0903007400c91190300c0d0490300582100412100c803000c10944d620800c5481042c00c6036545103499030007080391a0140980b030000650018640350000c1284040d1080d10504079491280d44440c40d590040031180c21401e0340090025010382801002e51609050006214120540e1000b424908580384c0090000000700700b142c010b2940b00d051841c00b400b4200310329100514070300b4890040c09002daa5140f06041e048112540c01d0380000c4c0b544022a580030100040904280c0022400c0d03a56109a84041e9140108050340e5018242030003208052401a009415039958170303000c0214480806005809000700b0201c40803034900201c208001d610741c1c10381c1c00d01c6414117500510044405640044e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 809530017 1250 809528767 809528791
    0x130218220b0c0307020312010f03030e030a0c0504020f0c0f03091503100e060d1a0a060b1305060a0207050319110402090315150a030f05010e030319020706090b090d0206 74
    0x2004102510011548642c00030801541c9407140702080340766202d80348401084120b440c001060441080081340308880c080c0d07444070351980c0c12000b015114007020038001c112254001c0e080006080680207404c03005076400c0c4603814502919003107820700f1814181c2000e150030020b1119511324000c2c045564900b0041d4120b4290b10b80340702c031404000c500d406041b0005980c140020120303a00d01821200c0726900207011110720710016400400e030f082c107a801e6401d107420b001d0003142c210483c100b902c00030048050085103d0340351109206981d40f00c1c2c140c043c05c50150010100722a1020090003040b928924400d40040e031a908203001c220014000031449507004005801840d07800145183c00d08510300c1205401d5228040c0801c03c40450103040c40d00721071004400002e019001102c042c00c1c43c0904002e2003042c1030342810580760700c02110381c0c00c100d01d07200441030300303000541d8060700050388611b1000842051903200c0c07104000d01124040141c0d40301036688041d080d418402350760401d90342801 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 809531267 1250 809530017 809530081
    0x105070e0102120f040b040e0411190e100806010b0301030c08150a18020301050c07020117040c0e04080d02161a040c14060405151e0301080a0b130218 66
    0xb52540c1481448485129012a2150310304c03d11108a40041c44a0b4540a03a104d550718040c1135a0b42003100c0030389807813a6074045170b2424107081c1d000c4500b00d0200101082150704080314540c407842c0180100d80481c1c11040081b403400000c005140c00f0f00f00b02000c003902c96146141145401c44103400460304c50b00400e158080d501e2428017501e0700003050542c081400d800080d4000c4200200d002c000c0e45c10f40c01e05003880845224140104403090007030380e900650400c00c5869603400801520300909480340c07018100421140e1445241c3c20520032007001d85071110010035502640c11403a1030f103c038003403c10380c140100101441e44804161400d0460fa515107415141e00612a14901c9403000c1c152500004a400f0355a00007100c010300001400701c9000c4c40e002c040c081c20b540008004426584000120001000b0b41e14140c1c0e048910100c02440440c41640c1c2d40c2c128220042c0400e01c901c400030280c240140c0d980300544401001c0c20150040c90710703100007100c4210024003c409401c0d101484 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 809532374 1107 809531267 809531269
    0x60c050405120a080912071d010e0702061302011107030204050a090c061b02100c020d03030519021806030405070509010306020c0105011a1801140d0501080105070e 72
    0x903203111040c2c0c84840181e42c0d43d00c04030000382032110300307000c0300d515442c041c2e5190120a050505499009a0782e00862544100c004505040c0708510001805250b254101281e880300e1035100030a814100030358042940c45031298041d0400901401c0b6140648042010000440d030250042020389410880350004040300d400846018071090400a80d05219002c00b01c03e504000301500b055448650811005980c000d201405018007a551040965900c1c5000b21031180a0b03180410f861800c03000b03802440008006440b4014814485556003106d01c80403100c10750802c0d03581d41e56a4441e0308002d40340600943c4102e6210350a1000441002003a802510721000c41c1d100a00160340c8521100e5004d03181c0c5550452000c00a10040d500401c0390310740d521000c28181806452a00c1c1408134251540c4001010315000b6165001040340b0322091041541c0602140782c64004c0c040840 = true := by decide +kernel

theorem cover : BRFrame.Cov 809352517 809532374 := by
  have h0 := BRFrame.cov_init 809352517
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809352517 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 809352517 ≤ n) (h2 : n < 809532374) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
