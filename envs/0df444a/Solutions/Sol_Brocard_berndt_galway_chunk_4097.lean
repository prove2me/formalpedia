-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4097
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:33:43.410583+00:00
-- url     : https://prove2.me/submissions/635dbf00-31e5-4cac-83d7-defa6a469f86

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 736690647 ≤ n < 736870503 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 736691897 1250 736690647 736690649
    0x70e10050d08220b04030212030a05040501080405030d090303050f151012270c150806040e031c060f05011e1110020a0207090b01030e0705040e010207050a050106080f060c0301 77
    0x400c01507640c0390120fa2102c4443c0380503035012104031614090104910482000410680e40212604c0359076a6100703000743e550707210358008900011410b020400c40355006001203600640b2038415a404e00c02144940401c448480b0f0058001079124824460000301e0402c4454203c0c010b000e0b0209418808804502560f43c90b00342e000400110381800c1107403000710750007414103403581098070705001400b281750458501014001d44100b100c03500001303082010605240982280c0341c03102040d41d0780303c10401c0020848c0c521301050501041040c6028840c06a00440b140141041d0003e81142400c400d1403456050b03800150501051080c0e80342107031990811320b4440031051400300d041200c0007042a050001e0391419445041c0041a4411a41c1d004120481540c00408003042070130040ca004500707036410b6015001603504001400e01035400d0903088030390640101c000251920300c031a0b440900d8119090300a403560b941d0b0768814800e120701442034a410640280041c00c0d030381441140d0038024481 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 736693147 1250 736691897 736691903
    0x60b09040308012114070501090f1202040c0c060f1d150406050a060e011205060c0306011d03031606060302130c020d0c030e0a0312090501180605091201020705070e10050d 75
    0x104c080481c0320085400b03e0044901d5001c00f40780350a03918007003100d641d0810740c029a030205945110100300c55400c2d008082c2101e10842d44041500e003d5000c2c0801010081c202c1010007005d150750740040f401a000e0514615000c040004101144040360400402580b050b601103401004c640071407412690f4005800c5500304600003000c2e203640c5038100c010800c540c8080c1c070032041c03500002000c285a209030700d0a54000c2c401e480207941d51000200300c9200483e401404104215010802e4001000088443c80030250480746800f5a200040400382e221120440c4c11607144c000034800c6040040c3c5103421041c90304400c1c070000c0075560001c0e40301d003e0b04211100304810180d1560030701d40300d4035940880840180c4205401070722400c1c440d8980d4504440403011030306848000516522035082c2484859248400700b81c29420480200c0356548040d20080d0721051031007006980c1c100a100030440248564000d0551510340b0144240b8100001c201000200d0f48807400c0040d0f0700c1340c030024001c582d4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 736694397 1250 736693147 736693169
    0x3030203060f0904150e0a32010609090c0503160302060a030204030b042001020705030d1101060321090617070305040201050c010603120e060f0f1309050a050103060b0904030801 78
    0x18404011400b60b42e0420140c95024850b001800184413039099400d158078200700046c040c000c1d0184181d50b50b110078900081c041c12803422281000090301007040c00b840400048098034100c8100d0345030075940c40e134011110703296440c0000800c004a020003d80100400e5020b080c88a803901507201c4030741103030310000e4020040080e0601500b4031a40c1183c0142d548540135018509290800350440c05983d1a100d00843c3c684251926030340c00009c0e61401c8860042c014428080d500344c04840010902c82c03540401d640355800400011162240429240b1040e09a16034034404084000d10b01c1800c0d900800600c55400403c4c0401c0044180c001c1e0f220700e40e41400320300d940320b40c40100c40c1d0748a901f135071000651908002104200d004038034001001c5440e900d03820500c02c01400c102d814071a92000000c801030400651203554080c101038000c050102854907499551400c60009039041165a40c801a03a5803005004219082c0305000c0c51100a80e021469071500341c0e0302502503503041c0224a1015 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 736695647 1250 736694397 736694401
    0x118120225150c0606030b0609060609090414120d0213051c0b04020a050d1a0a1e050402030a0b090102031603020c0d20070609050f010c02031c02030d02030c130509090a03030203 78
    0x90141510fa455258040f80402000340d403428070740d4182c80d055404510401c010000b00d509450108107881000d18002e000b070700e03940c40361b594118080030814110304040c003d00440b80d80302d885000150402403038252025030fa44202003803182c5100c210350401c1d4414482850401000d0450f820f04c480b0a951004400c0510385590000424100ca01d0340440d0340040c403410140d0070061851039401d03808042085058950715510700c1202034644200709002c104031105075203800d4000f40d0304001d8010f8000b5050740c440c2c03481900c60300100d241c02c0b5100000c1d41e400005100e28810041d40c100c0d0348486c545811810800c1080190b0345495030201048208036480040e01c0440e0042040d0030070240403441102ca19564132a00600214102e2041c03074813070036900f988100c1550089070071201140c0d00901400131078600654084074010350900300c00c114402802180f105c1c1080e403004602500502c2c6170161207a80303c0e450504403503000e41169024040b000184444d40c00002911000c2d50360504001d6125 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 736696897 1250 736695647 736695689
    0x2120403061a0406081e0d1218171206010801030b1f051c03230301300605010e13050705010e04020f070c0f1e170118120225 55
    0x1030a550a0840c3e01c585010f00000b5584800980070a0ba1104a0801008003071422203464688859403e0000420816400c5403182c80c031590055103081c42c00b071420031a2409076280e031140d50310301840d101100d040c00150b4803811034250907416840b801c24a0080510741c1169203118000c02c0c003078850100c07000840b6a43e8101c1d40764100920150001500e01c800c010700502c002101460b50741030503404038283c4521031403401c4c0091840580d00103010400d61450b407921040404001440402c0c003848041a80c000111000011a94103034074080c01c1c0200b10f650502c01004d08800780641504a447c5016418000064005c101075007140c4090a010382d43c202c404e40814081d01c10a03281c4000c41000046010810000040c043d0641741c404400c0c684807500c9106a400e12440c07184000050011200704010404034460380186402c2100001302d544d803541158028480ca221204482c2d208031a0810790140b0790400c41380c4049000c1007050601c401c0301a1700c801882e4018001c1e60110100003842c403044c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 736698147 1250 736696897 736696931
    0x1e030f36030f050306041404060501090c03090f08030c1b07061106090c0913020a08011d03070302070504021605011b110346081005040c020303063c040506010212040306 74
    0x30006083d50321081c11710b007601e880c00c0200ad0900503505500d00d004046441070f44079104a035451503010500708284c1c011f039141c3d0030382904024450309070444c0801c0040e4036401040b40c0301c1c40c402c51032001000c0031400c08002621030010700c10044078541c054410020703940c0d40001d00040444007540e89601c40e8642c50f10000000014007406034000c0c3c400040092640c81c158011079915540312074501104911a0646441b0305c1030540142c01a88045418000c030300d03256000b0102d2140b41841041015615664182944d00080c0034880340c3c00710003050703081c041c3c120740740300c000c500c48902441c90049c105070f054840450040e400c04c0295610102d40d401c4c031203035050102e04c00c40e14800140303035440c42c050001c0c80d90200721200a0b1600000344e0008240c1028040c2d040c0700c40041d0060350950ba00c0e80c050103111781c1825503d4030901c40400a1091a07458403078010080d8144203049125150f03880103001c19034bc409803540d41150b2201c0050304103040044140c0303080d20b602c86408035810900c0010280 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 736699397 1250 736698147 736698161
    0xf09120712030c0209061002070603050a15170115050a0e09010b120604140102030103080901050a0c0b1e0c04082109091006031a011e030f36030f05030604 68
    0x160001c80c1e001d1007080c50740100800108a00c201c91034200356448100b4440c6101d041c0c0340e12009644601010300c80517003c1c3d000340f90301c802070b08000a0174160303c07540e0700818100c0f94000d000302064400e5203100004280580c010300c03048644003024407441c26000c107020841a11445021004402c04655092800e4000d0242503200800820000340710152540d01d4040c103460485404918120441e0010018000e580c1200d030030020140c2424985401540d440d48035040c4002041b01c064045400100401440d80c0111010b15007214203600c1c1503200010035001030440b50801405100800c204000000c150a07541c03016000c0507080000e076070f46010b01c1c2c000c03854416030140d44c040400000306000401c61044ce038043d6001c0c4582001c445503040c070440206a020300054000181c0001d80490303600748000c440180c500000c402250b800ba03c1c089904c41d0380c07880d901348940c49001c4280350811500000291904c03046203a461840d40c0c0240c40c210343d02e65000c090180110006a86913180e900000d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 736700647 1250 736699397 736699409
    0x51908061f020a0f0b240102060703090f060e0f101a01030903051e030411041803051e0c0307030f050418150803031509091f05040c0f17010b060f091207 67
    0x504c2c10500c52501c480c4643c0300b195029820700240e804038900801a51055400c0c18040c0c018116580700c03035000700c010b046802c0c01600ca0090303240710b90b00014054403c00030020b03000d01c09031801142e00b88a1030708180700c1c049001321450828904a8030b03001260707032801d4441024240010074622501c1c05841c0c0d80140302c4d607040c0e07018001400c44040e41240d002948a1446041520706000c441400c100c11034175501504101c00158010101c000390240c4020110312050b9090913400000075401c01c805540300c00c0c51080c490f0008900e0700101038010001d582009168107056040074102268011988040a081001c5c42c0d1206540c0c08400c0320b0300e2680015214060a0b40d689140108030007521a848809541c06454094000354410300d002c900d0f2051030100344c2148902d0280141c14001414000d00b00380c1c1c003104c12410001c2c00d244444041c000601c42c6010f0a0101c0d0092080f01e801c5407042c80d0a5800758004002d151084d080c528200c65007100121441c40144003072801c00c524000198000f0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 736701897 1250 736700647 736700663
    0x2030f0a022518090503090f03011b0225080d081306060e10080705010e0120010c0f0216050906040f0603080406110c060c03090d050a02030d051908061f020a 69
    0x1088420201e002800c0607143c1600c0c5024600005107090303030445022607405002074005100040c584e02d450018001c01903802000490b005c0450300303410701c000d80c044403081e01681c03090811200d510515644601a41000565001403621740b8448a40741d914010025080090250024009110500285c611741e03800080c100b041ea0b44071088520702d010152820202c031800d9020019a0180004800c41910b02c1a95845030240c4110019100c401000c107000b511041201d980410f0039a092082170842c01d540d6480b10890b842c022000f03824034500800c0510307001c1701c0080500294503140342d416000340080d1000110007180c0c0310f140340140096040201a8030300081c001030520b600440c2e01010324580c2c030a03034140c80b11700b804000c180d00c9640a6818a0781082c818942c41d03180c150000b52410b03018400740e03031284096500003070034106240b070250003154010800c004095010410141200c0c001d0410140c2d908040d8001003450401c0c940d034024018558013038007561032081c01129122940f103410 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 736703147 1250 736701897 736701943
    0x30921050304180b042904180809011103040e0c0708120106050904060b07020f01200106060201050a0b0405130b0c0d1b030b06070b060d0204020403020607060f110a02030f0a02 77
    0x143c004030311410fa0752142030f909107401c0d11054903080c820680d000904019940400f0100c01ca0100811060345035154001c1d60b070300203080e1085910340c604d02c0580c07140404555610b0b04100140000d4042031140391541d00074003050149440301e16220743c029000e96841070700c400491400c6591403140c2e600510b40805001c000080051300000581944078048805003d82500c80e43c160041e0302404802030340c000000d03d20341405502455103000401015114442c0302103000f44c2c80c1342582c11070392040005079500d10810081411600c101c42d0520030464040c400d5003001038440380150280d80000d01115065400b00745920310840032106040c031004e03410711042c01c2c00101107400b424070107407401c00703e81000203286151808104807081581d2004c00c9000d41d44400e410301000b0400e000c1c049030019800c02c40840907a407130350007030b004491141401040c030383e40c0c91480000303079850a04100f02c000c0050004100c015004029220b86e44e07086c1d5400d40d264150020b0032840d140c3c0e02d44c0400400450640 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 736704397 1250 736703147 736703159
    0x1103041a150d030f1101090312090507080f2a01050d0b01030605150301030605010801052203020a061a030d02070812180a1217030c0a0e01140c1609020304030921050304 74
    0x80c0d04001d10304e980f5420080007040081c1400c0e242540d400800140d10402c401045000c1d660104500e00d0107a000c6501541c1c0b00e8481c10318003041022004aa5801801c2c943c01c00020344c4149403089085035007074008ae440040c0042c00a004030302c00d4240543d150b01e032903031040e48243d109034003c0800510005c10703c80484400e22040c0d000380800c0d5003d07401c080c0082403203d41401424007880c020102c041009401e5801c520112112240c00c03401c40c0900c1f15000c000c074441c3c6c040d0210307010034462243c10b041111410549425680c11820041d504560420000e054011031030700c021118500c0e039159169075009e681e102c00700740d6a640d030f5031080003440c3c04181c0c8229040f1180b0003e1180c0226840c1801606c0801020700040b2a504408201085014200c07441000701440654040c14407541c0f12188410001c156084401d003c2002d6025160700e441d41145103200c04018140208110300e141440c0d180280744410034040d10702c07500c00d5140ca0a003050421102408556000401c2e030f503d694a0760 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 736705647 1250 736704397 736704407
    0x70f080301060314060d02010e10090b030106030501080c030115050f1201110913050103050705060d020d050403120f02030114060c1c080601301d01020714011103041a150d03 76
    0x120b148040d1221136070004429080c12000c07020403a4050b15621300300c601000c104108100004800d0781040b1104000050146404001d54040c0040351808501581004182032034035410720102442681011119007035907a20540d24001c0e10000d5074200c050078a89404a0f8030880c084d00d50300001d40c40e050808819031070700b1014040316882180c0100c0f1031240078500c0c1c000d9070028000982590848042040b01e0719180c0b0040981032130f485005410a041002c2600442e00100d505401107044448000c00716006841103002000000780b0850030355040c845050400305002010700c0c0200d600081070a86060100700e204c52407140c410643d20039118803100100544816122540032030240203408481050717901001c042c6480c1c0402c0b0110140510a020340584459010118180c0c0050160903210500703000410555001e10b40b160f0481c8410380065003101c8107450102100c0500b4828480018450010110b1200f003690890a079a11245224015602d0000107241d21801624200041617001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 736706897 1250 736705647 736705661
    0x603040f0303050606030415050406091a0702010507030228020705060f0909070801050f0f0118080303010806010f0b191b050a060e030a020a02041e0c08090f01140705070f0803010603 80
    0x1e550240540d40b02d6100b0f10100340801c0e900181608400c0003c0185000142c0c00701c0c2d80203004020100d41c07511291600e0b046410303081204024800c0c6035003002003943d02406115008480ba2904601e001854402d0b20502108120950584e50341e526144645a100700070008c0503003070003480f03a41d40d100752a5014003154001c3c2c1c0c40038080c006002c0084c00031801000454100c07100071f00301e810b0782d000510400c14008104500c25060050f40c200d44203442244031404409000700000642d5254100489a881d22030140e108209198404801380004400042600c02040007142252100e9410144c1914294110b0003130b500d0903003004c000c80003488030002d015089036009210400164034206035164991041c5e00398100560f0143d110b04006080951065459890004811602d49d800fa030001041d901801c111800140b5010141302000d2010b2041d601c050340044000c201c1807240401440742070700010b103000c090040128520b414400f1440c1d072040c003d58010b42c0190360f5078682c1000b8000b0131070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 736708147 1250 736706897 736706903
    0xf0f2821050307030b0f0f06031b03191d031c0b090a1b1403010b07030201060503101401060203160b06030f0114070f14040e09150112140d0f08150603040f 68
    0x2d107185e5001508100c81004801031020301402c102d01c09003c00e010031540003034503c01c80c204d070f611801800b0109000145001d071001500c202950445201e9090580306001c0480c0054003401140880d0004004120f800d825120904001013941e5280341c01c0050102850158200140f441003003d10181503001c0040d100210b00042e0300000171520440d19a0b00002030f06244002c20401482810021000f820342d5512a20011a800c0c4c0c503240070034102041c01c01400c440d5034983c3c002c2034140e0a00040385025009600c000d60420020940c00c0d01e4285c800b42c40907041040d43d03000f0810780c0e282442101140050789000340030390707261517200c0f4103111821105000000c885c038a8140b41d242c400c0e02c2180f0120101c80310b00f41070500740600d03440c094070b0281c680e0340e00340300c1c51400680c0b1484c100351240c0240f103000304000c150b100a0030000070032001000c0317100007500588000700032180c210a1410400f102072610340c0e4a6500c01c81083c40030184c920005510039004020802000881855011503c1c4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 736709397 1250 736708147 736708151
    0x120d0507121d0402090f1c020a06140307030b01032406180812161b05090609060108040b041509060e01060b0f070b04030912050f0f282105030703 64
    0x1484803400c0700d0074030078081e4108600503140c551442e246020b4016042c0e40d60f0043c40382c00c40320981000241c00c02c0d480b0707261a040340c0304501e50605520301071807514000c11040c00d194a810000c0d0140c0e10b0903100060410080c1655004003804a03446030f4404035811400c1d119a9145490b00f000034030512040d4456040001c0107181c14950b403001014444084411410080c205101d02d191212125002000d02c43c1d80c00404420319004a80b01c0c0008030303a1507041580848415040800b400725078500201100c1c0562006010310540d640d006070440e038843d4201c04100c2041d21145000040c0889080c00c403d07943e4188843c000502034190300c0103003042c1ca088000c005050b03540d5405400ca01540d007007000203030000d1210001040141d01d499a1181c82441c0444040b178035a40700050780009042c003510160f22103e49010400c601700300e808070048070320b0000e020424030ba20200341130070601c0444202c45810161201c040200d00c12a082120070341e1044044042009440100203070422070b42070000034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 736710647 1250 736709397 736709423
    0x605120d182d090e03040909060e0d0f08010e06060d0902010212180316030302070b0d06080703080309010b0a05031b0f0301020a02060702120307090e27010222080703020f120d0507 79
    0x149a4800d1442c0c010048000c2c0d030401c3d2800d047c0c20020401e100302561415240c0c01c5110520348140078280383d5101a4990190040d0708000051072980305800548120844000348040ea668601c142c410900000201141e00d014a100403400c100503100c4400d0b488130046001f1140954091f10700d49a681c05904940e291100700000c1100d42c0118407025001d0313004510140050300c402c3c401054245500c1e03501241d0b00380c2d80c2541364508141035109450240000c41840082442801103c0c003d035000c681400505042800280d19050200c600b5043c140040c8036000d00ca40b039200801c0d100e400010001c64407803015100194135020121904001401130501800e4248003580070380340034100640d0369027a103034100a403410800c0f102070603a80740840300091100c2c074000300e80ca004000304001390025031208100040010380071340c0c00070072440e0802602006c0c0800c000004844080b20b40442e0f071004008404404110310440c16034003c4500e02501240c2d0380c1240c0c003d801400c0392407143c002c0c079582c2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 736711897 1250 736710647 736710659
    0x408180a2414032a0408030a030c0c020310021c140603070815041217161b0506040204020f0f0d0c02060705041202010e03030d0e010902040605120d182d 67
    0x14002c0d008150950200c28408658110202c0d008450603404c00301641d0003600d8840e2003255560029481480c040d0720018101032890b5141c01601060b040d030782800018040e065000a403208141c13510b42d031036a64007180780000100c1400c9d040440c0040e446080054108070401150b408004545503802840f802c0750009070402d00040d5a0f07010401402d143e0741c2511196520446041000342c80c1d01000110340c0032050380c3c410244094010040780414ad170f1810355810020b4500d064103d08070741d452042d180702c500400c202144250f0b009a040b90016540e001c060200401c9004800013001d00c5d0320049510090751010341d01220103a0101d80071182c15035580d07907040f00c06114900603403075a40e0480102d140154000c42400303403591401405e490810240e48004802c0316030052241259a450300c02c2c030030640c141845413401520042e00c840700c0c91550095101d42d654a0400a0004c0107980ba10000d0100c1e580c40e040800f401c4c0780c0800903000c0c01e401083d1404240d002c840d00c20070403e14000042c1c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 736713147 1250 736711897 736711907
    0xf010510030f0602090a031a0901110f041e09060303170a06120b070c050102030703091109011a0a020c030d051c06150302131e061202090102060408180a24 68
    0x312030b480700e4800d01e44100d9a4030103000e50403005d03c4e2074011306841070200c00140400c1585c1201400740f0410209440c0014686003981e078405001070071044204406072641c1c1241c000c9809440000c0c21103840c000d000b107007000c0e222070550b00004000d440d0110220405a111801100e41d0f5100d20f5891300300d880c0c103081c2e5411181b030f62080c034681e400b51010050000b2914030700203510054a051155461001d510380e5402e81c0e008075110301c0020703520300c201000c000160004816242050350b01c42d2866040008000b030340d21421009401078034010810f03040080c0300b00142c41c030025003e0140c41288080407400380c41900615250040c5544906044240e07609034400c80040314030340f08546181801c9000c2c1a002903000120040e031506503007d010450044002669102c00c107605a2003042c2da2a0103001000071129009801140b8010031191485a030300003540c0e41c015402c440c0301039451310001240a46c0403291032605406c051411030014403e008080c8035803e542c050315070303883c00c111a0f0f02e0031a9 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 736714397 1250 736713147 736713149
    0x5150a02121b1b0309090a0b1008160c020d081c05070509030705060a09050406030b0702060907030f240e0106150905130f0b060f0705160b0d090c09020c0f010510 71
    0x10802c20244210a907041e80e10000050b0401218107070303803604c0d900001040c20088102c03905020f00780c6494040342541000030030120100e22a140540c00d13070411244002e503000240e0551010400c080d401c0c441559030307002458840942c41070703806581c0c0c1d2110841c00ca00d4207844d001000407030300e010000f8960074080e008550003940014042c0c04801d04220400417283c000640e1761003001308805000c592600c0d5841080003950017014100e856103080d1200a01d0032100604822003600308441c2007000404541c2c41c400003550040c070440e24030020000450703080d0700481c00207400c02e0501250048220040d405407043c1c0f100380c10308000323005d08440242c8581500d842903981101c00980c0c00c24030703091680e00145411032400404500030580c43c0002d401d030b410000e81f010005070002694010840304003c0320108407002100a51098030f052484d521502803a44001e0549407201407034002c0140d20544c075006006408030854452051840c1d440d916490390700c4040f15980390070042031802e070005403d24 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 736715647 1250 736714397 736714441
    0x1060b030f10120515070e030a060b030c04020717280c030e0301020a020d03050c120915161209030c0b15010801080318060708041511010b1f0c05150a0212 68
    0x40850201c4490101c0e6100001b03005d0b10400561a446941d955030511841c02060700904001c140c15100c20201414207403900c8800c1e100e10f10412210740001d0310541504075080d4500780d03454030f60068400142500100e100500c0f000c4a890018010b80c0740c00c0148011410701940e40c0b0038400801e074003858201d00c12880788601581c480e40d83c2e01d02d41c610a8002680c408900104242051903150160300407007800d0382c0c5818290016501c104090307000300222580b200310b1044035000000110710151840f404a0000c0c0d46035a02d512002e0245405610140000c9602611060702c80c601015284074214481e0401030000b0b80f5840001943c1c40004165010048008804c0c200d001c150303400c0081c1c0d944032800845545000780300002e07030800e000b031245144941c1c1e41c5500c0c20036910400d01b542100d81c0c603a51548030b220a134806a24440d140c0e402c4100c00c406074142000d8000150501c00c0c0b43c100841d640403558550201042824030194001d4100b400d164903000b4290340310754950702c402d00407a82c0780b0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 736716897 1250 736715647 736715653
    0x1151715061f050d02040803040e07050a0f0c0f0506010e0108330910020c03130801020c0d23030103060207140d080a11090325062a0501060b030f101205 67
    0x200b152403a00d825442141c2440c1c10024a0000b0128414003640c00c40e5001548540022804101587c110314181ea4400b105141291510504e00c40c0a0700ba88420740c0044100080070b19200b04204d08000680c01c0540c000048495940c0c2d07a1903411007600090007040800d001e0340d12190310303003560000d202c40000d006020500e240d0715082d043d18500100242035042c540b00343c441c2d40c0c900030701905c000c1c415030240201640d9100c3d0402c034005031031009903120701d0241c3e03c10481c0d0b200c3c01c100030401c10360a00140c50320120040c0b803014034440001c03a00c48000082c10001000104000c441c1d401810719a210303102e00d150081e01d840c40b46440e030092420400202d00544006544c0031095844000c3c00c95420407000d0521110401181c0b03012a11840e40310100460b0503058600092041294000e00d643e150860b402d044540b4008003240f8035001e100d00061015500a04004080d0442e0000d4901c0d211034940f47d190000b148188441d007611240a403c0c5c0001002c590508402c4181005a07080401 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 736718147 1250 736716897 736716919
    0x61d0601120218070305040c0e01030818010e03030c0703020f0402030c0703122a1418060d09020301020a080a1b0f0c0501060810060e06060304051c020115171506 71
    0x260302015408503800ca90040071143c519100c000c07000380080c000c00d0346a50004280c82e1038500000b8000841d003140300004101401040012500740440d09a0844518441a00c0f00e502006070780d00e425032440c043d8103020201340415481800075440b4122402140c030400b0150501041c030080b071105554110b2096400c20952000c00d00a0740e201f00101c0d04007100042d400400c0400b03401482010000b10220301c500e8540740602944178022a050420010501d840c14201621a058406440f21031500032040810304911255295000220850300a00207658034030920b04000e01d4488103d03030030010107140841c4807600348910205018100c8490326806030791380542a069815071030038030003101d19640318400856090f8080c411000724504092010900324101281c020140c2c4000744030707500510082c020080803850000d001510786205507082e008010079044224058002ea560758031a00c1c184080000304e660308111050141144038041e46e0880a005240b02c2918105445159000580c501 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 736719397 1250 736718147 736718159
    0x180b07021c03110d0302040e1501020601050111150a020705070603090b060904230c010906030506061902190c05040b0306060d0206030601210b10080c07062016061d0601 74
    0x200e06007440d402800e0800903c2003c4481c10301e050102011100000d03004142000012440d001454100d451901c40d05108100100001c2d40d40d001441035a0411004058040d8040c1050207009000010071a019030300b4a09904410045e41c065402200d4910a400c0d00140d114400e12944042c0c944c00f90103503000752181010807a501e40080c0c400c0d6880780480c02d500312001090714000700002d50702c5014140e44800ca100142800000d03600800c2414101410881155244402c4902130480e4540c1c0340107010003180c1c200d107024248000d645070003440c031031032038240702014120404850f405c680c00d001034180082803540301c681c2a200c494101c0c01000b400d00c014075004024560011041c5030440701281c0d210701010180310a0b00300c801c495544c1e5100c0c92100d080900b4064410301c4d882c2044070b0700d41440003484041d4829407001821691307a40004c80b4403101c02d003070711301420541c0e800000e803128000050b180c150791081100f12850762400c08840c076142c1e10400c401024032920809031001b0380c42c1003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 736720647 1250 736719397 736719439
    0x7021c0918242c0103080c0a021e04060b121305030d0c11010c021c0c020f060712030e010e030703030f14010e04030e03120412021906180b0702 63
    0xa141482500d858844045441c03082c1e0b1408910412040349100c40c407898403010002c5500010b0700c090b40e2000c0d403000608200101208681126840113216903141c070643c0c074550621500d0380e002036102004094510903000201144040d00000300c1d02001203d07507800c418040343c0300c2c603407840400e00c2e00c010010b5010709031280018606400745050740e241c2000700c1101c00440f06040c003860045003c40080e404000c009104d182c0765407515000800300c4c1c4808a098618000c1401105010442e48104280442d21071540d90202d5450240400d91114a40d00c1c1c0409050f54580241000138030300004058083e40502590f600d500c0f400000c0c40c030709207007501c00328050200030104140301034460420140b100c4246290a0080070340070308001003800d05140c0201800c1c0b501c05c6242c070a5020041e410f000d82d41407c01c650480700c00300010fa260402c1e5101041c2d0512000106660303480043c5800903000340c03c000044034903401039038154401c5407100c00c0c5440342e000c0c81201940084d55210003c08680d041 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 736721897 1250 736720647 736720679
    0x402010903140106180603030e090408090919020703050d0513080405010c030e03030f09011101140a0513050f0c0a2c13300509030a0602180d05010507021c09 69
    0x300c1c00441d9075605c8150300740f8400b8102c1c89402e101c81d40c0d5030f010400d059000300c03010325440048541c101141083d40310900c0d01d000da8148148140300c042c000c100c0000201707900415581004006645600e00b40c140a800c5401c40620705a00c0341c00d000000b409421411200101a40d2121450341070030704050044038041c3d8031840031420300c0310680020303079039680c2040078002282d00d00303c807165503038806c0c0001040d08801c60362408590307041c040c070b150703001054002040c0d012a1801c00002e03255240781003041d081060031005400341c01a8a58100d0503c804500500c00070b00c00d64241c806240c8e12903c002d409500c01e0300c2342c041207645600703044002d4503440a854201442c00760540b6520b4142d20f643da15007018440051440c0c5191180c0c1c180b031030140000d004922940e090040c189849600031030744680e801203008004541c001000c407680001110700c081030301005070038030003425000d240c480d00030902940d184000d442200c50403041c84080c04103c4ca00c3c40d0a43d03944900386440c3c071490788680c03921 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 736723147 1250 736721897 736721933
    0x705090f03070f09110a020a15090f0308010905011a090918071212030504021e040f14010801140702031e0906030c120703020a1b0804081f0c02060402010903 69
    0x904100e49075034100540005064000280403003107142468020031100e400f06605604034043c01440360f0a900860110800c980182c941808041c01e01103c2c40141585d0000400f0410395085610a241d40b14041da4161800c00d841080980d032101600420000400481280b505041155490307900301a4280740e0000c21085411010b0340f86c2070400307801c1c654580c104134002c00003103014206201040498100085007818200700900f0944c001c100c00d4280300d98038140d8400d4901171402d290310307541d2000020f084501ea0411804414000000e140786080c07062149640c03c0c4108002d0203000c1c1c5d04014090b080c0ca400071403034031010a41955848121422030307115510140032400341030300e400700213501c0380c000380c0615075481c1e56070091004809005030010082501c14022000004c0c0c010604000c42e585011382d071a10280e8034a0300c3c4800f40300b9a04918040d02032034070100402480100c04c00f8810702050070a10040c000008120780e2600211000790005001c040100041001701c15500f1001e11 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 736724397 1250 736723147 736723159
    0x10030f0c081f0506221d0f01090506060405150d080904090303050f09060f010b1c0609020702030d0c0b06010507150504030e01090b0f0a08090708010c02240f070509 72
    0x650703070340901c0c00c006079558016861480c0d582060240e019500c541e40c0e0000040b58500b1048203894051003007880e400069204803580c88041d815811300104c0020b81c01074200080f1800a605100c0c454007174035091008030380a1290f0340c0491414503084c00383c00e01c1540e00603881140b4450020400409548082080e0345000007044071a040340c4450040d0b0f03c40341e000751004100d03400c0800340c2802c0d40100070080101c607042202030000c00a00c241106044070f83d03c074922902ea000c460501c0030114031045101c09001c0c42c00c0c0000446c103000b03401800c44a0b008a003a103001440190050755010310075500244100c40c6040005d00d1507000e1400351907814001c00c003100c2c030f43c02d00c0001c0303408a46081d20141c001c00c4524083d44c02c0c43d80d1005819014004600500d800c040040d13110300b00d24040c414041040c0304100340040d20082c0100321410040000c01c0090003840646640613450300810340e03956141075001c15081e01d165040c020b0150003803815182c800700954803105c0481300d98010408030b030741c824 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 736725647 1250 736724397 736724399
    0x70c140312100501021b01030c030b0a08010c03110a0903030f120504201210090203190c050a05010e03030712110a06060e07020a0c030311030d0c08100501020610030f0c 74
    0x210040014000080307840100e9403890400d5901002d462140340c1c0710504540c4819a40549440c00d50846208040c0a09005c5140c401581081c1c002d0300401f5001500003090040005100340705410104442d051514200501c010064905a40b8414020074a010030104501040040e11400d002c91045181d454003e00e008180080b80040d034509940c00e40d10341d41c0d4141004441004400c0741c0411640445001c5882d0100460140c1c50324601c0860048042c0e071060414250b4606000e03020340c10511014100c000c507075074a80004461407901580b80900100345010440b940100d1502420b0500200111b04051a071380d6003103440008010382c1410014044030884010404200c03641705244100000b0890324184180705080d5003008144004545c072903881c0d400428200002e0784281e0703405280181d038000d80740702c142d0715500c06d1103890b5130001c1ca00314010441d181c0c400c000d980107407100c141d40601250788100490341d40d401901c0810002403d090704000041840c4202c1c403036244941700141400b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 736726897 1250 736725647 736725683
    0x60519032604030f020f090105010903080c0c09040804090b0609090a0b0d02033304020f0603070c021f0806030a030206130215030408031012110909100e07081b0603070c 74
    0x1e504980c3c000c480b44481e42d080d5504518002400920201c01654111060340c50070700024001e4400d0300c0701400000313001443e4149204c06002e2065161000742812403036050034500014580e10a00c29040c8507407800c10307407581a103040d0741150001f030801481d501c0d103900c03605400e4009004142503694000c060002e07001c01a2428407030402003441c0301840c00400c0d801485100c10480c8a0200e04035420b01510412005030386400c6030b01440302082d1040c17522941c0f004c40070b40d4000000d2801940c03100d07044080b4801c802c4015100c0c200700010340d64074282c0780c86000a05a40d0840d040004015800240000d80594a0415035015413230001302010b00759030b900e91515140e035105035030a0300c03031403000403c21032202412a0181c0003410050001422950107460352409600a030340d1032441a080c10b000b0444064040123806518247d84000b08a006100110f04e55100d40601c5034450502611082d07400e004000700d030130b0300040409060b007071459030b517844200e640c0d681c03180048038851850042d00c006 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 736728147 1250 736726897 736726973
    0x1c0201020d0f021c18050402031003060213090e0703030318123006140a060e012f0c030f01021314010216060c031205090309040902030106150302070606051903 70
    0x89900948440d4078945c080b0342900c1c81c9516540025008038010402e1140b40c0c0c414007442c03011207800020041e05c0d0750034001e0800325044560311a0621605200c4101c891784800300d207040c116031003501c1c100240b414600d00d00034403c4032a10040c1640445a0783c1c0c4103040e008001d40c0d240d40d2004c403942d02c01040004582070700ca003843d03030030386070780e241d03a2041070084554040c0b80001d840c000700d039051300d5603150246c020030082510602504001c6001c0451912541102d0001c030000c4880618040401980d483c1e140d0f9010200d0541e4460300c6070850648402c0018800c95402c418450744000f041810100b240b00c2510302000414114851074500c0f00030184590107103405400d5550350300c1401500c1d424010604080c0e0802003406615201c18098201400012140ca180090f1004220500e03680002401842d143c3e0196901001c42100018442c0d41a4002d02d0941e114210420003030752030b54244488141d003400c2c182c2e1a11003034807051010881c05540745106005804810300c000c03c2c101d0460344 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 736729397 1250 736728147 736728193
    0x1a0c010c170a050c090303160c0503031c020d0b062106040614040e1002040806090f010614120a060c02031c05011202190321080f0f07050a1107060e1c0201020d0f02 72
    0x381860902488d8010410080303c0d0400800c0103d000354142031031116503000f15071000c4002d205266000901c80c00701141c0360008a80b5520080005495440b101ca00810100c1c0b0b0581410403d40c0d4a40003510f6480e0510900090791140e00c00c0c44006200d1900740300c000c2c88005003682d62803040c1c81004402001f28001400a040c002010301141d0504924941c030703007403400e100c00049906160b0248040d034595058802d03421000c0303a1510002503a00682410100c40c187c0140c013071820305c0c410361189034000008002c0c00c4d03095403014913442a8002508200c440a000b41160b48204000d00d6000d4500102c44010f400d0000351511b01c001c1d601c0c0c2e00d01400f00303415115080c54030941c6003070b4500584c1007805a0b0740986404001410352500100d410f0320045d00030300b004180034010070001c0b5810b21810216800c51380a4040f0303140d481c2c07607240141400720b90316005031164111803140b8091101902d1000c9000d0f42c1a0000d14456022050a46000914200e10740843c401d00b00110b00100c0382c1d4240f44 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 736730647 1250 736729397 736729417
    0x109030210021e0f04260303060f0d120e120a110609060f07050106050f010f0e090a110c1e0f07030201050d09050d2d02120708041a0c010c170a050c090303 68
    0x2d030361790315001c1c2c44084003078508030000428142010b10480b890010045a41c4410119020300300044940c0c001610030b4820303000540406190401d500c100d0b500844c00c80d4100304110344560401c20418071141e40d840c140c5600414603090400340030060708051001c2c000f4030790b00902da14102030309205c050020741c1000b8410b0790300303a440c0e8070200300b241004400140c00d40720a01c0e104451412889006c2d25111135030700014003d981200001d10711000399486070243ca81c000c45520b5035108050b50310f80e9100d441d8210017680740c1c480c280400d10380c6000150b4405050a000141440518540054909400c0260104c800e0b40e2240c1d40301c00019000c0c004c105100342d290301d80360700340405841e00b410780d080c20348000104000e088892810140d0002501d190f040d071014801703a40e610302d40c507089126008582c461540100c40c01104000d194a42003e03200340070409000308040749075107908881b1085170215091210317003442c010036210b0110350070580d1700c28100d48030145001d0404020901e075601080c401 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 736731897 1250 736730647 736730677
    0x131116142b1b0507053c01050f12041e031407080904050106020607110610090203061201060b031f0f180603120e04140f0708090f0703030503070e030109030210021e 72
    0x5c2c0280c2c07500034a901c1c0d40c407641c40b0348545241c003a4000ca111020403054084c00510304041c10303010310703841441100c504d03404da50601c6442d000d106515064020090300d00b11583c944d00449205400450502e6082460b00341d5a80f80807041c442140503100d0b40b1040741602e50140402c865175190710350b801824001d014940c020495450f00650040c19220a012000c0d1190000385c140f002e181403042d500c0b020f560144100503a41e0b00c4000026180f940d800001150395400c20400042c02d33036140c1c003d14420310082074150301c0d8049038106811454a00c2c01482c1c40c083c0c04c44400d01c031041c03205012100e075000c5a100052801d03165111003405051101e54207001800c03c110b000c645003001c1c041c4822000c0703440c03002d08413814094600004518000c0c500d0081000c000005417102000700060030b00661403d060355041c036100c2c10000c00d84d9004441700780100d0340305843e01c0207904052182c621140d42582c050b01a108020701444042d6100c40c10b4904a003030200c000340c010035000310040048490072851 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 736733147 1250 736731897 736731899
    0x2030105042409020a150c0f050619020304170d0906060b0d0b0307030f030e0a030b0c0d0e0d17072a05012702131116142b1b0507 57
    0x244582034200d803652482c00718144000c030b20040e02c1e83d86406050703600c01208000b071500d0f0325100f110720940240c0040c2010494406800510101050b100d0141c04a107400c8407480c515101110b060f480144e40c018084480344a0101d03841c00d002020f040e681103900320100c1c3d00c1e2403a44500d016030303d01e504100d800b00070001d03078074580b0b514911a6202000742500541181d529580790400d07803120004010701441503001c0c9162780c1d81c0e038a10560014540c4108059150705000c000d80d409600b00043c00c070040c615000142c6175119000600403113150f40342d07580800d00d06543c0041a941080078001800344803030403c640d0a610404191340301940e9284800521600c0d40341881800e603400408207007401515a0002c2c150f0301900981c0c21105501602d1400004c1070710700d0750380000d142038401600407200120f190010404410302d0600c1c100d001c2c10001c40440446c03000e00d911002c1c00300d01110440303e200c04001a000908980d8070060030075050152041c804441c15001820440c002151680c102143c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 736734397 1250 736733147 736733183
    0x332060f07090605090904080f07030201200c34030b060a0f050307170c060d0506150f0a1808060709061713080d0f11070c05030f03030112030c0203010504 68
    0x35140d004045107000c0840e28038000740a00039115908099001d24025030002c0d091214110407a4400511818041e80d0780034203007002402003000c1c07406911120405041042100c1991050342c51034100d10001d420402d9401c544855445d0816034441c6004002440c1100c14036800e82204000754012903040c4d02e9494418104902a6001d4020018500d10034000b80b1060310005107880c1034400002c0703504e00000300262401d15290a20000c1981f25400191204a00000e9002140103820071b4824405400c0320410019140c01500c54001e150302040c003d1003100c1f0310841c00f80c0f50900c42d5192070204140c075488041d0410608854010105440e0369003002143d9101446403070483d0224410425400d1480119144802c0400d018000c0c14000c10b101040d101e8a620030305804207954403c115603040d924410500d90401d5100303540d4901e610400080306e08010680ca103107035030f0010203149560b085c00800485505040015400c00110b03500c07000041e01e00740318481c00b49020740c0c498540c48070440 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 736735647 1250 736734397 736734421
    0x309070303021014010605030915012408040213150f0b130e07050706110d1b090609030c0e13050d020106030b090a0201210915140f010f033206 63
    0xf616901e640f52400000c1c049034030140d80045d05541c071900e040c0390780f1307100c051750a0310301601020702240c41034070703540006252a54620601100408140961001c103c82641599088003ca034060741200f0001c41c2c0340c1c0d02901c0c65101c01294408030741c1c450751281c1c84000d581c40d00d1070741e40c1141c610804000340d070b82000d6100c010001c00070f000050940c2c44034605414014000d00030100d0080c42240c981b52080c66600c40740c400e0300d00d46512403100300305083d1036811203c044501e0040182c0810700041002c0f90f010310403004142030740e4000b05c4060f03c50b40781026881110b00018103407160003100c40c451000046061011040300405a40003240c11429400e006880c200b010300015041e9120300040300040c1d0b0010700d04009000901c411400c10103480b50f0300805400c01035001130134210100c8000300d003200140c4c0302c0000c0c200764000702da40340d584103200d01c03040150a0180360340920150303030204009020090448009002801a010301c410640307a03c441e410107241c0c1c03120325034022404018400f07201ca = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 736736897 1250 736735647 736735663
    0x8011e05090303040f020d0f060921030e0705060703020106030b010b090f042318030d06090e16150513081c020118030e0a03020306041406091f020306010c0206030907030302 76
    0x10710040c0d032031800c25035100d01e04944d940000900803100e1403224010b002c0c0040c1402103035078100e201844040e040b450003101314000680c480341403826406444030039500c00d01c540044038910b200100405818001005003540180d182203007159250400440001e070320b40351440c02403115542d00b64850b6541c00800c0006580c2c007800c903000b01d00d410403d802c0c03000220749850803039002030910703081503c90048240c8184031040c000c8203984000261f010315100c00b0b40c400d008071a01c030308041041c00030200e100c0b501c0f5030320f0340007540000158803018015010003c4081c1428511402c0651030040401815004800c8690002404d50000c114004281c155100043e85064841c40200306a410590304010300c1c0c03440e5200a0104000b2060030020303900c50300201409181c000b01201d1292a00c1c4c6890142c14848900000282c0203620101e1001e03840042c0c0030b055401d6010000c944480c614404000a401c0244040d04220848150b00056142d0800031805500036030302400300b035401d508000c0d03d85600c0e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 736738147 1250 736736897 736736911
    0x180801021213051e1b040603030906080901290301051302091906080109050a03020708070510050901020c040f0605040c182702182d1908011e05 63
    0x10009484408904000075510410841c1001005030b82070818a00d8000300068046002c820300e0b001441c455400030b00c070326040120301c00215a84a41400f07000503542144001008240c0e902e4007800194000d0600320b610122002c00001c8070403c1b651007079041480a0302900340e030750300302001d050f60b0300f828099698011040200d601200c00186e0109544020003403c032076078010029012200100282c10420007841000000e000c095550700f030240e110700e100e0800b1005480341140000d40e581d00864140100d45008100301080748840c0400d4500b03903c48013841d411130044a441c40850344c2c07240f240351010701d8609030008045040070144801c48050762140f8003403019403141c8294500c00198004152070070000114a000207290303200c40000b010005d40040c1b14004240084050f6101041584020084611302d0140d8410380119131103c140c5551110007404203004401c050800000300441c985d0030099401d5410355aa020a084801541c075061700d107030000c81401c0c2d102c112401a5500321074 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 736739397 1250 736738147 736738151
    0x22050a121101051005190f170d020f1218100306090f02091c05031201030809011e0e01030e070b0d0605040b120d080417040602010b1207060c0209040819180801 70
    0x8003060081c0c4c0034400c0b4800c07688210461090b01c9030089442841100408510041d0189540c440ca005c40320f41ca0480500d4280344164039619800c10310001c1d0030360690b8104e6004d003030007203e50700001020350700c00b00c40021340440030304000440b61619000310800b0501a60f00241c690304003081d02d4151030591032107820060040c0030100255070782e8400103490b0380c0381c5501c03510001210303e0081d042d801000d1030110081002000013051103650b1000342200e00c03099960540c100b2440265404041164440c0c60000d031034041c007007045500039409000c8c99422581200c0c07001e030707039142081001e0b800030200090381a2145400c210b00d0034180152107418108884800c1081c15246c602e640d24a41c1c0241c01c0204807803030001c0b506100d0002d6429070701c02440304140d582c80741c5841001e030180800104d402e001c2c0441c40c5d06070482080103c0c035a0284c9440f5503842113805201d4080104101e00070300152003080003008101800186088914403203071454039665074444000803a1801c0607a15800b44031264 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 736740647 1250 736739397 736739401
    0xf05010506090f070f050c070806041b060f080f040f06110c010614060a0f03060f12051e030a050a1202030f0103120c0803061203070219210b22050a12110105 69
    0x243c5c00502d80b0101c031144d45442d5031620912100f451519807030b81c0c000e691a00540d001e0005000c00d6810300118004020b6152510301d030b849104940c00c80e1140038580005e90b030394020580c2e0f404942c10454015010300b25607400c800c800d49801c412a034a110411625900014501a101c030302801800024201501081d985070003400104119115028052013008542b00000d05018084d41c480d102422100300d4040f250b6403140301c0382594181c2008280c2c0d051054074130341401012500c031440760140347e41002d1414015086820396958018180c05130600038040410712401c07905101462007148850914031095141d424074040d01040405070500308155205028040751845045030b41180f01569904054820089000e085000d2000c00a40c808190402e6926080c3c0a42c0b1800694541c0300182002604c0a100c4001092811100601c081c46210026141a0344100c020201880008025035110415995242001c0f400b00c01203480d814003401c2d061a666101030301300030081e40e41008001034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 736741897 1250 736740647 736740661
    0x40608010203130b0907080a0302060f0a020703020d05130306090c03030e01050309060402090606091906021204060804152414100816030f060b0705100c140d090f05010506090f 77
    0x3c070925a0150520490801059000d03004104481c01400d400c410780700c101c00c20749002501c41e4000d03900d019040c0c1a40004c51a003403914401c4400907603241c2c00500c0e40c610030000c2a10325402006100e1400411002e000006c00d0880c020001c046205003e490551340c214580a42280b03031400c0700c1d0b07040180910400135400000200e850300325030103d82000240d03a81c4000602144500c64543d60001c0020117003040008511841e030040c3d800980a07124010107441c40420300d806a48181760018241e0b030003040124541c141040380c4070030f0706a004280e8101d0802c06080314289034001c00c0e1060b24070300081018908050224145a204a5444107416851840103010786405450460302c0c60000ea8042041806a0b0102c0f41e072904100d002e200c140d513a28000c1e041074006000561340c1303003d50091038a0001003882056550b1030146c54401074500b00008510094001000b001c032880d90b140000804100722031207c0440758451800800c5034901301c1d06125040001520305c11500c0c01c1e810a000d80 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 736743147 1250 736741897 736741921
    0x1e0b01120e030d09030c03030b01180e09030c030a0203041d011a03070e0a1202130e0d0818010501090b0f0406030809041a040e0a050f1504030e03010f110306040608010203 75
    0x464400c1021924200c0202440e00314401c800d441d01c4050315000f604810103801503200c0c0c20381406038904000703502d4100d006503815040030401c0200c03000582d0086c420b001c221407440c0d4001205904132818541c001951030320b075921140024002d40c0c00480c04000b04020300c403035040814003441c100c6000e545411462003000600031041500320310007000060b6540d11034a0a24060030000340103213903243e0f07541d906030140440f0342d07001d90003204202d0f0501c144e18901e01503011241d0708840101220004a10304484030350003e022020030a1100c415801084800d001d45400b03000746000005040240784100060100ca03204807500950601408002041ca044140c03610600240c1e804640c00d082c1030b03040e243e03098004070102d6010b17142096609001c1c1000994144280c4281d040380c076000383c2a1030f0956100810030104a6407840c440000307000a00c281c02c140644100030b00042508800d140391141943c481251046510801204015042ca000d009210007890920004c6245007400d444000c6 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 736744397 1250 736743147 736743167
    0x111606051b210306010215101e090c03020d06121109070905030616020111182103280e010203090603060612010905101d04060e10020408011e0b01 64
    0x395455403000440c8140c5040c07006603069810740e005a03882d00b440c4425207680c1c0e00103884440c0103106842840c403100784001c2095009400201e000361940e803519450403407e405608826140340002139002900b90068000c80240e8035140c1c60258076481c41d800c012080300c489034070100100c0c0c400d220790783c0030840011107040e458a00b6035042c01c0e00e030b8800b00d00b590400b002d41e00c40380c1c051140804001c0d90016070240f03590031680950080c84610102c2801070598041c9143d600700361801c034a0141c51900e0511003117902c03a0b207600c4810303000d560480540303030843e00708040c8180c211203642e61901840401441c03001c00c203206400c002c9500511000000c1d43c0380a6045a80e014007800408174a035540c581c0d080d201d04e000d540841007400d42e103034245400500410343d41810500c4107c02c0218408100240050b5241040320710141d160761581c032903001500c0c603480103440c030707026000001000440c1c0e400100302600c914800401d01c4000c4144068001e65100c2c04e0240091411880106581e800002c0b00d07 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 736745647 1250 736744397 736744417
    0x9130311010e0a0f051b10050c191101020c090907270905030d0f02070b040602030406200928030224120114040b1f03140711160605 58
    0x11036040d0668001500428075260300c0039140c07003030204070300800201d6112041e03803510500c140c505024510b10704481c000c6a010085504c403400301c44004042d48110301400543c80c007041241d880503001000f031001500805410303030b50a8500302c903282d04d0303580411101a43c103500f511201703080d1901020180d154071060081c0c01805814986094503c5072000c501c60300d00305005020810362031103151160b0b40740d0100b90114205420102038904807011442a0340030340c3d8019283c000f0b580e6450b174403c002544020801c5407080e0759541c00801c0044030b120b6448600300e15201c102d540c1ca07800c004100400c12291200e03001c10001140502c000d5812040840c102c03075040d140500c044910040341d40c03d0142000c0541c002c014040f034140e02c50388940d00304a04031400441002192024642880140c441d01400c080d08500310080007401c0c000c003000340c011040250303e40000d1000103000d443d0010801603a00000240076940141080d0000b80a49030004440b80f107449400f030710f440302c06415070092032031034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 736746897 1250 736745647 736745657
    0x19150c110409050307060228020309010806090414060a020d0b090907051525030f0e010c1506050a030605071e0804020d080408010203070c0c05100903120e09070906020c091303 77
    0xb242c02c00400b0404c0c0d90701c00e68003078015074651881e80c00c50002030706500e040d090180000310840300b51900220464141800c10783d03c01c2010340c0d800741440941d0078007030030440d110041090307040b0540101f80102c9008032001c0e4070150b50340b0318003981103040d28a0101214480d83c0000203110307542ca400106442194030a90b014802c10144100b42d480e640500c1c8a00900c5c9041c503000c0010b0000c1ca886030781c00c058444e859075101c503c0c240784215540390750201101e000c1420901c22a0105d40c48400c2c1d0004001030820100d6800d48613004981041090f500845416480d41c040c00400380e000141d41e40c8505080b1610a0001000c05005020b6000030700007070b0140d607500710740c082803000c0c0c80100e8001d402c9401c0255601d042c4080014082c6903250802d9540d8403103080c01041e0b9140c00e224016000c040b6070b075455280345c2181c4510560307100e041881e00c2444150b0259061644032011264440c20a07074542d03143c3d15207081c81c003a083c10400340680f8429a092002c200b0024050b030040262203400d0320305 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 736748147 1250 736746897 736746911
    0x120a0f08091c02090106030903080601030f110a02060618040308040b04030e0a030813080c0a05130209031f0f0605060d050403020703080c0d020f0118021e19150c1104 73
    0x102004a00c941c1c14081c0d0000304000c0d003041c118442030b03003040e2102d00c281c8548a007070782e80b04002c80464800190007000600401e01154466100790000f00b00031002c141c000440a201d801d005800e0f41c030a10071038025030440300c204005490601c8098031942d00071811b070b0004c1c0c6810382e030080120368014130042c041298100440c05251144400410030040078001c003070040d40381d0810101640202c141c400320040c44090124402c58080340c642c014040150540a45c5800c100400c491003452464500b403c40d401d000c6403241d41d80c00c1054001c0c1554160340e803980802e55a5141081e11124041030002c1400d10f2000c000540f00c48048646941c03840c2000601038581d840c0490528805038005805800041800c42c044a07021880490281d002d0b003c507145a0000302e03402c3c0c00d0740c411114050141e960b21728880054203017030510360311950f906e541d40c500501000300010303140c08440d0304a07841000110002e10a42d00c205c4843d4030b0340402400d1100c52200c05039940001e040c64180118000c98075000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 736749397 1250 736748147 736748153
    0x102070e0106090e01050d1707080408030d060302040b0f01022e05070c1a0127020c0a03051b070f0e042f040f09020a03060b0d0209041a07090810021c0207030201060e06120a0f 77
    0x280c0340036081607401e0f039a4030914680800c023f8000c500007644520f20344100861a4070f02510b1041883c001070b00581484034050b02e442c1c400030400301c0301003281c0700441d8069a250515125a91142240d030312424410002400e100f2004056054642e4a1681c0c010041c031100000b0303070303003010100d40c2d074403c1c016081c0718190301c81c010f40680762624005200e18420501019041406450100f249201c1880e010b2038480000703565500354858186074000b0400180301d0030450824455109004001240c000c001d1607007401d0b000b80c55160340281c1e181c03e81c04030700c080d460705000c0c444035101190340510485a040d0002035840205100082042d43e076200c9c5800692902003100c1070040e0000c000304958985800d00c2c0d501580d1154080d004822044002403400380541c004c0c07810390b07070484020000142c00c26601030081d030101d0700d00c64100b620307421030044d007030b03400c0c0002c02d1207922a038008940e5034a80000c8074003050010b080b49104840030b42901c605001e00080308912660002c1d1010f001c82001e00b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 736750647 1250 736749397 736749413
    0x60215061c1a0103030809150402060c070f060c05060127150506070b0603010c09081c0c08030c1309230c132c0402130b0102070e0106090e01050d1707 66
    0x161004021041450b105111100c001207018101c074080d407102001641c07080b029940b1b40c602512070180c1c006980c000b140150402030080d090003180c4000b1142c11a0311050b111a0001d415804080001d14401643d0100242401300500401414280c00842d041360805410050700340910564456580c01c00e546400004492440081002074101c03651022207040a52000c001107842600943c24001080c0c0040d00c580070200898911174080c001d0014103000101c0d1204400c600c00040007030b099584404102c40038015409080c00b084240c4c1e642c1c400c44520340070303010540e00442080b498240500403030f01507a0098602c079050842c80d030a0f140d0300c10340c640d103c600926502c008201e2400c40c01295112130911818041100b202c0200c50f030601540ba0207500c0581200c009400c449803282e0010f112000f40c00142ca5420140180c03004203407030b01d604460003503090307000400040814008000700c0c2c2d8031142c0c1c1e07405041c0540c0c004070050400d86a1030401180517003012003254000880c002403058803 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 736751897 1250 736750647 736750699
    0x61b09030209070c1704080f0708030a050f07150b040b0a080c10030612030e031612080a2006100f05030703111302070c050a0e06090f0a0b04050f070906021506 70
    0x80010003e02441c0d891801080350030500031038405220305400c0c0c1c044000006a003804441402000314609000c0ce04202c803035401c4803024000c1c03c0014044c10000680c26400489040001500001d01100c6041000241c818102d1200c1c0104a8000140301070013010a110a03a094103032070303480038904000812070080025510159012103100030000c10180c0c400c0c504180302004400703d4117000010715400c90310724070390312403c040500b252074124000360a0b0006422000b04d276003001010a1488200741480e1807c90010038142c0e0000410804103424080106001d03020a4640e801118185008290348070940e01020f8980d8070440d00390081e41d5284600c080c00450f00881c155180c4500f80341002031000d0f280196840307104c040e040440c81c0e07000524120300c1038900034014032480c1c5030440c05a2945034090310304004035440c1d000e042465103481c080d4030f004d500403078014134039850a24001080c2e900280c00800c110340248a0f8442c003002001c82c0540c02481c21140501034512000d1106500820 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 736753147 1250 736751897 736751903
    0x71403060a0501080601171008160f15050c0115030c080304030302060402122b030f0203061c0501110714010f0c0801060305090a021206150a0501091208090603010e0103061b09030209070c 82
    0x1041c000c1201c13011506000e0011900da800440d60b0308100ac03c8a005215602d0040c04014829640e0811280c40d0300c4504c95041540d60030042e1030486004000f41c259001000854040b01e82202e04004004080c0464401860f035003001e14189811039400940300e04d4042d2000c3d100d00710090703181c46003000a01c203c24000d902c400c0c480da1003001c8080109102d44681d098000820300d041c1040410882500890b44100c3c40185080c028109401c100a0140c032246000d0b5002d40d40c4a2001724000713080c40c02032454500071b0036030014890f82d100205003580c65004d010707813040b81040200032003540c006149505540b030364140420103a46516840c2c0c0380405030500650302051020304c403880803101080b2140076039040342c0340c03a4140042d0000d0008484044c4100d50000794501401c2014041040b4000806403050a881d0700d00103071030f00003c015410070b0300680c070441420f00040040101500c035600c114403800d01129504040002c011382411681d00c80a4007902c21040000d0b24503100f0010654180e034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 736754397 1250 736753147 736753187
    0x1b1101060801020c0d0e010318020d1502270a0f05060f0d1d010c080420061c0c08180607080c090405160207060228050312010e071403060a0501080601 66
    0x10b000400c15945ea000e8988040401c40711407519495500c0b0f0302500e000b424415007010003807404d6501b444545154210251480101c00707125541c01c2c01d50340010701e4001c0d10b401905404c01c42000000030050310219a84c1d00c0341d581e40501f0409486c0301040da00407130703200300d072551703150f000d543c1c07544002d0300c6050070100040d850840c016000a00700040d01e010600108002c100340a41040c003034552403019107000c1c0010102d2860709003860740002e520105141c0107810740d82414480392680c10008805401d58820365100c14201100d0780e40910141e03400b81807001038000c461031b00c0c0e07040b903103c02002d0030200030420154002201401e2041c100c500a0402070410400c03861b001e0303003003603a2100007050b11006001c0c1200010f80107100080c00d81c00ca40c441c001380c0304103484411002c030903082800821141800f0a104251110758082043c600a220aa403c06617038501544000c000c100b4401104100f031070280244900350b25043e941c9402d43d0000e00303280c0c245480c0c5000685000b8007012070010488 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 736755647 1250 736754397 736754407
    0x6011811040b030c0304060b180621060a09260403020409020105070813030b070302090a0905060d05240a2d0e100209090703202212151b110106080102 66
    0x2c480c14001714899400780c8810052115141c0c200050740f2100422400a0100c40c004901d4620b07204605683c000e841c040440c1040c041e582c040f50405604807600c00e0950380d078040f0b1206000801644c207844502c80001882800c1e194101d001c118020b6001c0640283c1d901c600c90b0046900581c100d0302015041f0807007645607800071600c0c0440f402c20380000c5981280050110384c1880c060300a54400c01001444040580c0c1800042001000f0082a16900100078003a64000c03610601042c012095001c4140380c0d2941c40c0c8048800c04107005c0c2c442c3d05c8440c82c0c4004040348021040d400c020301d032000c80085403a002c1004085014000035810f0b03070554010440800b940300e88075070040c03155902c00d4902c00e140740c0d12982d041d82214020704244888060085046202d225503a001380500c440502e440307402a05d41c50081c0700f01e4001900820703800c8000c900c004080c801c803007408406948842c8014400c0700c01e0ad0b05007404000040559100380181d481000360524400e4102c3d2015214500085450b4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 736756897 1250 736755647 736755661
    0xd090506041208270a080d12050901020919060807091d07090f06030b040510050306010e0408070615050321040b090301020c010207050109140115030f0f0609030809010e06011811040b03 81
    0x203610711004a8410120310b40700046c5a0b42c0410b18100c20141925071649038000c0201c000050000286941c401355030030400d0b00c00740d5a6a5801c80d8070441d00c640b04450345402d00710043d09140001e000e030300030b10038011801c0180108403901c003014181202001400382d20b6246043d04c0781e000513007001212a59440307001c00d0059140e80409114001201c06000b00d444194061284400754003d150f0035411460040c4010b45046086c81e030050301c02c1c03c00501e4442d894950004559040c40d181c01041101c042c1002203280070004007031003030510b890034528040c03140034502d10b610031807241404194001c00c080d185030741c080d81178a180101380e000a40d40d49840d481d00500030020070108940ca202d040c0700c801c920f0201489111200b0f0440104d4030311260940c1c454011803c1158022224402c0d603100b000300290980c001c2c403400c181309444c0d034009401c041c0302c0d25080d80c0d80311075001d100782d20410040001804000564940f00c03128100025010303201c0741d43c40114403442c2c000c0e00141074008240b00740 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 736758147 1250 736756897 736756957
    0x5100c030b09071e03061a1c060810050106020c1809032205151e090f040e010c08090a050c190e0903090114031314071203030209030d090506041208 65
    0xc1000c0c0710b6400c60324007130402d1082d41101d04902891049101a610050303860140c0340c02003446001c0790036400b42004400d1f00d60303019280716401c40242500230545140640409002c0c40e40504481d002400001842e00046030000001c1500e000c82600b0040128291910a00890f0301c41902d0200c40c403110010003c0f0716154000a1140500424090701030340101203803074050362040348800c44128102a10794018101642006620940c4003110501c00801075071207215409400e800e03c40046031a00b01d1003c041e040d08001001000d9903040015140c0004102296055038844215012400701802c0c900b01140c41c002504200c0717100010000b40034040200101820902c00241d80c0c0360011030241d0341c01d800c10702081c1c421150108047d60b080d00015081c14201c0c4030000710310f04848940d0b5440400c4800c12010560a40120b0b41c00106c1a6450400740811603d0f41c443d4206081d82602d0304c03000c40d0140c03140c1d11600b0059a044c80c944c100f00500c01003181d040500c0c0c00b001244a42008041e03942d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 736759397 1250 736758147 736758167
    0x141302120d051b0a020a03110f0a14090705040b040603180803092803050d091103060a0b041d1c0302041e1712030c091305010b03090d02060405100c030b0907 69
    0x2007480da220f400640b00f01c001a80403002980a005003c00c5072540d512a04024513903048160f104603135501c00451510362140510080c0890420300c0e80c0d00c1545c10901080c2d20014100904005d800c00c8207000c858010303400ca80880700c075441e00144640504e249055021080b40f8010140d14000050040a0a0020703102c040c0740901442d000034040d200d00100017075211504001c000c02d400b131022403512101684002192070044c60f0808807c00303840006814424125106511240c0e00c00c109102b90400d4490107080102855003c03510100d1102a030f65500180c07080c00400c50035030490440c00c20301c2601074034010300031104220310000e14002040c5086615005010041d210f103d100c1043d200c00096400108000c4481c9034551303101d0140341210381d0700c0f0444051700081d800050700115030345441054003c002c0210300325101d050000c0190305044c1500c12580455008806001c0490400300301445d08402080c07000612012170071007500604501500740f07031700c10317004800c00004a8201d03100715 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 736760647 1250 736759397 736759417
    0x290d020c0705090109020a0210090302031615060506071707141b0405060609010905062110030210051213060b040e0604060f09031e0e03160612141302120d05 69
    0x8166a8071085d002040f40a41841040140d124500381b100308166039000d40030b694001d1050320f1421070804898400281410707411600c170440c2d46121207110380c85100e184044c03c0d048071030070f18280450f00c4042514181c01e50045a80320300003194001c200f0544111182002000c2c01d84520050450880001200c9202e0860107076090400050031880c1400445c1d00300c0c00161902c01e21282003006201280d00102120040500c00000000c0c034032012031070b014820341c111250308d06014118410b2020341500b015003070342070200174084000c61440c00464107a018130f9862908486460030704106e0042c0840f00303030064106140c40b007a04a46000480c1d842d200b9401003400b032003c080e403c94942c007180d00c51100a00018a00501211085600c1608850701c11640c07030158002904100024141000c81100c0e10045038035800410034160003240c54409154054020468011504ca0740c0342030400051040e8024445220100c003107648d41c1750103035040d040758400c5892403c0c40c1040908181d00840340c1c6 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 736761897 1250 736760647 736760659
    0x203060901092f0d150519030503030c030a23041a06010e04090501150b070303110301061b17130801063f050a1a0907290d020c0705 58
    0x202d42e034a0280108042e1101a8203a000c100114645076400119a001c2c901000401004061884182070081e01c03202d080d21100000e65600e4041040100b2a800740c00f5a042e01184004101080022007500d50104248860980c1d0b640d42c401c0c0d031001440900c1c08219140204440184000078a5200d18030480c82010504c50300a102c0e04688440d21049403c140080c407985607044860400d40c0102056034426400820000d0906140b40701519050300040b86070000420a6800d040c0e15001c2ca40c7d141c810b840c40f0034a1541002030090600a1001520158219102000003002040c15111608400e01c4c500180c9401d444802c0c5e0004d5001840b43d011250708059020601c2100081c50030b0940c224405600b02e0540e2503603003040c5040c9418031684140e54040081004124144085070465204500701c0149003c0200c0354032485102070801c844540c403200342800404085ca13042103100c0480010400d18030162503500031f45214070a017518102d4000308018001c031000151407010350b5403c03222 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 736763147 1250 736761897 736761899
    0x907091707150806012c06130e0405010209031005060f01110a0b01230102150106110a080703030b0109120c0603020c0f1002040e060114030f04020f0405090d020106060906080f0a1e0203060901 84
    0x20079180f940c07802c4d118a00c6d159103800802207490000c00401c14064540d4804000c10394503d0303818120382c0d0845007955182d400040301030b840c0c42e040c000e0308040700c4044070800841c203040b0085488098050011410f20015520005803144100074401c407941d40045031005a68590340c45d00340060311841111954421800f04101a42c004039188211036801c04004105030310707010045a011030f081c42d03500340500400305100007049050000b440020b009403000b280b480965030004100c003540d5800606000c41030b01d40c0c01d00041d400100b080c200d40c424038026889450199426007041101c3c110141c403803082e07409804564203180c004c5c1044071460400e05800e603a5500054030620462100c058404504100007240d0008005030207800c5400030381000000c03090080460304581c81903600701d10725030100c9001c080403582400303014041c0c29140f81030404145050b50260608902a0103840d4680c0d580d000190710380c040383d001c02003444c58920501030150750021240020350040d034106000d0305513000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 736764397 1250 736763147 736763177
    0x60a0e0f0a0b0d050c040b0307051305120a2a0e040c06110d0c0317070507120203160206091c08030114011e2609030c010605090709170715080601 64
    0x3a101240da4000b6201c0c0740500300303c400c60042c5001480c00030001828080420760504440165115004680714140d5407154884108002c203100e60106c1d00c21000c80034102c800707030740c00701d070b00b2520300d030711852161100d49500d43c9141d0361030848103400404100c880300054a1310404081c0d90190780201028210307203442c0d40e000c941841110310f941002d5400702c0e5810480c07510681c1d050b031402d0302034901404003280d82241003541d02416501040050b0020030218180b00301000a201c006030140015441c10b240301182510740011300d040030344101c00124200c8a242c5820082c801c11504110b80404045640e02d44010f0a40082c028510156011038040e003095014009046e5210440020240c000c01003a6088882103580c5540044120204488040110790b440c0e900c1c0c0911001e030301468075056002d00041c21034403e640100e00c00c6c1040c5050018040c0c01c8100030702520a40207d0038180590445403a141032655031003800e40011078207030201560303480903c1c01d0080409a80c0c401d00d074004a8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 736765647 1250 736764397 736764409
    0x7061101060303020d0528031b0206010e01051513090507123b0a0503041e03150b06040e13060501060f092601020f04060f1b020409060902060a0e0f 65
    0x300000f000f5a0044807a441c400380680090301e61441d101d1543c1641035110070115040b401d24440b20404240c5030200c0440040c05074034920301c0150284000c0406625218803a40b000300188140d130b01404079848004c0000741404202c030811070980258503400b950341c04955000380b0040303480000050202d03141803c034102ca03010f00004410720341c01c480002c00880e08003110303461106103919031032101882e00c01003ca1060100c50b00c854000c01c09923850f00c1c500408601075003041c00c5c22505012400d5021b00010348000710003400c0a0b11181c002889002100108515109941050f02c0c540015810000140d40400750003003510710a0b00103014a0b641c68900340c4241454440c4540828001c40040c440909c02c0754010803a417219010000c02039040842c01da0072640503c51400c4410300014040c088c198000c28031045024441c80c1c003e02918080e982840c0054880000034030a58981c0000414004160041482550002c151582c3c5134800c003805080d10300c445851502907034041148403490303d044 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 736766897 1250 736765647 736765649
    0x1080703060e03040f050108060f030d0e01090801060f090e0a0c38031305012d0b0a03200301060b040e07080f09030403031404030503030f010806011202060711040608010e0706110106 80
    0x8155017201c1a08003c010358020030010031007600300d48001d030ba1301c00c0c5030b8003004a941c6d01102a1030300e07410011240c000520502050f0091405681499806c000c4c1070720304815036048441052001030a000342820284c00c0000c824400340c50741d825a1804030388030340d10285406a2200002d8812860079400824125150f042e031014100034400744001071040e801c054060b088580700e00b000080a40860039450382c0c4030010010a0f11520f4804030030071402d0801c0c824142c061104039640401c0a10b540d0b17903281c100c2c2d80d0004694150ba001c0d03e450340e00762025009040a03160710700919485940313900303a80310040c108171034010010701c50001080484c030003025214000d00e1654080d51400f401e640f4281d40d0002c40145441d0000301c10800000842c4061024600400724820200b41d207501d041012441c0280c103820428500300c0140c0340000681d0b90808503041158807172144100301c81e0b44400030303006004e0360707021820b1035007420b140f60640000810850706132840c176213511103c46170002c000740c200d43c01 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 736768147 1250 736766897 736766909
    0x417100902010e12010609051918170a0e03062e05060d09020307170a030f020c060d0e030c01060608060312031003030c141005100512062d01080703060e0304 69
    0xe1200e9900d03d810248820040c4900c07a20001c1081940c8100500c00c451089074140c0d01c1480c070428440c4492610b00544043d0a40d0309450040020142c4410340c07040340240308001c2e240000150811514040c103910100308400130181e6440d131800790b405100e801c0c035009440c62040d0b42c82e581c0310400d82c4804100320540c0e2000d40324506050b0310344010070007041260f005991500c24640001031000d41c1da0510044950f070307880035002041c003d180290518441201900a542020700403d00d1500e0f01816a640701e0849940490030050b115062400c51054504185882d402c01401060f03107500450700c0e40c000c5005504659003880d2620441c4104c1c0010b03140c081000c12508810000700344a4542d412405000e1007980b21840b103d881050b01d440071100c08083c0c1d06480d4020040c2500510403000d0003050180d40700070030910205803058a030305006104010001c224003c4000240d9129000442441803058144195864561840d40c407100d9200450f03d2504048a00d46601004400c0e2421240 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 736769397 1250 736768147 736768157
    0xe011a0c0a060c030605091005040e0d020a030807031103250507030c06051b030103050604170a052b0c050d0617101e05010e18010b10110f03041710090201 68
    0x5050b80c6400141c211904160704140c0c6400f40031945984242407036000701c3e07455000b40b0f8801d06d404140301c00d032000380040d10400d4001d0651030100070380100300c1b91101503061038042500c0d0707507411007540200007850049481e0380000c01040401020088045d0300308941d0145207040b58100d0604840501c10380f000100000d4041c0c04001c0020001c1d0041c6402ca140803014200600c2c0019200b42143c000740d1090b54654000341c140b00a000c45000e0840700d103090200c070f0500d804860b0380040e2062040107461022105113444540c0d1480d81003680060700398810005100b1101082001442034000306041c4800510b0f000d070014850401030348203001120316101030312011070880c10f0b44000b400c0054441e801c14202c1306120f84400c4091013038501034a425055401d80c2d042131051180a688090031410460307141c4981d50900340d0b545140d800e042012032034603c03030a8400c048a035003848440313039000030f907844049000f00300d00071500c0c07404a1401281080354040c0402d502200180c0d07104040c041d000c51 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 736770647 1250 736769397 736769413
    0x801080c030a062c070617060d0b0603010605040e01090605180624041d01050709080601170312010f030203060703200d0e0703030306211109040f06060e011a0c 70
    0x52801d40005608070140540d203121a6540004410441341c00c0c040159642c000c0207041c040d151b00400a40d40f42c0180200194580c5000004588000c64003070000c2c104445003800901b056500b500804050200504240b1510b0240d080540c042c0c0340d2190102c450304e04140c000750b502c40c050220081601e0200000304503980b5407040030503660710043d9420b031041d07080c1030b85030a171a2540d00035001000d441c61b80560042006180981c2180d1000c0c00d6942048014002040314101c0006c210b41910107090640c400186201440e5145d880f03400025201410301d10000158401100d8041085038000e605541c143e0b940e10b6002c03800c40318a500c0c00105662104540306041c108030340603102d00c1514003800102d04000f260700c46e2600065510480009481c0c100500043c0c00200860703404070203100320300b02c090100f030b0381d500310007203da180c001c0c06144904002414403a00e01c181e500380176003050341041220740340d200203d03d0351024000c0c0604998580060007900b10481c0860f42045d0743d0201038034102d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 736771897 1250 736770647 736770653
    0x41e2a020a110f0d05030a0206010306050f09100c0207030b0a0f2a1409040e0c0111070b0708130b040e090d17130204060906120c08010c090e04022409010801080c030a 73
    0x107090190f0002c0e03040280110a0000504204000c0c005481560000c084541c550718200c415150010040941c8026140501415400c005814039021031004c802040c002907440c012031030b100c49a0302c00b91240c050744003484880c032215488030000d03001e00ca40a000c2800c52004448070340c5100b002c2000000381e00d40c1c04075401303031003008603caa0502d41da2245144c061008005015a460b000300140c650b044507028a0441d0380005814070f0400341c82010b05890380c80c00b000c1e0852406003030005042e0100c002003c0744d005018030304110207003900701c19468a498580c282031380704400c00c07200039100b40300d042c2c1d84568480c0581c00070044e880e01c4008032044e9603506a82c6030300180e405142240c1141e12840c000c40c031069107000340400350202c0c042c80c802d03000b5181041c00b4039240d50380c4500981d0f49051f910720307519648002c2900070303a0056101c202d901c2d02d4074070114910b540e1420f80301000030031740741c44442d490701800b0041500d21002d03038502d040d07030340c840404940341c0014044459155006602e40303400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 736773147 1250 736771897 736771909
    0xd05190e0d0609020f060a02100b1c080c0a14030309060a050408030c16051e37030509030601060807030b0f1c03090806100501200606041e2a020a11 65
    0x3c8584080d000b035403074246440201da8107800c044000d10158000308070000040d10713944600c03003203084100c07001c86410500001031041c908125101034444000001c03500f02c401e208100c2c003004580e0040400b4404440c0010b1603489400c19184191f640c05240c01040c0341b003825008031401103030407940180c43c0d07840f01080440f855128401c0321b2940002c07260204013065081c402402400c0c03e50404249114218414504010104407156903004107824110b000c40200e415131018801040741c00301400b107880c182a01e4a0280d525841c0d0315100d540004180c032640400c0550064841c3e48046c0402481d0340300700314400c140020000d03001201d414032902001c400d14141e04400740130b801d103e84565110581e550a2400407100c080d0304c0c040c2076008000300d50b8081103e110141c2070034910460800440001c0703450310340182c0600d104a0300c070311000440140300001e55001028111003041802c00303030010302d411007000411200342202c01d00c407080c000c1c070b001003100506940e1140b14202001062810044 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 736774397 1250 736773147 736773161
    0xf0e0f04022b0506040605220b2e03060503010216110d05011d0f210a05120702011d0f060606030916170d0c0206070308090f0d05190e0d06 61
    0xc2d04102c00810312076800d80d00420100b4141100400b041600d00402030109403802d40e44281d001c0c0a41400c0c043d02c13100c00701d09242075074005040104030200d11f200010a2407000360340d0680200c1070544111500d241e0004c8111003140c86172814007840755a501094202d0088000003038001c40d04800082c0000e07500e8025031100c01005150703031303100011030312400d085031924a0240b010601d9183d902161081c00c103d110208200c54005014030328003003840304082c5050706582072a07802d000ca9105081405802598510302140260003000e1400c02d000070b0103031001600d03460305010186010300c0d0061001c14054103140c582c000420032901c2d4103082c04015480200662150300841072041d0460401c400100300a00c0700c03106140c445402600840c3c10244441043e9061209806615005850f031100740c0d660b442e05130426800c00d540d00f00165003482600c10280c1c032580590900919000d0b00f01c8080d0217041000102ca004e1070000d01c400b81c0321480800002e0b94403011003100d0000181c6640c01c915 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 736775647 1250 736774397 736774417
    0x19062115060807031109010f05031f021b011d060709050118050d0f2a050d0c03050706020d02012415050702130506040507020111031f0305030406030204060f0e0f0402 73
    0x703401c6a0701d050040c204030043e00300b02ca121412000c60030f01494000405c0b4050140148010102807808001a07521203002049000389460740000d800307141c103150b05581002e448061212500d40040c12694000e084140c5540e40400581600d014040e04c00220180314040f40e4503203181c014148401075609440d1001c09054070744200002140646802d070045c02c0a40c4540e008031b202e00250b14004004500016449500700d900e1032011041aa288100c0f00c00c84100b40d80b24001a815403c118050043c0d80d04058a1485010030004205900040202c00c0800941c000c11409050010050b00e4284203842c9030000c1148620901c412940c1150708042035030b80741001444c021403030707001c83c624030b500c0c4d05a48521540d90080010904185c0161a0b01295034802080200380c140b4501081c1d010117000060f942c82a0801d0310102c208803515040134540200031280c0f80d80da15580140030350b219003d4100000c50615844290900034492000e810741c004244640d1045010140300094000880300 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 736776897 1250 736775647 736775651
    0x7020625030e0708032b0b0108060409030e1504211110120f06051005130303051c0f05040c1d010b0d2c010b1e091e19062115 55
    0x2d0420080004000e40d40c6460f004001801b590382c04151007002c500c0104014074281214105075a0348070520980c0030034100c41c001015080c6040c00c503040751140340d5164101942c2c1074400340a0408101400880f0481070f0b4500810080d07108280041324414401070a502a40c44055494500002c3e030003040800b030f1610800c402c085010301c1003542c0c80b2107400844a5960700f4184003030308103401100302120710341c01c200d4500f64002e502803814010610010f81004004252410701c40d10a8460020f0344e503001106200c0324800c21000310046c042503d049510740b1500d00c1c000703020001000c245003102a01e18189109a10384023600c1d07841e0340100b1000300401d40c0c03102c08081c180304c00c440e04145150001c00590008010000f82c40c01c65440044d410720030141118004512a0819100000940240c030000455110080410712030007014041c050485804000c015082c4a5946114201612402d040c040c0f40e0707580305080c1c2e40401c1007039404080d0400e21600c002291154000c1d408c031210030240 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 736778147 1250 736776897 736776899
    0x5100902061c05010e0a0203070e01180510030b09100614030916060806040f110a03090602090312180a0b0a03021605060a09060f051326030c0307020625030e07 70
    0x44001c0150500e030640c500b0702d6441c40103001d540f00c408415070384040009401c61031800c00b42409048200d00380d01c11410010030103d040010580500044020034014080f401d124003001d8014024010448541e4021031610001842d080340510b40d03030040f1b403085d89810760b0040b00c031101a44a0351004052080c248550500c071030701c80f201152000c0061006949000f01d13800d00c207003000203403504010120291414142071110b1403602d5012640302d86203604000444602a00d44500079020789442c19506010f95214a003542940304014170680c44120f40b4001560742d52420040d0031003550084c050081400d208030070304280264000d01040b0003981446a14113815698a454000d00300c4071000c0550300c0d0610300c8200071300c5019290f90140d00c840184020301c0c0030001c0c2100c0c490b00030300142013003143e4104002680381840b8001c44030b842c2182c500c3c0d980d140c14901070610344d0080d54410014841d10002480413001d00c03070310f403108010300f07880400e6074490344078214045c040a00d002103d50142c084 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 736779397 1250 736778147 736778167
    0xf0a1a070f08090102060f01150c0201030e060108071502070305070308090415060f0314060f0405180604060c08070302090a0b0a030e190605090f071e1509030606120510090206 77
    0x10301c4001080c400c00030b481c0d880c1c000d48002818400c1c09060780c9031914800f4018000342003c40d004000d00c2c111860700d80c080f0941c60004a02400450b04003600c28001d4900220708907402142040944105062290075070140c204200d036912013a200150254022080500c00030318188010a000070006101040c02c88148611034403015541d488040420321482d10740014035054007030703030000b604480a50580751030302c03401169203000032807001d61040f40d0b2900007542c41d500c40200407030a01c060500b00c801e286403a140960040c0100f120b0364003c1106c2c00d0008070340a00c00d0080360021400581520080d915001c41c403481500b02401c210285500c2e0051009400400c002c040343c6402030000c07070200c2d2035180c14400c0850b20060302151003904094641d42e40583c00003850030442e8103803080317001042084051140c64090941040316004d041c031640c0c004141c0e10a10755001d07a405200c0402c80240e641b42000f0050606840c0140305800c86502c0740c2c05580550300910650f40081c100600e004400e03c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 736780647 1250 736779397 736779413
    0x11a03010f0e130629030f0a060b060721180501021e10020a03020322050d11120f0c0d0e01020c0622150f02031224060d06050f0f0a1a07 60
    0x500303603000e1061860040804c5e0284c015181c501850140c0180401a80401c401d5466200344940175102d00e4413080320300c000e0386030102211503884c0c1041481610400c0c0307219045035200c1c000049030029000781c8c032001d480d110b940e01038821140305130001c0110300c4040c40201e03020aa40d0b01078100328005c1ca842510a2191400240b800d18440d0798016642d161224000f4440e140c10103003036004428000346000042c90009480008005a00f800c214820708040c046d031a26480c002c018082250105203c004032000c0300140003001001d2091f04c0001400c502c049940144100450b80103034001080d02d0201d0600e03400601e2400d09424159140381200d03681a02004076980c0f000000c07031040d00b91000030fa0350102c42402c001d0024405580307486100d8082c1189008007810030415212012420003e8440c4801d90500300c590140040c1d491f8010300740e00200920702c9200d0b4a01980609042c00c10520300314484c0c1004150043c40c0041c500e090614040449840e0392004551081c100101c00c0030076005 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 736781897 1250 736780647 736780661
    0xc02012007030510111c0e011406091f0909030210060602070806011401140a0c0203060702030901021203100303110708030c010501090609090c141801030b011a03010f0e1306 76
    0x3110060100074518a8000c0c603066600c0b09104225280040c00b01d8100c1d403202c03c440441c82d896003d241c1020f03502c01080010141e00c10b01039100e61070440f0102d41c6003d9200102d2150b0b4007110080c005603038041c160b0400c20038100b01e41040201c58482441508210386c00310764054040d104a5480c84080d0301100100d5000e500100007603446107504106801c1c00b08041d83c0501281c1c103100d840000e00900180c144824803c04c6290f400b808140401c80d82e00c5080710080c0c1c590014101e500074240260701a48035446030301e40c0d41c014003d1038000c0c070362005954102d030700a9910b1806076860510b1510219940154204039003018010301300000b42c1c92508002a000d5130407413a000081c02d514050f4103004a4141d0350041200904002043d804204000f44c90f40480b1685c0e00c0740c69892000d44c00140c0201d040c2c51000c0b810002c540004014058035000d06410781e2918545403440b41e10079000f04515010912407c000105848010b0041c15180d100c0c45800813200041c1d00740d00355280c1c2e101c0d006d072502 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 736783147 1250 736781897 736781957
    0x16080a091106181c2102030a120b061b12181c0804030b10170a0f1121010605011b11030a02060c01020901020d111002090607060c0c03080903190c0201 66
    0x12910400c4207100c0003071150202001d1030f44400e00801900003006e0345900036403203220140601450f1940048401e9001024100c0000380603c2c0d840a149059803c042c01c5080080311620034400c40500548000040341c06003c61030f5001c04a415440042000d08a04016640a4504500c40203c0000c440e200640040d511800c100c0600b854003c008032030301560f59000c9100c0e8907400080046118002c200780101d03075041408108041c52f5424084110078546000316044420141028448101d01c0002c01c105e54411000340402a039882c011100daa0f40703030100004011031070004000054401c407800d5080100035050b100b50391141d0b00004e80c1c40d00540107025460b5000281d143e1550b0381400200c030000e04a0404016192600706903d5a412201142501566000421400c1e50fa941c04c01d9840c05680b2940511101500c42d000a040c080420001c1300800c45c04800701d000c0304c2004c820744860703c03600c0c0864040c0400300f81080310f1450004e1000d070705201b0240c0301c02c084510120700140c19030704 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 736784397 1250 736783147 736783189
    0x2070c051c03030c030501031a04111504170106030809131103040812090d02030d0c030b040f1e0501050d0b0601030f05010e071404030803010e041a16080a09110618 72
    0x3042c01c0c0501501d54540440c01003518010051000441607001107000d005424081c8802d80d42d140760004800c03070a402e143e0792001d00c045200880b04002c1004105650001400b07041c00e0410074200c500f80c030001e000091001d84184240026070610880c50014510314a001040c070b041e181209000d0356109540590745d140c1c001407034040380d0100c0300406800c00b003044001c00c6c0c00300000c00001d4880c01071f02602c002c080c2e216444081118820b40002d00c20745030044c01001211200e101080050080840038001107030f40d001000301c40d80091003128100c0b40f0140905480c1c0c5030560701d00310004002045103043c142e84400070350b008562441101c0c00b1f0b00b1210780181d000d080620029000d100e00e00050507404104210038000a50f040b01078a04484564a5054039600c80d4034000c1e0303074024200c1818038010705050420507402d00602d0303140c1e4815282d40f00c096954940101010a981404d017010340038503502c5031010801d050400c01002030036400c46c400c0f00c4560b54000080e50290400480c3c40c003400d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 736785647 1250 736784397 736784449
    0x105130b1c0b01021c18052206051203040303050307091d010f140105090f120307120306170d0c0204020f040b0c062a0d060f0602030c01141902070c05 66
    0x740c118451000c6040c030034002800196491521074201d91201c400d603000b005195040500300f520803030080c00150900808501f6007281102280c80c8085558070012039850038a50000f410741860450448140d184502440c03905046880a540d941d101401007402c1008540300090880041d4802d1400d5011240940ca801c3d454001d4100c001d04482c0c21403140b5003504032000c1050ba030402c00329a40c442041d070b80d1440d80c05400000404d1400545044c051a0100068a10402511140b022140605038604000c1144c87c0c100c040b64006200003c290700745e0040d40c034001003500031124110b40e54801000585440c19101d2010107540050788000801400071540c0b02142d0b105112403a40030194020801c510002c0f07010843c45070b2070001d00000b000d000094941001d0f810b5400c031001820014004103e41a84c5800017035482e40b00d00d400900c00d5181098030f40d151170100101c60302a600510040c104040c62644241c000c0d8040340c2c2c219444040044c1c0042c2c0b50b214045041d51115251010300120 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 736786897 1250 736785647 736785697
    0x2040b0c06190b0d0818100f1d0d1e050f03040603110304030807180b0f18040207050307030c05030705061003110121150f0e010f120804030f031b151103090c0105130b 73
    0xf500514014408481400741c030040c190728ad00d074000d941950010400e0076000b201452a5206044210020f0068003405103415079003413000000380200d84040d6000c21501001003041303e0640015140140000c1011000c00c401c94420001103070800b0010b60a200c4190b0394220000c01d55000c800a6000b0340804510f088a41e0407110400301559400e43c1c05514000c00c0d95030380c03030320391090b600000d05204150800742c0610504000b40c0b452035900504590007414060140611440544011103005116101c1a940d40d44100314451004e04c00d8110b610001540f4004180900182e5000107151111407900048540007101c0010081c18901034909180d414400b02148100355600144003442204201c4c0c0700103000c041c1246d0840340c114000d03201011641c502120064003000c0c6459594840e819003a01348000030483c00b4800d40300003030030880207041d603507109014001100c80303443c0c076000790b4041001e03540546c00800034040d40d2140102800e44945e0001c140e078204442e82e44055185002d5900d01c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 736788147 1250 736786897 736786907
    0x12d1202040807090e07180902130b0a051509090408030916060c0803130506040605190606081302060712050712080f04020f0402040b0c06190b0d0818100f 68
    0x2102820901503140904008246075114018880c10120716960791440d5442079003444002d0241550035007019007010050aa00702502d890401a881000d121041c0c4124400502c81d4038605540605103a03d1a07240c401004094800145402c0d100c5d2410400840d0300d640d0155580c0c404d6209250180d12800e101c20070614002e040c220540761028640300a100c00381d00404002d030004e81c007501403a603d9640c02c0c10380e0702d84615002c0082062007008180300801510b9000300340f08a142500c103180041203070300c0c0b82d000da8807a40b00e040d0114843d840490760401080308403241050018000034a08405591008038035030304240c030500012000b1490008101c0003400700480d070703100c40c60280900d080000310409082e8026000910600084100c0070b0141ca43da01954000d0240070065600c84c15000d43d8991034030002c903401c1e1404000c40c40541f00d0400184185111404041c20207542440c5030f41d22098103500c1103a603603a41c425078055036122561402040300c41d0b046070707035104a071000e605500901 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 736789397 1250 736788147 736788167
    0x504120503040506010b030603100c03020a270e180f0607022104140a0305061504180f080a02030903070f0801050709060e06070311010606050903060f06100806012d 72
    0x82001410020700022400000308981034801060202c0d07981e489a84c002880c20340e00202d0b600615003411140c406041c2c265016000d0100b9076141c203540d041d0700710410710403100043c5841030a0340c00c0500c14041e00c0382d4004900d60102c12848660744115810301c1303c0303240007807603c4500d4079a8801800c11507030380e07130600c070100c05442c1d070031320704c00510b0700c00001d0903414052405a071480b0300c44102c130449596180040d0500554102003928904c1c01e2000201039076940d900440d07030090b0b04010352210044d4618160385280c84d001042c3c0c2a0f07000d40c981d2031610b45d03401903448004510060102e503400b55028410710004004c0c68915500007403500c00e405003541c20050122091002006042112700d0700003001442c0300208030382c1700d669404940303000d4071020009540b9442e25840c0c0320740803488540000050442080460450382541c0e22071302c40700c610403c110b80b101c0c0c010000070b08440c540c0d40a104c00c86c0d00094141440e17054130a800c0c07105141c4002451ba0b0071041803040100b01c40c0160845500c01d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 736790647 1250 736789397 736789433
    0x4200a0908010203040218040f020a14010f1106060d0804030b01060201050117060f06090a0f020c060618070518040603060203040b0a0f06081c0203040e090a03020d0c02010806040b030705030f010504 87
    0x942149001c1d00040e0002d41c0c48a13426012a407d500090204400910180000c9500500b14a0201e4890300c4200c2680c0e44042281d000c1981c1d404455049070007a8004102101000000c103c19502c44042c001000580141112001014800400019442a1124007801d8150300008596241075503402842c9050070550303a440e005241071084055903d06034903440700782078540e42415101c40500c2401440000480d0040c0742c030200c3d149054950111b0b0207802418112990080318807901c1c041c501c0200269031050109100b00310108507142071125864122500030800160030f5076a4032810181e82c82258101c8a00e121101007009040c802d100e03031100b0315101441041514140514a642c6000b500c0c4109080c004400c0302585442c420070403a0b004d072000d190400c00c03d0901d0103880e507480b42410001c90141c020700104082051081101d0003041da016551800d06442c0c80080c080100313807920fa0703140c06004010000c1202c0c0c408000c0b034624901041d000041d40d02e401d041c10100202043e0001c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 736791897 1250 736790647 736790651
    0x3030c0a0b090c0f060304060c110109051509060915090a15020904050a0606020309010305090a170d0c210f060b042709032a02190312181404200a090801 67
    0x840420740317603082034039401984045c000402410302c140644060320300001e600410b60030f0041c00010080b01180c2c08400801d018455610380c1c441c0395202e61645422102c000d02c5500003625840011051981e461300b1800490550300d9182041d25510300c0e4001081c0003202954000032811030354205440307070591188014904014060401100a4480c400c1d202c02504064584002c1150403c0a002c03416a60358071901102c291000e026000c100f607001034410034961440c04143d83c200f2400303100d01451603601789007400e95410382160007500403c60013820740d03000c960750350010032403d42410081c405006a06440e4a90b0040082c00c0010080c4594141c4515404c202c41000000e0300700b03000d007805035900d200e106c61080b924101940300c2c500702134000e135200d01c04014020310401c0e501c110343c0031340b030280403100b00c083d241000942d80002c031000c5086001c010f40c4d5081000d0300814841901c0001c0003040030070410902003640724050042d003100100301c00006054034082d0f8008000c03034000e128003402 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 736793147 1250 736791897 736791919
    0x141b1605010f0f09050405090606090c0c0d052d0c0d0201060e04140a0c03110a0501030b0307150201020c03040311030706020a15020702060c0a0c0806060604080a1103030c0a0b090c 79
    0x9000031400380c1c208007401043c10400400c28000c0c02e49101400000c1c20810151814000b46591a5000d0320128020ba07024408220341c40340c040122600b07161000f005003402d00c0400c0044030795038031005070103042e200b29003d82e5080c2c01c04000079003012120021080e442d4401d0903a01d40c2003901842c104c00030341e03140030707010442da140c1031103003540c42034006c011890705003600791100d800d01524250007014000f960001000700b002880c1000c0141106540c00380ca803a4403030b001034081ba000c290049a056100d20790401031308442c05020b500700a070740c0c0700241c1014a41d905680c9550416082198640520310065519080420907003008000e28030042180c02d1268039500a14445445035084507a00025464150b44a4104035005440880c00b220300035501e506090310a0011805000381d140180b10101c1d0540c0307002001d03a0184d4103807101500140d4095900c43e004550003407096501070006101c2e0b410510810700c0302021950080b15101d005107000310905060403040006288941d41843c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 736794397 1250 736793147 736793149
    0xd0506360708061f0e0606090a0f061e1d0307090c0e13060b070f062d060b21090a08030115080708070e010c03120e071403030306100f141b1605 63
    0xa004100d4a5074240d001c51038a1b000003080092060001013600003026850018142d1034494602d0110313a0190750311105140b031240300b0030202c0e00b00300601c8c0018180040c040c02c2d40c89034110140c080d40300281101e050582d964405410f940100900c20046080300161100e241011492180c641420b440201710303036400c00001c1e041c240170350f4001030320a6103528111810006198001e144205e07481c4108403500020118900003140d131000d1400c1040c0c280100001c102002d00c00303903a600410710000003001c1800e140c41e0550600000d042030341030b1040411804c0802c4140d00154040d21f043c81d03109502c1200ba4002404000c00600040b0802400d1801c1081141e4001e003000d0401009203054001c1180c0c0741001c03205001c15076021144a86000d043c1e8040e00310002e0884200d40e00c01503204110f150f10070403da264041142da8a402c00241c1810040007803240300c01c0b510714006401d08991400f0507000180450b08444000070015010030076084082004010902c0c0a1080d11810548070341400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 736795647 1250 736794397 736794451
    0x10f020903060f0f010b0309032106011d01050319180302030703110604080a0c05030d15081b090c0306130f0207060b03030901020a0314070618020f0d050636070806 72
    0x4402c106c0e00c000d011002c1a280d410034001c41d0300b0180d5030700420000c3d000c0800e00500360517040d01d00b1408909a54010041507000c45030700300142070140c40e403a0442d5905090100c0810482001e074004640c0c0e94242000745140700e011440c0d4901a0b4000c50321123856140240189a4440100c2c0b40c9520800c10080018940d0b4202d42e0030005902e016000f41c0554a007a6156004031b40c90303091102e0410f42009840f0904010441c220b400081c00c840f46042d101200307408112500c0c4800b6042040f41c40003035500c80090b00159044032014000080b2041031410920444141000f21012142c00064038003e0106a000d03042215408a0195103040d0341d290002c2e5890080030001010b01c41c900e04801c50864480c3c06841609800210a009003d4682c40920809415a60423441036071420785c080b41a0900d03240b9180810b6000c0002d00722a01d4507503d88208148003850040340039680761111400811101d050040302550400801040d4140080d07181401e00090080e500502c0c4081c010400c1400c40d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 736796897 1250 736795647 736795649
    0xc0c01090e0f01050f040608150415060f0504201305032a040924021c060b0d0b030718050601020708120d09020f040207150507020a0c03021908010f020903060f0f01 72
    0x40318040c0181055002141c0505400c0d4080365260092881c1d03208500006e9034480e1045208030b0420441142f00c080320001c4942c01c0c020801a50000b00061106081c00c0d80022071a4861191903944035075204464541507006141c2040d4000c108130301000346040c100030071400d03010b4982d44603840084902074601c084007041d80040c0700d141c50b28000c109010305070340c0e401202d072401c2000e010242c3c40e02904002039480914150101c101e10034414991120707a00c14441901c205201d26032401940c4948000a0121060400d6041c042c00c0000200e0350740e1039400c24038083e540348000c502032034040000f90a01030b80e50b00c80400b40d00002c5209000c0b240c3c1004413407228929110002d8400c0c101c1c0040340a500f500d1513101d801910000d80903081c08070101243d02c903450000c20600090352061012600e41041700c00081c0410110700e42400103281050035200b4035210400001c0d52036684040c054250394400c80c80140083e80000e4094a50070280320150707004410700b00504a9003001911078242d0b241c1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 736798147 1250 736796897 736796899
    0x120e300c011104170127061506021b040606080c0706060801050117190321090b090c10092411070e1f050306010b160803070801050a0608070f0e04110c0c01090e0f0105 73
    0x518000c0070b01f00026540945601951b100317800301580d403103810296403202044460b15014001c20700c3c0841901d0180110740c00e80b015555943d155403600410304180313030400399048035600d444117070120350a24244150750013044800100400c080c00003100d0760502116002d82141000407103036000109400c40c1c0740811100c6115054a2400000d5070110002c0c41c4c280001080030000b84140544a5000035082c08a00170494410f81203c6140700169409170b240e110b028000d04822503802e144124040f1010040c0149041604000314103c02260a241080e00f003403818407540c40511040c1d422a00034840d4086c9440301c040300b4240ad040009030345100510601c00c500000040c080274880b84039001074046a80407003000d4032403c00c8880500300c2038090156601031b80f4400000281e42d40f0421009018502d1500c0d07010546100100032283c2c00c40da60102d40d0025160961000107001c9800207000003a030130f0010f001300c003c0d480c0c00101160a6548500000302a403420300c41c12031010b00d440341c11198 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 736799397 1250 736798147 736798211
    0x40201030f15062015040c0f1a090409020603090f16050d060e01090c12050d030c050a08073005100509010b030a150303120e300c0111041701 62
    0x4c8001e0328000e00c242c03d0644840720303020ba18101c2400800b03030541305000d207200300c10008203643c0304c904000d2040624410170002042c034040c0202400c1106005180da0900900041052100d54002c101180d209960800b81c1c2d030311082c00501814424080c00120000103031014800c140340c04001840f00d00c10000182142d03a50304002020304400350312901a45501c16074030345000303986070400055007440724016120f0f030096403d1044d81600c6841166100341450300e03030a05040e03a400302202c1d2a00000e04010034004580000480140d543d0410513803007800f80c0703141044d40d001801000680d0320140140021030043c8005112507a240303c10281510151605035480e80d5907000e5007809442111400494018910b001005040d44842e120054400e0300200340091483e002005545a514107400e1807201c14860000c869400e0204d1b6142103600b01241d06800c100d8605801401c5600e00c0004688020000508111400e408404100305c2040b0714020804011440c074100c4a402c28000702551910b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 736800647 1250 736799397 736799417
    0xc06020c010605031f060603050f1504091502250b07210c0f02010b0901080c060a11030d0b03060c0a0503010e0a09140c013c0207120b040201030f1506 66
    0xca4250b01440042000030101c0c1e00c2050060882d601000c00a1900001181480d1000c20468040c1c01900e0142c403005160300020b6450101c206046d1400011040e80203884184000205040da4800c07969100c29000c0182d5401a0b061401080220f000501410070140c101400100705d00304203003036208509082c901420000c1c1008191440c8071a050000a03603d08540d581034a94000c283d082400550f80080001031030701000c0241c2900248682e03411030f440049090842d0070090081c2911100354200f400d02030308010601801c40d000b01c034905544a6540c00320803140e14040001c81e82290300c04100d42d06e4210b02e40c0f8000c00d01d100500903c80c1ca48581d4000c1381d061711199000c0520070340c0151807585400001200c0355100c01042c42d2260000c1c804c00d40314980880310304003490191100700d01c0d6010808070446050744085044003442c003503001380c60000410700c0240500e419440e00c110ba80781070900c0c5c00e01c00035080f2800340d01c0500321589446280195100110449000d80b8118203000300c01b1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 736801897 1250 736800647 736800667
    0x306020c0d0201090503251403070b06011803020f0f090405210309060a0506120a060f060f050604050f010c2414011d19110918060105120a090f031107050406060c0602 73
    0x30406401005140c241502001148c141c400320241036090320603402c40f0700399140e940044540022220340400c0c252006001000145844c020b81090ba01c4050a442c1c11058204001040301c40c0454041c0c07925000348405081c01c85030030341c4250b6007244000400c0e00b13608200c1c0c191030340d5450040580f0f40355a9598049410382d81c07501c000c800d60707201110445000f03c0c4a4584034018200d5044086903a6080040109048005206c5141901c9000e44034605207441c000c10012040088a005414489516503000c0890412000048844481500c0085c8120540090011114050780b40e08005613640d005014103000340d400e608400084807003078061512004d80340c1d0400082a920800034131f03e000b07090900d81c0d18001c0030384034400c002c8030003444140d00e0f4403c00707448480407192140011003c00c2140f150100c0051a20b07001012410700145038004c5035504c58101d09001419800305652204440124030108001c01c0504070640d001e000c0c1610344040900200002c441c028103080d004584200d031 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 736803147 1250 736801897 736801957
    0x30a0330050c0703080702030307050708090f061b070608040b0109090312020a0215010504020304080417010213060801032307090e0c18041b0b0307051c060306020c0d0201090503 78
    0x40004100801c1120303003031000529142d5480b4071022404151030b007000401e1140080150b900c41c0d070042d125149486140e9a0342d100540c0b109105039881021b10070960015154180a8050000c202107081c01c00d01652903050724003410355008000700900741040000054040201d075044803021030000c10200d0044c942610141000307402000c1603440400d0895002d075001030300760024131081995000590b00e071424407003a0700c012580a0300b650401c200c1046100400313154480c50050b000001400c0c15600700c5c0c10b4100c01250b903c09000240418010b10074000036807440340080d6070011003c110003c0d80800c49407600c181d44903d650341c50740c400d07214800300c074280445048220000c1a001c9149501501041c036010265800c1c1d4600b0111002d505008560a00d11019a0034030540f0350f0440d80c50b003030201c9055001440350303200e03080c1c0502420f03003821260191101a6106110140e00e500310000c0f810f282c401d103188403008680c100051000070580110413101c18020014021842165458400d84 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 736804397 1250 736803147 736803227
    0x80a030f11030a09050105211f0602010908031302061606021314100e150301080a0605060904031b0312051005130b13090c0b031e010f060203030a0f1d0a020f030a03 72
    0x40001c8c03003004030603c2002c1c051380901c1030848030306040d580c448404034203c03851404020710700321042020a410480042510451501c002e102c01c0c900f00c1c1060001e0300e45429482c04466003600800c00b641c01e0755582c40c008010b0410910031074441c408010000d10710821801110f07041c844480d8045a1580300c54108103d0040c10080080d80c9503921b41b9040ea80e1241005c080e40d28a281c100420510301e005082c1c24040d0f50156075440081220b074881c03401042c4003800480520a40300100400c60201d401107074410400f14080121661400013400b5104245502c54120b5602d0400d00d8040d9a5640449010303034044050001518100f924000c4203003070450b00550b003001400300030805801e41040d040100e086000300100b03c0307a42d03140045030507405540070355409a002800000c18044036640b2805000e10b81e100c1c04a014800700200c0882c1100c118450303502c0da0800d101040540c145100c0020490780141c0050440b266543c40040034000c4800c030f040d0b0000318490038828654110304400d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 736805647 1250 736804397 736804447
    0x50708060d1106191e030905060403120f09300f050c0703080f13090b1804030309060c170c0a020307290112050c030a0305031f080a030f11030a09050105 67
    0x180b41c1c0c40e413284003910342c0201c2485204034140100c0412003044c400e001c1c280c1070591140c002c041c6501c485d40e00359650944141820701c4507a46401140494001d07004d00c128031350152034072010b01810710303102d0748a45907940c1010100c03024800c1c60b0307164541d0007846100365099514145488241d010482400d00c0c2642c0d00c05032801e6804a003c500c5022800000c00302c0018010034142c40680d1855050240c640150315642d02103404000b80c0074004032001340b00d40c030038424a17000070240b24a59413181114002c44102c2c1c002012444030203c1883c8002502e03400400d5036442c1810044d01d8400207540f4822240300030a40d5040780c16a06030101c440b020140140b0303070300780f8107640ea6858294510380c01d03001010aa980d4410794440b4440d0381008600104840e80544e100c41c5940e0762540c1044007040d00040d03600700e1780302008001030076400600c081008180301307035030f1010100d4030743c4001003881110420700c0300720fa082001111303121600b20495804031042828083d071121214102a04054a140b00301 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 736806897 1250 736805647 736805677
    0x1302030f03070321090302030706050403030902040f05011806050a05101806030b0411072f0a081b03070b07060908041e0e011e0308091c060609050708060d1106 70
    0xc0010990081d04c0d0b000140c4421107500100c001001040040d1052035801601680080068030086402500315651250107420042100c42e516400b04080341c0808007881a49540d46005001482c0390903400b251840404005018140c203040000c0d11605003841400e1250b0140361140c8120b80c000d443c00010300c0100b45070400302c0c590700d26025014103d0a0899840fa91520909004001c1d4090507292000d41242101000088007400130203070030a94280744072590400c00b144d811550b00e08080001074221000944212120890708882105800d1141c0c0c2c8690404c2c9014022007034403006031a4415040140801c03e0341c8a41001166032040e50458504100c40c806507aa0f00462148544100c900010480b07285070b83c0d90800c46501c15021804114a41101a0403c04280c0300c1c809452892801011080c14000d2681c0890848510010407203036591200700411401940344100e40d80701d40103040070600d0b49000d00002d40410124007004007111100e04c00c2c18015140d14060b20900d004100302 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 736808147 1250 736806897 736806907
    0x51512250f02150115030c02031605070e06030a1205070309120803040209070e01020d0c0809031617072106090203101401051905100215040c0302030609151302030f03 73
    0x101007000512074400980700b030741060410f020b01807252034101d5080800d03004401001c1d5134218042d0805901d50300c21031001744140c041c250090505100854130036001801c0da00c2ca414015100303000300428a910030340100d020a008038078110300d140503580c4e043c5495690b0300c0407850181c0344000e6a0b0030442201e4258039404080041d02402107020728003c441002e41c50b40c1d044000c8035207d051a42550043e00400600d942846c01004070900451041d130780c40d41020848000b092070310703201015805201542030340401062625006401d00e00381050083d010380d50412120001400682041005e071171450b00070141880202d43c0903201d2141c0c01001c1c4e4070390554184070180039015007519005041015030001031180b41050301032030003116000070300d85254a0300c000c1010740009140940254003486000514030b80704543c09503c590300c00c08110900500b140141342c54058001d000d02c10681c0410b1000084035450074a40d54400440e0380050070b0504140b002c071f400c0ca10410b9400c030041c840810 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 736809397 1250 736808147 736808221
    0xf2904030807170106020c060f0f03131203110a050d2a0f030e0606210607051804050f01050906010203040302040219020d180b180303070303090507051512 68
    0x81d02801040259590b1003000140c0a500301070190a110707040c0075a1201c6410380d10f80c28494042c0801400b50810181448200103503800359074401c458240d141760002d444c8008106100302101141500c1d4501040000800b51201341d05105041e49901800800300d41c805151503950030580114192064814100c2e42c40c584110120005408900c00301e0301700a030540c42c581c031911407a0304038445d00300207203500d40700c800a02103103034a5280406076101804d004440d07511001c0050710b0150f20a580c0b201d41d2480301c0072412200c2d1000843c054481c0c3d05180500400f181c5440009064030790883d10350540342c403000d006070314611a0341e00080d04540003003020340c0a01402810b00340700666a400b90b40034921080c800f150141701180c2030414451400205104400c04400078102d40c44020020f80c00c0494130000091940d0002032084001a480d0641141045014090324000344020384050702403000c1c00c02c0c0c51600c0d00401003407002009152002590080910740c6030307030070b40501c14200400f4000f815 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 736810647 1250 736809397 736809407
    0x80406080a0b12150604020f0f0a1107030f0b011403031804020d0f020403020a09050603030a03050a060e040b0a0e0609150603160b04080105130807020108091f060e130f290403 77
    0x103031200310350360210f00005c1a0b0709040c004c4810b410384510109240006400030240c0130b404c000001401c0001d0f101c3c180802410800070340019600a034410001c0040a10b0503910b0b100058204521500c150032101c4003689001054031015085015030590002c3d000d40400c009002d4481000d0b8580d043c40d85410900f580c2e40e00500689000750f96400000341c0b610240c0c0140c410540f03200d03030103510410810105a01c00c3d4031035030300504040e802040859a81c00d49070340c006015a425904a402c910500c540c0810a03c00c046150394080090111840d0500301d554881c6003500300c0b01d01c3c0030b8a00c00001c0030756505101c3c01002d40000000f6401194483c00b140c046a0050300680202c1d61900021038040e0f01901240c0512607840390060b0300c0c107401a4011280d07941c01400b040024460703e400004402002c8500c0941c00b401c00c04d000070164589104984038000c0540703c40d500200410a101c082000015003a80c095041540e210f410a002810501e00c04500c5c0d000206d0075002c80306000426030302c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 736811897 1250 736810647 736810663
    0x209040f06110d0225081204080c120309010c02011401180605041803080c0403381f050d020607030f05040f060216050105031501140c0f010b030607020703080406080a0b12 75
    0x501518441410a00181c5d844001d100409070001750305104100c81090715000030381d0302510070b5204d24101444014800d1600280d0004600d040401000300704065900f4440c2021010086c030003400405414402001c241106000e00c0c41c004c4041140b00307114003540d030000c1d801800c0292082200680700803c0d1359024600640803800541c0303c1c000f04660f0a046030654042d40c1e00801c091386402d91001d41d180c142d40c0c154a114101220170013407521000041d20403e80306803800444040700444465a04410355816044640302d10b40c1014250007507102c0000b5a60303803a40c1030500c1486030f21030b1103003510140500d904c00b100580c440500400c0c107503804940240c51080e80e490b10310200c0c2d00d0310300541d4140001c0300c9408260032074211005166224641d01d88490200700c80440c0b500c2230307180c045810306108410100c0c20317a4403940c0b5040c16003403c00042d40d0022252010f050701c00d04580d25a4200d1059228242c1041803130400719243d6000c561005c0e6032070800401241c40050981d01c010340321041 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 736813147 1250 736811897 736811917
    0xf080c0111070b0d15090c0903020f0402070f0b04061401150206070309051c051b010e0c0f030703030806061207030e10020c071208091002031c06030209040f06110d02 73
    0x100851259010001d948410380f00221183d5003403000c40768102c0f009100e00c0301181998524841c1c009024002441040850507499a030364480c1800c42c0180f03c0b4142403c40c1c030a008a204200c2c4801103408107040c04520703907012103482d043e40c071141810340250241c0080006e6118800c400012450703d50005842c9035030450b001d0b11603d588503501601181c032000c1c4043e02907005001c0e0002c0ba403254040d00c525084050070000c2c100007403000d4140040e05902141da00507991201a13585507413040000b401c003903030200c0c6e5419001c407169010a03203800240c48010140400c000c049015940e0b49410389201c41d034820520400b61406000007405440051401e020714002c0c28a4402580610700848005d803180700010310740c07207103000315142003828580303419580e07031400b0311030b004aa6903250b444140400c0726038010f540700d0000c11220091804055010540c0c0d5240c50802c00c0103803120322416501941041d52454005068200000034101e9611755a9586500180500c1010881d9021f0900508 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 736814397 1250 736813147 736813157
    0x3040b010503011a061c0e0307060e01111207020a150501060813240b1c2a03030305060103022206020f1b040c2001091a07080403050a02070f080c01 65
    0x681c03031041c14200d44810540055a0040e803071140c5040c01c002c1c000300b480075031080c8480240c01032090042d0464040e91036402003a00009240c0051041602820000c4018135000300242403411420340314521449030000078172101140011034050003030041207d0b007030b00074018a00d03183c0c0721848400200824056a40407030010070110381c00050101031901d03040c0e80070041160021807010b00b07041860344036141201d150303102d820350141c6d40c540b852004200d4411178a00c1c0c0725840c41386450f03000000c072071001905041c042c0040d00011a0301b50603820850703405080001d229224000100c02034410044031070456038101d18614411480f4042c85404c41e407590303080c1c03045481038030740f00e81d201c100c18007a40f0286541d0303441c042045d1030154841c441401c21420140402002c800411035175403071041c40d200b0146d5464140509000504001080e03440000303501e440c1916000c1c00182001901920190400102295082c0443e0082101d80302a02d400a11903150b150f5410403a682c0744044548180025 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 736815647 1250 736814397 736814399
    0xc03010504050c031b03060a051c031103070c0b090d0f050c030c06131505070b0103050c0118030b0426070503040510030213061209080f0a031a0307030201120207080a020303040b01 79
    0x38448005581c02412141d00074140100c00f45c43c070039a0ba4002400c05c550181c00c1c840b00241540e03445120b1850300a0340d80d50070101c0b1041c1d00700500b400c00c4a10341001b031608200700f02070006800c92040801c0e9075004200f9500c0706d06442c04907142203001680100034000c401c22200901500107510141d99004404851403825040c1c10300c4120300414503581e140c0305030130005204980030581d1600381041940340c03a0b41407003020303100e540c00380000380d0055038a9003000e00d00c4019540d1010f840782427448402902c101e124910390354181d0000000303202a006103c0355100c240050640824001c0c01103020514a4603002a801c110340c0f41d600c1446014407480303111011003030307582c003074001e507000c41444500c044550b92400c42c080c3c1c0ea0420302d0700c4c0480a0303540c030a40c1c0000102803c0140444800101032140c80b204c1411004d000c072240286049100f484d0ba003820442917a0000b110010741e542880e007268800c00b14400640030b40500d4500404840f0081013a1103d554000702540c440c500401180c0480c0e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 736816897 1250 736815647 736815661
    0xf050105010527040f080a05070302190b15010903060f020d050f011a030a090602030709030b060a08030a140f030a0b1906141803010501030c0f140901050f180c0301050405 75
    0x6043c16001c4006260300d40082c08050044009503070ba84030340510700340c0c40b4204080d41c0d2240150b010146c0c80012400204e540414035030304102c4000c100041c04180061071716181c681c00780d1240c0c02402c2144c0541ca540d14004544d100c0c10a0100541d84000107101d9100c840382084c0103508421211b151003481c0c84005207450910303c924604868001c120075441100d60318620143d0343c07004203048142c0c1e0300c401030180080c00c1440110310520b030350f80c0c8040c00b81d4190b00d0725207804100949142c0c482c5400010902c07081c440030040307070301c000c01c1c40c108143c044206400c0c0e0901409901d4900340101404020070040b9142508100301c0040111790689400305250300900030001c03540256400601155a05070305d13a5130b044001e0103501480a0001070114003000080e00307480c42608101e070300c500c0c0380904000d05040660304102030045000740d00c0c520381d480c00110f0382000f0140f04d010322406204a0030082600c81940341b100180118940b00c3c0540381c4074940b103017182c1c020710856015900d00300026180d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 736818147 1250 736816897 736816909
    0x1701050103021311070f0803070807050712180302030f010e0d0f050d0506010306120f120e0d02090a150b04031205040308160809030f0f1b0d0602180d0f0501050105 72
    0x103076580109810448061031169600500350600d080801040030085007000c01c12500400c00d1407840344401581e64a05400002d0421f00d02400c013105020741400b1144c000b4009024120454080d407074840d83d80544003070701e400100f10a92010b50140142c003008a109135064001c2203c09068808403107080302c030755004980d107181140c0322100140082c4203101250302e03035801242c0c10020514010883e13540b00c4608005403081d0500c1180c006655419a204110403001e03046100c49081c240130004041000100f081100c240310003d01c0f0700080c400068441c01c25600072030440c0110003414130516294a02c0c00102d62142c08282c0d4540c001e030950780300080c840c43c101c0d003e0b80e03400309402d801c28070b2004150480c203030840c07801c07110f905050014000c540ca007000f4070352014183d40014040c52200503481c6061540c501116143d080e8078118101140c0c0310751414852690340300c0c5006983da40044c0c6500450803d90020640c401e12086000051215859803c00154000c0c002000640d0f40e410030020 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 736819397 1250 736818147 736818149
    0x110703050409020a0c1203050603060708061c06091a10053a051b13050601020606153702010608100e070f120b0f04050c0409141617010501 61
    0x32810041403185001980250548049a04042ca40e454a80e40c40500b080c0458940200084c0c0d2603003004461703e01002400c2d040816400c01c8840342c00d01d000414041280401d80c842d04d00c640c0b84217241008070640c41641d43c00c0d00b041d458403080010160080034544191502903240070300890205652605030460300b4825004c0c00049071000300028080e49030302045002d00b40005c1c500354020045071f800d1110016040b5034803041c03207000c14080c0400500408222000c0801c0e0310744010040c00740d80004015030420811119201c0310454603140310074900c40c8070110b400309407a40c0d645000e00b801051028070b005862043c10740149c1d49000c3c04034205c1c3c1301c40c4603e5555a0040711a02000f2078203910400c3c4801800060351102c1d92070300002c0e9001c0c0407980c40000205520641c02c002d000b00e80d0406504000780c1b211128850500c2d40b41c080c2e840300c80012551007545e075082c40f5401c00001c8400e14200c400310b442503590b800310b604100083d031541c6104403502c1101c080c5000400140603c5940c4c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 736820647 1250 736819397 736819403
    0x9060b04030507080303090c1c06090c0801270201140c0a0c0321080103030809030d05010e0601140f0919091404030306080d350a09150b0f1005041a0702041107 70
    0x8c000004000100300345003000c0591501015211003e44000c640e0b1030088048003070141d0080c662051400200c117003114444441102d19080c10010390b018011004141d10900d82c091070200c400c2008000580d00902c00c0c603055107018458081c0242c10024044154400ca03802001140f0f02ca280061000d81c2040c038002c240c40004101c900103100081c01920111f4204103c5004c82c0d0420401d0711801003128803c1c1c01c101b1609800c9000c00c6501e40e4407801a04040810034125400c0c041e10a05012050066035404c0c0c2c4514240e02e01e0442c85404040c1c00c40080c521050144039144400da500e03450b0740c100362002c0c0d000a081050104200000150954100c0015510703049068000081c400c510302d0b084403102002c540f20025103207a07000f42c401e11401158589070018072054545000c086a045030700c1c5505081d03040c070010a251343d4400c0c2c44500703200025980d0b4000603240c0d50088503203208a4006505a0803a0f51414403694662000f801d403680c0f081e2420888400100003288490180740001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 736821897 1250 736820647 736820653
    0x2010b06180f1806131e05101e0e0915041a180304120602040312170f06010504090207050a02061c06080303152106240f030309010c020a09060b0403050708030309 71
    0x11800500b40309140d000c024007035000001d0402e0071b0806142003111140c20004a142d01e860a0100038404d00620400810104c203448846c54250700100140000501c5200c21080501e000140222001d0000400c1001101105c000500c1c151600c3d25a42c07011054100340700ca12000000d040810341140c035041411240020b5041910337009904a551140c1d5074201c1e005070302840f0000c001003281c0620b4082c01541d4880010300812200c6241c40c07500000e00c2e4003511115401440b49598000c0201d40030341d0850380740965513000b0350a000d1b24041d07803084000d40040000070510603510340310700f801030b20f500803102c10300c14256503120b035a0352808161034078651030344a02609440c510344001d0620b0404c0d0303000740208015122040845c209a406c5039024015001d0f150102000d4904020703c040c214011243d0544481c0703480c011aa90f80a00141c46040c0461440084159034032042c1860050401c020103111043d15409141c8250b082840201c50b90300c114040403079041004010761344205403c80007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 736823147 1250 736821897 736821901
    0xb10180e0a1b031a0415080d0c0512090d02010e03150a020901030f090503030f04051908070b0f04050604060c110609030c0114010b030a0c12020a08070e220c02010b06180f18 76
    0x8110080481400e040e15400d20308100140003942400700e610520b4890f00c2c9c00802130600c0c1042c074180105a00c002c1c0b1040d00070808880c80b5a40c0c2d1800514290302071a00b070981100f00000300307150840d0040e40750408405001040500350f100e4005040d140c00aa80910451070a00a84400d41e00f280380c00a24680052001070b0001c40748905060b44079005030304460700a08070300050503a00ea1a0031003916060800102c801c1446001c01ca96a0411082c0788a6116484d0a48415440f0200604000c0420b510741101161051148031002130003c1283c041e190071f401c0c4510b0b62035407030384415000e03020795003803000700e4007803800e4040c54a0480d07007208109881c690354039540704002d082072400d14051101c201400703030301c91030544090401907482d911080054280700304007174940a98507030818444c88542c1051401800c58020890f0520707100040450010040007081c0e026050b060707405a00480c0105c0e50020789154401c000440100a4503107a5800c6205000c1c03000070f6005e921104424000180 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 736824397 1250 736823147 736823149
    0x15030a03021903090e070c0c0b070201120b01020309121e0d050d0e070b0a05030910180b15270901150320040501080106050a05040b10180e0a1b031a 65
    0xd000300c2e149110303103000700d070b070545409900c15042c50540b444000550200e42c107008000a690116001d800341c00b83d02d0381014141e40c0004e12100a8400044119844100c0c2001130b900800949450702c1005010079440c0c00d03111a41076031741000300d0700d5440641d414512206850404212444e60011580d1464a003170041003940000e04006891385140d032095160009402c102040541034016641d5591513690901c1d8030798518080354020406130551402541c03d001404200f400240d656000c0a203918554821046403294120440159000900e007a085074150f400004000080310440c902001141c6414442d10b00700c8150301c10900c44900c0d114030500104d05101c45190120410f14043c035007a60386040401d050b80d10a0f401503142c0c1c0c0d120384090007146041c2110102030030081d10f0800102e12007000244410307400c1040c1c08148641c0007990120700109040c15400782c640008107110a0400e141c0003001010301203501000300440300303c0a280d075482401509004040c148800c2c0c030b4554000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 736825647 1250 736824397 736824433
    0x110c120d11070f0e040218010605040513060e0705070b07110606042c010204090609020f0301031e080f0712110622140f0706050f040b03060d0f0b15030a0302 69
    0x7888040151042110000e2210960250700c0d0207080703081c0d20300080b03090510500034031800841800b10880001c400502c5940c3d4424192001c1b03410403508100d02c004800340d0356000b046190007180b4110341020410503030540200c01484050b00c03d0504940c03a6907051411a005481806204003c0d0418004100a490300342c116034074401034241c6a443c68500d80520741c510040a078000d544694001c60308200142141c07103140e008000c02d150651400003030403402c1d24a44814040100b003000850482003500381504502d0340d10766802811166207820302c01c420703034090300012005c0b10107100407039164a02c140b00300d00c14034429158000405030343e2561591085022249400f92208400714031403030b80440c1c0f001c9440e100c0008108050903078000a50308807410440642c000e0f030140b100402032000804103a02c01c0701c01304c031080715119440b0707201e000000b01c44c140850703400381817119141c01040138070007048010350048a8541c0314040c4d2503071100505481c2d0000b004040d01582102e0a82c0c285c2c0f00020f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 736826897 1250 736825647 736825667
    0x50405040f110a060507020906041d0d020714061e09030d09030b01091404020405071422060203071a040c030b1f0501140d18081306030c031104120c15110c120d 70
    0xc0ac0410503400050700054144c00600c0e0356080c5074084011829895018003528026003074a10410f0a012509030101300d40c1e00c995403500c1042c1764a03c1403282104001802d91720003e03001030980303a0f0b40604a0340108192a0b50006880e0314072444000141c2c910588102842d0f004003c42e4070415998540800000b414010111024002045194000c01421070010030f80e00703881d80032034807104941050044031011913800180940d401081104041181400116544e80300c81d007102c119540c892a102c107510100d5070000b0a8043c800052002d6400340b22804500c03c0c5503100d64110782a0381c6c1004407107512903000342403400c400c10007203e20700302c0c91504075505041c00c0120030300040da0142d8540115902c218028002c8140d0350009002c055418006c907075a170806841c0500c1400c0840700d640703440340300e44c0c40307421481c0118041c82000c001110f44424020012110159144107d40f00c02600380310300c0c03190914150082c04050149498401d40ca0134004050f9002002203a040340000d40700c0d0806 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 736828147 1250 736826897 736826899
    0xf0b030603240a110322020f031207060f0b030a1401180c1502160b16050f030403030206010b0702130f090501090c0503010c141e0c0d0f0806092a04050405040f110a060507020906 78
    0x20f0235444941d151000c03c42d58803002c0141c80742503641c5810741000d40441b00340e12003032150581424140c0180783e40000322011055049800040c04880210307040d4018841c0891182500c03044101d4001400046c2683c1012180020400400070310b040b10102c0e00c95040300300c640f54862494009005610206000e408a5601e03080ea81d8505040740d105c1d01c1ca0b0026040240175180e20014003402016410300060380185000d400480c01e1814075030005200d0024000d00b4108d00b80d90700b0301002010b0441e002260301c90f0700302d802008900c1150400080f4001e090044a000c0d41c20320440092091281c0d0024040c0b5050303901075400d10401c03d10440340c0d10f15080724070540d40301c28065202d210f407042c80600200043c41c2c941c459105a841c1003c0c00c070f004000c00d000e2180d501081040b190303142c0d0046520500400103075001041c00c1030040691a8000c9400c4182c1042c9000c0c00c20080101d24800d075102140603416413064002491b081100c1c0c58554061280054800e100e90001070805070091030b00010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 736829397 1250 736828147 736828159
    0xf15130f090e211303021c050c1f0516020628140904020a0c02060c0607030b010503070503061002071208031801020f161e0302010f0c0206010f0b030603240a11032202 73
    0x5e56500024080095030408500b030039044442c5804000b400c01c909002507900741c409a00d44d605170f0072907124650750f882d2010244880010ba10b41c0804032400c500300050780c02401c1d99152020700c5602e5452000300b41c00d0049401c9160f00e6420124000c0720b403500420700450516284c190500c05000180d04081030a41c00d0110003002080103a80300700107001c800f10044000c01e0f030b03482c2040d40281a40c505403640307030501c42c00700301340042d00754008200c0c0c1d4061420340c1e000d03100c1c0843d400100d10300681907002d02c4003403100c030686808100e8900700550103601000020030041d040349075402d080344111099602d403a90100151246010302c1514100b2a5025020165403940c00e0040e01e44041d103007000440060f5502e10021555401c035205070000d4008510040c5510742c148412844145914001c41c106150044001450340e0b074100710710325041202000c45028001e280b000f402c2d803240d0035100100e41600f09407204112584a10659118007070303d009500d01c1e490a040c840c0d0441007400c0c8143e0f0000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 736830647 1250 736829397 736829399
    0x72103020c0606190621050c0703260103060c0918020403050606030f03071b0f0b040e07030b06030a09150207121137060c0e0f0f0f15130f090e2113 65
    0x40c2c070744541f038130a803d2a15000e0741d8204610b0020030424031100c2144044c0b90700c0441d141986d88070307410241540d43c081000141141c0c03005054480fa440b60340144807088154100a84845085d0058812030307100314215011900c8039004c154507603054071f10949a6610034001c141c0401c0210200381d5000d90b802189803001921742419014030803540d04040c5500d0300000f000c10511511403461940900c031841c0401c120040f10000811900c400351078407494944400348141840354490b00d0820a22014004556032a181c0c98011060b07103a811030800800c140c02d86030040d102000c2011000d524080d600741100740c1107081b2404080c10036500c06101145030004410011759244600c070324a5501c1d4841046010074541000b50b07220341c2c013440600a01a188400420782c41d1080014039440d81203590242c4101c9007040b1103ca80905c04146000c150010800920300c420513050794103641038100140904016903580d07a0b6281d00e41d40480018000000d27182d10308881040260a1040b00f44030100f00403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 736831897 1250 736830647 736830707
    0x100e01170f10050303070c0603020f0405060706061a162004020c0105010509060a0501080606090105091309150218010e01030e10020301080705010f05030705072103020c06061906 78
    0x940c00840e441d5000000c481c0030b000c1044180c80d0103070010403040b03008620300091030340c1d0084101024415107091540100e444000c0302501010b03203020f0100500101e0311901103040400c040c2c42240f00305c40788040402d64101444040313030111274884a040745a011030f0000c590360103003025030110307403c00107503410313240740c0c0196556000420300d088480c0c00102e41541410200402140040c008502c0b5100a2100704038990304010781da907000b40110780a5444200c1c1d03d005070360511402d11041e522219115140c180542d850303000010035401540c1e864504046501814121320a50481024489480009450541c80741410f0070f001d00c0c0c10315000c00c12071143e50b10300d403402902c410302d085085c0d0040b0040c07010001c204040401040d003440c006209402c0e41c0409085844090000004c100000401505000e0440340e07400110b881c1d1203ca10b80b403011071000070025006414030505a001380d5012540301d1030b005902a84c1d8010350480c513844145442d17415544d40c0c0c80c00700d044c1c1c0b0001c0c421200b8000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 736833147 1250 736831897 736831937
    0x20705150a0e060708070221070b0313050102070f1e0807140a060e070e09030703050f07061b031a0409020a05011b0b04141002190c1b03060204050a090209100e01 71
    0xe1710500c0c2c001d46403100340c410084c4a01080041d66404003403c034005042c0240059107504070b40c08195a25502c5c2c54001715400c0e1100c00384c0f4058a25030001690b0810024000100499039000b08801d43c0e860b080e180f10540c0c0081c00d4400609080701c24450040800c035003815441841f4072000440b0f010701d00d940e980400703550641100344000d4000c00c80800031000782d40643d651280492024500d44856940d000d442c501078150b83c1034100307202207203807010031655031304c600304190440c20125500381c000d102c0280900200303442c0844c8040400c5d440e010b1420107004c1e506149038000c102d8040542000c0c0119114100300700344103d4045001466004541800c018078002e90144079544076a503580c1002c80e2801d007100c3c6c0000c0b220361040100030000d0840c003d60030341c1c13003c2900c1e0803918400d85040050744001c0c0d0035000d024503285900000100555a8000d20881d0030503294000c25558512a2208900841c1000c2e80c01640a072802d606451203180c102c1e5404405040224014101ca142181 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 736834397 1250 736833147 736833157
    0xc0103020a0516140d0302030c160c0e09030901120c080402090645090604020f0409050118110a0605041404090506070e041b1e1b03020a12020705150a0e06 68
    0x311810b131091a2003418100b40100030102d60103040075841c60904203141c1d4003504c03070800501c41384182181c3c01e1040100d0719415100401030280481c20350f0901c0d082c1992654840d40449010800c40ca22000c480046400f42c4003a050190b100c00d0150742d55a024080004002488070b90f100c40e60b001643ca004104403820710b005082e41d034008461010441040081c1c0035940d200c1c0010003204030402070001c1002400d90b0340141e040d58101821f51103080032a0151442c010001c00325401c2a540c10000320041040d514024020070303141f1948c10703150090001c07481c4240500380c00110208028015080c040a884c5c0c940b00b40580006884d82007921011b082c214185c80c00b08c00100e42000521241c0340030300415609600402968001080081018211009401c0200d640c2c884500c0060301449c09084030340d030b0556055440c3c6000c0b4040f458001d48800b000e0904542d03c5095080078050603100080070400d540b8040c1c008001002040e62800b00e58108586d100c0402c22003581100c0c0d540c035a600980303 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 736835647 1250 736834397 736834403
    0x90402040306060503061b0304032303040b040203071e09020c10050720010c0c02090405010f0518120327030c011a0418030e101107080303010f08030307020c0103020a0516 75
    0x203a03c3d04103070806040400240c416403100c0e0003880c1c07449800700804100d0750059854103011680c017440003110041000c41c00507044c44200044100b00c184070010b20300d107214910031016220320039111b280f94140082400b095408240f0440f0051102d00c40c11b9004040c0c030450030f8212200d9107650024079058803411a0407800240352810f200144c1400036240b084640302820007403010000a14004000030680e40000e48240c07507200208040c09030a40c005c01131103e03424030901035807805a400000000700500c070301959102c2d04400251444020054a0090038008071801c0740002d5054007035010f03002c107918040540010440700011580c00d00c28400f004404819041d200590304080104132000340c80f20f900c40110154031000041da109955824080d800c540f294200c2d03000c90812203c401049100001c01d11490001086074880000518102c9a1a41e5050203d94a8207261501ca00060701c1c0c40740540d0160f018034081e903020f90050124240c1904d429410285150078412048072703011015 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 736836897 1250 736835647 736835651
    0xa02010b03100209060f0901050d1a01020d0804021503250206010f120f15020705070902032203020a2603070c060e0304051c03030e0d02012c0307031202090402040306 73
    0x801141020711020b0002080030a085007003401800c0440c0703051140019552403c90000b0b8a4402d903030080e0282e840f40c2d034070000100034040091100e0751018000400c15409486945850341c0014410040f15103c0c582c041e001002e41040340d04101d20b140c10141008500344c0e4954843c0c900510303154222081042203500410703595240c4101c40c80a904540c208100c00b0566500183c04200f00c400c6403040d4a40c840103140e1028280d2021800030f00072180300078014010140d002840b41019006075001d0014200141094420742d54402008400190f0080141c1c119220100214960400c4801e2012800c41c140c44514004803c17240140c1c0100c50f1107021602000003c0c0900c51241304400a054000e4004c5240030b0a11f8001112240c100b1054041c4020409942c02058480d0300110881842070b4101c813845c118014004e4041c00c0c42446c09030b8800c20341c442440708020b144a031b2005981c8454041c41c6445000d890481750151403000c0c401c201d940801001c03c04d600d50f44010001980500e00c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 736838147 1250 736836897 736836911
    0x109150b0304063c0c0f2a0506010e090d02060f0405010605040c0c0c0f05060708220f1e03080706051f1206060e010b04180b1f020d1d0f01020f01020a0201 68
    0x81c094460014008681020320b40b001002d00c0c190031001d421544c07550340c1840c604010400d87d00004c50044c40345013000504c131509182c0308000000071094161214150000019036400411300d07641c07012000b40c030005074800e40100700072140048410b81c01a0080c400804d070140c407500440c00340c07200b010302e09001482e54800c40d0700b408008007005000d003944041c107001503440c1600043c02070288a4001c0c18006002541940200506052044c3d51070802d001c034003800e560707081c0d0001c04c06242c4901da0603202c038550f50303100320a00e420725181980d600551650030521540c459000401006144007207050a003441c01c0c01001c440e4404c14028140040c00d0b000c0180149098003c0d204240e00100c198580346006200340500e840c02d6400b0b903004400c104c039501e8041201c1d64050043c3c0c007145604180d00440f9200707940540b801031103600d125902144e004090400d002c4a00000703c1541e00c8403200e01c020003c0c1c60b45018010714840303100510486842d0319070b02d0b0341c0c41e08a0b842103682c01d0160b076441c0c00d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 736839397 1250 736838147 736838231
    0x52e11030601080a29030f07120c091506030e16170c03060402090105150f0304110a12030e100212030a02040906060504080d14070812010303080109150b030406 70
    0x1030661102c03a513242031003030000c180d02d081c030680e1260b4802c07022104070811741111a181048102d143d112400308452000740e4420124816014581094a00c4038031941c010401c41e500e4040d05160300410401521100d1410300120000c1000d0929011540501d028280c1100d95008025001d0813108940300d01b0000401100d07890840860070135400b03034110104000c0543d4a41c01c01504444040c0c2e030f5a49041a200344120081c4074404420b40c04420102c280402d00c6501e041400700f5180175102c0c035200d0741e01e910f090310b440104040300500203208540350b520b10741080030210101c0755032030048940e0700303038243d50020058004551402484da03020504000011450095100030400c0d8200540340c18240f44076652074011a4141c0380600000c0012004c0284020003181c814940002c422030f2244024016244211303028402030300012111000421006c2c3c2e980301d00c40e1400e0f051740118002074503051000d4007030340004000361041a51544504010103006061410742c501c410204090484010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 736840647 1250 736839397 736839407
    0x5061804051e010e03070f02031c0206090d0504181a04020a2f1905120a0f080108010b0f0111010b090405030a1205040305093d030501080109052e11030601 68
    0xd244204540e040644121301850044100c604450f040a030f01e100c2c0743c52078004a841c10940d140703e186120400e05421061607030100b90399000b4821102030300e40d501c40207001205d0341d000e20b0140e411601058040d01064580540c000880000345614000c0301d5141d150005e0203e0f0844628200451103942181d440020942c03581d013a05000c2c81d803001e6002040481c45651440c49a0f24240010a10384004c0e0500404102e44580044080104ea40c0d80e564079400420308984c140410000c00c140c6400400c0100e030600a42071142c0c00a055034020750024001118014854444140595a107640c07056098950700e541d54032a0740544021991000303580c1004042608030b020034030401e46440b051200095002d0112000d4060444001c900d00003039071039204810300c0e09611024482d022500c01d10f42d64101480d030303101c000750546003003000740e9031500034034241d40c2c03100c00c01401034000c074018640001940500200c5e545600e0112012212228009812101c241044441078170010041110703c1d80c0c81 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 736841897 1250 736840647 736840693
    0x31409010e010b06130303120609020a030b042009060a05041203020114070302030c03040f0819020105090712020a030b100f08010501320f0f040504210f0801090506180405 75
    0x283c99092410f17115030f0780c0c12201c1c1840d020060801c01c0340000241400e10a13003001014061507c0c0441d030390f80c0794503405802080d20350712035030003a41401100d8201941040c02102c0e00311003040003510300841401041040d501089968090007001d02c00481c04540024181c0b0b0140e101e5000007403020103c0050b40300710b040041110040500400410008903a0300c0140e03a08254012820420010945400c00c114001d50301004002719800b14801030496054008a00803204041920000354031100d10743c41c1d0306495407004c9c1d08240111070800005a0024030250700c0982e102094400f20349a540160014900750301a1140d41c0d10740300180300034804c240d10300c01c4a0310304c0e4004003072030002181e0541c050a0080b2615200303608210450640784c50b0080420703181a0010010005403a02d45050340301c00400459000040c030441c524208518069210f400c40422180c4810405a11b0680f5141c0940002001d19801c5a0fa280c0c840d401c1c0e50441c1290f5020b1480340c0f01a002d0f042745d07413030405100004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 736843147 1250 736841897 736841899
    0xa140d0306150509011b080a1d120307080322061b03052401050912071712120907050901091a0a0b0a03020d14100618140907031409010e010b 62
    0x9120102c104580d00241124a902c0c800c0c203100903d0310300303182c014131504d24844c000351100d0300000e4524032195000d8450500b4042c8082031582e20b6a800049c404071542504000c40154010481d903c04114a203000c0d55020170105034150300d207111900310703020485945030300f11582034442d0841c010070010070343c079115010315510341000685000d160300c03802d4001c823260880849500e03600810542e40315008841c0704000c00f412100d075405400b04815910080e92045100c00c1902070f40e00c0d12080c001041e040010308402e00c01c0c81c00c0031490000c00081c0c00300035046400c00d00c1140400202c1da221034280a00030400d0400001d449100100156000c0c1c04080740d05100300101441482580040f40c2603400301d00b0646030042c1c81300021143e004c010704825502da4030b0802044108031804410021034010788926594a1103015141222480400c900340030300b5110500c0170000042c1c500344006a0307984400e4030310700030450b0100c411000b490103030305642250250351140c090403001b8409005003d1990b034 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 736844397 1250 736843147 736843169
    0x8090301090503191e110709020310061b080316020c100806031e120f09181e090606100e04090b071715010e03030f03240d0302060115020a140d0306 65
    0x10381c2000ca0084080d4488058144582845000e04000c007c11008010b0320b002c0d1021550781c1011010301d900003c0600c0364000141d02240a09501c00f410018400c0036a4002c0c1d659095884014218818600da100c5800845c80758650600301903548113030f40a507440c001d0300c4940303031810704d4003c1c14142036a004010001c4000c4a0060018540019444030300d09809004103413500140c2076019264440c2900d01644404121911342d41e005d88080c0d040d000d441042d54002c0c60b024003010310512220221540401c035044040011506c0c2002030600c041e6200074a000030030a1000350005040b00c0c201c4900b40c40c0c0f0b07150001009041900a800c035500503440c1c1002001e01d01e00841c01801da000500521b50420041022950841d20104262480c000100c01210f851f40303485c0912000d80741c054070300a03400c8102d0755104d441c40c1c101007540315880b236016406448540e08ac40c048000d0421042501011485249040804140d06004500307801200034013514885401e9440102912060703048060714007 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 736845647 1250 736844397 736844417
    0x121c0b0907020d0e01031104080601060e090709050103050a090206070b0109110c031e040302030a051b1002030d05060a120507050f01090608070e06070812070908070b0d090809030109050319 83
    0x640020f40f00b11403110310b141402c48680c0c85001280036080300500b080c4071907c00301d404101c0c00320115500e0b050340d03a01da56020f92031181a0070003007490420744412001c00c000d04818002540b10b600b000307a10851011022440318010760102c0e9081e0b06c902001c0d10300d0a05035005201d803030f81c14090894104109002c0f2410810301203817094503445000452441011f2291480c00e9803030414050714001c1d90003d080da8001c84c0039003089900d88004000c540301c1c04502006000c89440c101d084044020407035402941060800c8440c1002440302904041e400181e60380001041d000b122020141d00740b191000e0810640340005108605605140480c140301c2035280501c4541d0b40188013507803020842c58404281070070380010404501c50400054001c480010721540c020006c08036080c000d920941e142072200d5941c0c2e00454a4240d0f07801a00000c01b02000301c503407003007560340140300c8840c0036050040c0b07004d1031600082e0840f581d0381e40449050300046121108280500c1d2816800125414440429 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 736846897 1250 736845647 736845661
    0x1f02070b06030c011d1810030b01050a0e04110409020312040905180c09071403160e03070e0115030e0304080705090108010507050909090102070b04081308120a050c121c0b09 76
    0x7170004001c0991000d80e007880c2d25a5503510074501800c01d98450940e43c0c6542022000306140040b44e000540d40700100000000e8a410101400c4d01220390391520103006880e9075458070511800b80d00e150303520503200d00f290f05c051795040c001200a480d016012941e10703860000854107a0760000c1084130210150f81842c2c103022400f0800241c240d504440c0200c2c00d0740c80a0007917400e40750021a80007000d03004010005015140381303408403403541c04d0f15030340c80c00580751007003565650290041e2580f4100150041103803a031026000d03120900320303003001f0514402c80b0200c00e2031508940e0001c40103a00103001080070b030034540300e602d016119540080c0301c207150944004d01107100e03114a03035002c0d02c07014001880c0c0303900a506541201d503100782800303024200f030304002000d504014018004c0014030f400000d580800001c42d110003040c44501070f41020700384c010648170b43d00300d1180c0d04128043d0b1151400e041d0402d100402512045001030351802030b900c22100b08030f651116030305014003a82c00a1040e0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 736848147 1250 736846897 736846907
    0x160f1205070b030946230304090e070f330309080304030f03050709031106030a060b030901020a14070203060a090503130b0d050f010b0304030c03021f02070b06030c01 73
    0x681d0254210140d590300d51241d40c40c589a040d916400000341c201c1c81c5c001c40c1c0300c60400c8140000124082c0503420303040c218004e03000048903840050a840d0503082c018918800203400058240e603440a803030074960f646030032070b003a0340010129240c0c54006c83c1701403000e0401e0140c000050702400400ca107e4a2a80c44d0030303000c401d000800007202014904150080c0c03482a00040e107910f41c001301041c0c03203041502d400f034035140300481d41e8004030342000002a013075445201010100c0c1e803c83d0744481403401c01418484d0355407024080c64945c81d121100030660156140c02136006141d00c20006a540b44503400c0204464826100720b00c2c2c0d0388040102901507a80090324036004004075000040b8411a0f1a1980c0b0b588aa401400b680400410340003441c41501030203405041c90105c0140f200fa40c81c1d240450301c402d407d01400c1c401c100c1c20b00202c0c0200b48106448094a4480c0c011200d92a02426220b249440c41c500c0810b01150001001301c20406031105040e0000002d80003050544001c5c2c0002e00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 736849397 1250 736848147 736848149
    0x52b050906040f030509060f0a020f0717100e0a060507230f0306060c0f010c030b0a0f0303090614040e040c170d120e01110a17130b0c09040905160f120507 68
    0x100680810707815000e6887c0802c803886072181c00e040c01e5440352201c00107500c0d803203424000521801038201c001a40d0008059a0029503107440280c480c01c004400c0c150300500380320440c000144100d046400c00910640705660140c8407a4a0709224072003030480280000d0701c500c00d82c01d41c003541070109124040001c016282c00901c1140e2080c2c4581d90055442e00c0c00c1c0c1c9800e02e401d1a0760070041c1c5048242c2e01036000300803030b020980714200c1c2c00d6250641020960007074400100050342500c01000420302c070318189410400c5580c49546016602c0c0005c40700d9041c241d4003036270403441501c810002c8160140da66101c4080c11009810071101030304000e0514500c0500f1308140a45031400710444010a504c4003000310380d070001c40e986840c040b9000420301001e07002d9030107017038106101050501d11541e00740000750754800821845a0b80c0d44002c804103801070405182c1280c0c0b80c40d540e100151085c1300c2200443e004124148110340b600038048402c24456200e80f03610001444d80b000880c0001c250380e4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 736850647 1250 736849397 736849403
    0x31109151902010b1e0d02040f051b09090403031d1606030c0305060904020f040221090c0109150c11040e0a12032307141b070b030c1801052b050906040f 67
    0xc060800e0481c08991a00d9a50100035485842c1243c115044271065000c80d0245c41d4a501032020802040207403c02c0744039440480ea07003d602e1400140029200360840240c0114024104aa180d82c03111090302d414503507001420410280c1c0018400340d90b2521502c0300c0040149000d020a003020008980d103540c0203030000e4060740c0840508400c3d9142d54040f50200402c0d040d40111680d4070100ca030604000550721403000d0702440365000d00a6204030503a4081e9020400480c0c60000d14030300903100481d0742141102d941c0340034500c001032655544110034034214400003810b0002040d2510002008061980c503041c1403404803100000391452030420701c4612500b401060680314600d054030f10003001c2e501c000800d41d00081c0c90311a15520b0301c1c1a81c0300d4910b54102c503142da07110820b99031180003c41e90101340402c20310140e05500300015604070010740c10305150f440e03c0c900d5158405036203000d83d280903005c1803c008142400c4200d2041d958080b201d10060700346410140d5071103c01000d041005 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 736851897 1250 736850647 736850689
    0x6060e040207020f10210b0a0e0f1303090906080102070215130501050304050f16081b100e0d2306010b09011403071106010905070e03011a01031109151902010b 70
    0x181e0035a070141078500c044010183c4807001b20034403090701601034022a900140607000d041000240c248002001c00d0140814851201c00340d55001e020f03000030002007000798200f10f0b12080c0003603061040d11a103400b41203040c00150b0740705aa4018407003035050101b00c040f185181000700384000d90300301c2d2608042e50000d1a0880c0c1c0d9480c2d60500c0740ca0003049502181203400352221643c0c114030002c2007103007112240c0b02594000c00780054a4003101c1c070304248581d003201a00c0c8401581c144210100868454010100f8581c28166101c038840b0f900c1c0090550750522000280c02b000b044100900be0042040b160081c2c9486503890008180e429481154003280b10b012012682c0140982104c264020101c0e088036515a5178030429806008180c0d021400314641c02d5503504541018001c91003400d209064005100110310300440041c21907001141d40240244076140703d5a0380d070145c500c10020240d000d1604c40e07100c090789079800c60214981005580c50108150520307102c0303140d251244940c4c4000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 736853147 1250 736851897 736851919
    0x50a03090c1a09010f020304060c02060c0f1b011409030d030527060609540d1719020a09120609110a05010903080313140106060e040207020f 62
    0x71207445211140c0210892205011046041e44440c00c06414441026654a42c111090000581e10f0b48940d004a000003036903843e01e9000350404000402c690700c00342c0221400380303c0c09010107007040f0000494969040c0e119012071020740e4041c50030340c41016044100c42c51304111000013503651540348440c20616480b1700005100f512034215072100c4104107200880201060700c80c0325101e04044030342c248140812800b05440142600604c01054010701a4040d280c01551001c00c0f4000542c44617807598000c010340580c00c2850302810b005036081c1c90b0040c50b07800031902c00031b0048100100c0c0c0344074500d82c50040010b114510140d1844085140c2d100590b1107019950866054015400502c42101014882010810942c0c04a81c9640c014128800000c805004000480c652440745500140280d1b505201241c0090015500016541d420302b01100a513650904000c0540e41413402d81c0c0d40d90b4008104080d0442900100031030125001c610701142c5600144100012008840c000e0003807000e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 736854397 1250 736853147 736853153
    0x2060f0903090907020d030f090b040b09030d15170c100c050a06060b0c06061c02092502030301080c0301110a0806030109060204090e100c080708041a0123010c0201050a0309 76
    0x10448440b40b80150024a080c60080c1e0040d65410038078040c080041c2c5011a01201d940b9548140b00840340c3c0280002d0782622035446903908200040c0111406000c20090700c0755482c05803144054003160000500c00071407400e41e200d000c40200758030590058101981846055694590700780c0201900c0c10302c00314032a02d41c201a450071a030800300402c03451900c2c2c40403d01c404007001030480a120301c01150030b03a60741e602c10f0006295200500d240180b91080029005141ca0105594000c2c40d58100062041c9220b15a0b50101090705002000da00000014000c04d07505000d90300c1505420390080c0071030038002d450144031b841203145d180d080048400100700ca581c1e003900300e5400a41c10801c00d544580e21061440000c0c41114041075180c440c0305c480d03c60f030304894000e03940404e5544d00d03858a680d6410700306a407118802481116600c8048820b0f05480c2d40e000007260180860300c6060200f00041c00240304940c0b61481c2c0141840a030110220050b80d01c43e048900303400c1c080c5408181c400d81c6107 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 736855647 1250 736854397 736854403
    0x60e010e130b18070246020316080c063004030207120507170118050f07050114090d0f0f050c1017010612090203030d0b030c22090809060a02010501050114040602060f09 74
    0xd03482c0c21501554241b00008140c003202c80c84940d0080301600c1c2180043c081200c81c09038144102095034001c2120440361303180c8000540390041c2481c82c01c0000750070311303000c0c085002e82d0f81c08240560300300e1000384018980c1c10024003020b40384100d4200941c0c0001d45405940b041c186c8070f4000210399200c03420313150304000c3d0000c8548115200c8c00300c100317407540d144c0710b0b844e1071445014850703510640400203000e611a01d0307260020004083e01503d401140014000010054501079811410b904420300000e802c9941d030071892805100a48511007041d02001a0034902c040900304111162080f814081c3c071078503895044a11038142036444003092404030015200380d810103589400041101602c15010780c0201e508510101c040d20080c840c01802c100000808603000301340c82400c1c1444410b00502c40d849800e07028007524051781007164190000300c2c1c13a8820280380300180d448074010041035030040d0a2198015110086606150501c80001c0d030301c003c02080302e641841100301040100d1024 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 736856897 1250 736855647 736855723
    0x60c030e46050a12031404020f0d05072405040321030b03030d05010e010b07030207060804150207080a021002160b0c0403052e06030b01060e010e130b180702 69
    0x40c05005818079400d080c081d031a240303514400c0e240f40e1694940642402d10a00c100b520700f10003011000c40390384aa800b441840c0d105012400e030042001c580708004035000b0040328004201c0d104203400019560328041d0500c5400030003401c1030100c14402400010f110421400e1052091015440f044140e0f00c011000b420030a180d5941500000a0305143c918064028906903840d000312099166a038600c4a5028411583c0c041c0045e0412079007407082500c0703250240d4220303000f51440c502004c000e281d5001240d00c902c1d002c49544200107100c2c2c003600d8060115042d0f00d04100c40450904413002145201c016001c0703001007824041c03900182200c0c04071001e9074040c680040c00c0f40c800b5a40410312407101619485a0110604650170760702800840380a0441625400382c014080340c0d1800302c00ba900564918803a81c10f02c102c0f031000d441035458899118404906800011070750810410034042007030144052540d88090f00b1040000c80d80e0001074401c562903403501c55075154014179001c403a00c2044 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 736858147 1250 736856897 736857013
    0x2f0f0a090f060302090a09060b03060601021c091a0913054506060910122003150a0b120601050d080715051006051305120709020304060c030e 62
    0x3c11024403482e58965800710300203c0c89158100481070204003015507503038003202c50900507072001013103184003086441c01000c0014a401c02110054491a107085242101a0304701944140868129200d10301049100a03100b440d070810006800c00c410b480210710300314003140d8042801404031942d2515085030310086800500c907160391408504ad2080c0d1164410342e1405e00c82c54040c40031405950324601480101c07840300d0b0030700e415410b0f0750359403884030582e45c0800340004406542d01c1d04c040e1014001060388001d10b40301e041c1d05113800c40704041240c41001007240502030480701040e1207030b80001d030641942c108032180b5009001515280f507480c402d42500800c00c0e030f821000f400380e00400749c00140c000c100c4c144a801c1519225241100c050158510240700f0251900c0d04201c41c0c101a01c681c030f0082d41030025224019110401902070343e0050728201c03105995081c1c80c1c107005074141302cac03080d00e000d14101800d18282918030401200c080d0b9450300c402c48040c41c09840c2090303505512050f03002c0d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 736859397 1250 736858147 736858159
    0x22811060109020405270a32070801091503080f070807081809150d050709060f09180f1205090a03051c0206010501090e040507032f0f0a090f060302 65
    0x2e10b6810300d00103900725125180c000c2034010710f40000c83c4900460ba041082080100da0750a0b80e03261501c6000d410034841c0c003210b41075620360103141d41004091a400c0038020011101c018100100000d0119030141d0040c0121f603d4030101e410100c1050200e20210782d00721030b1058540412000d602c4542c4a1644018000680054103108000100010705410f482e1007030030744088500320082c00140d0004541d139902d02981150b100c44a490440c001440341d078020b2085441d010703210600d004c02ca400d2a0020f0030390003c90201004070b01214003c16030001d10840b2503107000350483d62007610021b04210014141c0a02c17100c0f03001d90307a2080003514230f0010010b010007101c907034900300591960002c61050100c96250801000c0550000820394100d6406a54415649240c405022004d140182c400c580a0007080300000214410a04000c28030b1620b5070020100039102c04007000e0030790b81c0c1d011039000c0c19241c090000c40341d484600d0981100d0340850049a00b924102e100801030100b9007000390721003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 736860647 1250 736859397 736859399
    0x30a05071b0f180b010c151d0c0a1202030706050a0e0409030309052104060e03030d0e06010806181009060e0a150e06040b1501050403060603081306030228110601 71
    0xc94a10031408440584120180302c14079080f404050320340420116000c07841c41a00b18000549140000c030b49010030080005000038107080c18070081400d489001495800150311851501d058070303d130340080141c0b5a00c03205442540e0f0106c0c2d00c8020f40e20400c0c0c1403100108a1480684c02500640701c0008000e10402c40021186000340040c05e032104c0564082c807810b07089180c24070306000741e05401801d0352600c3d401e06242c584c040754100c2e8400c068a03054001848414900006405207070b212540c46070103406150f0400b00d02d185040c0000f800c10007407017030040d011002c0c0030380400e00d1400f100c541003001c1281006401e200025250361f10001e00d00340f08103400b040500c014010000b481000d106024440d20000b003401e50380d1184240ca001e4805505040404c0300200c1d00350004103d800d06041141c00e043e9651203200480b2041c6d4005d6440d044e000a1010141e0b03a04060b81002d02490300301142000800c203840722040c50803031202c500810345061031082d1203020341044e10b2040e940004542e215 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 736861897 1250 736860647 736860659
    0xb04030c0b090d080606160210090905130519030e01201617010902030303060f0f030307060c0810210203030d06081b0604270603020405041208060a08030a05071b 71
    0xe01c201841c0f0310000d49002c010031600d25190080343d40c4404001862802040f0740e03000c1080c1141c1483d00c00c07040c45a11300d40040c280407180a1544030b0030811111a04404050502e2404c00740c3c91255100054691000c610000e40c01c450000701019083c640705e04007517011854404280006090381d000d44c440c100041442d0300044054409441d140c94640c100d1548a00125082e1101500020350541051001400c94201130b0044142d004000348510020074080000c6410b50380010801c3d542c2c1521016110000c41e00890100e4101455013409440d051411150010300c00340c210804c1c00a02c1b1540706035065650410583e60100501d48040100c1741d914100e80d41c0d910b42050460183d0480d62000d1440b41c070b044e000355411601d6103140315517950071420f801c031402000c3d49000c43d1310320754800012015881e244200e078030482c412440d03415001c140100103850405c0051456100f404940014090b415000c400d807801c44d003590404e039494405902d40400062007001c4414070104100a0010301 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 736863147 1250 736861897 736861903
    0x17010f0905011a0109061d28031106070f0f020414010f080f0102130e0702033906090c040e0304050907081b27030a150209040e0c0306040b04030c0b09 66
    0x190704030042e0300940301c8918010341782d401481c4030f2480814080e26031050410301d50049821100401086000e000805061070b11070500207080e03140c10403034450814020414950b0307601c8001c8204403102c6d07081000c00c0d074890750035015a050003411020b130b40c0c80000454032590050707254810740d000d0102840d80c407002400b14030411031045440c684181124541007180c180b0845022000000006a4650401200028101707010f40007004500c0f0070000510013065201810b00e2035801d04034120200c81a031044041c0b003012101c03404549811038814045441300004e1405200c0e50280c501040b4400345600d243c2c11070040760310076a0041a01c00030405484e074881405445400c00710340300f892040624214000a000790244904409880e03290140711800402e81d03240e2000380201111014511036403603071520380f030986042041c55008181032850385058024600d003440b02c2e200902202c000c40d00080c2e035a0358050400b1348040361000210301031500c20100070003195009000110b841c2040740405a03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 736864397 1250 736863147 736863161
    0x180b06010311090901091107060203010605090a090b0a0608060114030a06060809030c060c090a09021b01060605090a0306020d0e07060509030d08040201020d1103090d08071b05060417010f090501 85
    0x100192401c2c4100c1d00070542c4000341c50a40101401043e95603080024100080c25a403840103840c140501180740007421134001503018044594803191030740e0700c5c1800d02c00e0559054010800d0241007958401c0c141d110810f41d0740440c0d9003031078240101c2c1c640b41c0040e03039902c2a40b43c1802203080c0c001704018000400380c00074800ca5805684212407a6590710000d40c032401006001c6a072038102d100401c440c03000f448080d00d02240014014410340c0d0303a8906003402c90f4428100d900d0515103014114210344028850400100154109140f400e0140000250400001e00005142c42e42c007141401c2074500582c0004001410b14044079181903d41c40060705039080100d001b032003849045406545184111100ea00861741038000f407130302207130805056030207180754031105003d840300380406c04160707075008032102041d400f612905903500c0c12410081040c90103151070151002c0b0411041000f9151070080720704540000e018611a00e040b82007050140801c004d0180c1b00720700344280d031003d110042d48001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 736865647 1250 736864397 736864399
    0x70e01030204081b0a0f2402121810080c22080a03081b1c05040f1209030614060607150f090605011409060f060a03150b0a0807030b060913180b06 64
    0x44c800540c0c071440c1031301c0b240c4c00e801070107038480c7d10403103038540b5400801c1c0d0040c81440c5c0c1c1c0142c07508072807512646602a00041c1c0d400f50016030006418a070740c108901100840000c5150400007032030510080d500520410100c0f030401440d00b5482483c0c102d02c5070b140e402400060301510040c10803820014258001a40e004000010b260300c1080400041c800300c0c1c07070241d4042d000300103082034050420b00502e8001d0090340d0503d00c5031202c1c400118125201480404240c4642c180b95041d400c01c9811510842d078500d01200c40790041c00032603030b1010299040340707501644804900c1c060000c010042d142c6040014165401d0400350b02c1041484d4201c0d40c181c1d00c01c03514800092041d01c0411950440c26541160071054803540c812203401c1c0036008203403d010700c0c1800f1540c04124074000f40707440c901350311983c4d214001082d102c0e045584401d900ea004461441d00348244116403000940740c0c411025907134030950b224a000e5010025070b0f0002101020840003180242034141810b92650008031641 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 736866897 1250 736865647 736865659
    0x302010b031c09092f1e0c06010e0403020a0b270a030e1311070b04120c0809010819020313030908300f1b010b09010806070e01030204081b 61
    0x40c01e584102101c0d078641c807419503442000c1c61900103110002c5c0710300c0100d10f145ca01c0702001d40050321801c88a00481215070051107a65400800e41c0b00090509952010008001007100020354000024941d0548040c038940b81400d1300c80d46000c1c2c1c900004118001c2102d070341d040801028010808000344050710140c00400c0c460102e00101d03031035600c2c191009001c2026420060182c1c1130080252071403040e4040e0010f580407d0800c51809500042c20488107480110308000802503a0324020a00c0f00070390a21032a001095504e003400760246007006410450000001880c1074698034041802c01440c680465503402c040c0400300c0010001c2c0400d4004c90981c0b1800a5185400504203038185d184100801102c0a001d03544400c035000c184141e03000390818000c402c240559400140010080700c1c1001a5400046801c0703400c0d641c0c601d110b90b03c03510710310004000c010700102e401c540c803148520f0004c82c005500340040e8000e00940d0040103245c0f0501c1038951650054845840c240c680440701 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 736868147 1250 736866897 736866913
    0x1030507050108010e180c12250819021804050a0515090703030c1416030b0a02210402031f020d11090a0e0915190e0d08220b040302010b03 61
    0x10f450002007072203103010340003d820000e035020603200c0c00760200580000558aa0042c04400a881c2d68000c440003082c1e60040c0b13103101c0c207200c1d900704905c0c1d0010b42c0041c1c11030b2040c5080740d010703210551040d80b0b501981e17441301c0e100c0840d51004244684680d5102c00e1982500f401d0070103595509500104036001e114104074030031000300b011075a07441450a40001c00d00c250469604552245958000300c030102c0d403002488012880131f104842d03c2c940c4d400862040700d85542000d11460b40c010340030911092040040288100006d810043ea80102000c11410b40c0c4862012a26101d600d201c2040325003900c411501a0b40f0094005180707c00561a06011401e040c4102c26401d2003140040c540c0301020500400c102400c410090f42d00856110540752400c442120381030350300c0011144401d0102000e1600b8650003590702c00c00c041807030340900400e40079001001c0030302042c4014201640030520410b9150854041030422121550700402c0c005840c00c280c034001e40a00380302108240700703000b8050 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 736869397 1250 736868147 736868149
    0x170a0603120309022803080c160b0f03060105091305010305160501083630070215032208191407121b0b010509010b072003010912080103050705 63
    0x14410565001004210200c0581040c0a0449044440106032000c1e43c4030020129500d00c0c003600b050a928005801c0c2000b6001c03004000c00d600342c00a0044150500102f144000b01c1010b0380d511150038200156104420000980729042d1400511072045c280f10022040203004074494810300080c00c287c5200701d44580040d182d01c001180c180b03000a1071030300c044a1214100e007180f44650700010851801c45c030748000c0f0504209248031200c180542c0c00304e8100010b18a11080c03110303d0080c001150410006500042c101e4030304103444849214080040f84443c1e00c102c51261010844200d0504c08150b01e282140301600007113035040030015860a1b40d06071a006415290b4070700c504114041c6014134507603564280751980305400c0b08121500c40d100c0c645a1800300e59145440c007406e0300c14640e40c5030408101e44210141c2226090400600030600001c4801a40c40c8140c900d80c007111070390050303a10105e0300524444c60041c0c040b8a1010440e89029040145a03060ba401081680c2410703440300c6c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 736870503 1106 736869397 736869401
    0x406020c06130b011a092b0b04060c020f0d0302031f0603091110020a03110102090a0b0307020106050d03080103020919022b061212170a06031203 64
    0xc20720000e20404250307950050411000d58105c641034810f031000383e030089090281c01002806081000d0300700003008650300459220307100c0740f041e14074245040032a8042d41c0c03e503552440c201c100c2e40d1582c0301186012041500d24008c11403a40140b10031002940010440070403110402c4540410305480140d00d401401030359408180c000382d034140080106e400c80643e0748184044546004201c4d0040303100b03840a41c00d0f062411000c1200f070181e501a00c1681c80483d8410070050020860221101c00b6602035206a4020440746071a4818414050140080540810700d0100100010310300907208a50044c01c14800101418010b2a0719003a60004840107800d0b2140b04042c0b107540640c94405039098824000074842d03186030024140040c01404d001604406d4880d0074a489280105504002d015400703403000050316080c1d4078000101560300040300c0300c04139542c0c01c04080b44a4 = true := by decide +kernel

theorem cover : BRFrame.Cov 736690647 736870503 := by
  have h0 := BRFrame.cov_init 736690647
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736690647 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 736690647 ≤ n) (h2 : n < 736870503) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
