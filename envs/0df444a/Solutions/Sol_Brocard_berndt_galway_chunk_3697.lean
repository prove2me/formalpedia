-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3697
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:24:39.132457+00:00
-- url     : https://prove2.me/submissions/969395c3-037a-4680-a7b2-781464d1a7f7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 664748201 ≤ n < 664928057 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 664749451 1250 664748201 664748239
    0x180f0614030a150b03040312020406120b0a080115080601050402120420030a0c170a021005070203153d0302150d05090f0705010e03030a300519050402 66
    0x1c0140030101403500d9602031070043e2141c81c0d0000140c204009003903542e20305400c0143c41ca400204940340c00600c104000c0020075400010008514141c0340040b54030fa0207200000c0310320300c850b000b0400d60f501c1c1840494156205400304012140140165070180c0c1e039a20410049001d07011102660900f00800140083c004c1040e498440110000b0110008003160100e841c00f002d907902160b0140100409100c00903041c0c1141d10001d491900508454130160b0110b01c01e629043ca01406010001c50101d04651b010300950f0901c94001080342c0c003510b40001100c4843c44a0400805074027071182c3c03000e03a4460b00d60116014411011050030f10f5074a1a4207002c0c0042504440000000091110707000800e19030051500410f0a0030040054520020207181406009ea02c060305020341440c40070709588002c4203964036038000f800c0911203c0d038400c01413290a100c124588081105842c601d034105445a800140590b012081c1c3c40f0001301c1c034910110858000365070296005c9402114031250070780c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 664750701 1250 664749451 664749457
    0x60608060f010309080421150905150712230603031602090a09050607031410051e030705030d17132f0402131a190503061f180f0614 58
    0x105c2150454945907654080200c1510601050404000800c04600130320100c0d1202c0c14140e00c0044081002e0780c030740d5444c0382e030303070314040c048a203101800d1000511840c3c01072410080b42685000140310881d42000310b4020954008881042c0040c418041003050800105544d0351071000c1a043c400c55540c1d4003005480c80c8010004500c0b00d0301c84000300c00051080c0000780c0600901d450102c0c0b100b80508c00ca056011005007011101080c00780e0070400c995441c0100e221080c0c1124003d00c00400c0d1401081c200001900303c1070701031061036010084680e00410b40002d818100400307005030349075014250305000c07007981d02070f02d640174030000c10a811340e800f2003ca0505081d00038420311490184082000d0360851100c540d41051a100100005407004001e41c0e40c0340644c4136501e10b842008480da880001164035207604001c00407000400030344641c0d94020076651805c081c0300c2c0e0b443c08000001d160006284403684248600c1100203100c1a842e1500402e95910b0b4960a110344409007208031290 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 664751951 1250 664750701 664750703
    0x503070b1f1e0317030901060b03070e1c020303030c03010f0e011d09100e0102090406050409020d2d0c05040c0c020604050d0314072603061c030203070501060902030a060608060f010309 81
    0x200c0d00b0344000005034882c8103600510101c100d5041d2039140441c1c1403401c580b05540402e13521071042040021481d401002d51240080840d40e0015400764071444006483d4520b200a4141c8000405d01206001006c080c50484a48013402c00c60719032241401d110710213080c030680c2d5400100c2c0d02072048050040008991140c0b2080448000f840c40d0491003040d01c5589041603040c0c0d6000030540345508081c000c0c0005042c09903400e1010300360640c00f00302e04ca0341c1500080c051819418cc041000c80310341200c552140c04401405400a401e824400c40c910000d120796880380303203041c902c41d410314020b000e0300a0040d00100140d04083c500030510040030340c2c942c421410804e205522009044154029140440c090055030b0910441c00303185001c454288030072a410602c0510402c540c0f41e480c603000c0000c9511014500055483c00c0c501a4914022084001c01950030298041182041580a075105016084050201c560b90b604c05980444c000c0d01c40300d03000308680740c0790300c1994000d4002408007 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 664753201 1250 664751951 664751999
    0x14012402010e0a02151903020405100c0f1707060c0e010306080a03090605090102030403021207052812020616060516030e1024060503042904060c05040906030503070b1f 74
    0x289080914408102d01c5500b1b10101ea4045003c1c462400d00100044850f00e0382d08011013001e456031141d4500c251940d000505502420400c54842c4003144180e84500342c0c0894103001c10942c01300058011a024030f00540028a0310740e001405000000300091000d07010340780d202c040b60038050700321000c0e4000140141584010400000140c030703041da11800350307404603010341541c500740802c01c1807001402e482141158070780764407040e100d038080000d141111340f98404800600c080c0c1c4003180080c0900c0d403060100c04000742c0001c003404066000580b2659000041e5020000040019801c440075040311075a541c1c4a540c122406201070f5210021000c101c0e0401440312860a24240c0d00b413050707411003000104040103001c200034440d42054942141d8440080100720304201000e10a10b0040000c0c0041d603e501900ca0024018070455014082c00b09060040b2501d0f0b003441541c2e0f0344490b6040b518031403448001901e590140701d5102c2d40c0802c9240e103201552030403c052040711204a202000303 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 664754451 1250 664753201 664753207
    0x3070f02070b0c03120901050c0f1c02041203140a0c0201030b1807200703020906090601120f02040602100606020601030323121905060102120d14012402010e0a0215 72
    0xc010b04500181443c1c0400300011a6503103810001c44452a501800b009100da0400c8284443d1000d10f40035504c40c00090642c039501c4079100340f015404036182503000da8200c2e100150110302e01012541245030f05010351907241c118600203915464522442440c040058408070400700150b202c4d4000581032000200340b41400c075007184401e0220341040d50038401040500701d000c50040b60070740c28804032400b0b10018124803440c46d00480c80d41e00d8003e0030a03115104040c0000c10aa019401c2c82ca000703a5501d5081290364280001d480085d417050107807802522621854450040d00c44c0201001d40704654080d102e43d902c1c41e0b074280e4041e29054450a2202800308210501808410151106d01420202003d032070078050000104424011420480b8a040c04100f040d5a40c000520f01031114030501d5066846811000080040164111880243e083d150000030a000e4800600e0756118800c10410000301032800709034200e6681e405ca20000d07070800ca4041b070140c90b06807400130289511400d201c1c5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 664755701 1250 664754451 664754459
    0x100f1824090f0912090503060f0c07080c0a0507060302040810050c04050d020d080c011d0d0207061b14060604060e01030c0e0403030b1002060a06080d050f160803130b060402040b03070f0207 83
    0x608512a01d44e42c0001031070404081100d480e0030000c664010801c1407607001e09007000a8410000c0c45400e2026141c641c0004800f81000360030058034504540240c10b8071b5034292298002400380d40180300701d040c130740719020284080310780ea0b10980703000e072490300d1640b03140516280c18001808400035040c2da0021ba24503501002c1031400008180c4441090000100714800e801085104000034203506a1640542004101190005980301c15a121810320181d200c100d0164050030303401c2030300b008181d00e104c0c09822011032030000b07046000c0e1a0441d0140499a2207140c6881001024880544941141c072010084003050503500c41c2c0042c083e15010608036580c40200e9104181d9020700310041c0d0008080100c0f52440e8424500901031407005041080c400712402010b6000b0f409511260800000f0301490010815030640c400702e41c00440b03280c50f03142c070b0444020380d200808800d584084901300020030500e800e1007160240c0b8403003002d050440e160340d0700480d0404890401e507025403050390b2000c5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 664756951 1250 664755701 664755713
    0xd0905040902030c1512010909051b030c0d0510051305060a0903030209060703200118240e1e060c0313022b110a0b03010b03100f1824090f09 62
    0x42080b4005c0e2050941d520b0304076000c0d0640003016840742074810b2500820f03074002100440d0110101d0801e4005071a074110100009081c02030909481c1d0b4411003203442e031820010007254000c1150203024040200741d480c0c510b8200041d09156000740150018000103039040220380c0700c41001c5004c1d240c018280b0206001003192540012001d0b400300c2c4444811441c00b01038646503841880003103001f8418003100c0c40b01c00017800900000100a10601589102c032146281c0c1400021410450140030724140340b4092a21000e05007440c0383c10001c0229a4111500c0c00202280501c40c0910000c1c603603641c18644c10907031958550b0890b031000660601900440382c554422000c00b14218000c0141441403801000300d070030010446000d4410a07100300320504c044400c0c0da0455031512851079076a078559891108408554004968804a4078404190303658a0241410303c44001903080015800344002414410ba150410300c0200b0210b000c01c2c0960301c29030700005444203041c540410b03458400d81e210 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 664758201 1250 664756951 664756969
    0xc03060c041a04051008190b0306070e03030c15070f1e050c030c0609030310081c0f020a1205030a0c0e030d0e060f03010b18010f050324030d0801170d0905040902030c 73
    0x100183c4400e05101c561f8480601c00c10666864500800003c900d80b000709854540c001d100c401405940c8200c002c2c0c94506200b01c803011806101682e000084046055990f00383c00c1e00c5040c002624104544603d501407030598881c059401c2c0840f001c607a4941c2d00311002c1e4400601d044c1c1b10b000070303c040d03025008200005406161800050b50300d0345001c411080516001d5409036806a100d0740f49500030f501031008010310100ca03481c00140d0301640345e9041e444c15540c82401400b0184951101d9282036000300a90b014030503c850030710000380f0f046000c69016048408540e41a00711410034185a170107202c0c000c9602101406150418260f4100303100302d50000d0748030704082d44001502c0d42560b003210480e07504998003401d2071169545d0340c01c4001d20501000308900c610001108090500c0c045102050303004003002021941101c5120200601c40f41086c4038142c525200004201c4203044080780640c40a00696600185141b5160806c0301030013001c4c03c00e80e054098415821280e483e8064a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 664759451 1250 664758201 664758229
    0xd111b1c03021c02071202040b0d0b0420010306080d080a1b1805011103030703110f040b22050121140c070c0510080f060f040507030e0c03060c041a0405 67
    0x54400c2c450400c400c3c40d5061004642c2c88119045000180480308080e0b14059141e50142d41c00508030b680f01740410411002080044d0402d4600d00401040050b441058038600d6010740003103510540c01001035041c2e609901407031141c0d4100e40091461140301788902944803016010104011907a032440007500c091004d00440000d0803104006030702600020b5074401082c00703180c01140c0d410000e280c2c90701c902015106204040e203460310308020300c81c0c0030300340c2e02c849060707140550380c841d541c0080c80e00c160302100c075810b00e8051800c101250885074110000488406031a500760401c24041403c095414200c0d1101303040340d4515040d202030380d03003041c418483e10030054246d9a454540c00c101100f2061584003600ca440d01c80c0172031221690090591390082c0880401511503240c20b8009410042e2078800290090b03c2c8c0750070403a185a26412038034542c0e2510064480c100c0d1003009240c2c0b504401c94a040e5a018200030400080b0000300c03080c02c007021316603e01c5092913294030000b0359503881e84103 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 664760701 1250 664759451 664759453
    0x221a0415020c3f0c0607030e0a0621090203100f1b08010518091e0109051b0a0f050616230a030906020102181c170307020d111b1c0302 59
    0x481003007200400e03d00c05161007020348402192482c50204664502c002c0382118015030010401d00100741c00b61a420b510000020210304006444840040130320003824030880190108410300403030707040300348a40c2840e00d070003a0140c141000780c2e24130840034103428850b040c14903686000c0f2101564094414202074000c0b41e039405000d52621007040240c00507a0345030503000031650280808000c002411071151200c00b0840d40c004d1100302c04481c0144074141c00548a40180d180482268010030982c6541200440300001c03119143d46031492409068080c980d0001d4040200c1d00946051a64a600151085052200140d54400c503006032603030b60445580300e035000c2c0701c112041641049000c00604101d02c021405c0c501c4903986828000c107100c6040d4010f603014450380c1d8000c15006814100240c00500c1c0c0350b50803264822983c6a13600850755a8010b0080c40c0b0040003d51180805501d007800c075000400c01c21070755909140099004240e03469005403110b07000c1c0c00e00c280400141e500c080c00b0350 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 664761951 1250 664760701 664760749
    0xa020304060c0207060219081207021f020f1c091a071b0b04170409150f050306010b070b06040902130b100504180b03070803221a0415020c 61
    0x4901031040d2681c0302c9415040d500000c2091004690015011040030349203510f003507080c220b6080202d01c600ca151901c0c2c5105040c001008400b44e00010036404007540d61990782c81d40003402076080120300803c900c01d9294201082015120081e00c4035580c00d141c41d4860000c0c1c1c82c8603c0d0f545444030790070461001460f400c008104843c45800a0038000c1280300825502c60741a0b0750380d1a035022280c010320050181010392121885111000706440250080c0c800400c9000001c0540620168540c0f05007184040d8404001c529405c02180440c101c0d09154029414801c45650300805020000c0c0016040b0340d42c1d100b10000341e6a600c07a4581002c0036410002645000c2c0001d03c403240da20180c003402400810442040720602000f40001d8512007a200000d26030341110020341401d03040e50000c00c541c0b00110707104090410b000c0c406191448840f068480c20390783d030205148070504c403035181079805d0800c0c48101704e2608544000a00100039105541c42c180480c030000f0724444071289a80d0002c4500 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 664763201 1250 664761951 664761953
    0x50c0c091e0906180c01050403062c0304050301050a02040e0129040f1805091b03010b120f07060903231f0b030d181509090e011a04020a080c13030b0a020304 69
    0xc08a2a1141300c1c00000e820b030780402c88000703020380c030031488020b100c1503075900c186070b01d010480c51300c5400003030340740711685042c0c0e04102d40c1e81e890f0040d0007800d100b946090045a000c20092088404407020051004520303880c4c02a070044110400d0405540300050307016003181c4104160080c40601090702d00401d115041c0750344a0311240c03003079146003c83c61500c02403007008000091404810703102c07203a003801081031000202e409090f42c0d294468202d039070b031108599030620104800941c084000100c40100d5a100001c036851400da22020345000180801c13004030514441200d500704103810125405054641540300e035483d01188010b004a80d2410055600d103000d1042071058038682c0f52150303400d40050360f4040216014450004078a00ba10040d9420a01410f908002021044010800200d0340300c1d906018022206569090314655171048640c1d140c036100303981c00301407a44c1c0ca0320059541c0d200502140d502034260042c4408660200100281008054901c03038070010340c015071a4101 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 664764451 1250 664763201 664763221
    0x1060f05030102031009110c10090303050f15100509030a0f050c060a05090d050f190302010b100c0605071211071b030b070507020f1e010f050c0c091e0906 68
    0x2094000368442d9004200340b10241c1c10040100082c1c80d500740c3e00180d060051403c41146108605a40440d8011000c812421088a901400001e80a03481c01e0116681b41106140d840c2c00c01c64815910300c880559071070182c00e10424001d03030f00c5010b0800510744120341000134500200c4010448402e25889410020858103200307074102d04070144e40c0c1a051911101c0081c2060280300c40c440e020703001c0010f504043c08030800c64002e8644c400410340e075011003820a500031000031110182c006d136007403146504088c1002c01c1d40541c401c1d210b0303840c10b070714410030350b1104083c08014144604100c00c01c0042c24408181c1d11071450040480c040c0c2c565141d046190484444d04510199115410452400c00120702003600080d803040c5586023850761781d0424400a00360f112081c00103070300a900b01e0700d11281e15041484145120304241c90b0303611450070208045940c8d11505402c0802c54100840468441c05d008025641003440202d240700a079800b0240101e5640d421948004140e016100340444062 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 664765701 1250 664764451 664764479
    0x220e1305010f0e0c04090c031223041d09151e10030201020c06030a06032405060328020d050d0305071803031b021f270e150114030106020106 62
    0x40102c01d01112a58901c0b0030340710403600d5905800355813200040810400915008000785034402c01d403007031020300d801d40108001440c0a240706040245810307010810a041c1c262401c8038100d0300c000608038950328110300e548034090084541c03840b03140d903115080a15031804901c100d41380159210915071038000d98919103000b4080c03080408641c0c03014009070b40d01040c01401600142c030380690b640c41d0511210700600955202500301004404955081e541c51501c040021455503001e01c010f485001c201902c038840c22007504007006070007017848072422010b0359a05949000400c002041489600c500c1d08108902100d000001d65880801000a80054010701c211000035443d20070350307003165000f034030041200c0d0b4004000748880780c1c80c8086503034003040b1000e500001d00c2c0d010b10807004181d01522060100e14284000301c0e4020303401c4808544c50240500712020450a00721030b07190711014040440d02e00429904110308890103503a43e0030b0f400e0045000344520740c00007440302d1408081c0391b8850 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 664766951 1250 664765701 664765721
    0x80610052e08070f090308070602070804080708010c030f0b1e030a0602030c03060120070b1b010f050603060601030b0d1101020a020307060c0b10030b0703050603010b030f061b04030305220e130501 86
    0x8000085e060000c24107002c2543d104640c4103800680d5250a8100049a80600d610540492154203000b040005064100808540140e2410b00070240c40c0352002080c0d40c03012858a8110b00f1001c41100d0008084103003c0c00960082c3c15203440b00e40907100d0005a9108492200c6103180000600c1343c19607121000038105d9044c898030141c00c403034000c03040c2e458888a100f02c04c036000e40490045004510000d0602010f182e5034000c0040a400300d1b00100070300012103c82d8400e02508000601c203500034043c21200c3ca400504820001c0308650b2100303440c0c2c0d482c416050441c070030304a040006072800c00c2044040c10070b5483d40321060390186000341c10b9000041c000303000910f8450302040000d4011441907000203081c10040b42ca07541d1140424014004009801e5051094800b1144401e0f0041003950058481d24628003c4034003007243d1440b2440b81c0c6c440200082c02c02c100403140028012000712408000103014003a00d59502c2d504106d1200660f20809080c000c10303424010041c091144900c05 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 664768201 1250 664766951 664766957
    0x120302040305030f0a090f120b0c0415032c0f0c030109080a0e181f170304230405010303031d0c0306130206071203060f080610052e08070f 61
    0xd400d50380c429450340a407a280c4e5011407004030b00c2404040c052845c4201600f03138031724400740090340d0f000c0318000609051810741e50b669001c408140480325806c1202c0a9400c000070004c51a50514001c40092540c0581320500070101c01045c40210005a10b605c03845009078010019141013a0803113090950b00d06401d4801da1500034220000342aa000f0348625108a0030711100d00840d110214a003840c1007903210003642c80c400c04010040304604c24046844030440b00e007809454440441d245410100042d80100c1e6106210820840c04c106007100c24a1515826004a45400402050a40340c01ba042140801d403103041d0042c41b6140544012400090f10004010048001c004a515508043c1000c1603603900001100e082d525910211882564042c0c030504250411607130080c02882c0ca4018a44d0849048600040e403c2c40011224040c28102c000010213601c2c1c1810491272000210f46c121031013040b00240319401c441c0042103c1300818030380700d145047c540645e000301680000361071403083c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 664769451 1250 664768201 664768207
    0x3020c0102160e0610020f0a2a0f0e1003080409051e160f03150e01030b010602030309101d01091a0105060a0c020424060203041508071b080408120403120302 69
    0x5880ea83c542c142c0c0015043c0d5000c42c1030309400008030308140341507066420301d200c0c0c40ca402c81001114021001062590701100604080d420401d804030b101d1840740c241220b09010040c40030045030b024058110420240030181507503255200b0300310347c126601400110340d440b0100600496805a0301030300c880f40c01d0604101e483c1041e4400440c1c4200302d019410490240c8022600c1c40c066400f180441d0800041010740d1584d45044007001e0400b4041140d1f204030340c80001031580d00000c1562300500f40d04000c1c24602083d140c0810050508111030fa040031505031a583c141903007031260200d000d004420f005404040c195002c0606a4180d20440c001c100402c510320095070300c41c41d10540b8a90417200032a0810f40756030014540500001c400315074102e05100001c51a40000c0200216020180007003d0000382d2042a103000300115044000314000340b441189140e01c14950000842c4200d20560800b03031106041c3e4609606124140080a8005010700c184072131441154080d50144c60305501d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 664770701 1250 664769451 664769459
    0x100902010f08040203070f030b0603070b0313121b230c0f0105031f060c0b150108060f011701170f2d01060b310e06130e010903020c010216 61
    0x25030181c0e40c941d2800c200030440071504668081c403503d4000c00c542883c0240c125202e0528042e651801d881d56442446148070002e4a818408243c0b8412118402248100c81c1c2a0f19400b104003841380c2c0c07610402042c14030040182c0040c1f144441ca542c02401c0f1500e02c0102101c0e0380b080611601180c0f01e0320360001c01283c000d9a0303885140c4d9881d80080c84c000c2c0d1039485150340c54400d185000d107440110f441c003220200f0705517400014160507500440300c40d46a5203600240c0c841c6d4852880c100e070b00040009000440314103005c800540b46203010301d08480e1141071200c090030748180c203800141e00e049050003100130700c400800c20924a500c0074005000702e1a08a000a00b1714404c00c160105400f0b15080003215001c000c0d800384002b4010092030f260b0b1460f203a001d40720341c034005001c014000c40c0044034404600001c1c008460681d411002c2c2d0f00903a031030b0141005610090069400c2080b43c440e0101c03180b80c4400c1c0121180c5500c0303600100a081a03580001e400e00d80d4104883e02102d800c41d000304 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 664771951 1250 664770701 664770707
    0x2012403060b0d150e0c150702090c03040f021c06091101090603050c0a08041704030f02042d05151503100611030406050f092d03190605090a020a090e10090201 70
    0x162041480c040005021000c5c19101414241c5002031a584a01c40a9240d0511020800140380132803080350342c0d541c40c2c1d4030f541840c40c00b400240c40150594002040050050500c2a403100917205168004e404a01d40c0e07680381c0041d20702507902140d5041309111100c110796040071000016041d1424140054a000ba1403c861030140f06100c0d0200b11094010505000b61412801e00e01c90020301e440e03036256200c1c00e00d17000507403d020040780580c3c40e04000245000c5c1c0001e4055542c0d0f40c038070101044000750081036018000241486403c28075003484a422a501e25481c40207042480c91010744038581481c2e03182d506d0701c49500440a00101000c0445000c00100c201c1d0107444607030030079a40360410119422114040c005502c1d41040e40301c10903c0800e904042c2c000f00c1880c41d00c0c1c030f80b4203d0b400e5005045d190340403400081103030711045515000040194110950148091085403200078290700064140495a40404c941c9a6a070745045041c0005000c2c107100c00502d84401d0049404980c002 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 664773201 1250 664771951 664771973
    0x10c03180f03090b0c01020405030d0c11010804140a0b0f06010f0206040b040f0b010602100605040219050d140f07030501150f050d0b060408010212100501081602012403060b0d 77
    0xe00000ca607028000815003d22070500180070780381c100c580c5074004100c00c6030007940b1070700406200784541142c0c0c070100d80c4501624480c0341e52022414441d01184001580d10502c06801180c41c01450904005581d03020807001d4000d900840c1c0152203030500510b10707000d800d40686402e0400c41c1d2004000d24003600010456009684005544101c0c0d0303d034106012103d84d0303410000d051825039000054001c0d03001480c00c001c0d450b21130b400c014859440741000200e1103280380d01086240501081c01070a4006d00103028071840c120700210310b4594000846109034011640c60020302001070030303c100590305214440c054200500c80401c400004a0003805070200103c4210400034001103500c1c140125411100c1c07800c3d00944420348a944a1b030055000c3d40290b040620010300c04000119a01c01c080d800d4411104107840e901415101c174400d44800012840342003003959210036030651036190b42580754122507502807243c0072160452400c20261002e64070402d105d000300000707680c0130030381c0c031820 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 664774451 1250 664773201 664773203
    0x80c04140904060b06030a09020f101409030a0c090603140615041805010509101410050d0503160c171b060a0c0f0501090507050d08180409060207050708010c0318 71
    0x707a0409640e1842d0040141682c0443c0c213402c44400301c01d1080c1610250444071a052084490306600d183d590140921207684020940010b0392041c21615007038100307801043c03071000203000e5035290760b2191104844220030b42d01118005039124006c0041c4a181041c00e03080d09a47c0001d0401d03410900c160032016202d0ba0120340c81180d594010139202d00800d0b005285041d03204009010a2030f00c1c0031a151100010710940ca00c5a003070001d4a414a0042222a4442c0c0c0070882d1564400f4101414400c0c08030056000301c1e6644000c00c901d006c000e0071881140c1003103220f44005035040d41810801c52008600042441669000512041b2924081100c0808030381c0c05a40c400c1c0c42e03402c0030384e0032502480e2040e000b0341a4031142c442c1009200064118041c664000c0d801c40301c02c141c0c0e50090141460f103e02c030240442005000c0d0002d503202d040369541d81c0480040c00400c40141315100ca80c2280d010300f00407203003940003c104014000d400c1c00348414201c01400d0400c003110b074422034003907d07041e803041c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 664775701 1250 664774451 664774459
    0xb1e010905090f22111e030f070305060a0207020d1502070b150319150b040b0406080c1e030717010b0a06181a1c020d021c05011a0a03020a0e150a080c0414 68
    0x1d030401c15202c46c03004d2035050704801002c581800501c1c00f01940c8410741c60200307072030038012140001c03c00e8680e0700032640d40c0ba90182071888803c01d142c441c804e40e1640782c0010140c2d543c00308074001c045006501c9860145402c0030008401c203800d58101071520003c8502c010341c40c3d59492174000421690004441940125000864400140c0000030010305048098590213880c14002050311b00f0005a50007842d07006480c0b02c0c0c6206030151240c071210035441b2800c5c1d4554817000c010f00c035240d8402030300c0782071010410022034801d28060000b03400444640080c03001925080601030410540c01c03c800c01071040c20301d00d0385004441c00c5007011a00ca601407044060012700d46440c11000b45034101c0300d0314001244219110507202101441d5801d1540007201003500705000810048400622403a0191050080d01d2400c800e00f00f00340c1c081e4110728000b1051040d290805d10540d03e40020700c400c040c0c4080f402560b00d44403540701801d00c01c406407c103d2140000d11040c460070b41020403c10800500722 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 664776951 1250 664775701 664775719
    0xf1b02030106050901060909061a030c0a0e0904030e031b01050306010e011b06050603121213060b12060703060e060a1e170703060608010b1e010905090f2211 69
    0x2001180c05804a41d004542120051000140c1380e58086421010b0f1442101d0502030699210000080da80480d001014a07020400100e00090306e030600038002c1c0456800c1003060101003a00007403406c1d00494054000c1802c9281c140501c0c0b4040c4506c50809504420047e08034420400080250000420181c1841030205002c051360b130284030414005581c4c0e9022481d18900d501c0c0000c01fa03c0c06403480c60003072203021034151800410a098400c020144002440c83e030350343e280b00000201d00002e0580d126652000450740c5038803051545040d038030b002030041c0b0080c00c14120050032500c2540c0001c40251118060100903668034201344201d0b071405442c01c0c410001e02c119550310406580c0110b06198001d610f042d0100d201149030821280195404c11405507104601400c0c0c40051802650000746140d0305030394006405c400038075066061404940c1d0944540c04280c540743c0c207549221b54511540c040100c0030221110880d101445802954038601440c2d880498174041d441c00103114981034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 664778201 1250 664776951 664776953
    0x60207020439090f0f03061b0f030207141903021b1807050c030a020d020706030c080f2502030306040c0e1005031b0a050c390402070507061e0f1b 64
    0x2030003803501030040d04d20100d1040d59914410329500560b4401152030314108000d0151859644140503044030b450b4032280c84244064204400035441010700301c55a041e80388441d0a201801c001141d5000210b203030511485040e401c0c06850031001202d01292119070142108842e2a02d000801403400a4a100825911855029581401000340d40c030140d21012907125810b6a0000e40d800d0034400c2502591012b07600d9130340841c00c0e199100c803941c0c086001c0030007047c80701501c135007402c5d4090706004501006807500300918801d400b00d80203040050f41b020003403041602d030074031807080c514955040c4141c04030b0f4030a020841d04c0b18002c0c884800c0c040f000c00015981c900c40c0c03140540241c07084a4682c0d07103036072080001c0c007a40c1000d100c041e01031150320846045801c200c0d800d4156807003001109607102c0300c14024400405d01400d141134216809000c1240000c0040060b00041c00003621511a142e4004c041004090701001c807903010008000540c2d24601d8200d40d1102c1501d40840c1c40c004000a9 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 664779451 1250 664778201 664778207
    0x50d080f04050d0c061e05190e030d05040f140102060402010f030905030a1d030a021f0306090e030910080606190e0d120201180506060603041e060207020439 69
    0x89900094101c10f201000c1410800031310000400e0394019229030049a0030800d00c00709443d420380440c8040350b0104542d0381d520f0040e6082c4c01c000e0080d454054409000103012078203100b65629100045040840c082c804400907480b600040d06106140303410303908045000035a42c0d040913001a06010744506021016071003a000071030420380081c103c03a902c40d03250790001c0149460031440c00c9154100000d000c054030300131500f903401d0b9400a103d80103e1061512501042090742100000d043e628400040c0031619405403060104456024640314085d243c1440314141d02c1c02c036031008010190041000a64580e4151080410310714510349071800403900641b000e044038258580e00841c0b243c01e640400400070303841039100c0e03526070091000002c6a40703c1d101c2d0845482000300301b0303006200002d01c503007018800f0315400f50103402400780e0b240140589003108501c1d0f003026601c2d190005803000035410140102c4e0601c509030007200c241400d00e214409011030707001220100a0030b155002881c40b80c4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 664780701 1250 664779451 664779457
    0x1306030b120601080c0a120201020624030109060204030b01060c0b010306050606040504050a0606030e03090108010e0916180c14030a0b0f030709090210051c050c04030611090f0a050d080f 82
    0x400c1c01c120341041d615210025075506003000385600c582040100440c0d0280380291904006a042e0001c115945030846000c410344a0022101e0700ea0303030b0b043c040d5041e96038240101c20219010b0240142d460341503084c503481c4c40314140c01910601040030383d10b0380010005405e0604494024a00050680355800000d101d40309540c0540d62190410f01404007503142a841041110341613101005a400840403a64490003541045804104000010040400c810300354980c00f462250070364045005200c4104890712542c0c120340d0f108080c0c1d8400c0591110b880c070944e00590000e0400c0c41e0380600b000082c04070341c48001d0075240055201c4100e20b1180d2100d42c80003008000050a4072070070354442c0c00440080100c11000e03840398a00b0701c0b11609950040d0200e43c0041d00d242107809005161213541400342c6800341422a4103681000300002040700e070305c99000e40e5000341c0d130403640d5240c4080c10844c1c2c8440d1800003901c079002e00c03281000940d03125108070076010b81c8045020b8441c00c1c2c401d1040740c00c0c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 664781951 1250 664780701 664780729
    0x80903031207050309010c020f100b03150106051908220201020a080318072c0405030d061410090f050d0206130f06080a1401050f061909090b061306030b 67
    0x141c481c8041c40322442e04000a944101d680b2402000840390481080340e40f110442c200580e15004410b180240e201250025140792501508880403a0b501351150002d004099210100155000c61200d106868a03008c800d800d401510308500f290402c4c500c0e05c84003580c070300031201c01d010404101c0c2d0304690091017089808ac3d000014107440389814210a0240b08a0203d024020f02801501242e00c1e00d8084114034081c0380c406003007a00030007040c051801d01c0c1c0c0c0644140c0e054442481608100030181c05102c0c050442ca80c05500410420424040391001e204c501c03006100c0d91180030300000c00300d0000d907411070700d04881d40c0c0318881b00d80c00411078a10559618101c410504500490400d00c00040c2004940300380c3e403800c513640d542d0b06102d011180481204091807907400c00400a84c42c1c04441040030003401000b080c40c10340b102d180b0f064800d11804d401d0b8086002c00408200135065071282519141040e21110700c0c141c0ea104038100030900900560081c1542c0f1618810603844414080307040c8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 664783201 1250 664781951 664781977
    0x170d0f030e0703080a0e061602151c140c03091b0103060302043204050307240509060414010e150405031207091e0b0a032403030c05120c0a08090303 65
    0x425100e0801d400251700000b165400f15504480c2041181090b00c1101c02d48591003107200c1940c2e10f154208400c03540203010070b12403480300b4014107224441800c98890402074400000910541c2441400100180245002d03400c0740103100300680e080020801d040b9012022099158034440d07440140c005203c0d64002940181c58800400c0c0c500040e1900c8010040500d02e51040b8500701450b60383c048403007210300804641040c40500700107001c11003505084403406841640405411030981d04595040366048102d40c000c1e0305101c00d018182034445d13034404038400240074001d800c500c03d9960b08200140740e02d00c03800f4400050180701061003510307442403c117840ca00c0c480c2011440200b04050501407648489801882100040203005190702201da0301ca40050404002c0d100507001400d14900141c3d0852014091540c20b2044c0112040a5403003030711002c8480c005420540d1034080d18207854040946d00b0010b08501605c00181c0018180c0d1008146549110071802300707007180580c41c0d0308462 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 664784451 1250 664783201 664783213
    0x3002120712050307050f030703050f0901050d0e01140114060403140c030a15050601030603030e040207020d060c050a02010f0c0801030b100308040608070f020105042012030d0e07170d0f030e 83
    0x4000b07003c0000c3c15083c0c064030440d04a03c14040080d40c6a110346040140890741c100003404994011070b01030483c080741411300900340004291020140c0f00e00421507030072a556004030510883c45900020b02508274104a400a221039401040043c8201c5c00701800900c40840c481130500c10800030b81042c2400a07050300e000030280e250003903200b00c9002860410318101800111154480d114110817603405556912903030400b89d06210080d0307c2480c0903038020400c0031904d808203c00b4060402518400ea4807a40c2d07940301d525000342100c1b03025140741c010b0380c01d20a1090029600402c0907054030f420402020b041e40300ca240241824500d580000c105080125001070030682000300b0600c40c07442e82e01c403001c0503d0b000f2403c078225941203800516016408074550001110200c0d80c2c074407010301030002d80c0c464240c0c101c100d1031500501c2100240c00d484a038001d0654a0601c8080d0041c200c0a00480000701401c8140f91500300e082c8451040046c4010740c800d01c503209411155541c1050819699 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 664785701 1250 664784451 664784453
    0x3010915120c06260c09040b10050301050102070b1305040c050d0c08011d240d02032a0306151504231212030406020c0a0c0603063002120712 62
    0xc044140c1d1003030b10082004c11528001480c03100c0b00e01407400c0e03082c01981005546941c2900c1e190b4000c0701c5403c0d00b01c0e60354041030215448003503100b04158000c1e16129282d61401000a18040d2035400c0035460400c180041d100b2800c3e404440e44c2600d904036000b00300e0340020314045a42d070140c0c010b245151307400d04419904103500004400d05075046031003900740d4108140d000c00e00445003607031045d000f4510241080c50803201e0400c1103820800041c450400c4008c00e40000e1300e006060400003d0601c40a5179a141c510101d00703001d00208016800b4000302d20b00203100501d01b110303c1c0401c174000c0500c150544242d40242d82150301801c4402c2c034001c00d08440c00c82801c03c2070f144c135600600808942a000400035000030303040ca581030345040100c2c40d43d0f0b21a55a040a07401c040c9920300c90344242032105000420b01c00f410000703401150790014049140c05c230174042c0200526844483d01465001d1000c00401e458803860000b501520440c41c80906440583d103007a89070b900100703015000303a00d044 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 664786951 1250 664785701 664785713
    0x2160b0403020d03050c0d05100902180f0102150c0f040b0403061d010636110c10020a0903020418060f0f1a10111006030c09050f07050301091512 64
    0x150040707009a003101c01102e041001070f0308440e01a183c0d5000b2020a120400c181001a00720b654040c105542c2c4120843d6244c445070183c0c0c00000007a19900100c1c411040e15042c0107103003841c0c82009100811000e0070050540405076000381c80b000008000045c2c0c2e9a1544840b011900184100b41d0302a48c0e541e039034280758008240361070005e04490030202c0103040c6000140100d4050313851013013416035081035807160040003050080d00d01600d01c8445903103051a8415108040204081c003400c2640c502c0360761041400c248012517045d228030310510400c5545a80400d110b801c2e213078142c0b00001e500229242e550400d00f45103200030007980c00c0450382a00e81e0400d4004020787ca811900500c80304a03005a10070b6550410b100194100704d9052944132680c1c803410380c40c2d400781105030554901c036036002c1943c401d07150703650401d4888a03200041046880c045108490384000c0042d6141080c1c01c020708004c006100c107218000b6016100c001900c074074010100c07000000c2c42007071025402c02105280c02 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 664788201 1250 664786951 664786973
    0x130f08040608071707052101030605010f080106180c20010b0a05041a280806010e0106210e03090904110901061103270303071a0903160204020a030216 66
    0x440d00045082d070110307410b28055516032040d80604032030381d000b603680c404e07048070340350008201c1d5071403035111080e005003c40c0c919003854041c600a000c007251640c1441ca034031400070050342c0180c0f420ba25042d020441c08002d030100d01c800516070040400d4540b03448004480c441c840d186400030805050800805140d01580300d2580c10f03c054551000b89542d407800c0000f100d0102038107000b904440280c01682e0301c0e000c515002c51a1103103130280280341d0480c0c10007060550b9900710515591003000184458180951410f0061807545003040400d13444c000c0c40c840550050380750103959500c1d00c1d00006c1504003070058800001020b03040001e80c0c275080c142041c4400750f50200f1801412403100129001e40b1900003061442c0c0c014005520300401040c150301d408840d910f10014000d1088074843e2155000d01c01890907500400b07a0f841c220b851140391154045001d0401551a030040000e034841c1260251446a210740484005031035100d03482054019104810105800184006507002080169a04 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 664789451 1250 664788201 664788209
    0x20a02010b191805180f06041709032d2506082703040b04060810170a14030d1d010510030b28020f04030204110a080708130f0804 57
    0x1003019030b414a000c018021550b500a0322080301d0a1030210210700b4003a00030982000d003400f018140700106080130b40c24403000031075180c426005a418002400301c40c0c142c8a4050328882c1c5418074103003000e00080d40d100c458020030b42285119900300341ca03030f620b07261150080e812288160b984800c00d00e0503601d25204444d00002d15006150070104001d48078580880c031401c0c105001c0a94081c400d503a01c800070b8460400b4182030300c0100808204282c2c41000f030030060549495070300d400d05204016040c020410707000301e001c02a12504001c1e0740c840004a0420558102c4c40e4444480401a025401c6109140303048a19a040c100010380d5890340c40000c044607000103000308840e454400c4d005009405901c0701600d942d85182c01304d10005022003103070086c03170012100c402102911041840a98005848003654480081810001d50a050050500381c0e0000d020701e074a4903403540806050408003503d07003c03c1217060000a0040440511b007449400d0b040302401700714030154036100840c0e90203405 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 664790701 1250 664789451 664789459
    0x71d1c0c121a0103080f130b12150328150c0206010f14060706020a050c01060f050f031f020c0a0813170f0a02091515030414033406020a02010b 63
    0x503001110b4401c040301030706803035001d4a02403400e0780081d0b02d40c0345504103411800300101c00c803400190b000203680040016125040c20340610340f61040740a03c966000303940083c0283c20807226480d805242071815211001504040700e4210042c0c209500344481c0c80c01c1c0030315480e2408031000c2500c2d0300010840c4c100c42042021071201611511402c411540101040d90400014003c4c9000a0595005042000c5480c81c025081c0b000c880c15050a480440d80540309c0108040c4091005082540031182c0315101580105042c0841c1e801a01710141400c1c12824210b0740800d41254001040c410b121106400080898036004240700e2080e011030316218100310501c3e1490702d100341c401d001c281c141c0d45515410182503045482d03000d200101c10000c16540c0c1040362450402c245a46180c800340c00d000f405502d0586038039261400c88a21040101d07062410351042c4800c01d50040d84207005c90034040c0c1203880b2209809000358445031004042d100a003000d0020650b0500141e05511040007180c00b29 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 664791951 1250 664790701 664790723
    0x105040506180705031306050a0f0e0c010504140303040302060301030503180f03151902070602180a050d060902010e1e0405100b0a050c070b0f03070305071d1c0c12 72
    0x81c0030091444000c0b10040301e01d401c101c002a600030300a402455119004100c0b13081c040b42c03940c3c0d030b0608507801107916200f400e542d503200c600c0310b008138420501c1c0c10b00040d005201c00002d00b000605140200c1c402d0030210345440d520554151014800c0d05e00030341d4090910b6840356120305d41140ca981141300999444802c0c211083d4041c500700d10700c083c000030060003400f41d80f41a030f070b4050220700c2c0080c0014820128400c0340d03130180c0090300c02407200c1381c002c1070010b80396417004035105007400704c40954510031f015400d0140701681e80c2e07104c4c040005034041b034002043c042c54030040e655480302103007460b4804211040064000392241c00d26401c8507003102c0400c004d59a00141c0404500036000f04a500c003c10300c4090340c924060300003002d0043c4a83c3c03c44003840c1d6104001a210362011100d0365034420003009000d1216054010140c01c81141d0a01e01d13414401030164080c0e0600c04d003c3c240c0f2a07012500c8043e26820b00340344a0700b50a401c145809040c03500e90350301e03c0c005c0d0944070003160b14070340c0c038 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 664793201 1250 664791951 664791961
    0x18020c0a12080c180d020102160f0603050901020a02190507031506080c0d0305030c070c0506030a230c09010309060212090105060a060e030606010f1106191802011e050702030703060501050405 84
    0x149084030004da2000b590000c1c0342001da0180075050400100c01c9056200e50440c0404141000c1446002000011010200142032142c001c0a1307030005004504540c0c014881303802e00319000300307500c144020b98011030a103d00c1c5504041d0310f0154203500182c40c1200412010b0048440c036009201600c100108a0b03208840e00003c4c020030007091407014000031424004204a00100d074024141c03503000d078180780340d030b80c1c0c035034001400c5517000787d0b4001d0000383d50300d4455142d95850107800c600003c2c02620559a860f003010309585610601306081d04045ea1940c4d4002000802e505945202d0103080203130400303145c2240e405000300001d40307103d441040c640200148440c441e0b890140c680380e0180150065840340c200545203a51411040414801c80301c80324030580030b04101251040690862000c82010050501c0c0b0848a00346402c01c003013880303090ac180160341c205400088a8580800000030340c404c1c8002100d803030044034802503040c040d4080000622004d600000e05031902150304004984030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 664794451 1250 664793201 664793221
    0xf0306011412040b090a0c0803070b010501110a0b10150c021507150f0204030f0f030305060907170a0e0a0f02101704030e04092907030c020718020c0a1208 68
    0xa14161901d10b01c2e81c0d00000f000035421a0b4920340003040348085a000780d9060307841900944458001001030b500c003064040901900c080d1140c0101400e0908100c80c428114110741c4030290404083e050a0030031700490b040c4030030a00342c0801080f004901030301040c0080c10092003410a41020391050382000c5903414071200c42412207034079550018100005c1d6691032904030180882c4000070020a43c00d0000101007900380f103303204158403402d21403068840354a00501110809446907014100f0740c0c04008035a6002045502c07076800d84502d0035030b00d56030751011401405560291149074012141e62004000940082c0c0286a1013101c030304035004c03840c1104480c40000540680008145040402c0c0482d0260140403520b42c0040c0c004118000d03551280c1840110104c0010082c030500d041e000789948445041da50040420f20f428091000c035510002d40e01d0043e405411200c03099003880111072401581183d402101c144282e82d09038034039080104a2290720041000891a4200001c0711014 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 664795701 1250 664794451 664794457
    0x4061502280201030902030f1608060702010501030b060906032e0513030507150906050c12061806120307050f07060f030e06040f15050903180909060c030415020f03060114 75
    0x104589001e8004407030b4004401421060000b6030309070040c48a444800c0209101403000c845c03e121840320b01c0703490505c2062510034020003400459240c0720042c800039100100f0356800400407121b241b09170300c071040007a007040d88054908001e0446c01c0380040485008080003480b140417900d0070401c40d5903840401240155202008001071410000e040000d812a02141c2e15402103207000a81c0924903650802101c005440e108014413000c20304201030389542c1d6555501041c2681d03008000001814010381a241c0038280d184681c01c4140d1101c0100410810b0f5001a600101196001940340194036102c0300c0d640544030020301400303e111101c80c028000d0040742c01c0441d0041800b507455448517103280d10700320821101050031514900b9582440d00400e40906100c001550742c3e040d00d46820540d0340006c03040c8501950030f02040010354400401c1082d03101150503a404e82c3c070303519840c104240d403030111065590240b001c82c00d030105e000f40b14080c40c0304031000c0e00d0b01c80742d4034000040c2c9602d40c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 664796951 1250 664795701 664795753
    0xb0a090522230708030d060906050d02090c0a020c040906021803030a020d050a051903150603110706050c160b0402090a0e1024080109111f081504061502 67
    0x3007a101c01996100182d5000b1410800c9401070b40c2c0c0064a0300c0d115070035a8400c6072103020040d00c0394428088494203228840050004898503000080c0a80c08608600302c01072440351210340100b640c064a40c000c5c04101509003000304204031030351252404000941203407229a00700c41030780700b01210038280081120102c01c0c41e40c00034041d65405020840703e6502c54800841007020500003500c1c0c00109503030b010354101594030040303070301035500c542c0ca0346049465010008260404d00f054100c1040c0d80e003100c042940002e0081001d9907042000c01e004d100d403000c01d510b5021802c1c0200180070700d0540481c01141b080701c9406d11604c51081306000e6070026429001550880d4110940d00389041d40007101707c4075403900b50b401010016000354150080f592142440340d466100e5001000f00f8690300c088002022116105c00e658452201f5406148600f0000300740f1002002041d91154444d44212501d4401401444510340310741e0518180002c2d0703418440540305880243d80340350280c4d0281c000503 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 664798201 1250 664796951 664796963
    0x2901110318180906160305010f03021926010501050d02132f1e182b1101020d0f0f0e1801120309060804020d1103010b0a090522 56
    0x10301c41003220041c44040403290b40c4407080001d8601891210031029201c0c40301c00c03024010394074261100c0400703c035601400c4010549040018855092a6607035417060325019a00b80c041500c020340b6000c841c1881c2d80000082d24445440da82500800c00307654210300008130000e2116903a110203204907030b405002e0003580940c44460340022401254440c140710702c2080034400300c0f9004004180ba84124bc000c2140c00003c000a040c1c1040daa1204d5205021010700101860110f005d1118090b030741005041c6481070300c0002d0700e4251298a803410210b980c12041d900c1c0c00c0b14046280001846800707030702c11400360060342005203c6c01d0041c2c84c119600c10340c035122944218945502207515201c81c440e40359104081480818000b418201c071180a80046401410b514205003000350403801c1c50740c0050f007000b59140400c001a1900f0242d21195607028840c1d10400440d200041e0151004500b080e03000400c8200c001580724047e08258080c0d80d80c0300071080490384009003d41b10040c02c4ac8080d040c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 664799451 1250 664798201 664798207
    0x15090506070203210904110f071112010e061005040218040c27030b090a08090616080a08060910080a110103090b011203090f0e181029011103 62
    0x22800c00600a0603400e01c02010343d0046001180110141c3d0980c095244044201146a00c1740d07041500c01c6601840317683c4407007420240e103801c0700741591148400c02861801e6203160072400340c9500003032864500e60300b4020b01c1080d2050920a42c0c0f04011181070109000c05907000401c0d060070b00c2240c941c1c480c03410b007603071040d0042e00621001e0300e4403041c41c0c0100a80700700c0380800400503141008a00c030880010107213503451401c01c5405c044015115001c81d0304a06030540000746100100c80c090002520220740b51003001d40c2e1060141d480f02005402040000f803403c1120798000b640c2d9208181c122030300800ba40740c4541c9003501c0c520390b0154520642c002c49480000c100c0004004001020500d00842d0b06421381d41c0c0d0034229202a07001c9510384011001030820582c10851f514043c254000003200b0152510f00c007840b5602c00906015180d5240e0041804061000c2c010501e000500396002e00c401a080b82d4850615108401054a045000e44040312150301c030f203141151a4040b2001141 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 664800701 1250 664799451 664799459
    0x10908120406060e1324111804020906180604090e030318010e0d081308040f080d0206070c030509030f061003150207050c091302030615010e04060b2a0106031b1509 72
    0x761061010000f03d0380d0740f11080c3d080302070904c40e0041b004407010380c6581984074182003d032032411052103003941c0c0c27086005010350750454941a0503250a03202e5011400c7c400554140800e070345210b2030b04007080302400d207400c42d5801080040154011b9405c094050281c040f1f28840608840070716801c0031154115856410000b445104560b8002c080c0c0421200d8000850b80c408519900c00da202e00c41046808000b003150100c00d1081c4c205003540c90000c0d1030940381c1144014030800c86030000800b8003401154050150320200701170414206142c080312101e00380280342c1d80c2501c8003071004440c10451903103211091030a41c0203031a034155100c002003600348104010040d400400511028a98075200203640240c0c2c1d00304001d500501810060185203a0690700041c0380550080156006a0900000708200c1e03030b00b0400c4440f0002c24140109030211001c11074210401440c0c9106030359800e204020040c40f0000481c440d085491029a5803019640d840c03201040781d040c3d507040041204071000300 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 664801951 1250 664800701 664800713
    0x150712030603140c1f0201020405040606020106030b100b0409020708070609060b0a09063807060515060a0c08090402070c15021507020304050d0f05031209070501020a02030a0f05010908120406060e13 87
    0x201421700d500025082c681c41c1c1c800304086569076400680180c1d1201c00410511200c4032055410010000c110341c012400c0c01c0c0e00c040648682c0c40b0f1a410568009080d00c14050981e003036490f0190b21003818002c40c59a4213103c40a40f111605007031080b0100b0500051740c0c40c20344501011103072a51214140101a8004040c41035080c0e0f044005091900640500794428080209075031442401700003a1400c041141800d42d4440400c041c2c0101d03010403d200703001d0b4000106100711540009110758606c414400310b0301038024550018040b00c0b01040200d4501d0107001500c01e4124603508036600d20b15269207000440e6001d0b82c4001c09604100018020741c1020a0402c140c103024010f0203074010b500340c0e1030915551240308112190321440341405290f940a02a10300101300074401003e140560340c000070784808074550000d00c5441e08581c0441082001c0d000403103400d03003142d1865104c0406083c100180d810440d81260302c10f141c108042546000041c4c440d02480c071032140e203110038100356035407 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 664803201 1250 664801951 664801999
    0xf021c0513030302010c09062604110315090f06010f1202010513090b0406090c022a0a0312110a0c0b0c0c090109060e090c0609150712030603140c 64
    0x92010440100041c1089218140c10000158401d500010301c107584544000c242501c0d5403c588100030014502546101040c9100101c030a0007540d0681c1c81d4440d031900180110029140c55054000c410040c40448003030709501384208070103402d55100e19080c0c10816141c103802d000c0c821060070b90b600c050085600440b074000c2442d00c107041ca58504801030310ba040100d40c099000b004802d8590314000391078100b601403400108031a140c02d2141e10506c010103074562201c1c1809822501c0d103501103580381c2d0705082c0200500500a0003408541f0b480f410a1884039502950b1003010455050410001050006925540e035401c8154200710509044640d02640c0c403074180f82e0345600c241961644a56640b5002074021300703c5080002c2e132180f400082038080b6100505580954012220f258281c0d02c0750021501210011644c00c00b00e504401031700f00f103d001d00da00141c11a11144941e1945517019401001580d000e00c9040e100a8504001503035515500c078052071300311040c030f00900390f004c40e0007490f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 664804451 1250 664803201 664803253
    0x50109052a0d06030c061b0305190e0909010c1403060303030703180b0c0309010e0102040f09091401050a0f060504020313080c01060806090d0f02160b2b06150f02 71
    0x501c0c002c9101c12a20540e880340e081610030a4416804100454011030103141407540002c44101003044c0da140545207000321032594405141c40315049440c3c40c469903500980d0f04009140182608012845600a041820035540441c0044204101d0160800c3c1924030450307000b0021860350765003110440c00b84c03030b009440508406d13200e0300050001e001807401500c19410b481f641c503180d192860b511030a58406440208959204001c240018844103407007406a072880719000c29003000b0f6140c020311890301580103841ca5480c000070701800750600d4200e050741485121080c400c142d11a07042000b2403200361840064407015020020000f95450064003041e880d9000000c0d5464ae03801360542010b804552071112600724040702442180c10181260380c0745054802800c1c1c0891040861138222240d00807032044a6022841d111b145c502020030350300f004040710006c843c00d00703205001c1c00601820b000d80d001c41c03881d600c04075170140d00c11700307c03102624030b554020894800b01100c880c1c071003455202 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 664805701 1250 664804451 664804531
    0x103030f030e0a060c020d0f080606031b1804061421240906090c221107030e0102060603190f0807020607080d0b221814030d05010905 59
    0x106900b64041c00340841080c1034043c4001103000491802c0081c01c0c852024070038030502844024030340d8580e41c07042e04180e201070250380050b81c80d12400ba2404220810740000844031400007250780c5461400c8424446010040c0d03000e015443c0c403007250300030103026810b0841d017020b10615042608188001c419405202090548070580d50007100d000140820b6408a0806902d1702d0034030403241400c00c0036690080316440900349c03602c40200014a81c240007400c840180c12031480291404005078082940c96440204d134a5582800303240241651106945140c058040c1000288845c00c01040d0b50205901c0c0d5441401004d4003070303032441c00e02c0082c428207984540c0b00340b20210061701c49000415120780560603507601d40507100204000da07a913031078080d8001c148200d5045800300851828040e210200c04001c207441032901101c0885207403943c00a017048a0f1066108c100980c00310050004081c0c0400c14043d5a0300c82944005a170011741d03ea0410940846020008852030044031901c015010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 664806951 1250 664805701 664805711
    0x108150703201305011407051c0302210405010507170604020a0c06090327030803160e030d180504090f0201260a140f04020310110d0f0c0e01050708030103030f03 71
    0x140300c80d4201e4000d800700000d059100360080c8415038106c182c0010460fa410869032400020765150f949030754040f0041d07006c600ca0082002c01650190b01903507980805441c601c042e540d410004405000c03000d0780c0c19180b5501c0c050124403224810003114280303103d881d207100b803983c5814050200075840b5901410820040302001d40c000f82031405a801c03068000c0c1d864610982d800c2c001d003a8032014003200030740c4c1d601e41510100000749175801540c0d0b03c440820091000b40401f10020b503114802001444c1d418050a0000604039030000c4c80d10106005584140d13541030388810034403088406555002c0c00c5001444404c80040d0b200350b4880441d80001c0c4402c0c010704045500c04010200c080c0d075100042d6403240400c13502085141b80d00c23503210180301900d031100c1c200394010a44601d41240561071aa48460000d6240c0d04910116187d00042c8841080350b802e420741c2a000a02501d0640000aa211050b0b10b40542c0b07d102174030140341e00001140d207580d18641d026602600c030860414145501c40b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 664808201 1250 664806951 664807001
    0x5011b0506220605010b190504150e1521060409150c0203120c07030806041e0b1f030203010f06080c03010e190c050c070e0108070e18030309150108150703 68
    0xa0082c02d0003001e03408000e031f440361094000c0364414000e0b207402004000c1d0a00080000180c7e807400c60052a681341040001200c080c00400d03203e03595804043d640c4071002406001c01005c0c800028000c2540030034500043d199041040240c9900c40b40191158021120441c05100c1ca580320600250710380c011285040c0a100100d04060b41c225910381030508003044141c10325802c054816445801100c0800c45141844803012041c1441e95440070b81a039900c02190080d04c41c034440130101e05d18480f95001c110b803007501c0140a98024020300c100c07072481d407000003415402640c2150180c2c0310144107038107581c00d05a800b80c810760018110301c01107910b030407543c0c20461107118000003004aa40e500381e641c07000a085600d4242594090300d00c0f440000e00401c0b2070071000c01c62005584400c2a0011151210307032084804400500c005c1c0c001e40070001c00d002801c0d100117654a0700c010399201d200c90750303030360b031440282c03076400041506490507032a00000e48854070030343c090f0348020480b40700003141f2000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 664809451 1250 664808201 664808213
    0x201030e1e0708060c13060f090f260a0503070828110607110c011809050a0c080703090c061b050a03020d0e06070809042007030905011b050622 63
    0xa480c10786508251000d10281c502885401c1c0d102d2402c3c10098544003404541c401c0303d4140344201d0042200300041c8043d120f00c84c25000c0010140c5509c0f4400c4945c9601c03800842680988030400303011908003000740a614007040703803030321304c2c1d00280510308000c4180c039106031943c42003906022140d1242800e0006021b07a9010b8006204030f80d94840c11644106882c9281c00005000103007881172907180142030078000070313040f044940c0a18107440c208100480e141241c0240340c003c14402c0381003504000f070a8200f82d000311084045a03031006119210b1280940c02c0b0b9207440005881c41c1d000c0e0809000c030f44d00580803080c2030f09924202644c41c224944605041c106804011001a00304641c100d5401d40c2c0900710080325201118450700c0c0007010707540d1340c1c002c3c464905064080c540341c0c0385180382a54201c808401261081a40e1a950b41c050719000300900582c1c090240441c0c1100f6200c112032110034802805c05910400410843c0c276101c3c0030a1400041900c20000b80061001c0c0740c000070b00d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 664810701 1250 664809451 664809493
    0x30804020a1d040308060102010506031f020906030406090c0e1003020603072001060e0603030405030721051608060a06120b0606090a030501050906281116030521070c0201030e 77
    0x2d240c032484181400d0600d4000d10700880500080d04684c1032105024959070007144500285054812640801003014a8a0040d0160001c015070000d0701004102c1480205d4011601030b42c401c064144000d5200c4005d0306580700c09817042a000014600103100604041000b160010300070304042c05c20b0801400c1c9003038111210b58401c0000e946079107041001201c3c9121243e00712108034040d506103030501c40840c3d5181c22078450152980603541e0098011085858032100d213603008801e41d600201c0c450710800070101507203c1c1000e60301c541c0c40080c00c04104d5120b00c0713055070384011094407401c0082d00d807042050300213009264425410009106c590765080d581100a5105d84000b086a01d0480c1c3c1141c109100102400c1d00b0020161425559016200b4414012082d100c00010301a2a15812403114001d03c0c840441d4910032590902c24075401030058100140c003450380740d404600744451000c02c2c4805540040c0030540303260f0741d02e0040d8004d4009004000a00b000c5a8100484241c100b111030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 664811951 1250 664810701 664810739
    0xd0206040f2f031204061205040c0503070b0a0908010b1507060f022703010e0d20070906080d1e030c1e0314090c180a02070b071d0a08030403030804020a 67
    0x80d5401442d00d982d05041c0540540c021041403054201807500801510501d02c01d000014215503400008040009459214010b40740280407141c0c01a180e1610724010360164548102040324034400184c685c005005d24800c60001a01070036000c421072203441c005800102e822117401d0344501d880d40c0034485601c0544240c10300d070100155000c00030301d181540c04004816040c080d905009600d441c000c400250f460350340d6030b80d1801c13011943c0c4243c001c6c41c1d070040301034480210f40144000044e9009903a0040700039601200c09803010b00170b54090581d036518501c03107200400d00f0000309800b000e42c0a58441c240b001a6410150351410f00c19501480ca600030244000102e55a8884000211001246540d21403c2c040c014500148a035000621408040001e003c0580e055000075030580c200d80c040e00c112030307840310000525040100e0f0150601c881e08281c41121030426407003c8903854a030034110102c07014140038524090854904030b8401d4401042a600018190400216022a80c0c0005021 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 664813201 1250 664811951 664812023
    0x1b0f0d020304051008040b0105060906040b130608010b0a080a0b03030409090f0c12211101020309070e13030e0f040209130606030f2912010905100e0d0206040f 70
    0x82c0742010100714061429180c51400c0201c036004100c0040c903c0200c103815100125046925800003c1c0050b50038461508240c441c40d00104500c8a2540900c55a00a4034403030f03110301006a8a9140030203141c0103004c0701d240040c01c4a0040740300d170119039000c42004a809000e403440c190301c402904080d41d841e04411200c0041c054000c0c41405a500307207071806003240b00f5111310180321a8448020600f085007c91b40700d016820780c6080c80e58020040d16103210068402503450b440d24050107a194102031290004140c1084001082d0440088001d050140c0c103448446443d0812011b01012841c8402d1076604640c1c01c05c401201582c440c00e29840c5080000c401080c01801e10030014151240000030b042c0c040c0c1001c1d0004a140317994403008260785409402d80100100d0354000501c03041c10a294041c19500c0c0c49c1c3c02c0c02c288a0301280080004c102e1200a02c0003079091441c039543c1d005c420551b41c00680006d004180040c3c040861101000c1c0504940103420344044482c40800c46c52003950446 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 664814451 1250 664813201 664813207
    0x9100b16170406140a1701080a05120906070b0612031b0d0302040b0703030902040f020324090708012c0c0a12050f13060608012301120302031b0f0d0203 67
    0xc0150720798000e424111100307200350401d8a8810080d00000e410103404070107000108604070310b64403403845220302c044480b032690700650b59144019142e800c40c0c00142d0301400303010151030b11003081a0032035036400d070054036591400d01c041c0c0b1821000c0c90050034942e0300500c0c0c0480b4101c1e6a03c204050010114000c42d5460304a582020783c610f40b130320700001070040c9401400100300f03404802d0162006aa01420003107001829480060018201c10f440c07100580c0c408410310100340840c141c2080c41075805a441c054900c0342c01e040000c000030865454000800340001800721083e004a4810100d491048104030284072440d80c20310f214044424080c1010003146810100d5071141c100c4030460806c442c108024280080f03000b480240c0207280c10302c21175002d0481c60030001c055002400511010000300100c265a6038205522034a0644000e400034801f0700115590000020020340c2d40c0e40754000314a0912081c2d00d07151454415110381d0898000c601d291070b6502c1c028071840e2102030341b5030b02860f5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 664815701 1250 664814451 664814453
    0x1050c130806100e0c07060606180603060503030a050705100c020a0c1d07030e03120a0207030e03070602031c0e06090f0609161403030906160b0f060603040209100b16 73
    0x354240c00c95116140d20780c044014001031015040e602d80c152000d5000d801c0c43c84d030307031240070603040d1107050001480380d854184d000541a07408050b00b02d0841c000c9000001507595a90218141e0719240503065151300304004800000d80510010554944164152041510f8842d03251084881c25040c0b0809a0405140f070000c01c00f840c0007500c0036181c4101100c1c1c03e0aa0b058050108000c001c05c844280340e035907041624041002c106481c0c0c44004520780c903081e440c00d1014800a034001420403400b00e080d8800620940c42c002c070b502c0c010b0311407076801542011450310300402403103a102c1d088410703e43d03560640550024140542031080300044003c0c030301402c4000c00c2602e0100006d00c640d000c2e4020925480d0b003443d0b40c4140008868044110414464038500080d09510451702c50543c4140c00003681c240e0381c814410303000080d42c0180d8258410342c3e03d0700c0117214400002c0364060707802a8200000ba00600c2d01c01c503d56000b9038800700d1300050a03150480e071102a880b080350f003080380e50b20302c03c244 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 664816951 1250 664815701 664815727
    0x50a17070b120a0b092710060906050f03010605180c0d0501031a0901060f05060903030d0c210504020904060213030c090e070906030308040f060b04021b011b0801150c020301050c 78
    0x2107481102526800a24070b0702656118145000514907030b28800d00c6c1c070603c80c5002040010100c80110484100102903075012110010581446044d000e4800d00c00f000c845840c040c40b41c1400c50710081c0c640700c400110840342464441c8001c0018030900009c0c040100c4840c0d01d4032030540030f14820388848410541050441e2a0080000c0c9400301d681e04054040c00700010078401a002c543e02596607944944059000030f0030740c000c0182e55007900d0315051201c1c00240e8007040894035603503603040d0000d0303580e6030300c0b03514082d1901190043d420101420200700000d8282e80107006400c0b04c808140400c7d9201e07940c030f16090080b648103c12041d140e201040900b002070080100508400c941002401e1a6503400b4000700c2c0c0c001c002800d00381113820701d4018801130740c1089030007007802442190f07a0400c0e000d5820620348150f850f00421361074030100d1224042d26126441c1e020190b51120790282e803070306241218130102c00300756008210b400e00c241030050b1024041c040c010021750800720380301c00d064500d80c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 664818201 1250 664816951 664816961
    0x207060f060321020a02030d0201140a02130b0703030e0a0b011a0711010503060325060906020118110307210209060d031e0c12080a0501050a050a17070b120a 69
    0x30345481c0c0074040001030b00d66035212400034181c1c070840709034103148101a420440541c2010750140583c0c012101c03400c1e419440030324188410b14200c9650b45900c4400002c03401001030a0071000704041e000e100000d82003000d820003e101e0700e4003088044a803240c440c10440d40c040b04076082d0030030b07000503c0710704469000b080300c0342d5031302040310709282883d11a0005040120309880c148100000450b100f902d00340610540402203610900c104034407800c0c50a4400c1161040c82d001489070200400c04178410300030420b20070a11303502c510f605011522807041d108a01141294144a001000210142c00900d031403402094403800b04d400310040d0040c080c0302040181920320500c0d00821540000f904102004444802615030300d081020703034a07040c1c4805080c60b2000d450700c410001c101480350303802039415205400d012400d11084e640c400130304c01c0f0042c843c096a54083d4210a041c40340407500c612070b080b00e4401d042101c85182c0d403641006640c0e84442c100142c1c0754180010018142030900030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 664819451 1250 664818201 664818221
    0x6010611030901170a140106170a0227061b1b0a060207092004080606040c031107020103022a100e0619150b131a0301060c170705030706020706 63
    0x950710b841c0280c0e00003803072000300c4000140e00d8210040403c84400c0139a122a0b5040f400080b07480d0a940c45001c0602550071030808070801e248614000f9200304200d00035070310703070255a0f0001d02a1161000e59400c00c070712a403400503040704040c0700d483c168400c020b031070900c11440e41015100340d011b13450400915102000820780100c0130690704001d1070754005010380c00ca0721100c00000c0e98030404070300c80d521030b0b503043c00350a0701e25400320f80840e00700404510350f40240e2046070104214110000107800355015100e00d9900b144050140c8405035010350000d104040c203a00b40300c5d2468a808494118070555112295425071142218190000182c86200c6c03403074550200030000e40c900001c0750f100c0c030004140c200302c0322512950190802d141503d0100c001e4050007441c02d4031a2031803408840b0303c50b03c9104060140141c01440307001c40340a030b82202d0507a0f03455034038a4003140d216128070038800c1c80e010076551201c80402040011a80510142c03030402e1007900c1c0540d444400d42449026100300c000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 664820701 1250 664819451 664819453
    0x1b061805030a0b0c0a020703020402070614060301050408030a2408030403051e030706090f06060605031906180506122d010b03070e0c091302030402151303020405060f060c06010611 79
    0x4042c000b241c4010121a48040138000c1e40b40c1d00c09030707030340200d00340f54056200940040c008510501048034070742225441d003590500f0b14000c2da40700c208140c2a40e1703050340d010303041e0036003000400c500300c246403c100c1e1015960124041e040c050004005d00d01802c6500101a6403c04581842000001e01840c00008000b030090042002e050f6202c584a21404c840280400c1d030303400c3c0700130070403004402544d4496007101080040310b650b00c0000d03189034000c0b9459852030012488080082009201d4030094030b50441c030468034005880394072002094003801655014181c00c0c2d0094807140c04101e0008444680c4890030040c000801314402075141c111991440c0f81d04089119000d80c80000b0660110760726600c0380035640c6c480d07403511003503407290144040d001107144c2c0381c282054040c1d400441c01544281d4094001001058807200c00e40a4032901d2070400d92407520030000752605402c050340050004001000002140340001c2e01640070305440302051b0490700041107125042603a1358950030f1000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 664821951 1250 664820701 664820713
    0x816141b01020307240f050a0f0b01050423120604110a0611030a230c01090c0506122d070f0f0f05120a020c0a05031207050702090103020d1b06180503 66
    0x40c0c2d8580900d810400c0c448028543c0b80171410f1124070507001284103825070315082140d4180641c0700300c0500200302c4808101c0b03040c40c100803905e500c104104d03400c84820540c1e65030313890a039500c808040d0b811600c500c2e1740a0a40c03200c0c004105014440760b400f441c419410495141481c20900518001e00e600030307000d01040d11a02446600040200c62540900740303070003100e00403039030900842032240c0181d941803600c0210300320920041c150710000141d4011500b042c040e81c0e8603410803425104040001025000801c040b0b50803200b84006104d020003100c012605184001c00d1004081600711214000104080350550602e42c024640c00c1c44800309261024030039883c00c0e800b07403052140c0b031032014001d0302c03010001c3d001034501c0c0e056403174444081d425070f10030b00940e0519070341d2a084961a1924400c402020a2150780a4801c407080a9030190605403075a10310703000c01043c3c507000001900e4003500d907840c80c196120792001040250101c0e484d000a88003544050400e00050364000f03500030307071001c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 664823201 1250 664821951 664821953
    0x40302100305090a0b09150a020a090303230a0c1506050f0d0201170c07050f0c031c120e0d020705031924052815030816141b01020307 59
    0x1014000362000300d0304010482c0e8440e114214903083d440b00313014010301c55001c14001d100f240450b007040030350240b0b80c4500064440200341c000f284501000d0f980030030b0010000300000b0b4040d20b40c00c1604100c4440703048103c1e0b00c1c2c4918a8160303100302c04110000d61480064820020000401743c04001801410008142010041102d00c0644002c0c1c900c100503a10f0035800f103a200d50440c040b0b05000225802c11303410b140032500e680703401859080707a26004000604914440c001500b84403088014001c1c02d880300b180c9444800003014240c0b000401030b81c160714080c142c0e0a030040700340c02850070b4020500401c0b11079000b8100425030b0001e030302ca500001e505410501c02440d000012503000750264070184852140141407010140c00392881505010801001c240c0d110310349802d2400340b602d02103486501e00200000c0301c515060030080f03240092810b0002c0394200000d400540d0010700e507043c0114140e10f45442c80400d0746104140c56000281088100c0c040140c1c264a0707070400e0004504200203 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 664824451 1250 664823201 664823209
    0x406030914030a12021b0f1e060f0f0709080d020a0b01062303090c031203160f1d03210c160e07050d020d022107080106050904020306180903041a040302 67
    0x14442c0704114a5004124101b207540300c481442100c1da503110450300c04a81854403242c42e0f50f0001c9401c050003181c443c3d03d40040743c0c040f9400340300c0c5d01d078000190f4803581c4843c485d0745a00310280c00307101000b00c04000860400c1c0200450b5041c000650010512200d60f440d00501480051704580c04001c0e40c0541042240f50001c1300e10280110501d40319101d9580900262a1210800c076082d0b05103e9940f06810342550389000718000c5031480040b64580342d918105540e1440700c1c500303107000500700c0e001e08111341c10315100e01b011411000b81070b41c091a0a120418807415941e0914140d0007400080e1103940c060100700c00c0e0a501c0544e1000b4445034500040d89810400040040092240004501c08088003960403a032050ba0400c0045440d03e01d0100030300103103000304241c05c000003400008641180d00800c1d00382d040300d416a41d0f05240480d96400d2001a40014020b40d8020b5040240d40340d0409000700c1051152030814001c603101ea10701042e8500b488101e441840f801d6408210500168907 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 664825701 1250 664824451 664824467
    0x3071b0503100221180d0224100305100621020a12030302040329090f061b04050a03050c0a1401020d050322080c0f061e060a0801020406030914030a 65
    0x403402c0006882c0c42c000841901c0c105203080620000c4404c0c88100019809840d09005c40e1001c100200e0304058543c403020ba80c7d90500f8410001615110500070040040c0301d4001da171b03c040c1c6200702c40c000710b540b51f41e114508907e11a6486505851700720511801c8842d140340c1540e140858000d00d07090721540c0103c0c0409072103000d00780c10b4514801c1d012041c113000760115401594800140d151060711580741040361410007903150b8059224101042c60036a0004420061b0740351000600b01396187c01a203040e010001c20148514600309000007d40c0e43c1e00c00c4240ea00450213500601400f6035a40c0401200d030040e41c001086442404e498800d169900003125081c01010b401d00c2175a0743c4a03500150760b080d00000607501841e180071051002c200391880030380210213402c02101c005e400070010158640394111aa0283c400120031801c8004400280841d000f080c05886040307000d4540000c107007a0380c032642101c0c000c2903c500352030b000c0003d82c01d42e10994000d6030015509100c003412008104603 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 664826951 1250 664825701 664825723
    0x30712140f180d0c0606121106130801050f010501020f0d05190311070f02031006080a17090d060b10050315130f061206151208030406091403071b0503 66
    0x41e00c0d80000509116039100d026880c0d01c00001182d6000d415a880208203198450003107542d0343c10104005840d804c0d40d464030300c08039400385c0401c1000c0404014007400750420400e0070303100c40d2503400004000c8030030b214403401341c14494800800c540c10403002a1a004401e008000c0070344c060b41640e0291540001074070610341d59a16140860008400c0441c01307015a03d1240b004494000303081c008000b44000f000709900e100b68203855900007a4400380d011034130340c0d104821a54100102d140001a0812403000c052901c1d003070010705051541c0d000c11901d8482220480707003c0c4d51408085564540f0185644007911185442c41c910b141000c40203010007840300d0b440d805008139543d0002014103640004c803030b40c41009410401241d940b111941c4a1055080a0717883d1460610101d0244041c02410001d407800b240300c4030741e031144030354506d50154001041600ea0990300c0039060005020700b40115240c4101d80020340d190340302420310309059400b000d845080c2108010701000075450102d86036640c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 664828201 1250 664826951 664826971
    0x40213090201030b0907020607020d0207180b04200a03110a0e01211b121109190e0a0b01120e06060d0f17071403071a130606030803071214 61
    0x4680307840180c01a01051044035403140d600c00030001899400152580300700c906034201d501e10000220243e803200241d0044001c005501001103c003a006500043e2070b883e00a080051040d50313481c201c1003080700144041d4401c850014000040f1a13040c056040b400000e81d102516160050b1405410510002c42090500c1811036400c00002801c00d02c281e05040c2440040c400001c1d02400041c07101044c91254020078880004644c80c154180318426402148544080c6410b80220400280c0c105001e0304034014004410045055602c1247d003e0080703840e140d010a00c0d44c2402c00150494411121740b01502e450103404428050000651a8110009480300c40004540d4180350944038181c0401525a400340c0d00380c1c814000105004200c158000c0200b0032100c80038208083c0c0305d00c603508014080d41c40c0314200050b00301c01500ca040d00800c103000910030454941d62860b00755200b0b503100341c0302c84101104110320190041c00c3c807140c02c2c10a000400c600c10034a12065a0300b0303800b030402c20030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 664829451 1250 664828201 664828211
    0x50301140907120905060a1a0a090b0d0516140d050615030309120d0e06041404050c0d0c0e040e070608040b092803140a08150a0504020409090b0f040213 67
    0x9118000c0d26080324011081c40d05000150080c03d01c2655100e0950761030f05000c0c9029460320302343c4100c0c0da03550340100b0024903008031945003441d080040c0013050342a542c051145020b003800148100004810808282c01e000d07459854100040c2c041c3d6041d450031400340c403c0900c1721001401c0032441135032200317005425905040901e00403a107540100c01030240c1041144c1505041420000b400c00ca80c1040fa80d00d49400e90202c00510049000300c0c868940c0710120800c2e0300b40c0514140e00a954095104503400d4200044a400401510910740c802c1001c110703404820506810a4060302d01d41400540c0100401d81ca0940c004041d140d00038000381c442607143c0701048018a0034040744014200b0408510302c0c148901320110200360340418201d0120304080d41420015054100b07036007004000780c854a00d00d035603015134410070392401a41c40d980240101e401240642e00c40c4040d1000d420010320000d0815580d1514a0030030740301810840803040764004000060303030350300700c6841004d400f141f000c10 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 664830701 1250 664829451 664829461
    0xc0d02060a03051902120f150d111305040303020c070b040f031e0506010b0417011b080711010204180e03091c0c1a0307030b0907050409090809030d020a020a060503011409 75
    0x881942013031000d60940b400021074040741c00c680c12070340c3d0007409441c2d0410000e41b5482d500c2c4c91488048202290428404131011001c070b140d025031202d200d80d02070098080e9040f07041143c42141e4044038128003190b4041100d040c540020002880030301107a0500b02d01d440d0910a90030500c000d5880001c00318441c1c0c0518404a0203001401601941e00004481075540c490341c01000030307007103030003548030401d51360440c0c0075103c1050013601c00c2c1c10b510f107100492072580354004031030020000300690305002d4403001030403c0c04404d01c02000146101031444a040e00e081740c40509035100d22103055500c1d40709100350005560380146501403c444c400c0921301d541075500d0840310100070358cc400e6058880700858030340140d941400135486242c0b980d40030441858840100182c0b80b000b56070303041c005942484144403e0300990b00450455001e08211400c019100b0002840e210030b9265044c0103800460b8404218201030401101a00450070042d0856040c00100044040082407540c420720301280410 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 664831951 1250 664830701 664830721
    0x80417010b2710140402070501140412020c030303040c090c021905030406122c01022a0706080f04021519080613090305030c031b0703110c0d02060a0305 67
    0x911601c0081c0c03000807a905500354440e031241d409007584400009030030000700060703c1c011402c4151030b50006501041c0798280203002c000e4004c500300325281c2d981d030440001005492428544218842c1c0101d441a0303444501c02402c00b8a45030b21300b8080c0d4018000d12000460240a01d0280c80c120745c400103003188410400c078504221040d5000040f01d140c095601400b0000c030051017a991036407505034240704d07610203107400c560440e511540c0354401c4140702c64480610f21b1402041ca1441400541048511a0718241c0030881900390400041412242004036400740011001050b05003846900d80c500031404080d805c000030402403150014440f4050a0707240303541910700c0340361104e800d03041d054040f40000d041c0c81d00541e40c03288107184001034081034140c4e40c0940a00282c6c5030340c40e00d041d030700c66103a10310454002030500d0b400c100711603001000100100002d032102c01d001e96125104440f819020034103191070500240d008010000005000d03840f2842100d030900300e641750000356566498942 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 664833201 1250 664831951 664831961
    0x4050408041d160f02030d09060b060f030f06010302070201020721081b0708070807090e12033c060d1b08070608060316030b130f03080115080408041701 67
    0x30608020320412848250684082184100807a00107a100740d60200e10a84401404c50300100041e88108500441002142c00000c5058031442d404522180b00000046043d0041111251603544c088204960501e400a0807600401c0c04e0804610300700564000035155035440c0141c00391a00c071050201c1051401488410b0482d0300004103d407500c101c440b030380420008d4000d12803083d10a00e40c001c00c106501080c1e0104403200c050040411502d4401590301074501007010b00481d01500303641c25034580c000d20003076108000c15521208441020710001e545e80c80258007100d41030101900008028001e1074845400071411104503c044e41103140032058400c3c244200002c10b80580d4000600c180b000651205545a60322750001720b680f6031003410f070344803005650314114040000b010008a01021400d941040252203c48411a902c0d21641c4804d00d20074002c9002820315001000550010318402070104194940004079007401d46841e00c0ca1b00030741c0038041d001220800b0281c3c803801c3c04d5100c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 664834451 1250 664833201 664833209
    0x607140f030a1a03070803031b040b0c010213090e030a12020720040c0e0a09020703020a0813172b0306030f05010e010c0206130803070903080d0509010f0b0f0405040804 74
    0x3070340d070b442c0210410010700a0070701d40340701c490280c1ca80b02c481441e010808500b070340e142c14001d60542d503030b40300c841c80740c0b05508103018014a4100404240101040014201c900c0408005030395180781d074240c815202d82c00e600201f492880c0021107024030502000310703011103146107043d85101d0084918038000340303d0154002d004082c41ca41003a95414a052841d8661004540c1005080c0c0310440a5984640e400c0700e03640e210018100034406d420507a8050600c081c0a441111800d41c40c5954a0215a005004001e41141485000c004102c850b250960b01125980050144403404101906400d040c0300c0e108071148071074504602d4294400d070b121000454003d802400301c2020f504045008020301100c0203429403c111062a260f07000180c0c281c081c1050b0700c41c41d9140400c2d529019003039003000d09800c04005001c4400000f145031000901100801c0f03010018160501d000350908403041140010351480c144404500240d03070b4240e0300301c81100c050f240030070385503124640032040e4030450b04 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 664835701 1250 664834451 664834477
    0x602160f1827061b0e0d0318060804020f06092202160f02041d07150e0405090114060f0a03261c14160f0903061a0301050a050405060714 60
    0x191000c8200036650b10700e001901442c001c004a40e40042d801611800e500c0004020440782141c540840c100700d60719030041402441d000610181c665004402850103034009000900024140829880c08007640704c0d0500c0d0444100b40b414055101140b0700d519108403040368030b400b8507252004d24280da012501562040b80544448840c24603000741c3c042e440300b1040e800b03a80b400900303206000d0046050403500b48403400034403140b032820000000b07806031200443cdc20000006001009511103014050041d1003c3c40085072448042c400302240d401c00502407441054150075100340c548403041c80c5803d0b00d4000c0c1c4800e8040c1403244407a048242c07903800744112070400103071765542c01c410f505800030301c0c150b404000d0000c0404103406000c24001580d01c0030007040c032522691125030259240c80941c000504188204580e07030f4948008030707504400c45014502480881070024602882640d5100c0302d65581003000b0704240d01c4181c4e4803400240300c5000d00074041e0b41c040c030408107002613481c10034005c6 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 664836951 1250 664835701 664835741
    0x11d2d040c181512020114160c060905040c080601270308040306090b0c030114040902220501080c010503100e0709030b0c04030204050a02070242040602160f18 70
    0x1200c6402043e012181088103204004045100420240b08054981d01651000c000c80001036032001917900104082408040740c047e01c00c0003d07184d080390390050015032a075152503132800083c041510719404100041000c04e10030040d080ea00169058055103000d002c288803030080c0285415002c0b255080a0801c102c042000410081d080d00680b2500748070310001d480907280c05901c00503901080c01103601c0d183d2014409401402d0590209580c43e0001b0030081074800900f00600c03440c54640781801003e03480e80010f0103403c01c1004005420282864081d14515204a031060000c0f03140c01a440794036106400300b407040b803003104050043d50b00109129071030b00340101c40207126481ba02c0100d004904110001c0e9900c0040d200341c46103d60042d010300842103070000980310a400d18004207440e4541a038070b0711420724014034040c1d101c00e030251303010f603455083c0180a85818030451070296085101e950510489610211000440d00c81031880c0403420f40d075001c1c0c0006444030740070b00340d2070302851 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 664838201 1250 664836951 664836989
    0x3200a0506012408011514161a090a020609190e0703060f0e06130b0102030c01110d061502030403031805100203030618091207050114011d2d040c 64
    0x610710700a00481042c4008100c048140c02510020b00c03d104104a0b40e1454035401403ea0040c08203010300c0c40400d00385850b04030982c1061805941e28641540c0082d10040641c00030710304840c09c103410000404c001c1081d015a507000612510503600b800b801036501342c0b140d415901c8043c15403000380108007810604c0340340845004000b0003003445845000c0e40c08840008030f44034003603d036900485016040c58180321402c0b42c00d1015202403085241103100800004945180030700ca40c846048240002d540d441e4078900424050315070390741007081d440c05106c030320b20404c42c1c0000c129012240d15060034866150f00c40000c40c0d034401c841c0e0001e03400c0a42c0e80803140810f580800158031582c0200d83e4908243d502003808a00700ca004c0714940040c1d4842000c42c00c1c41c03981a40600010b61007540007050f15601c003881d404403d8003c1c0d0200da011036440400e0180c124001e0722540d070010210305c000031440b10500ca40350b42c40c082d0125003203a800b000e1001c40c05004981c09403c02601682c401c1911400d80 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 664839451 1250 664838201 664838219
    0x706020a05070e011a07171c27030818070b041d0c091e0a260604020307050f0d05010618200a052206171303200a050601 53
    0xc260044840e40612000443c607080071010071030684201031815030101d507008452459560240300f003030b660465030002640c2c88598120007032031603521020041c051010750a00701030a44164580c200c0c80340b000495900c41d03100222039140c0070250146442401c40d2620140c002e28641560140d1b0b01d00d0064041c04144107885a00400450b101d0200c85400200304092600b500344050f1001d600c1c620f010402c0440516046909013007031055411008218529080080d01e5414039038490850140d1580208036100c100001140c1c5010081c8003420007803600707500181c0c5070031480c003489108011070400d07102c00c0d407620300c3c0c18929958450000c00c0b01d1610b441d880c92140000810042c001e0303080c110394131b40c2403412030301d000150079025044900780410007100360356540204844014403550b1151000022508062220042940d070300d8158041004010b0000341703d400074103540d00315510300c450000199002110040b0084540b56425060280c03401190811024007005001445001d0001c200782c0c907 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 664840701 1250 664839451 664839463
    0x5091504140105071b091a0d211b050705010306080a15020703030605120c040c0c03080a0f0e030d0504021504050904030e01120f051602010c051204210503070801050312070303090f05070602 83
    0x3003000487c180186144013046849000c440e401495a800351521030000840902d411600c030f003281c14011f00d0402e035030b180700c1142d0200c0340c4e06484551003010108a0f82d40c1510800c000303002003001420100c2156101d1141c1c2e103010084000340141c4c000b849105043c440d6000802400f802040161281c00d0818180d5a40c40c0c100700300e034822403411030210311250188140c100c219030700d03440d2030002d9034039006664000c1c2080d032214510562914403040100c1000e10083c040f900c00741c81d00260780d0406005110103030766940500e880d4840100310611040c2e035191141940a64545002d40b416004c4000480d891f40100e95003880c0380d42004501400d8841c140c00840c4501c025401103001000458030407401d941c400e030601004941d040040c5494020b0503120154082e000300303094403901c401c10440c4034050b43c100848000207070001c03050100e05580100c581c2d006240840090201080700a5081c625100d5042e0080a050380e41e100d050070401d840c500451b206800038151070352596101d04c0651510 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 664841951 1250 664840701 664840721
    0x81c1b14040b04090f0b011b080c0a02150307030e0604020a091a0405010b0403020f030d0c1b1d0105100306140d02130c05030f0a0c020a021002030c070605091504140105071b09 77
    0x500740070310303111ba952060032243c403c1d070001c1a0104048000346c4600d039481d031120107a0b555a000d03c9840b0009616426a10000c102c01c051500c2d076240741008000307089400f0707005c088000b508050140805a81e40ba010f0500b03072100c0c81c10000742c40740c0c01040303c00310440ca8112250017034113250002034403684a00242007168000e403082681d40542d942015110222410b0540220300317040c40c1c0c5d1020842910240e142d45060301c280214030303611a0300607108051881407200480c05464018081030030305000d440500341013410f081c00003500b01085007810302e640404e9280103143c086601803e42d5103401028840c0750503040200a10b00c600c0750003e080f0344c003c840b015142542c41001c11420b12040c4100385d82800140d024120b42e11143e401c002c065443c3c080d0500c1140f10074028413000b0041400350324001d00c41c80e121243d0751a4003105001c42c031602d40b0780010030355005200400081d00c07000424801843c00f4a090b030b03500c4c8440d28001c07141c0c4070b0b90345412980d003011040100d845d06040c0d020300d00c0e00c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 664843201 1250 664841951 664841981
    0xd020705210f011d0d08060a030f0f241a090a15030206120f070c0f030825171605162607020a0e01120b0402040e0a081c1b14040b0409 59
    0xa4210b00300e043d00c03000300c01d580c2da0382c1180785003000700b003c16208009203a14910030302d26030801ca80bca88801902e445403540c000c0d21030509111400b088907041c82624460814964100e04030341b440d0b0005060103500401c01c22103251150b20800a140203010480051640105113a858481078078400b14080130403110f14060301e503284040f80c00b543c040e50100d80c1d0243c0c007460007580c0d01c40c1a0707400c4070407040242c1a41e282c21040382014036031360326000040308010321031f5854100c106d00ca1030b8100803c100c040e01c2c11b08040c3e020b085500040c0c1d80601202e188410921480d451803115103406003248140c54482c10b404200300c001c80000035078600060100c1e074001c81d0310200980e11030009004580b400c0c030806000005003d04600002e000405980d0300500052001800700880d0180d00e00300444101c08403210000022020440d8400b404540b00b80c140c401c1040010074510b81d8140d840030070341f100701c2c014815035128013406841994100d2b4050120581020f440b00c1d80d54441c8006042c8030003501c0c500b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 664844451 1250 664843201 664843213
    0x120606090509010203271603060f360c05090c0d1b0f030f0e03040807090e071512061a03070e0d0210030b12031204050d020705210f011d 60
    0x48102c14002d8a010343e280703c54001c1c00490b1b1450825100d04249001900340c0a80400c006002c0d1043c854500198001c200109411400c84d1441045a10000511101610700c480020031000b221400070b4101030380c5107850006601c02c0c186034100031103d502190340000c840c41009440000c0402509001e000300034188030100100d00d0340d03408101038020850004070142118594540f003500900740c0791070074000011300c241ca01f41c0c000781142d006400443c2d07658041c0a080002d80c04034410107001c0106800038110b03450400b05101c2d48040c2001803501048106045041c0d5a2501d81c0100000d0100d1501e01c1c40204034000b404040b900222800f04c017040c9121141101810041e506030081a80141a680c224041840c294020300c00746580640099400000e43c18694041006105c00450032611740785900d4280b516030b11f00b01c02c10000800b150000322042143c2c3c0c17150170004180408119481c1d074074410305c03d4a035240c040d80b40300c1040c6641c00e2140d101c20b0303d0001d01088648004210176200 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 664845701 1250 664844451 664844461
    0x2120a0b090c18070e030f030c0706140403020402071a070c1110080106120227042301050603060105071a0603100605010e0f040e1005010503011d030316091206060905 73
    0x500c2c1d090691140c2c0d00020081d15460280010100c20381d40f03c40350341007183c0364400301c9000c03e01d01910b06014001d1039000188d82001424100500300c020107003032804429113110008842c1c030302e0140d8440240507d0700881c10340708200ca40c140f0403209802000350440307072f450710300e000901403150f1280642c1c1d007900c003095036511810103400d01280c00ba00e945070000e069280ca0011140d02c8280c90b03610008035400d014103100314004c50b80801a000a0b0700c03041c206403604100304800c80c0da501051103015110703c50013003a4040007249890448000303c0c3e209803640c3e41c1307500584961242140082400609040320f0421040e07003010280904016402c40d450060704c2006081210b22034040c41e0b002c80c601d01e500400034600b90f01d47d1661006e000d040890a51040e00c2541e242072000d20101d024a900d075070047c0183e00b4240b10b41502c10aa0200103400b500c0c0100901d0303142d100190900380400d217148240540c2601030803042c4011b00030356403503500c00605800c01c440280010702079030f03405900b0003003c13903 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 664846951 1250 664845701 664845703
    0x206030903190f02150408041503021215090a0b010302090a0801020705010b2422230301021e0d09050d0c0515040309260303100504140106091a0702120a0b09 69
    0x60f04150068006245181c402000b8a0307151034001d03c2107800d030b0002c01020510015034a4440c0b20b6025035140940c03118070840004041c1c94000f000004201d00b402c400d00b0503561032290325500b0100c4400c00040c0400040c0049019100e142c2e00140c0140d60380000003a80c0d07070158010f0402c18041c400810444040d40204101c2001c0b42900320050352501020b40b11138654003001b8456501032044192103844002e039019881a41d95000c2031421030520314410b501d00002801d02d9000100720000c61800c0d404c5c0c1450b03040341082c00f038485681030010481081d100000e80c004002c4c01e07001421524a01d0407468002d2a4100007001103c44e4001e00c491000404140580ca43c022545600d4200b002410700030303c004003444c1400354170990380c50800242645907052001b5030103500d6401c8c42c80e0781c1034100300c02e01c4290703182582c04140c2050340b140100112548071400509883d00700b0103126a8046d640c14801c0a4041c900f0f01175400300c0301c1690209010700014000443c00c2c842c2a1184856842c0d207055 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 664848201 1250 664846951 664846967
    0x2040308270931030201150f0f0e06010e030109060c120b090606130314160617060621150a0e150904230a06180804051c020603090319 59
    0x20325000301e5480c1c041540042081400c0040c404a40004a2044141c608041000b04410400d0700035075587d10340035098038000f01c0c000d00030700050320401040520b0a49030042c90550352040340100070202002c80e4407603100b02c0a80c0a0f070f010080082c4404411418003c00a25400d8400000b144140005101c0306131180a0450702c0d08008000350541e60b100c0042c480d056201e48034550502c01031040200000d4021800014400300320340c000c190444000f85440300c260b0694002200f0300054a00d0315130321000e0380c0741d0203522400c15030f610b0380c50b41d1110450b04a22a030089250310912141c4041201c950007030003e030904071404950343c022203a130340c14194040c1001901d990310301000400343c04210703003801c4000c25002417149840391124251115210138a5101c003031449056000b4004c0c20007440b80394041c44004080100854007000841d60fa084107500c143d202d500d009907000c0c0400b003d10008d600c004a9502d8001d40025500c0c6000c1d001c1d183c49502c2f58072083d0b0036084002c0c0d41c0b10303804d21030039030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 664849451 1250 664848201 664848277
    0x110106061704020409030c0215030106080c0301030b0415110c0a0c060306030b1f03061415030f100e100c05130f1206151e05010e030d0519110102040308 67
    0x440c400c68803a50203200145c1840c032015411b000e24100000e0040e242c074192101c2d20841d81e11000d85a505010780200b072954041d0100c10102024001800803401250440b5041940f00c1285442070100b450001d015052010703540503c05e1004c00c6896240c200828540c406a121300380050708652600380a400705d40403400050031a94000740040c007080344000d4188a038610840a0401550f0340381c0c0c0d08025100c8140307044001071440404c0c0101e0101008400c500d00408901402d00924825842c43d41c80b09202408440c0705d45804940c0c0d88410180301042100c45000340a000104c041f400c080e100b503010411418a5000d040c1000403208000b400010584014200644e103402281d12400c024010310760059000c01c0300c4400c0000d910501034605c0c001d401640b00b01c042c05038545000034001e8603024036060b0080d00041020300841c3d50200403034141b03c403504c07104807800207881401c8918210140810403d076100080110520047c140509a0101039000402c1021070700201c2900110340c400c6 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 664850701 1250 664849451 664849487
    0x90213060806061c080301060c03120b03100b0406030204090b010806010608010b03010501050703020c090415060504020301051011070803121b0724090c170105090d23040b030711010606 81
    0xb0100c0d1591401415140541c000d1407418512070500c0c0c5c642c550154020381c01231011509041c4910101600018451a5400c055000b00070070015080420344440c54a07991607025691902034075070917a0782e039100f00e024580242c8104000f50541c5442c6620350b2081c06860a1441030304000503000303105c0c40d200d80c1a204155021070669103024015103203038100d40401c60942c011281d400c00c0d2034030b038550001d11940c025203840d03d521985202040c1100c006801a500a500400043c862511000710041141d491441c08481e844421542681403041c0d50304202d40710b00000640d03084141d04ec84415019070b107151b9100c1c0052015411900982c0b00e0700300020810200a40544910543e90760780011700190342c80081507515041d030380c07441d100e04550032144040808000300800110240b08056120100c84000d16441540d42c4000d40343e0307010111a0103000303544990007510a052034040d2802090034141c165140c0c1000127018102440c5010404099840c281001035031b98850025681a902148 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 664851951 1250 664850701 664850713
    0xe0720120706020403080d06030c3f02031b090106090e070c05010608031b0f01060609030602070c03020d06020c0c100f03180512030f0c03270a14010902130608 70
    0x280e089454010220984505078280000400f14861034010035804102c0080040c6580c118a40b0030424205030b040507502c030b5032441800d10084101d0b18641c6817107a00100c52940d09480c405955100b242416000b501805100400440032104010703d1b200c46104584580c102c3e0388440c03040b84d098006104108545c41c2c01008030303030542d0003001c40100582c00781d000818000d441d0841c46180d030f031043c0c9084648015540445043d24800c4c84078045030401c020080c03006034903100d0000d00d403442c24000a4440ba6000881ca030821900018103002107601404800581074030303042143c0290440d10b2042c1e00d0340200715500da254501030890405050f00c42c2c45019007215090000c500400c00003c5e511440c0c0e4055207204046041005080100c0c4a0b00304801e40c1c84c9018501d40840300c40203801811a140140180850070b03964a245565982e11800922810249034080b58507041d14840090031041141c407019003018810340140c81c0c1d0038000c1c1c0f03114a941da502c0b45090100c84040c4120100c0d90418 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 664853201 1250 664851951 664851973
    0x26040306060b18040b280305070b090f060a0309050a0b0a1a13020702012303040c09060303120b030a0b01181107050a0f1a09030901030f1401030b0a0e070e0720 70
    0x1d81d01c040015400a0044220690020411b070440001e9441d003010641148000700104581001014054041101c98600708605400460042c0c1b84035110b0340d1144201007a12041c1501c02d90003062000d400608440d440c440750300f000702c0603a209884e42e02041e030030044000c801e1440881402000d5402501031480e8043c4080014000d4104503c01c80c108000449840384000007403000008202c00080f8203543c0c1e041a1514028140ca2a40006c0b1540d04000d410030200c0e40054200010041204002c2858003088000030305000d2100e400900509240c0000300f1f03100d0b01e1560303186910701c1810742082007840c217140c00c4255000d000390050207503004400020004018814000c1c01a108075101569074003841c240d803580c0c01003201e06102c0d0b030f400401c10700f059603450b006135500070503460000c1090403000303440310311a1001400701401503008400494103049044e40540405400c0781e040d156107645511035030701d40ca4000d03030744800000e0781d600b020901c1b407020899801c054401d2200901c00050300c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 664854451 1250 664853201 664853209
    0x7081204021201090f200a0b03060405100b09060a090b0307020f0606031603021509060c0f06060a08030a18180204090606090815071b06050414010c0905040926040306060b18 76
    0x1a03500c6c240300d4240d4001540a981c444110020141c00030800d02a00d030314000c0140400c0ba20010603660880803000700c00c01840c100c8104403504500b0640d2919074a812603c8103464546c03440d400849e40103400020410f01507408142d140b0503084501c01d407030860319107900305690307a9210005044c00380c00310041080180740c070130800d01c0c80c801e051005904081c8584005030003904a00624039080d0040e004021f00c1203c2032220660080c002c491050f40c00d42020101981d034010540c000c01805580e42c1d40107134104180070b050b0f00038000741544032444049041590040d401074460001c8030760070943c01064132401954100141e030792200040100500e403ca07900d0b44034001402190a010390f126210031008c404030400c4203181e0060b98081010304080c5450ba104850b404401c0603241d02d008460900a40d101740001c0071524202ca011800383c4480c18980305076030040d260079010880760b0210b0b240540102d405001107a00501c4204000d0743e0b15141e0440c10700c1405190410082524089409850 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 664855701 1250 664854451 664854473
    0x3022e0f02121308341503090c0302030609030c060a05220f06020d1d060403050a0e0f040203160906020c03030f030a0b1201020903010e01060305071a07081204021201090f 75
    0xc203940d0510034041c0e031344560314200240f8030360403540f0215088002030136440042100b03c1d403801d0900003c450f20314100700c00981d060244207100c00c040d00c840341c480031700101c0c585201c003464004040d61000e051407441e0640c4c1c0e62041c0201462809000001510746429218451140085040c840c0e00394202d84d0071480210141c2c2c40c1111040143e1480b48c0100e041c510261480c42d078040d0b000181c140c14040000710000c1c1c03400c500191a40000d0400c00002e60080c166aa0000e8030704140039400820400034054003103040071160414400300400c0060004011110b000c191181c5440c83d01c2501e50f075089840d60000608190164000c10003801c607080d44200440e4010070035000051071114500c0065014417040700d68111580d00443c4104681c40c003032045c43c901d1140c0100030021a1300c0c5a580507128803041c80b60a0400603851400541c08000404440d4142e600108140c0e45654041c0380d910311500940c1d0503030140e01b480e00d201c07500001c140705503000c2542284e0154614a610303900c000380c0513 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 664856951 1250 664855701 664855717
    0x40f090c090e160603020a0e06030717070306050d0b0f0c0c0703230a0609030206061e040209190906060f0311180f03010608151b2203022e0f0212 64
    0x4400d4010300c0354030f4004605280c002d0601a6005a07481007100f40080c0003002002e6032500c02c00c410401d05c15565006182070f441402c0303820300c65089030344a0070154014130170740d807200350050710140d1b81c04104489174490600c6400007600c4100d881e2569001955035000c1c4114807942036000344401e0002c2448051200c40c2034601c00c4082c207850f4403003800d850802a1006040350203030341ba5030134030f400c040e0140500ca43c0a80203a800600d6103014420201520f1420f16059000d95400682c0800f5a20b40000c0c003180009014054002c03a0796401c00c0d00020039180c8102c6001404100c100b006880c401c1c09000d2045000c5400c49007003010f4002c040400102602c100e0794404242c01c161481a10300303000b00c00c0184900f5020f013600c01000340ea05c03826004000d2901d4080c8040603003180c45801074609407081c01c60303620401c1c0e02c0500325019000014020340c00207503000220f43e000c2405180c81070300c04046019404200d40c42408210340944611080d184071720301503001802c01c50345640c81b10b80500303403c2c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 664858201 1250 664856951 664856953
    0x120507061b080f18030909091212150d0209010510170106090f0803070807030c03030204050603040f060b03011413170307030b010f05091302071b14040f090c090e 71
    0x100381d60540d15000310901003288000c00c20400410983e003040e061156401042000c40202d02020000e51640702d20406e035801d03104415001c04200c01c41c000300190009402c0e0080003650b6114240a80380091070700f1500312218000804405000381070211111981c150b001d80031340b02590800c01084005151f28060308104945101e0842c0100d4050a0060080009483e00d6588a00701070f500030b04200190801d452985c0704006030000914040220b0701000c3d0036160041d505a00c0d46011406481290f0000d0350100020013400b0901192103074a02c40140324a80800602d5015414942070b2090030b180840715100c042c00041682d03190070390f150201d912074103280954444d006c80c140d1103504145d0b0321030002aa266204415540c00c41c181021581407404d21a003820101e2000810b80c40e2940c508a17007441d0082a650100003061806078444581001c1c1a11100c1e00c0c0c0b4080d90450070f00c0e101c100d22407810704503903903c54011849a941c8968000c07103030003261030070f1130441400740403108807005030313 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 664859451 1250 664858201 664858211
    0x5041202041407200a02064e06091005010807020109060515090f160c170c01050a05012c1e07050a08011403100f0b10030504020a1212050706 62
    0x1c2da00840061280c0c85031380326010340851620b654050020000072071902e40d40b05000d0040582c3e580e45c00d6450b000420010030f40c44051802c055030805c5211000c2070180c00714149041c0d1095140500204082050711030724070242c0d6140304000040e1815681c080303120013046010301495110700300882d40906203000100d0525541c5da182821288210744600003003520b0700c5203038054500503040c160003201d403070080310560814401d6490044803125940c01800442e030b40d4481080300c2c0c808038a0300d1304003101b0b0742c546480c03012036158040d05040790349400d107a240c90000f00e40c40800100810840904000c18003807410150000c1d0301c00740000d0440d55110302c03c617002c80340c1a00b42ca80c5c150702c21006559450b031201da00b4040540b4418041c0c01141d03610803c0c0b20b032400c1580740020001d000d42d0582e200451310030500078000004040003240075402c031000d5020040000d8058200303500030b500c00e5461480030340ea02c40c810401c89100c2e11000300f025186902e01c2c442a8414000b410a16026001c0090 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 664860701 1250 664859451 664859471
    0x20313110a0506160507080a08040e060315190608030c0d0302070206040803040602100b0d0b0705311e0605030601080a0b03011b2304090c020f060106030225030504120204 75
    0x15144d0016083d00220b0720304d0030b0301c640802809200340c00040c15003000500c1a0f581e00c2d5540d13a03c41c0164015101c04d090607a00144c0159020800503038110010f40011400f420071090341003e1501f80081640d203641090800202004000304441541c2c012001411410b501090700720080d501c052030590340072000744404142ca240500051009001540081400c2c035803000306142518600d0505501c10b03400c0c03501490120700c918079010361200152420344d81e41c951100c0400c0b030261410f0100800a9185042101d8000e00c100c042c406075032821034031203800e00b004071540b4190b0001e030082800180090010038031650141e80103d0b0441c41c228404510380120700302082c00c40d144d40c02c0c1e54400100760440030b040030381c1160303010711505070300048a031b007191080303d80807920702c2070b407054031700b00740d03851344041e6a4034802c0c080c0b9035404200d001550300310350b501c2c480100a90000b102d9182c9024071502c010700c0354140360030f071443d5541c0c0c96141c003030500f072501810001d0445040d0f030036038206440e200a0a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 664861951 1250 664860701 664860709
    0x10f140a050a080d0f030b0913081b060717011d06061e04050a05060901200106080105131a10060e010909022701091412070b2704020313110a05 63
    0xc041c1190fa0000c0c0300814559030010b00700110035050341c050501e80180c68100c0d8584502d143d6020940400c8403500855510f00201c251044079074100311024070455142d640d6901040c4903026113005d50b108907400d03107054030710750480c1030a00c40e1000d54003101e0515100e8071411250686e20001c02011a81050070708084003419045c40d241c1c220300150005001d0010b403620070904c0c3c000e48002d4035224206100c490010b00011081d100310416407410705511980b4890940106014080c01c100038401401d04a13601003100a41c0c80c1d044405049109805040d02451500f40303101e07909507801ca9083c1c518044080d2407000300c1c0042039042292403000400c907842e450004002c0c4d60041d0001e044065000031411440c0030313100b01c174181041000d4500f009458005a44040c1e0700208840300e101d01107040b1010742c03800ca030561060641d0400462844072900700d20900e00381d06c0000d03c8288403284906402c00c800c82c44100e0312000440140600c08000c04c103101c0c4842124840901501c04094482c0002 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 664863201 1250 664861951 664861969
    0xa02030a080a02190b13240204030b070215180a1703041101021605061b010c050c19080a03200d0f0e0106060503040b0907051503150306010f140a05 65
    0x1a116031400003100101140c0c10000d00002000c03000301c50130302154681d41e54503405405040360b8000030b007071818031091007006408101241e81c00c01041400d16928a0154040d403c80e103c203450300e4250340002202030307001241403c690544103031820669038032891520036070260940d4a11981c4940c0449800045075441c00a01d40341210503066202e15240c07425441c0c41502c0d40c6842c1c115081610203014801000c80b842e001c1e114116852038443c50100010102c11007c00300c000007a41c01c1115540b4030300d410000034201c40040006a4541e0000b07100e4081034410151340041600d2402c000030260a4403c1e40042031340c07609510042d8014070340c040c8410598105a850721a80c075601e410804460b0814803926524140941c024401903240030030182c100d00008002070445174299002a09602062200320702500004025032890440b04104c04400d4108540c9918480501c00c4018620300c0c000071003e0480781c444d12038003200d82c244820004610901203405400c00985031010403c0e596550310 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 664864451 1250 664863201 664863203
    0x13050a080a09080c040c081518070e091b03040206251202011409030a300b2e030c020c030a05210703050d0903120f0506090603030c030301170a02030a 66
    0x241c0e04080c3c14503045609000c5a0b03803582d03124a242100390701082c0d801400e00c550000b1160303000c8c1d6208540002050102c440e10300c40082e07400020040250154210304880e0b1041020703100307120303180d41e42c8506020652507542002c0a581d01030000038010700d071060080c0f40f4040c010084900c00003c02003000c0c0c103507281001c206c500d40c0082d1000440c1d02d5092088a00c421f0f0685241e80ca03e04014400c1505c0740b09031030001c0c042002e80800c4c100404140c21000c0c4c020b4041c0c111400070112241d00b5240105a650740701c03032081440340b6000c840c8a41140464000a407218810b001c0a80401c03002ea000f4049104020300754000d410542880e903509214101815010b10040d1018840d010002d0100d4a4050326038902c0c848207101490210794010103851f1301c00c0514000054040d400d00b020b440441d10079107400c2c01241445413001d8180f206801c503500070f00c1c090300e00001035100d010426480c0d004d0714504c0e40300c0390300610042114200182403202041110400d9905040d51034021038209065104 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 664865701 1250 664864451 664864457
    0x37050306210613060e031303020904062a021b010516050f0a0305071a04050d3b0103060b09061c0e1c08160f030507092303070504110313050a080a 64
    0x183d81002d00c111401003504804400707020351318000b440506901c1c070805a000203401001031500180400400d41c0c0900c034045d0720190b1040484401d403403250500024120b0000040c05110401d26000c0c0110003c035080c040f05855140c10040b418107400500c201042d800d55aa100e50b40004c00091004d01802c69118020342d00c145d603c81d51814607446441e80448042c4521007500d082101203500450000c43c6100c2c1071801c1414105103201c5198004605c0400003d20000508107480c4040742c3d01c240d040b402ca0030b0303c081c41840c0e903031054031100c1c1c00750090793394012004000c21205416088101c000c1c6607202c800014105d0000e8111724902480d41580c00720b8401540e515010281d040302d482e65018480f20002a25460003600080c00a10301b540440f05154072880800c9400d0300920141c8090860184002804c1c4502c55400118041400c111400783c001d5100200d0300781014029101080300000382c079403a54466100200291a803404151040c2c0125148200001c000c0c1000704180d912035a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 664866951 1250 664865701 664865731
    0xb0415031a0f01060c0f02100c051b0a12050a0602121008012c1f0213090e0a08030705160605061507030e0123370503062106 55
    0x215165008119807200c8081c0c0104103010030412a1140310480e0640c1e25a1030600c81501c0c0703902d000c0c0600203051000940c001c6446511842d41c0d54801801d0034602e02407000c468081034590707000c01917071600504d505c1c3c0050000c40c0c2404941c14005800050503c1002261144101c54494404a800803085180e03c07a45140030300641c8a01824154042c01590008022a10407005051360a01c544500c058142d500da2070021080c0c0e0003070000c80c600b081842d42613544191003980301c40095000010121409403001c40110b0141c8042c81408000c500701c40041242c10120740366030046403c01070a1000b00302c0208050603c40c00130301c0421404c04d124400200b101d041c0041080162440c3c2286245452001d01c44500840d9008a01d507012840a09100c00032100750712100e14030350342540001c00811000102d185808918480c0c10b0100030805091040d24001003151044000e5150600340010314280301184251810303550320f820b460f102036406038003c11841002c6040070011136140e0411540d003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 664868201 1250 664866951 664866953
    0x90c03170f121005030f0607030b04020f03091501090b0913240608060c09010e040504060b04090f0c050d030c0b19110a0e0916030b0f030319021218040c030b041503 72
    0x30f001890040d200c1240078014617090610480d9440c6001040c0204041d02c50f0100440c0d80c48540c1100c0800320421100782e92498000341165850001c0d66031400760b607640c2c00002810349464411200003003c000d00302034080e12080405412605100d0090700d00560b1010072314404814620f0340601c94004400214095140940d4507040070001044054101e00c100002e5a8680c0e1213034a00484481c201c8000485460b18108100103240243d85c481c0c1051401070b21400b8420202901c690051242da2140b25a64469044c007001d4540c599008021842441c900800039051076071190344a4000201000d00d45242c034280010340300c1d0061140300340030000a00710340c0180e02034103218000c0401d4840103d0b038103150300b030543c600500800c0c110400d03a403840382040c29940d603000030f540d010004080f251294140d0003125440c5080c03081c490050702c9950401c500520300312043c1c0f11800528111050b2003140c0806000c0605501c190040c00c0641e1100f00102e03503070321482101038100800b4010607045083d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 664869451 1250 664868201 664868221
    0x110a060809070e01150c050705031e0613020135010b0d0f0c09050d050a06060b030117010516030504021329040b0d060c051201060201020307080604090c03170f12 71
    0x1604152143c651407801480740b2569900003680e9100303a4982010003414034103189080ca0805c1d00515410300600441030710b01c20600d4507202408070240300765040ae484006504290121500e0024089004040c52002034142c135240680003072058a07070054141140c622403403a00a0980200d10383e5500481c0601507182c40d4812002c0080c004001008100a0700b640034000618a2048501c2007100c05000001c00c101400300c0003115501c0b06041c06000d480300544201c6400900441c801042c80010300f2440340b0050065a00950300700c0d081215107103290030118060000204240d0300a008910300c0100d0401610506280c00d0b803100c1d0041810440019041c0c0305c21099205a01c90345c1840c034510041da40f03c0b581c1012480c0d01000001d0400800b0000352400e0149422104100108200000340070350190010b600c620700e240d0300c1c0e510307d41d034940c100f000f2a081400d001d440e00310421018000114803040c207007140015078045a041215001c2c0300c401d5a03100c2520000701800c002e0521035004a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 664870701 1250 664869451 664869463
    0xd03020d0f1a090c0c0f010603030f08040f12090302100807020d1701170705060705010204050307050d11010f02100204171603050d03021309020a020105340c110a060809 74
    0x18101014070400d220a860410b100c85110606841031a40300042246400d40c03078200c902c418003000a403000b0811806805000305082d120940209045844811843d0b200710134042c0315942c41315000c080d0200c6c0b9119a04a03000d20700090060142642001c00540e840c512041107884041d511414245810a030080c104800e0a00700400d01480c515084020111002c1207410342e01100100d03070003c203c000e980c52520045900c100c1c2c01080024000701400b030b041d001002a42c105400300c40d056955002409200d208800c03014010102250000f40d141d8811680755900114038030482c0d40102600c0901001c90344194028050b2018440712107120013000d210042d07600500b2042c656800b440c5464558a50800c1c20303800003095400100c2009030360040004e00060145440110b45890515002900801c002d0b180844540c2215030031010460400780300c0350b5091180c411082e042e420049080d01e82601d5040f080711807500383e20b914000d0b0f46644190f4801000c4650390400c003070804104440c1048 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 664871951 1250 664870701 664870721
    0x7060206060f09060409020d150c0c080415020c0a14040e03030f040f0503190e0913080406030b0d061802130204120f06020d0c0e012a030503180d03020d 67
    0x500305004200640e951525a15000c0c281541e100c409551084001030051200002c0291710400030640d16050104080380c0315840300c2c42400400111007940e00503034000c1c1c04424018001c2c9400c01007841108044002840d8002490040b110ba460040000500702ca0741500201c01000c04200440c4151400d0300880388110008030107180b650400507910088071800500c060000e10b02043c90300d082000400071250218a8903151807038200c00e00400919400c00c282c04540301340341050106a00c41007e4440d82c1805a00c100014605840d0010940290902c03003403941d4003000030030058001c0b8131280946841c150404900700c048204500c100514581c0c2207075480c0c5414810300050101c0702d43c8031030342c44c4240e4102109140311140783c94144081c1c032400a0502d46107040400203491b060b04040d031002c40c200700f62640e0702489040140c0410b00c80414002c0d000542201c804100400d004078002e40e00000e07104541d804c070000c07200100d8a000015003412000a90025849a0f170b019207100714a060 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 664873201 1250 664871951 664871953
    0xf211b0615040c1d09040c030f08040905010806090a14101112070507110607080706091211030f0d050417040602060a141501120608010e060f0a05060a1809061d070602 73
    0x1400c13124071580c11107040c0c0141603000c1c0d08144007241c01d01c010f0309560340055230300800920b1700550030718101c805a0020702c280c5480a04240020500c0000491014401c0c49030300010034502c105525200c1488000000e00e0310306000d0880a0b481c560441d00610308900c80c0380b42e640350355a1840308041c444500c010701079001c0080501480000030b1200c2c05840d144081180c000340c8610082c00d0034443c901c1a038a00501c56031034481e003601000842080c416a491050311a81e5403000b0085441741c481c4941076859010040420074905481210340c8010303041030181d916059290b00c0340d80c0c0c2d407010f0392203034000718003590142040002c2100c850041010850700705c40d020344141010320007200441104d1070790341c0c1070224038050781c601003ca50b840f1400618004000780480e84030694a140c0b13541d0190303054045580e00400041501030b103802074078068a000350000040c245041d2150203030694007000d007480e464483c1c200c0001318019018840803013085c1c00100000b50b07403c2c24618038101d1903501503415 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 664874451 1250 664873201 664873217
    0x71e02160501020d0212031e0a090b01300c03060c050415030216110d06051003110d0c051903230d140904021309110703020f211b0615040c 61
    0x402540803c2001e050745445041946239150360782e00f50010030004c08000c2100034030600300100c91005402021469001b442910300707070303600d91014018007a0469580900000c07240d0309032121034803d042460303055000350600c803111600e130754542040d518003544a2000500210f401c0c40380c0350a0b9540d008081c2c110341000c61a0003642500e840392040c1404002e490442d2191030f1030529250f9070070345612281e100c0b104100c185030810480ca00c4100d079010959010100b40d00a036198103200a440c16078640005105901915100400515100058003000a4003d01c24000005a41c44c241d2119580603201c030051012076900e4040c3c503103640c0c2d0f94000200110501084000351505081390344121040c1c401594442c0310784419658111940d005801181ca030018901c012500076019119a510a0b426a40c150030001a455600d21221300400300c00151800c0380d4070188403400c01808134128503035400c122091000129400c0040c102d40840c96603030001c40002d1640380c5489400d501c1401401c041d60 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 664875701 1250 664874451 664874473
    0x405010815011e030e010c03051e061815010f170109051305030d06030b0606130608041109040c0303030e0f030702060708040e01170709091208071e0216050102 70
    0x40d000003400e4880c00c01210900500140d2181440403485904191120144105800b0040081191007070100d240d5107003203503001d1590310078080c16019159829400c2012112108280a0701c08080c142d0740e400740c2d0800b801a407903101e00f140e09208103482ca060b001f141040400140500f0000b4007002d0405c100e0441c40304a919400b445603040d5078403000c0005c0c46075152000e80d08107010122010b041440007080707080e86040c00c2e070006029a44525030001c000d8a03007405020040c00f40c00d00218140c145a02c091015612a0070a26880380c081e024001d1140304a20229007045001c2d641a1000e42415500380280368050140d2401c3e031143d00000d242100140c81526141c0c003692800a1190340c001034607d0910a1842c16680540030310700d480300155a4a01241100103400d5204041c20b0207684000158050540b0a50016580017032001d880180001411140b00030001c1c08041413050308522825030030040d103c44c10810080d60000c1c411550121825008604658031282c115130118003900 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 664876951 1250 664875701 664875707
    0x9070819030c060b012c040609020a021b04020708190311190806180106080a200301120c0f0909050f0115231512130b0c071401050a020a090b040501 65
    0x19000c0c039000310740010208440030040b6a80324403203c0c58a036040342e62111102600d1110380288a21801f114104050b66881041e20180c0c05200a924090b0704110b160a030340518802039a818000024001482c140c2c107a03481d40d0b603a800c18192940c00d4080e41c036404135080d40611840d03040f400c50311061410071812401002c06148603000603c20400f8240103d00d880c1c541d00c810000c0b0102911a0252561310781100034000715040707500490940c10400801c0301860a8011b42003103c203009030031444c0d40e082084918450074a03000880300c8400b0300c240000da07544041b1200001e8070000001040040e00d6040c02880c1801c10280c4555076498080003001c0d100507251200e08445c2c160000b0003241c0c1103810071548041074a9030b00c54105201e9420008803a501c0d10040031017070700c0700041000782c1d02d540d209500c0c1c032031121800400c0c144180c3d002ca010b038075030b14028010741d5100e14600e07601400c8003545a82500c2c41540d4600f042d640201301001da0b10f400400c03110192903442e01460600c1e1601c0c00007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 664878201 1250 664876951 664876967
    0xf09010f0b0d0e0d02160605030103051002090105090301061413052406040f080a030f0f2a060f200f03040f06140906010e1006020a0210030204030b0907081903 70
    0x41c1050001020700e030154050304050b1070000c3e1201540c02d41c411601c8082e407100005d2403407640d40703644e441c804180c02d40146c069034140e030341100092880c0d16100200b40006d50004142c0c41c10f1003401e07c03044807556024054031000d410b660302c42045149005060044403103d9880f84420182458100700c0800076042120702c0b0700c038518081c0304404080001042d45440395802c4100010a031681c040383c80080001c001400c4c0f07100741c3d02c03000c00704c05890084851420010000d000a0b4819800f0074540100007500510f0f50702e0050601e28900b001d903500d0080740c544840d8450056122002105402201c04404e0103024200107000d140006110002006110003000104800c0b0901060800d0200540c04001d400c881c4054414a50622400d8241e03100d9003407050064120090000954100041c803801045590507001020f0140540d030800000f41072040d4554101a130a00000003c60241c0c0b074405c1c01541040094003034182420780b07282c1052002001000071641030881880003031741c84186 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 664879451 1250 664878201 664878209
    0x1d0c03030a05030c0d0e030c0718050601081b0f040602100c0801060507031407060906090b010503071523041e0b030c12040c050909010b0406080a02010c03050a0212040e060f09010f 79
    0x1220740d60b003801900c00b0b0000c0c03411303803000f007094440810a003144800c0060707907005441108184000c69901d141c2c004ac241e880844005002030070300f10110382e0b8140b041000d10300440005003034074101800115403040fa50015070102d00160b200c0302a0b01c85402041c800d02184941e90b103000626981060000307460b80c031448100404010040760f0041d500146042613030310866216000b1311403060302381007a0000d0181034000303542c0070340540c000003818500001c14000329100e800c042054a807040c8420344900c06022035601c140e10501005c115000d84d160000d01c0540b444030b09009807010f02800240280f5007a40201c0d001030410400c0c00724000806042d01c1c85550079415103859031340c451600345440d40c410741c0031580040d107040621803200e0040d0091103d50100b9541003100b02c1d540d5800c56511181c50300d019001c12800a55000880d114400410704118540101c07079083c40b0604000380e82d980030380e00409003102942c0038010380f07191814000328890310458144d00ca55040800702c2d42e0034081c91007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 664880701 1250 664879451 664879471
    0x905040e0d082503050105180603120c070f1d0a0501080c100e10110111070b0c090111030706051006210f06050406143d0e041d0c03030a0503 62
    0x100080002e0708040b180f02e1a40d0458101018026012001401418007030080a108031801862003a1000030380c11140c1c07003038070300034000c00703005480f201c00c0400c0d60b12107000c0b41500e0140d03a0000c6103660f0700020040003000d010322a1042041443c980760046480075001e41035503810040104443c0000040400715890201c0301400c403042d01c904245d4640c01441c000a4100301040c2d240b0a0ba40e400c00080141540b40703274001c0c001141d01180111851107034420080001190b50302080403d01c00101074041c880d81810018a80c80002125a00c2c41d005020100c500b56144c00420101c49180d503402402484175040c51142d00700700841c0319881c0c03d0603409040030540da81003c1c040840f07146c0c01140041c90f0150040107201d448070804880c80440c4c064641c040e803070903109800311041d40780c3c0e03984e459610340d42c40c01c02841c401a1402e4203513502c80c82d010104100001c2c45004c580ea81c0c442c0041641108405031006022002c131982410502c001c00d0b031017070b00280b08490059401030112540881e01c08 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 664881951 1250 664880701 664880717
    0x50703030f0c05011b031d151b030103050109031e0807030504110a030809030c09010b0f0c0a060c020105040201090b031621091202010b0f0f0d050c130b010905040e0d 73
    0x49422210b0144001016040d0760910140d50742c00c010000d4030040c801203a640c140310741000d2452500800404000c2c0c003141d548180608860070064005154021001881850300c201020991541c980c00070b03041030f2246d075580c5110808040c2c115000340d45558a03c0079001e140c260220000d003410030700904200901d074807400010204104240007002c041001070861400715200c0c00d207117070710360002d00100d4003900c580280c2c8002c40c6040400726048464110038076240030f003030000b900c4054228207001101d0307205208074017001601c10302903500d81c05625030001a482c501400010012a1180c1c44000400c03020428031083d04028542c200c114801400d01100c0d002000c8261056a1450070107403a04619061150b4100840b009413005076083c10f500030b20640100104000703105406e0300f0207951004504520503aa42801111701000c00e00440c25500c402200801083c2c0c590701d240050092182d9465044d100f960300070b500e10001c1c18041d0750400290b44002c41880e980c0c0b818200003020300100c4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 664883201 1250 664881951 664881977
    0x30e0910050301050c040302122b02010209040f05060906090f070c142b03060506120402010509043e0a08190c022119081003050601030f05010c0c05070303 68
    0x600d10000092030080e00802807031400d04c1559a0541290000700c0c480c2c0e00b49420803410000000d600124818402044040348101203141101c101d03121440310203654090000341020b0707469100c0e40d00f589581c80004901d620381f5400b00143c0d060010078040c032980030a800d01410056886105902c0007950500a04880d06410301001d202da1180343c500080c0f00c0d84004420223a5030300710301d103108c0c40e2010f0320359031150350689c0a030251000760090a400280500a5250f240da420051640160042c18081d160001480100c4c1c25140c00c0441c45260050314040d016182e001069071520548058480982d101046403c089480c0318080640c800c115510340416442000051280016100007104101c24002650065128042c1400000e014070032040b294886e03000000c1121a2040c10260103100700d82e071040261504180946004400d41443da00440080c1c07040050382d0195000d00c0414959910a1800c24250340881e41850704000c1c0b10241e0300d0000d00001032010980c0d83c1814141460051 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 664884451 1250 664883201 664883221
    0x6120c1d0a05040e010207210e01051e18030613020108041209051c06050f1314031e09100309120503040501090c170c0303030c040e060a030209040507061704030e09 72
    0x1050b0020341d4464508140d07200810310550080802c01e1141d00c1000c01580350451528400500b43c0701c0c0c60100c1d601500030b0000b980310b80c3c002c0980700d58004203d00c3d05404045c0d4404160854805144c4c0003080f031030104880c0c5000c002c11540180c1441d042c1f0342413212640002d08000740503000400d640c4c8004020201203000b5080030300507200107091084251028036521020348001710f42599014030781800714050300c107503403441889820300010b02841c0c0702040d07581c422542841c0c0c0e109501e0b40014072a0308403c2400d0702d000081860f220076443d07240c000401c108007107209503420340d2082c50710780410400026541d003210810101d8500b09682c41ea80c032030510724017412183c04021304400c0d41040101d0124040890807002e100f200003100c4200050106140d83c134441a00c03850041403050004000440d8a60701595121401408081039a65203501140000500381d40483c0c039500051001d0158591005000307002504500d147c200034105624054501c142051307220f4068000344000407402c0b00303 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 664885701 1250 664884451 664884469
    0x2070503040e040c090c1b1b031209140f01020a020919050c03010e06180114010c0501020c03090102060a0603080d0c110a1101110304030c06210f0606120c1d 69
    0x4504007807003102d490513280101500400c1d01600c00a54600003540031a03d10070361486462811002d10040c052003181c80d1074480f0405058091075158403c1030100000f16804004502d0300b115840b26000241440311403425601400180c9014107443d0704040903eaa00003149406650103072111540c83c1c40d05200302c41000d21120200c00c40034100424003841e80c120000641c129100724150300c03140d4881e0000c02c2032070805031901c004503110074030040c80701c02a07035040070700b4040301410f10f8190280560355650036a00101030139501901b011a41c3c107610358042c01080d0b80280c010504000710390a60b81c8225117801421a41c40c0d003a030b96117440113282800f402102e40e030011810100c1d1191041841d28400403820750761b5042c001050020004501c0e5000825034098076400100414000d09048086982a10404950700c500c0d038084102203e00d1400c0c407c155410101900100d242c5003801000752507038070441a0380e00414940141c090026a106c2c18083c45442a2601d042c50b0718200030010792121 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 664886951 1250 664885701 664885709
    0x20c030c041a101b120905010309020a05060a0908061006090501020304180b061c0504030905010c050303130809060310030b010b0304050c13020415020c0a140307031407030b1503150c04090207050304 87
    0x2001381280c410a024401108500075201c80e6078440e0156110401142903c0100d4002500991082d43c288094a4120050021705a5914004800a5842590303503d8000c00340c0d43c030108505224414400b07641d00c040300b00060402800110310703091a050440917a21005224400441c1c1d0341c10404070140d6540040f62042c01480d09980000009090820010402900c0441c0451041c03d00046c4950066107800d40250b08400a542950b581d554926070502c140b60341201ca80c0c030f082252520903500c210180d40503291341d81c003110541341545059848000183c02444034880107104000c0000d40c000740351749074820142c0d218001084030100510113401503130440c800ca600e00d030007403010480c0d00180c00003031f40c48111805201665904900040020310074209034050f0040c000500c0426603601d01b8491007044c10b0111680c10b03a49486000b0308460550713266804540e0691400312501c0c08002d002007a200c42d206101c52402d000318040900e02c0b441c40340310f040715008140801405030078000e9030018 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 664888201 1250 664886951 664886987
    0x1503080a300507020f01050709030314091809010c020a08090f0312030c0a1d01020c0d0c050409060203040b0708070801050f030a0b010605030106170601020a30020c030c041a10 77
    0xc801c440300c4005402c04440c0a80103108400c03540c3da04190501030940504030795124040101c2c2540c400b1690005071260000700030008101d0b1090940356200d107100300c1c8484100302c0860341410990385003581c0c6949240c0c0115482124100b0118403a42c00b1520401c074111a5454062500d00102c0e0a10484050f45007692401000b0023114042c0c40f40200303c024409d90303581c41c030301441500c03c200b840301d1803000a0059000c0c010000c0d03242088407116840d2030041c0b107c0c1c503245903500005003d580315460708036031468002c4144810000701c00b041582102e01802c12543d140381c0400d005210303840500c50584142d48007500c050844d00c051001c0c0070b056403c08440f020a40e11500042e140e51320a01c113410028001c100100c080007501c001950242105902404000440b500d41803490003855518040800c0d084032070180c03002e05154480e56034501600581100a450030405041c00d48000003a401141400c21643d0b0003601c1901ea00d40d030142c03c4404008641000c1011101c00c10981900450 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 664889451 1250 664888201 664888277
    0x160c0f060c1e110d080c0f1203010b130308070c0609171020120f090d0e13180309050406080a110616020307030308062704121e0903061503080a 63
    0x900c10722000030b08200c0c00e110121a00c0101f040c01003590388480d10b0f003101e10050140018001006050001c0c02451030341603458589640301c0d2030316807a43e0f00c4000c0031a00451503003420414036402c0584400100150590f0b0580c04040c04800c946503040540c030003815540d2082c1300d80c000711900441441c000102c2240a1b2200309000c2c000400744820b4031034040d604280400102481e00004600c2441c06c09a96000d81d050301502c03d10002200c10700b200101285ca441e031890030f11001401400450703000740da444414610302014402207990613001241a904030858a0002c1640183c03160341d42e0800340c0e405681e40c441e12074502c0f0f00c0000314a000b945401001400418541d10185030f6004940440d042d859404100007004100c51000c002010a030f02a400098042640d031030fa010079540e0141001c0040d0102030f0740a4070b001183c4a5031402143c010141403051090900c200450382050780d00200302e030b03411502c803824980600c07101d500400082e03980d121030519103209540014007540c00c6044d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 664890701 1250 664889451 664889453
    0xa0f0804211b1a0c0c1b060714100c0905060a1b020411030106030507021c0503040627060b0303041a0c01020c101a010201050411010c0602160c0f060c1e110d 69
    0x3d040e0018882a0001034484000300d9550070300e0004460401d5101ca00500341c4040220f144003085003200c0e4240c0d031000c0240541c5001c40c80700c218440819410780040c1c143d2003000c00000c821502c48080300c504103d0b00303d0048c495038036000d003114a801d6003410540d0a040340c4413860000d50840450094219081c4101405121050030203141640d1075510184140c0d56400005c0b86d85e50003e130004d031031140d620107400702c01074000d0000f550003900400340030498081030200204101a60a82490700030011034282085c0821032245854200e01100514501490a03003c200c03080102410416a4100000e804002d99030950466203450360f80c10a55240c040c54824042c01442c004450680c4400d0b940a0082c02d9032042c0304881c420f90f0f0000491090b00c1d86030300110340480490808503502a402c1000450f00e40315802071002c501e10800c80024a2800e02181c55100303182030344010244480030101100048255400b10100d0b202c1c0040d84801c403555040194111600310216034001d981e00c1c40400c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 664891951 1250 664890701 664890713
    0x60102190b071b0f1a0f19050415092004090b0a1104030b090312060409020d03030c032403020a080d08010303210f150b07030804200a08030a0f0804211b 67
    0x2c100c60100004000b9600d05c15046c8860034201c6555004042c90400c2c0d0000e021591b1025070400e01400e40103840d5511386403d88201d50301d4260995080308402280d0b800c442c0218a51007100b01709070340c140000f4001d561003011840e00580318043e4141c954103414181030808047e9001035030000c20100043c02d00c203450507100e038030a01020f00310480c400005105030409000f01c0e000c20354041d091b482100c1700c0e81c03421802000301e421480101600c80d43d0f12850510b2501d90000441903c0388000c442c03a00d0343c41040b01d61b44e0980d00595640d0802c0d054600e426070884070241c1180c0d01420001c11403116244a5141c4030311122700d8200103454141c50550350a81035204003402e0500140c10b002c05503c1d01d0006c8002d009034200140083c0d8006c00060020354a040200704407604400488500125132001610b407d4854020300340d19030010801419242c2c1c0030788140f0980c1c0c150304040a05041c16164201c0440d00040305c5d44011445c3c0b0b801103500342c070940180b0005120054899100982c0d81707066 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 664893201 1250 664891951 664891973
    0xc0206030f0a0b010c08070b180f1e0129060f0a030b0f011803020d0c0305150a050f04020a0b07030e0a0b0703110312130303020f0d05060102190b071b0f 67
    0x4203010760f1402070100c22550140010007810f9400c01c140900b06190b960301d05100f444010320716a480c000c00c41c41840300fa030f020042012008001c20140c907925040d0701314840c0010410950802c00c4e8102208256614071410364403100880d20500c0845420444000c28128880c030742d00444100300016038212a20b41c503511a08100c04200c860203541d20de1680119400c0101d05403402116501081c10001854040a1240214071901946500c640e69440396801e207104040581d02c44e100402c1000f024031254407826500100032110360340d4605144e004035500140d80e0040d4100e190300040c04d9010b1500880f107440d13100300000c003840c55564480c0c2d40c0c10344680200b54102e010800380c20b261440c40b4000300c19100c00700601ca80041c0303a6607c144600303c1c420780b20001a0b0500da42001124803003640c15005040803408414049114140f290009140c00181350000d00c019000407074400c000303040380d400b240c1c000c0700501c0d00e100d10400d100c0014a0220220380001e000011140d0b110082007907803029 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 664894451 1250 664893201 664893211
    0x1608070305070b180d2a1e03020115080f19080c0604150608070510200303070e0f03010506010e04050718030f0b0f0702030904020d140f010f0501140306040c0c0206030f 74
    0x90785c1c0c1074030004c42d00392010180000b9034026148440060351014002c9054050803502070140b0314913001d00c002c00491000e20401083e00140d460320750100c2d450310600050030003009040010074513501218145034449400c003c108600601c103600c52410700804100b43c40301688d0101c1a1011400c1034906011b480b4003055480400e2818001b00150f07480c800310716030f400c40d04042c0003006910942d0800300d942c07200d00c4500d604c0d5080902d804041d1242c2c100051441175010340c0704c407a18200c8980c01c001c3c842a90140440c480da051600700032150741c2c004036903000030000740c40115950b11500c0042e00c002400803042c45144580078800001d001c012010604018000c00c07034202d0507201c00d01c0456a4020441d01d20000d40e204100410741820903900901c02a40710302000681390103081d4001030b0003102540c00c00d0070f501070b01d0014005200080344007001400d003404d140e141c903107802545010500001344a54421940d901e210100d460007844108030321a40100403603900d145c00c00400d10702c1001070300c3c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 664895701 1250 664894451 664894453
    0x5070f021018020319110f0f2107060e01030605061c0b0f030114060906030f030403032d0509030610060c02130e030c0a1b05210705100c060506061608070305070b18 72
    0x11140701b06e030402c40741743c02c00e590001e07102c40e0328800880140b0441c02c0d80070411a55215140e40c2220400c04c081c040c0c1005080701daa94520854038000005060b103075541c002c80c0c480c1038204884800c11007501100614001502004070361001d46030b0004401c08214440c0c00c0c1c155007440040360115130100d140501c1820100c40c00c1c01980c554005050742c0d210250a10469940200703c1880441c0c00781c80d6455840291042000603403095004e034044006540c3c00b0003010660200d450a003515090040c0303903010005912814045291000041c2080c0039440003030300800c030012000e1f081c5056900030140041c00c1b50110ba0761040001002c580c0c1d1400c0a0b0240c5000d0350b44081d004580c080c424200c0100d9200030010103440c02c000383e200d4060760402011100034405e0b038500040382e889a044085642060341c446490480403404d0500a0740c8004042c10303c00d0f0350400c581c80e850002c3d0040704075840c0e00310030615150b440c68a03042d40d580c8261040605804610b01c10000208008144061820003082c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 664896951 1250 664895701 664895723
    0x1e03031103040804030b09240f0a05060f040c02032203020a09060503100b0118030309060e030a050d030c0203160c140118031101140c030306030105070f021018020319 73
    0x241200000e80001e440081080c0b100700010004504207004558018100380c096410001c0d0002c81502d07070110b20201c100814150208114610303e4100d010703070b80101c080304140b00501c2c1a02c0003a40140c0380c1c5141a1140d5070300c01e18185407900c00c0081c0c64085000c0c0540718414810005010401082484124411021100c0100d0f06031003c0c01400100d0b00082d00516184503404104006001d505250074100407a465420390b50031320042c0c0304d400542c001d031a071750b0f41d140c1080310060460f0513494280380241e1203150444002000001c1d9100180698500081c550360618400c0341148100c0c1e40e2210313041c1940140100b4451700d2001d4070211750301c1000f000c246840746001034841555a5103100f00d00c0b000740c0402c0000c10b145d0702c1e40c0b103e000d4051410300314058190201d00c4030b80d0080000100a90b1000c800c000082c1000d208094200040d814a9840c6101c8039034000e503900c440c000c092120319211030581420848206520b19516070040039640a015650079140300f0310070081040d50500101 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 664898201 1250 664896951 664896971
    0x1210203010f08071e030f0f050d21090221120415020c10080a2007030306030c0f08060c0c030f0a08060a06030b030309091e1e0703110a030e0a1e0303 66
    0x1007204d84110040e403605c2c4a200500d541c8031511a03254141090310074898003604200018000e200303150b002e0130243c81303a1021000a090200b0b060182d240303115013083c50b080013000565560040700782c1180e10b001c1b10300303003860780310200500780135400035880c40200380424041150704100c400b00b00320541d00d40c00c4854980101d020030034812070f40000d50010440c840045954a4596000801221414020503200022403030304040b06502803401640080c0d52001e05100b004240103881d0010325a00c14030384049810b20894503118000a04401d0341c201d000640c582000e0340c240161111005001c00c0d032515a40c50020140c00310f04c088581c10311900c3d000354080f52503802486a0380096401800035070030002d014044c040003140142c000b001c039030080c0b00140000040e00e504c00c0e10800040048460302c4c980c0051840e403207800a403020040c58241040315050740303c00004d640c1d100e0600d19002c24a444020003060600d041e00c3d101400c40c2c0e032504244207121620599000006110f03640401140d000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 664899451 1250 664898201 664898219
    0x6070f0c030c05011b0509151801050309070b071505060409030f0f020312010906030b0c07050d080c160804061107030803060f011103040f15030b010206040201210203010f0807 77
    0x501002404200d1009480000c070b4451034054094500c24000024040d82604565140c609411103c1c0001600010320b1050790030314001038400891030780100b0341091401290311907400304480e802030401c2004000a03050708001c01020004000c0301c1091031340c5204a003440100c04480d044001881410400440c1c00f50419200d4482c40c1034040e640c614100420318421107040e0500e000301c001314401400700d059424100c00c200c07402800303401c100190040c03651820110014008000514141c418046c0c4e101243c000300b26400c4030900c500c1c00e03102d55030b01d07091099100d01640d8180c1c9101c0c25041072100c10020307440c00510960313440340c0315511080550311145545407410300004160b118203102103a01401d08410703140964105042100c1402e5035803130260310390342042d48242c0303000c2101740c01001503030a070702c9184012010313500c0d0910000403100c002073740d9110040c00090404c00d10035407442988024103503102154030010020341d5203580da81d1805a982e00f02d80184150780c0101d1000080b5084c03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 664900701 1250 664899451 664899467
    0x50a06060804020d03120209040615020c0603100306110c0a03020604020103150f030809030717030a12140f18070e09060f092808070f0b0c0913020306040212070804050607 75
    0x50b004003420300340605941c0482d0180000506c3e0079441d6000d02010701a507540b4001c16014000013011501c0110704414024a410311003550329004110410500054005506412090740e411440100b00340e03000180c403201511a00046a00c0307800350300d03101c030f0405a0203c0d606000d10b000f41d0301030014000d00380e40324541e04068480e141d0043c0c90380c0c400704009469200a02410007000741540c45d05941c1c1d4000c0d0304074089014a4050982001405465140d0000000d540e00d90203041c0401c040e0070200582c0f0305c1a04054607aa034400071040010302d030036044054400004410700265544c490750707640640c500d054252034031891405180001025554841c8800f0b21581c00c0400802141d1207a49031620001c03c8410780503180d440c10513082000c2000d41005280d003070f1041c51140c0202d10142042024030b000035100758076005c4104001030003aa00c001303451100030166600103a880c1c6071800041c000348101101c80c2a060101300411241c140c004c04441c2c4200e00410076250645d0721480110740c1d402c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 664901951 1250 664900701 664900703
    0xe150d0b1008070203181207063c0302030415110a1d010923090f18010b010207091e090302030a021c140c030c010e07050a1a12040c03060f050a06060804 67
    0x1a00510001300391a030b076111b00c1c1d990782c440503240d05085054090034900302001c603084800815107021402c03841032001c0c3c07420714074a6560f503100401204603094014040488040050030960040082010f2040e1445400005124954104040140d200c00c5130841d81000d50501d000c45c07846180380e200240e00c06510444054160345094181d8105101c00940c0c1040800c004140741c41c2da00500310703d40399070707040901594a00d4601c402c1890002102d0509048201629142da4144900c60f131090740c002405c8010740794248000300714a8003600f900c0c0c0a403814039078000070082c14520144d082c10b8003c0010070f0443d10075800d40c0d100e59407d407054160242d80580b0180042d0b400514955080300e4600504464141e174425a85032070914440e55082d224007003560342c600d170480c3d0400c0000d03140c64030019005245041600c81030500040c1800f00740c0c09500d020b650700130803050024042180444070400603680c071110800c6100b0300100d40000038001114000d1800d40780403004070f105030103104098412 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 664903201 1250 664901951 664901953
    0xa0b1f09050604031502070510020d060e01081903270b22030c0308070303020c030a02010608101505041a0a080105151503071809061707061b030e150d0b10080702 71
    0x7061180c0c031711030095011b00010343c1c0c1e42c045c5814070300325051030340001d080d010071894010a80c1800c1c60b0340ca420600040e841407415900c0904040000c1c5286c034860211113816003418000340b803001c610700c03450708890210409074820403407003c54034001c0d400103081e0030440140c5103010f14025450f030f061132501d140005490b03d4061802000001c030b1b0a001019024802e03e0301604040d60010100d2640c1c012100000240c1d454041c1403004003c10070082905440080041c4030040c80b1250303800f441010b0f4014039014584403da4008108103079000e032602d807030002d000c02a04603a108000e038000e22084d54500c42441c0c0380102041245001a814002c00c0c1d0195150b900d035441e4004251480b020101c1d905451800034440003c21080368491403009100c01840d01d441c1c5110101c0050030211540c2000061101c813813118142e014201145420f45503150420a0111110b07000080340424545d40c0e0181c10800024001d01046a03030708035001400d001d8800c02c035440100c01c001d45070390300101c6080e401 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 664904451 1250 664903201 664903223
    0xf01060e1e031203040605060114031006030e0c120f1002090a050f01030608060901021e03151c050304180c2a060b0d03020a03080a09080406080a0b1f0905060403 71
    0x403190321103850a5081000b000c480c0800e07164480c0350b41540003160107440c05542c03072007005140e5801007226582000740d03d010614603e030640d92070154400c41d0054000300f541c1c0c0e0301d02850000c07041000c0201800d00500240b610804894001c3d0748111410703000709180500e202c0b1a903201c0b00c030b00039980340f070798002c051480160030300c000d101150254007009410992100800030742c00c0000d00107140501c00310030026030744e0b100c22011110b910740c20030543d0314020010420407410303007003a518000350ba0f02d00b2511404400c4504112511401090001900c203010000d0001000f810004035544c3e202c178209800e1100701903101058071070706450588060111310b0b00455002000454100e844454401c51000469044040114814a041507000c030701690148000005043e0080f0084d6406940300d04103204002c02c07507031aa00e0030302480c49240e05103d4040c021815440c0542c001d081c40c02005088001000340c190407007801c0d0600100c40d01d020501c41c1901040d2824a8400c4070b0650307030844507801e9 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 664905701 1250 664904451 664904479
    0x216030f150213030605011d01050a140102030c07060e1815091806040c0e010e040f0219081b0a0603060509061521150405191d03070b0f01060e 63
    0x486074100c0798a00c6680d8204406000c1e15800603c10000d180280380000b0a507041075804c064034201004040c24100081004100903034030b0805207005d45a085601c1880300b043c0c0070050786076001d1103144201d5401603071008280075520000c0182080022102980220280e904081152030252001e00702d41070324034000076040c208502281d81090702e942a900d1a000c80821041c03c000701681e0031164890b15280030849100301c0c10640e4050881c1d841d41402c1410a41e075480038019102900038000c001644d0300741c44c80c10175047c2410060200c0c005856001050a00c0740031541d00c504e250303d100310400380340490900e2003072298405650014204e48140d48482c401c004071441c1210151183c5030040050b00014079059152002078040d00407040500e040001d40014251a44550300f8010f40c0741c0010400074400000ca44111000d10040005034860f10320006610031040c1d40500c00c1030300c40000c81404201554000920503034182c80411038a0b625182308440c244440c54040e0ba10082041400e1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 664906951 1250 664905701 664905713
    0x912050909060d1e03120f0b0d032a0506090d1806081801020f040611120a1809110a08162c09040c03050d03060b0d0b0d02130c0216030f 60
    0x1241190198581c01c4000341d011000c20309180c8221803c400154401220000720185800355687c145a141000c0c8401041c21021a13201040e58102504010b0300200c400d40300e013541034035000d08032602110b03103456a0340d6040c295500c0d0f0041c1e5841d40705200c0c0480841d11507106101001d6000c421848811000303103800d074210f078140e402414458681001c4c14060144030380920080c1142d030395920090b5290303031034080080c0c140882000000c103aa042075001d0303e07980c01e041c400ca41208240781090380000d070b54036102e0118540aa000244040c0c40c02e0041000282800e02520448905545191041d55040500400340b48059090f20200b68cc0d030044410168803c0305801500b004070403901910005178000174141d420540b4140c0d400702e140301040c82401401d002c00180881d180c1802c2c80102c0c0b400883d0302081c0b207411a460003299a40807c201c980d5550105401c00c1c0d07070020000e0701c00711003074072091000300382c1140070f080035101d020000e1060105240004049941000906100c41c00326100c40b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 664908201 1250 664906951 664906969
    0x304120812151221030c070209010b0d1d031e0d1503170a0e0f06160813210312060b0a020d09050307261906091205090906 54
    0x1100d14000038065606006040100076205803250b2800040d40d01c91103041c00380c142c20b02c10307969039580c01460351800043c8000f10310082551001c004590740366201c0c8601205401817420081d80030074141d000144071002d0134050500b000422004002203160407010700b095600c1c0c2112200030350003c0c03002c48411010742545002e686402e0310504d160441d0030300441c003210384010b8011184c00c1860002d00034800180c1c01807100500c09440381d4a40749007a00c018200b0503100c4416132040d02d0360f50014101d030320380805840f500a80e45a041500500a1401e9580c903009040b842d500040c10004c000340601e40300284840ca00104034540381c081405460441c2c0d600030306c40d551080030340c81d900f000a103485800001d2001001e1903000d07000f0f100b182d43c4c1c020500c43c800c1c0d024912a500c000400c0c004150807600c0e08290416107013800501c0d001308401607060000741c021220001e81c200a8580901410390000349070fa074850f4040303040d509241c500c1503800d4001d1540c4175070002d0385007001a0042c1010000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 664909451 1250 664908201 664908203
    0x50915040204150f2c09090106080f0703050d0c030f0305090102040e010303120b01080118050a0605040204032303070b04020d031e050c0606060304030507081615020315090405030412 80
    0x301500d00703602e0340701408000c0c09190f080320000b88003803214400c1e1680103c800708229038081c40307003003180c1d1500201d032619030003040040c0c803072128000440c040300d200758041d034020035404054803881e81001c400c0316200c0e01d0510080e03443c0d0040c058800c1003984078508000589a00d91285420b11800000c118000c2c90010554070080d1350821010850003034400c00305000758840c9e5603100140728080845003c0d03a00d54407c290502030304034014460002c1110459104120040001507a507891503116000b0b0a125403205400c188001804011700201d2006005005d0003401400e041d4441d40301459520700c88e10201130310040748003000c1001460b10000d041d400c640245460050810445403400d90400c85680e884003242c000214184c000740e00b031110319440041160028194070f820344021300180704e6030318000c05d8407000041708035900e141d005103015203a4105400610354032030490075a00a42c0190f804590008440b941d00302c141ca000c2c41c81621443d8040301450406250494030303010554140c80c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 664910701 1250 664909451 664909459
    0xc0213110f0d0915050403031a0a14010320121005100302070218070905030d090e040807031b03030618051608130609050c090603030703020a12050904090b0f0709050915 74
    0x50348201140c20b10ba4070781c400e13500c0b03404c00050604041c036028003200c1004080b50088036070030207248220b64500000c442142c1d040ca800c8603071500c04e080101c0040002c0642585045020100c0c482d00d00d00700d0001d840001030014944000303403070b040c028400001e80352262903401840c41440350412072298015184940c400751030001000e08140d6000d101503000c80c0c58000284881908200e240780801c4480d03400035807800c0407000381d42026042c85c0b607034800400c09000381000007034240416100c1c1050b40807039940042545071950141ca0014040d11951123541c1d18812061040c10207034a16100d814028048a1082800c003240b10340c06942c1a003000304000300102d400d452003400b140301c1d8054203003003d200320050030709005201d04021200c3e5001c1e00003400f0b43c0c4148180030000b500060507403552600981d102080c10070800302242c4a1044000c0650040d00f0100352404001002c01c889028100ca64021840742e60741001c03c4803624454403955a00c1071200002c540c512080310303881c003640c0034050 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 664911951 1250 664910701 664910711
    0xa0b060d02150307181d0f0c0705030705030307030b01030b01120c1b0521040515071104020a0507051b0105180333011e170f07060c0213110f0d 63
    0x880c444030300b50000c841c102c005c221390007450f04100050391000009054650144000e982410490003005900100008100148500411b000b060480160b803000341d0b2000403603540794080e02d4000c1e00c0341c00c150f0b112070100781405000c1140c1c6d802800341840a40c810707034500141303a00300d03001003018105543e8030f00240040100c100c44032088900004c20300c03e001c2e40c0207191b030340207034400307000c8075a4951480f2040000030302044c006030b92040310500140c904006daa50700c44695041c2200c2c08006514120b500c2403000420b01a0a0f401801030200d00b405001600c4c8030f00305903200344021407494002d0b217001610401a698030104a0322510f08441c9029040b1070510000141c480d00e07058404c019003511411031410040c0306a49100302c0b030b024041050190034421601400684409000d024880003034003400320424103c4005c001d150450341d4518201c0d490981d17510303c043d01306c244e1000183d004203100c0181e8010b25070325026800182c20035002e00e525080d07600745214015013024506400d00c503101c03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 664913201 1250 664911951 664911979
    0x6050901031505040e031c11040326040608060306060f09061c08071407081c110114040602090301060608040c0915091109011e09030201050d0b03120a080601020a0b060d02 75
    0x2407041610079480390000b5944c9025454003141f2a0003560000024203041804100b105030f481015070301200c1e27015402c90b0504103494415810380d03080900240ca64003001c07800042c5030360f1205081d4050780c019001e072410740d103a14003440981c8039000c8a0540207285240070030240c1c1031445114201840c40ca0051034000d80582c1c1c2c491403684021030543e07500f4110046600c20403818411400180004802000a00307410040c24854030503107005035051049503141845c0214080d002401e640d01c40c9a00c90a1928240c80d0002c000e4000c411404d000f58604680407900c18003841807107010325007008103a104245024100d03c003a0249044031450b00d11103450000f401c140a00036061044801c0451685a13104140010b000b2003400307011100d41580505d0384c0c0e00c1650080d01d41e800b034940a1a00690381e50b14900c0d00e10181400d40b8415406105a68146880004102c0642000045070740c0300315041d242c0000480e51501e08141c064826160400450200e141c08101c4800381c5102400140d210180 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 664914451 1250 664913201 664913209
    0xc07080f010b0906100807050307031b020f0607170117030702030a030905041a060a030509011506020a06180510090219060c0c1a1b030c010c021b03010606050901031505 74
    0x48501240c041c1e465103401410340c81d08000c0654004010303100101c000942d88030091070400041e03d02d0083c0100017000c00d4159110780c028160400385412810304500c0c0700d080007980e8203142420250680108001304003954400d00100a0052410b0b402d03000c00e03401c0088210001d03110b120803542ca44402c000c0500181c60038012002d03070328025140d58030100d11740014030003a0341d107030310f0348a00000184200c00d0b65680c400081ea2075040d42c1d80340000f17043c0c0c1c5090b441801000303504003464081d60a2035001984650003c1d07003000c1d041c8a01801c0c010780319040041c160380070002d04c005105800400c1c200c2150440b42d0b010f00c03105030004280c80c00c8480f228804244000780c40d0402c9000640007200c010134021400b02280062035589800840d00c1c80196680403207000d208a000503584900018103003050080050382d40b41d01c0c0c0d0384001c0000407a00d107006951054400d0315070b5243d1060142ca41540d15041c071544085840781c0d1102403900321020b004600504020328646032800100d49c001c48d15440b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 664915701 1250 664914451 664914463
    0xc030a0b0a0509150f07031d010c020f060402150c120f03090d14091e03120a0810080303010302130e01060602030d152402070e0705030709120c0b0c0708 67
    0x1016000901403400c1045031407041d41d070300600500b52984038036260300341e114014180b00d5003e00e000105038610344940e1803c8005e003c4008007000121001c0000b4076040e4010f500000240700950205e465010004c01000e4807a801110081c1d03101c1802540740003214140c1c0000d200c035036041c009503004c002480d01c6030305e01c580200d2610042640003104020011100708102c9194000d1410007140340d103104029849541b0072003005a008031150300c0c1c02c10007103906620014542800500f50f40234011514440e8207160807941c000760000f44071102041082c102c541000003981e107131002440c9141c1c21074081c0032403022080c071032220061340c40300a40700c203080c20710800c0c0143c40c09a0113035546201200d403a106462260fa00d42c01d903400e04480400401d551416200c0010300308164102d1002c04d03a071402d9050140c00e502c86110702e9004810049a154000015072241066446080d911501e0700587c08404407411401004094408818821010040c01805000213030b582210728498440b02501d00300b038 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 664916951 1250 664915701 664915703
    0x40f23010204060c03030f200a09050d0501050a050708041218090c110d1b0b060102151e0a050f190209030a151406180a090c060509010216260c030a 65
    0x381404040c100b01a4980200d4000148011f8284102c0030107088605014010f142e0260708041d0001c0c10b025147e004512804c001c18004040b00500141801c1aa000e448212006e0200d20f14100024a599010380300e414061030b046600451b4a104804c0d00303a40071001858142c2a50080000000d2840100e0040e6041100c080c1d580c9030700040d030048202d2404903d4280e040a1203000c040454401030000e1100c0341550700074030050300c0740d20707031500603420945110007215001c20701d0810480080c03122007140b100c15040140d80c400c01c0d5901c040a00441e0020b4803942404c100b40000300c1d400311425800c8052540e880c0600500c3c00c00c0d110006450f020416404851482d80103c6a090b990303414400c1c0307820613100c0b07031035545245050310000741e05000381b00d449810b07060980c0105200c6c1401e0f9003d0b01d4020761000b01480070315142c400240c0aa000004c440d40103204459000710b080300343d1100e0404941c66034103108485200f00c5501100312803401c2d8501000d00c649050841169020041c0300c1d140303 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 664918201 1250 664916951 664916957
    0x30f2c060c190516060213080c150d0b01110303072003090d030f11030f04080c01020f0c0f12030313020a061106060f030f060408031905040f2301020406 67
    0x21601010a42021001400000072a400340422070b8a58181c2c1c0900e8900c1c1c1203441c081e0ba07a1040050780880341c0d80340200c0075051620100d2285001303290460040c0a903400c41d0222915103003075a040140c109c1e4410b81e00c2000c902c090044401d148550f030041c2c107900f001414641003082c00498003a1854204660a01c009085641e41d0071203110300110506080301c503e0701030352802c40b04002050109401140c02070822074203800042503e8482e07a5a8043c0e1843e0800b500c0d5180703621090550384e50414040c2c040d45004910002d2000c0d800000c1c20100e101007840904010018030b01004441455000b943d03401c81d0300751030010148036044c802148034003c407000c403aa5006d07181c014441010540e40100052002c3c0b90a00308146400040c011f5000800301d178450001000d0501080c2071485a1510b12450b2017680284802c00c01614040c0d07100380408640b407004000ba0303801c90402e5440030781c0e0183c605680c5181000214140e02e1080d03071031700304a07002030b0324004101705a0340c01c9900c035603c80800 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 664919451 1250 664918201 664918271
    0x90e0109060504150e12030c25120f0e0a0308030a0e010e0a0c05120c0d0f14060601030b06120c031003020a03051c11061303181d090f0a03030f 63
    0x460002c81c8070f9407511740b207008000e00d0004c400d8542040b0b07510010380301401406d130228803034801142601070401e0f0b00311080c00b00b003094a401e103003602040280401400100f10b0300081d8054180c42140c80c0e03000c5040041ca106e070911b01d1030b00d44101540c005032a45005035142e6101c00420b103800d02900341010301c510000d120ba43d450f4101711b5000c03501608090321071000501401140c200000304512540c20480b8a02e80d00380c01450304054159010f14004d050040c0d0005075822040003181403031003520207880c244130b10b0600e02d0801c80c66210784c0401c001c09a0481010442d5440c6c00400303503500030580070000b0140394903600082e01400440d44102c4165011440c8042050101141d48014200900b8000702401540c14140d4803500000c1103120b440d101410700b10180b520510041000b00000703043c01c44a030b51100101c10354040c0066001602c038030300b00041090808005804101d8401d6540500400b40503030b5401ca000e0407110520300405501c6804840f031111039a0301072800261780c51a0a01 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 664920701 1250 664919451 664919483
    0x191115090a15080414071203180801060f1a0c1501140a0e06060705011407030b010201110a020706200d081906050f0105070303140108010e06010b090a090e0109060504 73
    0x10041d085a04040c10040507440c0000c0c809800c00e08440c0c0040e484074000100c004e0403407042c0e1600d40303a54040029010032040c0c51090541003030000d51007600c20044821881e4442c0866402e032210340c4100d03030131429100d1040100c011101091421290750700c082a180003040d070a060320f06050420f0808807200c01500400c042041140c040305128000d82e45040c810b840c05080a40ba802d004005501800c0c002641e00108042944500344112420402032043d081580001740140f9051280c01e02641c6000054000b04541c40207903002c0d90050ba0081042c1418a40111000492640f00304050050b455200340c02000070b01c505080d03c0e030b055590327511526110105402c03e00c0a00c03184020203140030801d12030b5480c1c008040c501d51000b820480d580f49402d1170b08030014182403017142d2306021801c0c008180001c064015640030085d24044400590302c40000c203000e4400c0d02026540090305150400c0a201c0c941c02042203048040000190100355480e01e13000d44404071000c5a040a407050968 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 664921951 1250 664920701 664920709
    0x318070b0c160e0c0a0e0d0609120f050705030405010e0d12051e030f011e0806010e0412050a0801060309060b041d01060b0903251502210c19111509 65
    0x31000f40241d031011201420501c801c0c04581c0703d8200179070100203281c006080b507a00c80e00c010300c0c0c8103540039604221303068a81c00d0000f43c4a842110503400070310b1750007030f80c0c040070f2040081d11100c0c1c1d00840036600c0c10f4644001902d0010725007140a42241e10b0074681c10129141d103161890040d003944901d9a0b030481e003c030001c08000320031030400080c8018424401d181d643e850030681901c508041c02c0d42d2a0380048604900360085601480391403041c00004101350035030030a502d008601c54540321052810034401500c0c070340145000c40300007428034801001421b2184c4c1041aa072b40c025480042d12b0014100401c0a484014021001e801c440030030a03800d10a0920032080104502014242800c500b100025140c0d011080e074441d180216090a100e58001e0100c0c070b100402100003965000c80018401075100c0c0c100c0081141254401d2000381c500449200407990032041c513401510343c2c54172000c043c24440d1000041529040d502080c2500e545c0c03503491701d402c1d00c010790003031591f20b07812004104 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 664923201 1250 664921951 664921993
    0x207150c050c01030504060f02040b0405100305011d0402010c150b1005130302190503061f0509010e010b1b03030112050705100804170721230318070b0c 67
    0x260040200c408064400301d4004161449903100910300881c0686450070403001600d91561103803100d030302c00100042c8054011004004549054035054a03d400b015003c0e4200c4100340300e07140220300c0702c09400c44100c5810350215806481410588110190b81c0c64608035045180340c01c03010b1550301c0c6038100403450038000244035003480d440d0007441d11401c840207020181032132000a000b0043c1c0f002da0030340800400710f42c030301401380502126120f00e000142145a18030f0407600050300320046001050504041103802d040e44d40480d07241601e6480c01c01001540c0c1d100c64a1f01d07100e0001c2d4071150015140500c000c1d8024004544400a1410345d400c01a0800520390302247c030a942840320030080c01e0300007516a43c49904904c0d002507031030301d000d4100414440c40400618100400d440141a40d0f14400c01c0ba510150b01d035101d50202e408195040300d504281820680d4101041c00040c0641042c103200c0b840c40c0354100162101d06507244181900c6421008401110780c012010414140e80320000d6 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 664924451 1250 664923201 664923239
    0x10f05030a123b0a15030216060203090a0b0903090604032d0b010503070801200922020403150b1518060408010c181a090a0e090c0f0d08090409030e0a060207 69
    0x280b50343c8615045e010700c1c240d54404822000e158011850582e282c03041810f001116410030415540e034582001e820391540102481198499802c80208800210000a403964002e0103000145018210303101c1112290080c0100074260240152400301c4040c1103440750700740c0e4480c4503490b80070350501d000c142c01c01119420444041e072418910402010400c07905e0312120041080d250780c0d45540c040402c244d00130051800a20020360030400c8004d402c280d004100301c0c0c0c0200e1403c1580c4480040d41c01c1910024070716030742e01c1070a1145401c0320b0304200005040c4102c140012914070200700c3e0101e2255001580028542d95541001400b605c0c1c0007800010b6210381c13a52102005414001d8407a221071041c000c900015001140c840380644515114901402e44030024081e03914101030043e0740c990104480d68010102602015624184402c10307240b01c0780e0040e01d46040604003801e110007440381c22010703030400040d0424104140c407800003181c083d10544d03014141071401c2c400106800012004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 664925701 1250 664924451 664924459
    0x201080a0b0108010314030c060f0109062106050c040510051804050906072609100b06162d03120b09060a0314070b0d02090306010f05030a123b 63
    0x8019012607030f010b0003003819241c1c001e1151617548545101c0915500510b00500300030320a80007030201b12011030300003a04840402034240620380e01e80b1281c0c3c08600c408049c0c1079401901c81140000140150082035001c0c0e410003d403414550360342c0004130b038088155210310200d5400503969607940256441d8115680d002e54003030180d81000d0700e01030b90b00e02000704000104010544030150118003000951040b0b640955040b0345070500078a440e0712003c05051500b201e9141101446980c1444000c1d1809461240f000040042d940e440d040040102d40320800ca101e244c02c40c255202410403498080114042d030346281c81200401b07100d0084811004044d0f04c1203e00504010081e56800300c20415654002c03015506081b19001d40d03860f040840c2c2103010b0004012408900d4004250b0243c0316400d812130480d126030b660750a0b800b484070b145005442d00360308081190004550965003000e00d1170703d68038200041034080c50b2030318000099141d1140111b54100c00d0200011244030f401100040115 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 664926951 1250 664925701 664925711
    0xc0a060f0903110d1b050f0a0c0504140705030a15030c2912041103150906190902060d0b01050d020c01021803010e251208030a05010f0602030a030f020f0c0a0201080a 73
    0x10001604d0040307124050a0401d40b005181700070040280805004110800c00304c843d90030042c0f0300361140c1a40b90103464091490400d1f100170050100d00040d025244c251941c519545524015201400070015881503070408058004001100000b58200030000e24111000d0907005240300703000b0309400d82c11204e00d22810b001801c540a0000c0e050b5410503844401c0300091440300011906011940215581e50001030040104280011075254801c2c4c281c01200d103031f4102c181440c04100e5900b04800b0b03400c40b100303125540101c0181d6000d4040802c050410303900740301044500105a03800340036468003903500865a950620034004003401d1044040340244400b803030b80d40b102561821015181d8a91030614200c041c0c83c151040c8450300035007140d48030a04690b0b45418101840d60080c0c3d222010540341c1000000c1200107110b0079025038507194041d51030890b00c1c074801c4000d840030340068840c6550820240750103625900003420355642c0103001c1c005840060001404802d070080000409900b01 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 664928057 1106 664926951 664926973
    0x5040201030513030e04050c0c06040804090612150902041d061501020304030b073009020114040f0b07050118030c0c090903050901050c0a060f090311 66
    0x3038805202c01d40302c41e0041e040c0c1d11141200600020000614041c035464036800040d0070009100ea40b50812040005640c01e10109660440f4583c8000030204100f4070b09001d03a2005040b1f0300e0326940c00c04602e0b00d2f203034014071510350102d000d26a81e284080c11590307281e1280c8080e00c51801e48420100480704119503400d0195007411003080d0071029032405620000032076050300d905c46250101515070340003d4503d809002d0035401c006185400004018020f032855440342415418082003070042400090b004540030f0203540c07054101080188801007a40c105070341100c0c1600702c00740d507803600d0703041541c01031010740003070042e07841418490024141e102041524690007000c10f0407660360f50355030389821a40000b40c000c0c0440e5003071040f058258081d101a01803150700034142d030b5807401150f40718030440d401020302d4a003050741c0b07210140525501c00030405007001c0d02c000421030b80d103071 = true := by decide +kernel

theorem cover : BRFrame.Cov 664748201 664928057 := by
  have h0 := BRFrame.cov_init 664748201
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664748201 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 664748201 ≤ n) (h2 : n < 664928057) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
