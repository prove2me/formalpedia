-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4255
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:01:23.28285+00:00
-- url     : https://prove2.me/submissions/0edc28ad-d654-41f2-a3ce-16cb722e63ce

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 765107913 ≤ n < 765287769 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 765109163 1250 765107913 765107923
    0xa0821011701140402130e071224050c1602132f04030807030305190609090201080c09030c0105030603160b0702030f0604080412060b0603070c0c1409011232 69
    0xa002e040f20285020300c4016240c102c40c4100d14110240d00281c9040d4031810340f8103091807648034003214683ca144c1201840b0f141500b110b01c5101044603014010b5450041600f500c0c4111049560080d0921601207004100c00b1a07011003480104001d01e4581800410001c581d4521039401062528040701e142d120940d0710b503504403210300551075082526617621258140301d503001c018200f40e1901d0209009040720600c0a40b00f03e0102c80621500352201c100d4070080ca4a03420582c0018400400304040d4029013003164035400c0041c1c017414903c01d2410040d940e0303900c00303031403a5090700c2005420045501041d52040c0600f07841100b681d80c540243c01050700d030000c01122583c0c4e40d005101404002040041210111442d8030a4001c0c014003901744035000b030a0084005400410010820000c650320140010b0490301c03814600c1c02071500c524040a4035401c0c41d1005400c410610010b0109020010015641510500886001c8000714403034800d145001d204400083c0d0300101c4082c4036101c1488 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 765110413 1250 765109163 765109181
    0x1c1508060106092603371e0c03021002071a010e09102a0806130e0304090f06032108010801020a090b0714030a050403021e01020a0821011701 62
    0x242c84400300b030400c0d07002818074481ca0800303a188a01e5440d0030000c4c40040c0142c035003c115121520418442c403020520b440180e0f01c0c8a9015507640c83c82100c5a280a4088021404a403191105454881440946880034044800e60130b601c00c1001c03142c04a8240e000500c1c4503070ac00c80e03400750006034010b01d9080200061f0080c052072000c2c1e00401040e880f000480d52040d400215000c2114400300c0c904041c40c407101850150b04e0240420005101a0407480e40381c01142d00356a074811450f140d640e44400c0303811002031503229030010403042148090503000a4165001440c0010780c0982d05d07510314011200e0314014007446840e12080350b00050b0480b810303500416142000350310302100841e00401d01500c40c06482800400490180c05100602c41c4289081c458142200d980ea6156200a8020380040c070007203100754044020f00d0601e00850914882d60581a0020f00d400495943c422071641c000c0c0c280c00a040c00842400d1814210307280450b07008040ca08681c2c0c82e071054000c2424292643d9030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 765111663 1250 765110413 765110417
    0xb0f0a08071d070c0b10030209010311091311240307020606031501120f150c0305180102191407120e2d210601090f0b180103081c1508060106 62
    0xc001c40560400713001400c0c5540550102c0c490307514908581040d00850700042d4001d41408008010041206c0b0b545003006411035216680f42d0340e04001004030a000d0030f009001400002108901c0e086c24210249a8624885480c44106020030701c01c44c2508110b60200040e80100709001c0036080a20651400e810042116691981000040080804001340081c00011000040c20600c40c0d000007004414a82d642c05200b04094410010060002034032043c114194003a03800b03041002c1403080780c0c1440c10710103c450039031400d41c000b510940b030088850341c4040c038104090800110742c82c070424134010340c40e01c48114291100c01408589903841c503d01680e007615501e00746c900c607090a03885c0c5078088101c801c0380c0c040f04044000c5044500c00403100403e84a49000844c04070516000560703070042c464030802c0414500420009a108141d600211100400c001070020800a00084c8813000100c69254440e004d0950402d04559840341501004c50003020300340070351281804064014020344c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 765112913 1250 765111663 765111719
    0x60d051005120d0c0317040f140d08060f01020c0d0602030403030f0c051603050d0c200102040b030a020c032a0d050c0d050d27030f0216090b0f0a0807 66
    0xc0410ba60740c560300304801c0e40600102030302c0b8400301031103105940084c40c61482218a581482e203090203402080300d80803111aa814104414030a20026519004541c140e8409409480309803d110618181c10b404a046024592403400359850300e5507018a4a4030501c0016a2840c06050040407a2284880b40c1082420b102402d5015940101a6609144a0b0700060148605440c0070b40c1c0e684961001d2a001794201400a10391a8121581c09400c00c0d4a00120014100c0d00c20f54601300d118034090311180003402d101244d072842007980901503522403501128549030001003100ca01d01442040d1401c0038204040d00041d58001b88000c0d0310440c1c040c14440e04100314180c810307485907681c03020003082003008614450101019084001c0612843d5207019248080c0c864000070400000c1081d400305110142d1056424800500791840103100d15100c481542400300b00f0014210524195510908041810000f6910420401e0003410008000e02c142c1d8988030031300341e12013070188021154203d4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 765114163 1250 765112913 765112939
    0x50718021201050112060e0a09030323070f03020f0f0d0e0f03030613020f0c03090a170607030c030e060a0e01111204080f040b030c040e16021e0705060d051005 70
    0x28078140e50303054640900341465800b80e04074001005160951003035207100e5840301480020001944004200ea00030355080c010725040c100300031070385c00c8000102e150115181c000104518030403030035048403022a05d005450f180a0740c440201541041e510b0000c0030a00082ca07040c00e021502c03c14800c0c80050002c0c0188188070400c8075240d0000400c081d01640280c244030072103624540c1107645107681d28403d25101c9010005588e03998202448282c00750b90411404201e83c841c0f000c181c001143c1840040100769182d1400700c01400018198101381921204200b4140c48248032151043c000c0600c0017070030901700407249003515003031182c034000c80c0c00401808224800351060b40b544590041811695030260002500007072055a001040c1c40c2e8000c4148110105038070003d0089072580500428961503030011004200110303180000560300503a110074040c031181d4610202052028150b9130b4440d43d0380041000340c2e1000140420050b030f80d40800910011030b140e44405094190703505500e041c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 765115413 1250 765114163 765114187
    0x71401082a0408070905041b0810020a0306030f0506072a021e03060f04050c01030b030309042007060f0c0201090512031f0e1b0a05161a0405071802 65
    0x490012000c028088101c840c000000031603007228000c0507071504803080e90f6a9008480004c10b41940c1c202c2d10103c4030f541c1c05410707207043d260a0040e55004400750002003684001e040c029880116030000f490307110080040804d00540005001d540564041c001a00d8481e0001b01131800c0c012003162940b4003000d80c46003464504c41000000c07903041d600c102000d118a03098500c0c80701e110188503818841c000400502444400440d070203607119004841d0540701c450019415200c0044c1007a4040c0d000b4000c40c81c1e24a06134001c41d16400070801c0d1900740c0c08040c19103c0065200032402c0d61f819407250004650943e00e48120001081d00d0b20003000000803d6031100c6c2c81d1498095501001c0001002059003410500300745003403180c1c40310101a2242d582d860040264100300c4d40005241913851325054040c52400848403020400d5940500d415140c0c9212158522001c0081c3ca041003203240d600102c82c0050925405a80107100a01005d85000305010120303500003403c1e0300560051260f204024 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 765116663 1250 765115413 765115441
    0xb0a05010602070b071a0118150509060d0609051e060f010303050f030405100603030c02010e0307030b221707140a050303070e06090d06060612020c0d030c050f0a0207140108 76
    0x20713444140d420f41e1290542032151240d83d443d21500d1855071102c00000c0e5201e40041c03821407081c20070320140000010110082600d00d400d05c82d098100407003000181003450404060b01c04a03114120015040d501f0b500c17924034081c841250368450343d4141c1254a4545410440181d00500ca403400c4030340c0358110f94000341203000c3d001000c0d542d40c40100119003046001e001c0802d030707002c6030101085069680d040c01805402c041e541680840c0412484d2034281c00e0104205040d65040f84110b507141d20340d1112511080e801125640b500b030824500c0700c000070040400041045600311002da12840c40f82481c452210006200806039400201003c0000f50301005a036802401c1d800c0c4200750420300c5006c90428410a4045da42c40f02c0718032460350400c081a80310000b610940d030b40d01c2001e6152186218124400c008c02900c160f07012417065051644240c2203080700c110213190450801d154440f01c9c1010740c015044030009600319003810b001015800708200c10b090002d01e40b0b00018104042101020 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 765117913 1250 765116663 765116669
    0x301050109301e0b01031403030f04080d0605040f050a0606090e0403030f09120c030e0301062402150c1804020909070f14210601050702060d09030c06090602070b0a0501060207 77
    0x105182816814004030711480c900624072205814201c0b40c4070302d080d0a2200c4240011120880700d0050820241000400c9d01d01c10b80405032918100c4d11a40c841c41283c0c0c2041230311405884e1500b00c0420141c542e80111035441403201008103142c10b045901e0f100b40c50070f51b0002010440142c10400082c8040080e098101d605420001122600c0c060100041c11440c5406800203d22004030184242c0c44684040840d010f40d0790b903048a4400e004040c2640c0c50340c0301300c603801119800d411000203480303595905584071600443c2c000025802868001c948102d03400000b2a402041d105a8120100c08414044808990862405011200049800d03034003074058010031900c942250300d942d004021110408840c820115121401809150044201c101d04001040c48680c00319501c1d50047c8103480e040d03070780285401e06214071000c0c158000c0241200a41c00c000b0100524004584070b4070075003035024000d8401507a1748007a41000154001701910580440340740c080100001640403c40c5070907 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 765119163 1250 765117913 765117989
    0x6040f0908120a0f0516350a0f0507050409060f030201051801020a0b15120c030a150b040c030905010b0a050303030c090f03030406030e0d0918090f0b0c0301050109 72
    0x10944841c803c0e2402400552000000c0c140380400b408070f00c1a0381700a5020044495440c94130340004000302c244640924450390280800c4249040b100703800c0020070301d5200551100c0042e040f5501d1324000182e4806444880200340005414001040d1a0140402505081c1c0440d00385034070f5540020403e01c50b01183c0d116040c2001c1031150140e00c00e2020f450b105400c25140c2c081030a00f40e07404507807100142030780783c410f003000b203010a100b010104481482820040140c5041302568440b02010405c02940c240b0310780d904d200d20050781e99144100c907c415259640040c1415091038100d0031074025484c5207114194405003004950380000440781d01002c1c0941c40740d101d89041022650b8000c4120344a9814000403078040341c259896030046c000c40c0d540b8401c80c0c46004d22200c1c01c1e2a5000c07180100c0c1138500c85412405d83c0b8003a50340103c0c400d2485480749600b01146500d40c1c86002006850240000100200400a40d0383c00460302026165480c0009840008000710a8681000030a2101 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 765120413 1250 765119163 765119197
    0x20a09050d0515071d01021f02130b0d05070908030733090609050111031e04111e0108011e030605150a030c050301050c090d030804170d0506040f0908 66
    0x10880b0038071000100b41e90410f01a4268206118007402d00e445d00c45400014200003e01d811a9610020750300380c8000c114804000c24403598001107011b94000c0c85c601c4a0b440c2100c000090700c10a540042c46805400b00c000078841c2406003004002d414642e001d107079558414481d01c00403d40c00b030503800c100b81c0d115040c02d10380c8000031031300710068421001d4071006614242e1003005000c055002500300d548580f0081040c110145425504d074002a100005254101c900706500d200c1031502064105004512001341c0e000300700002480040080d00034400c00303083d47d041d00c0c4c09582200141c1c0c05002c011040c410841000016451a0000351002800ba191500c0115441602e0b45001414001e0081c2155071881d4481c1081c0c144501d80b03100c0c41c0e000b580b030306c0c000603c510741e411305440c2c409200610303082452240c0c2c0c0301120340000140055405840c0050a02c8042a0b8170b03000300f002404c0c0b120003260600d81801044101d40301030101c0310740c860a20980c0800513440380102c2d91400e00c0022104 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 765121663 1250 765120413 765120439
    0x130c0909021f021204060207050a0b07030c0602070302010b04020f0714061306150306021b070902030c03040303091406130b0a0905030406230d1e1b1b0203150907060201020a0905 78
    0x4d18016000981c070181c031038006000714100d075010421805440c816100c285109075200342c0d80071540f2407050302900003000702070a400041c0c0039800604230785020f44008508810701c02c0010b400ca81c0200440007035984009040000c2040481c8110040c5000901030321543c5001d64104070840d00c0103000501d416581d5080c2045402d0131130b14038000d1608a001103440b0380340307401030100f100522050540d0601c0380e140005840e88150003141d100f980445d441c1401c0d070316940ea0039070150480040486140000a1070200100f80400c0b1085c8504064890028007c8080c24042d80708071014210a01c0107003840300d002d02207040001114200c4006250542d040d8400641040c2e03060409802920202c000088401d800b0311309070810110a5070800d0070281c540c820280b03000884041c80f00d00680891f4180441105074041d0700c5c0c0824180010400340c42d90901c580c00a404c14100c032211002c07025440040c00915401004601c024000b00c1c0009c5207451a01c04018252074a18401e05100d2170740c00c0010707 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 765122913 1250 765121663 765121667
    0x9070302070620030c3001031b030f080309150a06051017070e060c070e3106021606050405030417150606070c03081801030b04020a0e06030c040e130c0909021f 70
    0xd45010310a15140c2e6000f030300000041c1b100d80700c288420f8810052950707042d07070b49a10050f9201e0071a540462102c0100f4210395402031150001441503080b1f0145202d0640ca41340d803120418414200380000251079820141007003401d440c039030324410070024001c50b413030392043c0030240c410f03080803807803c002200c2155840000c696101d9034100c00c0e070a0003569400940c295031031421364041c40342020210129621b481e2528040d03a403160700568072490003281c0300003040c1c10341d00402402815580d1340c40c51503120713114a0140c50f015202111554000141004802440c0c2c50200e001c00295011f000d008001c510310000031100a803410744602d1000581004000e01031850400444c1e20464054550124501040120351040c0b0554003281c03c101c0b166001d86000d10840c1c44410041c2c880f805001c42c0201440402d420080c01074950f03840400c000305055520440350340c452a244c0940740c4a80c1d1043c90038002c020f203a0f6009220707035401c1aa101005903510403402c18002084c042c0d05a440854040c1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 765124163 1250 765122913 765122947
    0xc0418020c010e0a0c0302031e060403081005100903020306010f05030312070e0d0f0c0b0c121b0303190e060402060313060902101205160c02060708040509070302070620030c 76
    0x3407940304d00c61070154404000c0944481c40499008800351000703200341d440f00340204000140c1000d0b660f0004000200028010084181c105141b0590510500c0d2948081003195102c00c0c50000440c20071001001185400c00009014001c07591004094a281601003035403801a44c1c01035500c5400480062695407081500380d45000c002400d9000907803260605901c4c035150382c00142c0b00d0303142c9a00003280c3c41070060101c480340503141c8000c000c102104426003200ea0841c528840800000241610710280204050342c003a4014000b150124540f09000d01d0441720031500340701498014508100160b0345201c140e03580461084070341040680b5500c2c000f0002e0110b080008c1d440b04203403202003105135201044080d40c4001643c20065501c4111025280940d4080a02d0024881411103401400c248000e0010b461241c0c40341030800341ca610024240301401c6030324100282d80400d808061013003a004590180d1040359220007015540d40b6941054400280000c480d000006840301003107495081c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 765125413 1250 765124163 765124181
    0x1f0b07110603101d09101509060608010806011203080406020a030216200d02240c01110a0906110a020108181002030a1d031c060e07020d080c0418020c01 67
    0x440650740380ba00214440d07103400721340078084005151040308000001141c000d00e0103a1044401003418940e1501c44202826039215260350b66401c0360b40000300007549000342c0c0094089910b8840140d0f04200006140090507403000803491000c02100d07012907080800c20307810a070020b03805603440600c5c840076000383c03017210a03c0a0151101e080e02061106030102960b0017806444141002e80e05034003004402c01c0c400d071001c0d6000c00791150f000c41400441140e076000b500112403040c10044a055034508448002d0b41a03424180c0000b000380e40c981d4000032a102500060810b1495007108040f46c0355107401c4a10028148030140c400315224040c684500134000054a0072180388110350f109040194200380c50307411000b0705002c418900ea00201c003c808000304503e00541c02c01070a5076180a9070301c006040707100b00c540c0d145400300384110792400003403056100382c00510f040b880414006000000c004c00060780c0745000e01040c400014014403400040319080c0e005611003041c258114014228a1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 765126663 1250 765125413 765125419
    0x30d0902120607230913050103031404080618120304050106030c15210e0102040b040518011d1504090308040b0a050105010e15130611010509010b0d080c011d01020d051f0b0711 77
    0x801b038482c01c2c20700b94100e06d050f80d1007540c80125921804500e640b1901680c040d403403c54001d180000d4a00c0e001c1c0410050703221007030048546811982010140030384c0161000d84a43e5107500c010b006000031940d250b0024805104000912503542400800c02041ca0074603003c1459036a15114240300d0301e800c14000d030350070300008541d5141c0d184400741e8144e0044c42914001c20034503503070148074680301c00981d040302c01203d460145052100f1840c41003c1c0001c04a0100750a00290308184d9162032040e00a503901ca42c80743d942c7d90030241440c40509400602c800e4100b41070100601a50b41d0213454007031507000c29a14280e07010a8030038280c1942c054201100c1ca445071103000000c3e0b05900916040d80800741c0002080035898202141c1d00380d95800714400c1d04882c4207168200001c9681d0010401032445500005410380d9101e01c03941500815195180660f40205480700f18400c503211fa81e4000b45020341c0141131521014001d1501d14051003801c8800402091100a201c406e40840741111001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 765127913 1250 765126663 765126679
    0x601210c0917010c09120602070503191b030207120507181e2003090f010501060f09050904020337050307140607140c070305030d09021206072309 64
    0x5400010141c06a61182c050381d02088000591030704010310440402400a507104c410007410086a0030f24443d1440341100d40681c01c20a03031f0701041090001c2d28960020191004032144506c80050403020308401240d0203000304c0407500e00013a00001c000c011554803058184100754a820080d05102d80d5911007449010203200906401140c3c0d0710200200b1107184240074407002602c1d9000407289038545034070900d88a03418030a00041401c024640c01040001260302400d94101c6180c291542070b4080c00225180d0300404079496081b110b060041c120540d05010645015000281c0c3d50078030107041001900b840d0b00f144811580180b05051b001e40d0185848401c0145151203640c03680402d80607a401800d030702e80301e40c402101207205805040195a448061640c038204c035400742e40902c0c41142c4500c02c611b40040002d4003030018140a000c048000110403506005100c840010045121a40e4218000700810990050389824500a84401d1000d10b0511080700080381e1140402075540003900c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 765129163 1250 765127913 765127931
    0x20c03010e250609122910140108010b0a030204030b010f0501030609050108030306130f111209010204150e03010b120a0317060d0201030b0301021210030b06030c09060121 75
    0x144034500400503800d0380840c400c040c1d00c4001042c145003e04800a140c24104124019000c4060640f0038044d402c10030021420480e01c50842c0340e5007a00518805205c8104482c804902030b032080148011524160b02c00c003c03400003003254605011381c150355030700401c17203013000340c40780d07050b20060340c0d0184410340fa44d46c5038200c0c00c842c2181403280c140040d04080c1c000c1660782c000e0160368101c0300c0304c80c0110708541300c0c030007040f83c0c00032415414204a5519208551503c465000d1244030142401c0310755692404094500c40500b8018001e80190303004001c200080002031040c1c0030320f66440e180007100800c0800000e8050305401d8071340d9500510703505c02140c20105c0030882e02c05a51007a15803510b04080d980600720000011284103a0003020000341401550080d040321454032001000140303802d0300c074200203038107400581b010b502080600106104010784003002c03a411000450082c0124014040002c0d0844c10082182c0d04101c2400c02104016402c124116081c02010344203020b1403403 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 765130413 1250 765129163 765129191
    0xc0915070609060c050301080d18060509120d0903060b0a0b040303083c18060712020d0504080a0f0309020a0330270302030706031113060519030b100807020c0301 71
    0x780208e90032070054a4007484024012007282020f51a00240b120817545802070540b0f80b43c1121800729080030416269080d040d200f4022983c1c200c0e1240c54414569043d420702008446c03503a0001030203610707a201d0030310080c01d0031401d403001c5a0b032529010700c4a81d1030020804981c4441c4064082c0800c0b520170341481110f41c406540d01c2c120292200442c82c1d030f151141003000052105914002d6005580418407c51084500310140f0510280c003500d846480a0800d0407110111800c1e20040c40110310003c28a60003140340d502c803040c514013882241240e40000d411000940702c01400000034403184600300c10001c500c40480040d914005146403000c1d00083c1821800c0919402041810800080d60b407400c6440130003601d40240c020405a8100901030f00103020035000700f105410180180403140c03003601c074114081c0c0b10966415440d500a10401c01554800754401000d040c01c1180c800c00030b842e01070036100c00070907524140c00c1c00d8850701c6059040289000c0340c0d94141d428407403900d240f10 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 765131663 1250 765130413 765130417
    0x601030507330f11060415020a0302040f12171e0a0314180606120c06070f080d020703093006200909010608090d211a01080c0915070609060c05 63
    0x2c402d44400c148400c0b8440020b1700d402049500401000300ca1030038440101d10307503014100c2c1d2041420700500c1c081d141d0001c500010101d41c00180710690b00300c1003008000407401010708001c10341001300e003400c946071260503424114180209440c400420490402803082d04540745440301d0258103550f605010140804089443c2404002032244501140441c00c0c04504440f200388414083d142e0501e010b01000126071150b03000b541d8070f4401903c0030007c940e0000c010440d44050582c0107981d06003d15000d054202e01780c0c080c11001001400040070210b5a444410070b00305110000000055039180900091000c5c4c05945e051040d000040001050804003d0180040c100c441c5030260703a81d44070803201801c1c2220410110b40100d4800c19249000d0f0641c24100c642c00c040c00110480301403800703011200c414084030103103039161000329007551b00500c000f0340024500b003440c1e180498a50106410b40d05102200c40031100c000741800a00c10103a200d511400e900507002d00940100d00300040850f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 765132913 1250 765131663 765131687
    0x1101090905010905160518060d0902030d080901050106020703030e091e090a0c1a0f03042d14060601140a1103180109090605030a1e02100f090503060103050733 70
    0x2a008005184500074002d106a816240300d1a0310301007402400008e02c032054000d07020380f6035170a03160070b19000141c3d0180400c94050989a4454484c6e11b440d240c02429128103130f00c404159000200d081c0007081c2e102c00e8201400c3c0082d5100b00094840d4041d100f58141842d0440311142c00d40e9080c41105500071030700d042072030301951100d600c032502c81c02c43d070504451048c1401c0c0150340810008030b51110100240d40d220f405034104c90103058007061508124440c040700547ca02440701c0b9010104403c010f0402e000005050050405280c0f1100182c1601c15014000c1020880451014042407064240007002d80543c6c042c0c984621480e20068456020f890a50f804540044404140004144240411520020020702c040ba4881d110b5100b410402514040c246e144a00d440000d611141c0c50801441a266580400305012090090507a20a504040d00c250000e0004001007070b0300080c3c003002d507202001e0800c11960811201085009182c07065158400c0c0d258103040c08035000540303d042 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 765134163 1250 765132913 765132931
    0x510020c12061008010b060301090b03120a080610030516050310030f140118030c021311070b070e040b0d1101111e060a0e19020a05030304170115060801031101090905010905 76
    0x5446013002c0303080e500b002e100765800000a200401910985400240303400c0005410b40741461038080847c8a580e21207040e601c0420301c92014810f00d400c01d01d121508003200c5240800031401e0801101d0400001f0442c1300c07041041c0800482e0004c02050180401150701030b0724248003000c1ca2030911000c580e5102440c046504c0c005203007031205d002d0346035101e0841c3c0c999203e10702040968204130a44019005588042c0d03601d0020345010386038400200300490050780d651042c1d01d4011710082c40c08400100c00c0d070150b42441280b481c6c5444a98081c0c010503400014944440381c00d80c0101c500300b01100300c1440b84e2040300910b0b1a01c040074005296181c1c21181584c034955a616440e1003541c1c0c1414211001e540704040341d01d4400700140104041a2000703103031241d4a940ca80001b8515045a00803c2c400c0041c8060700d03921402c01d100d507190441c9658600c402161074114081c04031101440041d051b5070684080c1105680700c0e210100c050000003404122650f12242440b008000817140200 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 765135413 1250 765134163 765134191
    0x921080a0b010e060714010b060c100b01020c130e0c09131a0f0c0306010c050304320f010809150a0e0c0307080c1002010b04050f040308100602070510020c1206 70
    0x1e41075100f805040071144001d00010300d031024965510b01d240410b40c4400402d55610703a080c0e24140c4c3c441e80101480d05035031000302080d0068007902e0040b0f81c40300c89014103540c080e0307035002010b480b5042c20b0814590301c0e213400141c504040751014140b0480740f19030740e0300200c99002c0041e00c000e0409402402d50040c0c0e5000319880b00c075400680c1c148815100000d4043c1d40d90001100b6100680040d0f9201038180741c804a49045503598501e1078016800c8854484401520302101718041940c10070011101d50300159481007800208081010030b030021410803000d803000802c0190204903c1c03900b03c004504c01780303080c43d10084c0c0d8802065402c40c89155400745400112003450b0000340803083d501d52001070070603415450300b0040d450f030000086100b555210610b500c22643c8600c5070a200300c14203a8040403130b180503e402002488010038110429410950620141d580011060243c4106584020070348000351f00aa14140c800e00c0c80d0703a4081020304270b01c0c9002801083e09130254030801c070300724 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 765136663 1250 765135413 765135431
    0x160510050c0d0203070e090103060507020d090b0f03130f11130504030e10090302060304060c091a0405010c0c0b03090a020306070c0b0f07030914010207020a0e0f06040921080a 77
    0x2003954400d485840400c40140700403001a03800f90300a540040c03050401c410568442c03404181d241c03c0136070080d40e080e680c1c0c1081094040d01401000ca4020003450001e000320300302008a0602c1c017802c1600c1b159003502000041d1010066100a04a9904803044540d21006480c1070b140c6445100c075024003e007805e542d2886a15103501a1a016075850b4441101d0b0801307030000e104c12a2082d1002c4010080303060000400358035004020b502903400342d603010507000d0482c10301030081140c45d40035440c4444c09000e525001c6800c1e406071010f40b04246840c1d1103181190a0a190b658143c1e0001c188000000080c400c04070400507007110031510030ba0644440b039490300c42c20b60b81c5a0710888048c204c0e11052001505070000c0c80c4038154003548a05000480602d40e03290380741ea8400c0c03d110701c1000e0398002100029851300c0c02c6080b004003c144801400b514002c03c040d0b02c0c14402400d62400b441d01e07400c00744108400c444148040541044985007080207003540184108010341e00c0c0305405251802403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 765137913 1250 765136663 765136693
    0x90314070609021c3311040f2c0a1112090d050c0d03050c0c06010e1801060f06030b0f060309070609050d0f0210050c120307320a141605 60
    0x42d0b8030315a04145000080e884044c10080c41d8015405c600700300426000000d480e06401744030380300c0124246548a51560304100d0110041070f201d800007410751100d0502e861241c905084601900d070030001105c1140d4036544c802801401100d20942d46207131010030001040306506420505c20003446040b0303141c00c0643d600c152410702c0ba00310224015009011400606402034000507044080302040300c0c0b40401520201b41001d00a13041007800ba0081000d11100700b0380c004c00d401c0b0b001700c454000c010750342ca4036408032040342c80c0d4480d440616031903184180150f0744010200b0b2100341c0290507207950f46000502e081d240c17001030041031f010580110001c50300b420000d54000500f0307801402c804221020340c00b00900c103006200c0820400c4000c00c00c5110702178060288808040a280c441c40c0c580c201100081c10103c48000a204d94010b240042d101b9540018403c041007a41001308560356909560101c40404041000701454100024003070250406108000020303400b070b20035201541c0004002c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 765139163 1250 765137913 765137959
    0x130308120a1b0f030e03070b101502010e0a021e12061807052b0804080705011412150103061d040309080a03020304031709040c0807030b040c050d09031407060902 71
    0x2c2e0390300003041c80401040f442d00a0303014085402100d01102d0803c00a5500d082014200f160600450b020a1408006032020380550880000e0903000910003040604400c903601c1c0c90035030011344904410391828200c2c00c00c2c40320042d050f01d0041c2c26000d500d5481880a9034491702034a203250070854200010244841c081180015110014042c2d41c0d01c15000150103000f03998403502c0203000794480310707503400504941c0003400109442400f9080c170a10b0302001400308031080304601d1081c0420882d2001400551598aa000d80c40e00c807052401e04220780101c0040095401801c603422004c030b00c0700780780304150b8401445a0310030382c0c40e03001058070b481e022500d5a49030780009000d680107000520004005010052400c85241c64490408440d000000e0035140b2b010522000304225070240600180e0502131910b0209090b40c003801481e525000061071482403203125000c581d529245c00003050305c00e26014403010343c03c4440d261a10007a0400000800d20a181288205c4041100805503140c03605 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 765140413 1250 765139163 765139211
    0x2205030d050a060f080109020a0e0c070201140c03040e0108060702030c0d0806130507030f060503010c09031e02030d0807030e010b010f110a050717120702060f130308120a 75
    0x510305100890903140040c1901600c450001074940b08040785500b14840036000800418001256180280c0180034041880d504003032254160b1070304004034942d240c4100c4503260360a02c0c2c8041904952481301801e4056400403410501000900240f5190803c0055059841000c02e50724079031034010b4280d0380c030311440100042030b80040d400350100f113005034001d980c0120f000e4102002d2420b0b954104044400490380d0001080c0c2c1c4010b400e13142400c41c801d1201400c000e80007080742da02c540c28090901002440010414007001d00461146804c401c000c12407194060200c80344002d16030406041c0c450b003101c0c030301c00180c50b002041060141c14040c1c04100c481c107844e440060020b6550803101c070404500408401c1c0f20718400c21001440400100c030080c41558680750151400f01c9100d4104522016503002c110720030302041e0051b940c1e0354100e982e0200081c0d08169582c00352500d031194a60b403540003901154020807107145000001d0718107072180486080c1080340030842c001d884c503e1aa540 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 765141663 1250 765140413 765140423
    0xd0605040b31060303121a0a12110d0c23010c11061903020901090812030127050702030307032301051306050909070623191202070b22 59
    0x80948110b4440d0360540120301e101c61810140c00403215041d19007618865801180000d2807445a6800340d03001e031185003500082c0359034000002e4404c00000c0d55890b11401345000c1074006145071020405202603c9c640c40304050071656082c00d4905145a8810300740c070405001e018029421510301d151703103014440440c8140c48400d0040d075107860b202404080040e0040d00030b4020406048046400d8483c01c2c080403480c5c1c0c015a6640846d0001454400507601c08107403640105001c5441030f8020060700d065900c02c2c10300701e0407100103256000f100c0003541a005162864070051140c441d41c080010b42c4640700a407418004485a0109034100382c80b006482c10f4030340655001030080e0f00d031558420b810011810b001040c282d03101d50000d4040b280c143d500440700c0c2c0c01500d0401041d500311001803207805400720f04000c0074a044002c90b40911500d80140b8120054118a1280f40d02842d41c40c400d40e58043c1d011503e80121b031070441c0c00804107403aa44450350024021001104610b145502c1c419444 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 765142913 1250 765141663 765141679
    0x11040e040305030403050702040f052a0d0216150507170108060609070e041401030c0b03090a06110f07110a0b0405060711030a12080f011e05120a06060b0d0605040b 72
    0x1a07103080794180c1000d8401c0741005000c204040159070b481c01038424014443d4400681814446c0a01c3c207011a01e2001610a21010081694030380300e5506552000144071380259032144030020000d0250356421008107820741802e180000340d05a5805a4481e252a4560420142005103402110042403080140302c1d84404005002d50500c43d150035008003481c240001241805400038080d543c0300c00c5602c2011414000400038000d02105460003003420481c010b00d103041c1704c05243d484001c2040042c1919450b80d030703410100340d082400c84903220800b803480b40d180c04441c541004108070492620b0310500407008040340d13090980d030895007229070007041e0718500000356841c0c498020006001e25814012410401c0226403000c07504415031030240c0c0d4480151070140030703951141d130040c1c1041c170320004104c0d14400c2c00100d0003000307270540b00c2c1161891410b030b00301846145006101003000b4401c0b4100800020310300400c1014002e2401c6030101070083c6600c410600040314112008181c3c00508 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 765144163 1250 765142913 765142921
    0x1005060607081909030501020d0c0e0a0e01440c0f0a1701090b0a021b16030f3e0316090b210d0e01021c0f05280311040e 53
    0x701c07484803c404080d0404104160b0b49403955803c90f0030031528003111980b503503090791005600c49102c003550380f42119115400d905101150150b01014028903c0242c01c2040680c1c02ca00c40700d02d03548014800c21a0140e203080041d84414003001d01480c4c94030140701d903065005841c0351550403800381c007201034246e040c060328082182c4507180c007400c408580c5550320054440440c161030100c900c51303501300c0805a59034000d0703000c201151880c90b038810810b4210303800c2c0010f9924100360000440345c11010800c020601410a01e1b16045481c02d101080c038040c0d4454070420050340800c41004191940c000c1d90101040b0900d51074116450b008031070802e140c00240310f80d082a5100d1403ca80c409041000111001c611300814459403841079615a0301c6410420b1807603034014900d8401060a01c05407000740c1044403181c100018424070007081c0028900006c1c1c1c003601c0f80301583c070509202c0800d24050502e805400020180c01d07664140000d041241603d02883d004040310101d400c140c200b0340aa9039 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 765145413 1250 765144163 765144187
    0x12080a2009040b030105010906060e03030705152509030318060e060a021606170c12040b0726010e09011104090225080910210e1005010602100506060708 67
    0x11003800007542c030656802c8140280c3c3c03424800c050192014004c0020b12604001002d004c0f4295403c9243c400d620400c031002c0040c0020594004000103031410106a072075040074011031181510300200c0b2000c00c0600078000e02d034048285400c40303000f40c036102114031750841c3c1c00346800482e0155201041a100c99101c0e5820144000c2001c0640c1d841a6036213507180b51850042d9100c00d0740910001107060701c03003640c1d1407401c00c246a0414944c205243c0340500030b107045c8050300e40050000d050912090005104c00c6d0094013140209403103140004030348405289901d072040b8080c0101007118203e48002991180f05104103019003e102010321305051401540d00301035842445450108240035041d07404a00948080300c42c4c41d0322540a4544514100060080c80780004403444200260480c821140100060150030314241411000c04c11200c4044070b1407a107070589140340780a600d0b00300001902680400c00c0c2900001803e01481207841d8082000303c42e0240702c40240a4200400000103e86 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 765146663 1250 765145413 765145417
    0x7030911040b22020415020d1b0b07050702041409011a1e0d0c080d0c140c011b03020712031707050c0607050a03090c030c081002041d060d0f12080a20 66
    0x4540620054a050b845001d80d1080341d511170308040240c0c1c0500b83d180e01c055017100200b002002902000d44d5040c01a071183c080ad0b810151801c818010001140819902e540d04100d16440310582886660300304400e586000f0301144030990304041e4402c0050206103002e41310011102e907400c2016020800d19000c00c54005000c0504944007089204d000a440200384080b0440600d19254002e4410700703410009036100c4409880d0f0354581105002440985e000389545260124510411410104a207000e9180000c2500150b8441e4080800102050391024444040880c01c032402041605e0780f40d010b440c103000d82841d1503010b0300414005013242d8442d0019121240e020301c2c02007032001c0c0c291240007514880b40c000381d514420303400051001c074030100003810800c1c0e03540138110f00d000c2c03410a0000c038000c018246c0212440340800406c00d6580e0310300715403103400d0b00700340c0407040301c4510700c1c1c01e041d9240049240000710340d02000160605085125010752100d8056001510407620b407210011a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 765147913 1250 765146663 765146719
    0x18040303150306060605120c131401020a060204120c050a03030804030c0c030f0b01080d0504141002070506030a0506011b0b04020f011b110a05040c05070b1b0307030911040b 76
    0x3006100340002c00300e0128000c40c07004007259201c0310b50741d1000d20071241c3c545000400e410017003602082040400e10007442040c00312280848005044088480104e046c041011000f40050b4008540450401c80c050720103172000c1d10030344000080c0c1e681c1e4420320a0840d6541b0014001c03403485000100401e0081c2c0030080c6a5104922a10600d0349a075a001017900c2502020750342510010700501083c11308004512200c3c1c01801e080381064030b02210400210715000400c0d00410030700409102450080000e00044d04c401001e45d038036403400d600004002d20080740c0782c03400100c03540c800c7c20021301d5126141c9003090b0080028401e607035858017400810050b0640c840e04129910904180702c4007034490b5030309803030b05c140e01b4072241200010400000c0c40c4a50400d900ca1403400d120a003003940c0010448024039442800039101c1c0e41c603410782ca03580281e0300c00c042d03808800000400541701c1c1e141c0c4c031800504d40304a09410780c405002040c40100c4003510610382c0c001501c0b40141c200114440003051074 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 765149163 1250 765147913 765147941
    0xa08010506131a0a060807090503060c070201141207050c100c17060a0503100609060b030105100809100f050910140c0702040b0414041202030f090603060d020405071d18040303 77
    0x1020800310082211130269034000800548250140901c1c0b540c852617550080c4070850080c00307241030580c8a0201803080c0340000341845918441d0105920980301a5030080a07621001c0445103400301002d0440d621907e80380180380182030030040186411300c10034400c840c283c0d07100909488403101c610f20445010f820180d1080d880c06000039950f034104040f83c0111a0f0b80f4002ca252407628543c40c058400d01d800800c04032800344010701140d220144184000e119500d04020f50b0340b140f0400d6402c000110301c4846045040c40062140100c82e504400e00551142d4210340d16581c004002c0303002c03134004800180d40803d220001c110301026000c003404200c0c1c0010302c002001f00c0b000d0005412510241740c284a058040c8080005004058005201c038181a0000e58a4070720401d00005041c422032016130b22510020000c00c1081d00c605c601070100b127034081c20801542c1820000944103400072042c1260401d2007600c49040d606221402e44082041c1a001031181e868903a81039010381103004035084 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 765150413 1250 765149163 765149201
    0xb1e1605221a0c1c0c08040e070906031a060a170a051b03090d0c080d15080c01111c0e130b15030105031b03030d15050a0801050613 58
    0x14061807005800281c0080c180c8084400c5142101c5508041c4541610b003680410074440b80100c0c5102155500c24914038100e4031a200e101400c00b91a524904d0101800c008004034000c13507030140080310b103405003500e500ca0400d0745036030f560b0860554110329840d11140c1b400100148031414108003500072407125080200840240c0d102299180104948404001d501c0344140601c1628500d46200c803c1c1084680518610340041001c0c0e4031118117060004002c0400d40007402c5c4455007040c1c4001c0e6840e01414003607100710880030640302c07400d402880490b014404c441800da601580c02d00c070b000e0550a0280c004400708166240001c0284403a5600348280d03606850200e90341c80820203408488003c0002d003000006050103245a03c3c9581c00422510420050015030740c000740c91144a02c0c46400c030802610503a0100e811402900c01500741c01342000c07075010549440e02000420340d8411383d01008081e560340070090031303102c1c141c5480c1c0e00035584140050541c0e0242d04080300c01e8038426100d003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 765151663 1250 765150413 765150427
    0x228030807050904090f15050c0301030b0907030803042105130b030910020c0f2415150a02010608190c0e070903020603010e06130605010f0530040b1e1605 68
    0x1000d0390b50100048030070902c0e91820004000112400300c005007802d1030208114617146540c0c0c0f60510ac18000907184004400000b581c10703004228140145034060181ea84908051030000342c0142d181c140000701c04100c2c4017250109204e9010707280b0040048000000e80c501d007402071391096001516441050252200401082c01d83d8002054040780e5a0010b020b1035040442c4c003410400f4280b984a503c0b03428403e030b00010080752554036042100540650503d0040800041c60b0304040040360381c071071002085103520756030194881c0d81114034000075222480c0d03c0003084000c1d0105007000030003280318450244008444010026404034140c240381c0115074980d000103c468009a020344104211001009894100b1708040c1c04003070940380080c40704d03909000001e00200340e090418020007030007141c000c008042030354111020940444d1061820369030800103202890301102c040e203004030f2800208000540c7c0c4c01004000800e043d00400d42c82e1560710349a4070000030148a071041200c240051 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 765152913 1250 765151663 765151669
    0x6130e0c0306010815070206091203070527010f08060901060804020a1e090614010207050103111201030503030403030516210f0203090703051c120914030c0d02280308070509 76
    0xb5000c2c00b0002c0041a4403c8072095007800203d0042825085420140611242e02000100d400b0703012030310070180380c4031b940c0e60390215054044c00a40f0b10b01e080c035918100041c0c00300800340d5414841e00303903906800303042c59210545014900f070722001d03004405140108100341c450501d441c0c1040c8000c120f0001e032659080350741c0c03800000582c5041080d420b43ca0811500310944182c0d0020105191980c00421401c1c002139200d0046104580c14952074401841320196004215441c1003107680941d01d0310b503183c2c200390382c2d0b80c1c0080b241100440d16042c081942140310b20000c20711002181d5030040408c80c02d0301242948440303141c28042c52500e0b28040d00ca48005400610710400c082c200803c010f034614241185003c0550b17014050000d50700c0440181c007a0301018100000e504a000401e90107010300d4200e82a4040021990306404041400c8a0040000c150450341000c503a00702e89045901420810844409080e0900d0b070300c16244540c000240551041580b03c00d05082507404d1410f10408 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 765154163 1250 765152913 765152923
    0xd0303060302100509011701270608030d061d04020603070f020a061a030610081b15040b0d060918020409260409050c040e130c03060c170f06130e0c03 66
    0x7000000c80e40100b9501419680491241c02c01d43c061f801c00c4411b9450101200c01c950300b2007485808402d003031440c0021084c1950803002c001c2804104030f036174410140114100414030341c05944414514150b0180e2090300040031203001d01d800505113440d40d19806000d5698070091040c00c029401620544004100244610141c0008a25014181c11040000c050600030001c10440e803241c5206004e206240c000113010b065044019401180c180035640040ca1545a0750990f121b81840000d010800003140300203803400c805001e00502006031141c0400058900c60415105922030181901c00546800d4103c01c02c154040e00880b02080480310b40041000700c45024080100c40000d4104094444e910840307a200b0040d0501074103047c28041443c05544001d4290420344120300302150610501603220701c001c40e80444200820342210901070104203e0381000d5018001c90b000103046c00030070203041d03440344c0340c018007502417a040c070402a0004c0540041a420034410038000700c1080e202004 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 765155413 1250 765154163 765154189
    0x10e010813081309051b04060c140d05091e1806060d0e0c030f21030601120c2604150509010b06031503010b0a0e0109050c0903030307030f061202010c020d0303060302 73
    0x3503c2c1096814200f014054600207011108541d20031104000120744050950342038070f0043c58403103900a100d0801e40e09078002e451030645079000e5401401d000039000001481404401c0e16101c1c181101c142c1403c0362201455103d41c2c201942c204d81080c02ea06e034803012944010700500c11818100c46035500c1c2c0440340c1c002c1812016038010701c0922000d00d0204089140311000e0401004242c3c0d825840d005541406031410a00c000d0120100b0b0283e809519019090421030400304000003a4820043c03a1013943d40b01024940948030311001c0303032080003030741a22881d004100b000da080d0003040c000005082c028250070340380d562501c0f00d5034159a02002180158490140c408408078000c00f09802c4030084c4101d6480f6081c02041004070f2000340140c3c5044590903003000680303030340b188914020f500ca9920095418080081040303051030701070380400840c10703013504d080002c552640c80000004003064130107400320b00304005140061405054003c1c119119140105550f40c0c0c0368003003008502e602c1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 765156663 1250 765155413 765155437
    0xc01060509010b0403020310090302120c0706090b12180102190206100b120109020a03090c030f030f080106020705040207080d110706140106170a1d0102120f06010e01081308 76
    0x6004006070315203642400d001d01050420149007515580c0042da80e80c82d0a5150120180ca0701500d90070726000340074903921303200c140108554429112100c1c0e522030b1440d0282c0c4000c00c1c50640042035802c030020584503200041c0240100e540c03501c48a40c0c0305003071900c03000819036408020150700c0c0d809110728000c0d894580d800401e114246030000720001d01d2190800c04a40343c080c0100b09846100c5182181129480030b40181d451500103011006014021070103000f210044800004000c1d9462062003800c0c0280d46203940b420381c110007150034100a00c101700041e4030032501400641343c654003d01b603081c428111545860510714003030080d075042072200c102d03016000c00c81e4011f224240c003a007440caa0190410040d02d40c10220098903c40100004a41c100903c0300010308080702ca6120404a220f211100100c0345000007116020f0f610030590b8800100007540400e409400e480e11080c000d9505858445c1c0b0740491900464410800801403141c0300401400007010945800061050400d16 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 765157913 1250 765156663 765156671
    0x61c021f0509130c090506031b07030809160812090105041d011706040b07030e010e150a0b01080103120302030702030f030103080403021e130e0f100504030206060904030c030f03110c01 81
    0x504100090a040e14004040c818140400c0b0300c0340580c000f07176074001da03101190741030340301c0e1101040c070118110400701705031100c2e400207140e50505412207200381c8170348807460880302002d60f082010b90200a062141c02002e51110038000080b04020014050f0100189012130038140d5500e004448020503085401c0b02d070040100612001e040d036440c42c844400400020440d80c14980d640540d0001c00034924810161340d08910301038600290404034040e60681c00300d030040d68150608205a6805407100400c0070300d802141b103900c0d400750207014102d87d004108040246042c0340c0982c00b07980000d00b6941180402c00180307485508010242d4040d43c001c4410a4996046205206107251011146000c001c41079195050030b64611101e038814995525002c03604101072641f0b1460034281200c041e040303000310040100b05401c0d03039201a1003580258200c2701e013511030000b4450056415038010300001c2d11038040c480480d0145405614110241c42d000906040110020300c0c16040007140488603515 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 765159163 1250 765157913 765157927
    0x70b0109410f2a040902070501050a0e1207020f1903030806030d0806030a110301150617070318031b081b060f011d0613050f01090c0503061c021f05 65
    0x41d40d5041c0e4000145000700300b4905050000c44800819107020b90046440d08566141c0701c6550300c02e44004020166013907445030028070b0014044c003c100c0301410160b2a002d0420a5080e0002d032601f505100c1040b810303d0f000e040e40910903000900e071100780d08200360140307400c3c90a1410a501000754000d0780c5840e06401c000c410103041801d1050304108100180307043c4551640c000c921460102d40c00b805031981d240e00340d8042800350008c02c00342508000050000200d282c0c0003241e6148014111040000582e224002035084411600403c0d060014a002c43c90000340103d1144200b056515640c400344040c40d6100c0b00190b0107030030303010343d00b00202540000e10308080110fa500110f10007140300041d03050803041a110390300a625024a24807420200d0b4040d280c083c03030340d0100c44025030188100c0c07902012500403200207104d04411945001349440d030301031144054270b004440040001c020a000c020f0142c090001a900030b0b0b030321680c50780300400361001410340098001035507221076480300c0d4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 765160413 1250 765159163 765159281
    0x6250c0e190c0e0d03020703120c03090e010f0302130b0603040f03080702060c16061e09020a0617040b04031115011703030402030304090c09122006070b0109 69
    0x800c01c210468818107040241c50b4041c0c01c1005030411190941d8000444101800c0c12880c201441e031001d04400c51881400c07030443e500c2180d0130507003030080e1070784600075035a04681c24101a0920440e00011112802400145010034000b070720131407007600101d040101680005e8650b40141e41c1240d01c02003502c03402c0105a00a102c8503400340a83c0050f1010f4900490354450501c21095100e1690f0b0b04400080100049503106620f1800441c2941071a400c9050305076000341080c00d010780c07180b50345800c000380852182d410741c0e0000010039244a0076482c0d0307566800045101400480a00082e0081c1d84030b650300810101c0d10035401aa42103019524041e07024a88100c4001c00081580040003000056207000040f40c0440d01070500014040d242002c00f11021386c11034020340004800d61140b0014002d09481c00c401307800f10344400005a80c1c003142000100c1c820903800034400c07000040104103a4619070b00c10101c0e11036030412000e01c1c0d42104241424002d500e8060b408000401ea0782d070314444 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 765161663 1250 765160413 765160441
    0x1807060206100506120c0c16030c1e08120901030b040c030504060c050901021b0f030f0604060f050919030212041d09010203060102100908040902072402040506250c0e 73
    0x1006031380e41890601031824400680b61300401103152520002000b04803503034104444130250151a40b503402142c0c4904c3d120070300f43d1071442801c0003519141d4010310260346041a81d41160b250750010a10100a16075944003034200701412414959115608041c0e03031a01e000d404501d440c6981c0018044c5014600b40040324100035102041100501c44a203050741c0004010711203507504500c00810b036458400180c10701c240b0750181c3d5018051041110080708000441c83d01451042c4414440c042c064022001100e104980f1407106920500880d541160800c031003541080c024815500d040074034a100c0c00003580a544846280c0350051520708014074180c1c0400d40120030000250710754200440001d5842600030b0501490a50310415241004004001c40d401092103c0c2c056496071004e050808d10194050100e81c02e080720301c071036501101d0880c400c44051760001003079a400d110000c1800000d0038950f05030342d1200c201000003040441c0c0303c0e4011100400c20f40681d00081d00d01151400e10308 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 765162913 1250 765161663 765161669
    0x318060e0a24120e070b031e0c040509100807060c050c0d0c03140f19200a0b130518161b02040b18090609070609030b0f180706020610 59
    0x31011100d504a59842c081c0c0b02c400202c40d031490030048040b6280c600c00000c0c101506192142c1c8182640001e4400c1c8190146208464124010003007c20fa07648122940078202c8120b20860001c000602482c9002042160401d50205840b540161249155450400300703070007070750104030110303296030400800304a0020000425554803da42072a941da488941007180001440740f00316800714072070b10700b0400691034130803002c200300c41d03110161803a4209120101030b404e65804503e07000c0c0b943d619541070001c1e0100c1d21b020308094070751458015003900c0d980040c0106c401200c2c01c40d00c00144c80d51011640e03030b644c0541034042400d6040402c00d109050260410800901000580d90901d1241141010f042160140c40c0400d10748034003c0069648803008880b5490030348604140103c80380000703a42417040201400310b4003055150301c41034400c15550b01c0014030300820301001504801c500380076982c2241e60101d004030b5418000461504000d0715420040042c0c3c40a0100058078071072012007001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 765164163 1250 765162913 765162929
    0x5011b0501090c1806091503030311071a0115020a030e0f03010b0603310804090507030b060d090b010501051201090e0c100e03100b0306040b101503140603190f0318060e0a 75
    0x8602c01082811f000b12140701c05424182d075407090340d62032441c0700d085070307480c44d44090b000780c42003c20498100c800d1402c1c000c14102d00808002d40d40428000280c0100f100c0e0075441c0c056840302080108401c61031031802554065481d60005805a00d4080246d40905810030340312031003020003044a01c81d0508100b045003107031002003120300800d480000b1642504e00c03014010031550b45550f415009004030801c070640140b0700244004100c8101c0d403140030b406108210481c0b10340da070384004403000e002e01c8100400403501e034801000b03035651075408103d610a5420503190180b80f103030300003000c0c003081c040310030041400c1c15080b000e20301d0113000e902000e20030544204240001c1e4030210399520700c02400100202d8941d00403419019481d00d840c4010600c0800504484c0ca034014010040c00b074050110394194010070101d58035203404684141e2225018003000c00c0b2502070b8441081c00300c0e5170b40313040d81800815545007030200414800c0070003402d21516030036001480d0800384450010941d1058403 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 765165413 1250 765164163 765164171
    0xd0e1002070513050c1306120b0108192a0f0216030c06051804020d0b040f110306090705090306162717030c060f040b01090605011b0501090c180609 65
    0x3950343c3d407050403044510840f00060700e40d071401e41d07a00d8984204a0000c0583e901400006202544040640d5211b1302c0b01c0344c01e00013204c017031005480341e8000381c807800129407610503045003440d00c80d4000d24001409004d440c0b1f43d0f41c46440d16544208104240d880001d04070300300000220340410034460344a20f038021100e221451512203862203d942c0c000c19040000c00109810081100d510403060a03800034000c550350b50394032400500034400c28401600880c1444550072802015106171011201c4004603030346580d890100f0020301010080044013840800e0011228507202004624891004050305080000260038090006020300c2140c10301e640101912040001a0320162822038160030340c5c12100d40303180c228040c25800390844d25007040c8030302030800840304000c1c01c4441c02180a541a9072050340c0341c3d9410b03c2500c002740241030100b1070150528508215420308441118062000001c0050050356038883d008031903407100c17185210b08111304c40c40040320703c030f54001403c031200208 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 765166663 1250 765165413 765165419
    0x150405180c07032610080f0601080a0f020315010807061403101707030807080915120408090a08010507020a020108070e0915061902030421020f1207080d0e100207 71
    0x81d141c0c0c45014001401c01003003020f00700e40d00003615804048094480024038842c0782c4403808280c070028510400e41248113400850311415008200d59050300d41c00c0002e02900441138490300800300c1403c1c001c03601031058182e000c00340403102030200e0103400484040c2000b6031400000604008030000340c101e500d00c08000b40007141c15018001411105040242e9050103003084440e0b050071000c0d4402341001030002601000c01165800401c1c03180c0381110b02c9a0300b54022078042445010304854002e84013017083c00b0402088040001d0b011005004141441e02ca0310f0b807258038296135090714020050303802188070a0841da0040c540c50b03840b0629240103010840c0820014044c040040c162500703c8034690010441034a5540807a80205010055900049e80c5140b0082d50f0b6070180c464025a50f11a40d03000c9035448102020003c0c4070380080c40a5505070700c0d5410030810b091000d08004180c42000f5001800c0038041c085001d600c1015110340010076108800d001d0280030010b600c1c1d0454020360414 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 765167913 1250 765166663 765166681
    0x40507080a110904020f07060c020d2003130b0d05060603060a031509020d050601170303040b0703020a0e10020c0108010e1e071b14010f0e0d0f050915040518 69
    0x641c030003030540c000b0031260000350495106104803003030283c02500014000754140a01801441d041c1d118000c00c000a1001c07400c00c9844080059415000911031000f01e15038071010070703500c800ca4030110103603441c0040c000b010f50103519056003d914459408100d0201098181c41540e50007002510361501e180b0f828000101403800b6404020812005c0e404110f640d0f41d0140e101140076036025058001048079801c001d40e4414003480343d44107409100640300c1d00b01d00302209a9000300e9000c0c10078040c40d02c03503040c240c3c065040114500c0400c442c1d4035811026545840c3c00c481d0b10403683d005084140940d10004012420580050010490040c18460040d44080a603188905180c502c950b5540311490126260035000c03108a00c0303005602c8800d028090b400d0308101030804e20000030801c040e81ca070040801c0d6802c99010041c540c101042c0c804a0754041c0040422150b0240742061800040c800003910312400004502c0341a000070038103000e5410009000f400d084640c4a030003150346002601 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 765169163 1250 765167913 765167927
    0x315091513030206130c0611150c0405091f03060b0316030602032a04050904080d0905030d1407080c0a09180506040606020f06010b1b060a091b030201080f0c0c120405030c040507 78
    0x54400300000b00e03a14203010202070280e501c041c9c055480b00d820302c0c20322281650803500f00303008132071181c090340f0702083c2d2402809044030b95008e03100a00503043c51860300c51a0040220000d0650140a07075045400001402c4030342e00080d40c1b151f84c0041e1241422102200400e6180c1c1642c0215112003d0219148800d8025a403c540088626440030780e0341d447e060034030340503100c10304c141c0034200110307041001804005080141c0c0c60328020000f000b03440f804004000c2003a038a41c00403030a01c10102d231708007000d10f0051142814070700f0300e200c040b0355038411107100201c41c0400c100c010fa9180203000c403502e480e00546000700703461310040001030203001c515500d800741840f58003008030300000c911380805c64942130300c00300740707a424148d030030030714140561201030f05100508440309a1442c8800f04040000030180064a0301a0f45624060b075a03640212003111000c2c00807404240103000d00130b02c04908216044d59010000d100b1030302d070307807414040c985840c87c140580d170f00c01c07070030075042040450340290 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 765170413 1250 765169163 765169169
    0xa050105091203150d0c0605181e040905010e250501181401020a08070807030305010f06120e010615050703030f0c05030a0b2805030f030304020315091513030206130c 73
    0xc0403225203844d0f240011044d640303005008080151858000400c00d4214020300034540e620180034903081040343c20030101020061ba00120f000c090041180030741070541c00301d070740309100d18000141100b10a802500e030040d070121111040061446e036181d10403032401c070680103120030b00705604411001a1400100328190080c08011100c6603840d00f4540e02c00c000072250303035400506841c1d54402c0c5082c10642c90b4000313003064012904000001030840d40c1d110320642220f1195564001c540d91000031400a40340c0e14043e03100664803114041104c02d00458641424246504d600f9640e10381850080d00b079403524101d908a891412144034540713078002080700c1e030262490701c00107051280400001c07003120001512041c1d40b0150805e00040c1141600d803001901c8044040394800380c03c042030240d0300c0c40111340003034054102d6940100c3c0019403601440d0031440420648074222001d40d07142c54a080201c0b6807a90421600c1c1001051540522115030007014480d030b8601d040d00c4a4a4840c104074244c4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 765171663 1250 765170413 765170431
    0x91a01080705070b10230609040f20030414070e06150c010e01021c060b070b0402030a0b16030f1404020105030c040503061306050708070c08090406050d050a050105091203 75
    0x2400100d0030740c4624100c0b80110b034003c00280136404c0811070721064030402d000700302001d038810b0404403a104072000040a001001040701c0d2034082000103000c05052208401c0510945038003402c3c040360310721549405090b224041e6a81c980c83c0508015401c940070710071071030b8140c0040d8000d10000035102030303042d030001082c0d48404051710007218101e000e100c1c85810300310b2540703400729801440d072064000b0f09208002e0082020b6603030a50090304100ca82501c130386842c180d420440c541c0014220031144c1c0c0e1180c0010161840c0c003c40e91070354502403104903107440c82d0325142260300b00c0d000e0b018850412000c216803005c00c212001e03440500d280f050040d0010741800b1000c800a044581504215000b03001d020741647c0e40760400013000e81c00543c4050044500504040000d044148180078140c860519071391890a18209030302c0311100c590000a02c81d070003d03202c5001240c0c640318080000d046d10700c00c90017440140160700740f81d82110700203004259075401c90040e40014080305801d03640c02640003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 765172913 1250 765171663 765171677
    0x20c0901320603090d090504020a02061f030803070918060e04020f03010b04060f0305011a0a120c1d1024200a08030919021810030605130507091a01 65
    0x401031801800e100100881d50010b030020130010344c0d24000c10741c0800400c4544510724102d850b03004003c10707030046015482c01603121000003085140c54480302248105000c240c0c2004a843e42c031003004660080350b02d50085001440b00300503201200c0c10203007010701020000c01006003404244080c0c2d20015001a10604e800315030a4103e80e001e500006466600074020000c040d61491444041051031000b51499443d0481503481c07500141451040840018401074000f82000d82805400700d07141070640c0ea995006a000c10101ca04101102000c41c003143e41c0100c1d49040e98514010804079000b503100b4107420b640308140715a81300186505860981010080b041c074103948106040c0351240d20b03100a1080c00c8640092100c81c2c3c2c010b601440742682507500001070a03401c0e544040c2c0054000f50418003480100005003085c03010203400200c05c200103204603640b0340b10342d4240c0d1010388012041c002c001d0200010400200403041c0100300d00f40e030034002038540c00010103c0e294058100e50500080d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 765174163 1250 765172913 765172979
    0x150f0905240a030b03070609030512031312030f022704060803040b0d0f0c0e01080114030a150b0d03020c0414040c26030a0806091806042d0501020901020c0901 70
    0x941051440b44c002400b124a81c0e65a0b00c0000e0101c0c010b1702c001d80c1d050207080038503198007904508881c0318010003100421041500e69442e6100c00c0f0306074006040540d04c04034501c00c89141e000510103078030500810700303c0c4072410001c418035072000b84040b0300c16440c2080410080c540030064a04441c4010500c58480c2000003401019003040100a0309051400d840121500d821400403078001c031083e030f1034400f80da13268a045000040d05101c10f40d85644030802c03140c00204050000051004400c1e004151100305034045008662504022005600050f884030401d080920498001481c1902c0d00c40260800740c40301d1180c0803890140405e03502002d43d59100c000d01d081e0003c2e148000da03104980d81c03007141c01d50040c85098260ba003c1c0c0b181c2c2000c004110b014400c0e0a000220001550103403845031290342c0c91075045100d00031003010202c0b1b9042580a14100e03000c204581f0783c043d0001507130b80d0030284002424132008415070351003180e0007001440f0f08240701c200320700141c4003030b01c0c14844074031 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 765175413 1250 765174163 765174167
    0x3080c03070306080703080a03150803030105090a09050d270e06060f071703010e1303051902010b10080411030d120b010212070f0201030b0f03190c150f0905240a 71
    0x10544c01014140c46070690000412490305e00500041245035410050b0641e403a411541c0000d4502c44da100d81c0c0e0040c00103001d145801501c2540110118000003440303046582c91a08184081091901282550072044404201d0781c030200e2071001c840c1c0c0e0121920381060800c3d100c0141c00ba101c6401600c021507008094600310b000c40f10450381107130302c0102e0a1055559000550703c2406411212003004005c50245908101003001c2c1c3c6905407642800c11a55207842050004210a000c04564954156034056110203400e903034150b40603a07402c807085c0750909140100100456265000b03074032108898002e280c0c011070b0842d800440510224402c050f1800407403500e480303004e40070741c40000050f01000308181204070030300c2a071007a202804516514810481003000509407180c05801402c500306c84901d268080041c214803940c4001d41090310317961403001444a105940303010410135603040300c50542010b000801040c080365500043d003144142d2109110395094284185100803a138400054 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 765176663 1250 765175413 765175421
    0x1d010c0f140408070b03092109010c02180108030a1b0203060711151302010f03200703020f0f0c030724110a052b05190e0d06020d0c0905030a03080c030703 68
    0x811583c0441e060b07540c86480714800307079009031000013091007056801e0340300d40c1e04a4294024840d0440301641002c1ca400c0054a81045550040b41d200041d403500403005001c601049000c2c002800065844d001c0100c000f0b460080da0b00070041030018001c0c4840010307030b000140240d02c0f02d80d034640010040034002000303181000360501145ca1440d8079003004401c2c412040040180c0d4000d90f54640b00d080040b4055084809122507100015404d008030394204408400a207140d910170310440300102c80201030306060042510004e40c3c4c0382c004035100c0030b5601d0f040000002a101c0788405294038902d602003004514100a411020b010807144019a03038041845154a4190050151082d900105403d400c4005000034041302a5144440c1e4510f80c0b803050003541c0d0000c40325200045085c841c000d05a039412004406658003030b541184400000d0b0b000e00152440d06c0744100e000c14402d2482d44c0c060700b00c400c190030560080e17200c6188000840d9100d4440d6420184201050741e5988132007a080b0094 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 765177913 1250 765176663 765176669
    0xa060b13051e0c03060a0306020901050708070b010e0f13020d022701181a041104050d0c090506060c15060310020c030c10060320010917011d010c0f1404 67
    0x1103140c10100702c240046680c820400342d180c100405216502c02401d4403035400152113050f000700003e07005000140495005010484050406904094044d40e40340c4207a8811401290440200001040f01541070a020354200ca440480003005181241c0325600e010354142010b07110300c056104202c203640b904100f054003000b00100980320407030600384040030800207205508541b43d8554041041740c041c1e100710582c91004d40700d00041003100c4820400500300a0351103440d07690b810003000605546200b8007507151403081d000c4000303a514000c1c0c1103080711002005507000d0f020400070f885280f4408503110300b28650200f4045030640307599000c00d2400ea10140303241d502c640f00041100415200001800f414680700c41220075609800c5000c50548185100013000503070450800c1c0111400030703100e07943c40b040c1850008030b00c550f80c001240d504050640700f000180d5655840511410074100c500854a0300e0074001e000780d84e060307032004005000b1600120200f09034a00d0340710462225800b2a401 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 765179163 1250 765177913 765177949
    0xd060606020d080a230c04050405090a060b0301140c0a0909020c3a05031f032a030503040b0d0212070f0207060908060117150a0b011d030a060b 63
    0x24080e00d440c0c0c003a50301c2200d0850180403900b4080001c00700080740c0a19100111200e500c40c1c02842c01e00b4060032a0356001c1c01c210300c0942d0a000100d0203403201e03c100c91007038152200078107031440300303041c0070084030600520540640d042405006407200300e65001c070b801ca50600c01d825510007901c1c9040b5980c030001d4014a0f880c5000207100c200c05400010759400704002d1403060803490960782840074403042260780b90300300b04000c402030084860180000e142d10070145404c040b4041c0415001488000c45904200c0d00d0802109845039200740003498070260158103103414403c64110f844c7d40380c5d6802140702d0b0580904000802d2040c2500c0703501a6081c0001070841481b42d8248440003405420302a0340e281d0040c410b020000464a2148017808225010100a03000c0c59007400c0940300c1c9400f4203010200e0510581c8406807281c0150242184114200d020001d0703e54019000109030500c405c15041d4600408000410b056034041400696650b103d1300000311800c100c00032900039191144c800c1e030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 765180413 1250 765179163 765179171
    0x30201140a1d0f0d0813050d152a0206250c020f0f0429030d090927140c1e0906040e0609060f060103060311010804140f30180d06 57
    0xc018031003001d02510b4251480c500b40136500c44050040700400074502278140c0500d8011b01c202c00256602240d1100301003404016034000030807040d041c03020300fa452400103a0103442040010504500c0300f148042c100d4412511035454080c0050000c0c00d2018040c2c800d017a80ca1044d03401360b9500e0844802c80401800030f01c007044d402d2240c503498601a2642c45101003558091b10080c0c50042400000140303185c5038141c1e95810594060000e050160340640e00400c00c1003858002c1e001f00c401c1618907403080302085a6144101750242c00c24444000c064011314444000325000c800c8108038080442c8140d402c0b0005a65242c0080e001d00603600b000400b034080c503000e02070003041c08a000c1e03108040480c940c490507203c07040110300311358003403001601000051140c1e081070f45c80f9011207500319000d01d640360040c03031124000d075040484140b64403030b084c0d02002012011100d460482400c0da151039101d10400440ca1121541c1489500110900104000c43c6601c0030fa481c40c00c0d8181d0341c0c0e0042000c02c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 765181663 1250 765180413 765180439
    0x70c3b012403060918110a0b1624020a090b0307020d0e060f070b07020c01050702062a0610030c08070609060c05030d06030b010617160e0607050f0304030201140a1d0f 73
    0x1703103031440381c00a681019822940741c0403801c00508020885248884044c41c110303000400d40c2d01d02440000480b021424400e090405606414480618030a91800166107240090307014101d095280d20011071000c0500030000380d2500800c40c5014024142060380c4d40d491041d000408030b20600d15225840b0502041034002d21040c191001d2065070140c00721000614014015203143c0112680291b10420030030442601c10000039044036000c180328800d1a140000c2140e071401c1c42001c8070380c0040c2c050104402c00c140a00ea4006500601d0031002511b002401e01c0c4c0014911907450082c42c0510104908440400108204491501840c40310400010f500e901e0514121842841100006140701c10062147c2c004c10b041c41d13005507044055000422401c1405a1305000e051804903400b840503c5000b0200750140150400a84403202442c1d59a0561001414014901f1040700703441d20305001c03044240ea0080c54921910b4082e00b45503a0251403807000514080e211085540c0089610607c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 765182913 1250 765181663 765181691
    0x30503040e010605180f030a23120f040905130602030a050117010c0909110408032a03120402010c060f1a040b060c0a020402070c3b0124030609 63
    0x40d100352000c07201414030699a680c4101c0d428000c5d09035980321010f02c59070081d4680b6111100043c110400780c242d03183c0380c0c003079114058080160300d88009000003080c4070300d0071703204180039084d08100c0d960002400c1c103139032100403052406203001c0c0340803955a45010550010042040040480d4800000e41d5213252202c000005031500b0f00c6941c1d024001e4001010036040180140410407a15580d032416140c6000900d034040c1914150030f402d100d1003000003013030014081c030092207005111001e0008101c940540c40b00c15500c1140d480c0300307540050102c0417188244200355a00f241d0246030120a5406a040aa000b40804a80183e915160003c4402940403c0d81d1510342c00cdc030219000c001c0c0203c03032401d00800e807140f4074444a4a03041502c6047c01844c150b0701030200e550243c1d502c16081e80e2142c0004e042c260f51109200168031446004100d60380f0a2410301c1c400d81204c1c4400c64195151405054014401d900241c2c1e8564601c0c82181505100350301c480002c0c00f40980c2801003400003022 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 765184163 1250 765182913 765182917
    0x100510050a0801050f1c0f0c0b04050919020d09050a0c1a030a020c0c0907030b030616211805071a190f0c0b160809011b0c0303060305070905060306060d02030303131b030503 76
    0x2084500032034042c40080c1490105064408480026100e0350070b0350341c0c2800010b001d500c0043760707101c1540c0c00e04c24034080c0803480c0708205009106400900000da0319061032601d500f0140e0040c8010581a40071003c11032412054a0b04031b040700c140940c5981c4041c503504d051005a8a10923045030440f020050000c2e85908100c07402074003507040d18142d44441d04800c4550312601114004100298408610b40420311803031212071941c2c0f60001081e800211b40b40c80d01c20380c02e000179a5568022601800240c04051074480c2540010941c0e51800c14081d08110300c03130701c1c001e00c91418881c000350020056401a03900510b00c87d40142c0c03803521031415809086c400c0c121340032020000b0b047c0d0f1000410000e81446030111003030082d55400c191580861040b02d200d04100d07011010140c90351070001c009502004103001400722540041824901141810b1a08100400c0c0c00d124451080284d0301503180801143e81050310b4240003514070361682010306011401a50070107000c0c0c85510008280100800 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 765185413 1250 765184163 765184193
    0xb160809041104091407020721020411130603020c0d03020702120607021b04062d0e1918021e04060302130b0102010e12121b03100510050a0801050f1c 66
    0x5082041001240d85c4500c0a42c0c11242000075a20403941400440c0c1030088501440640007100c541c0794580b540030a050742ea00200d000c80641c0d0204a0340c1000c03c600e02c5441c003500642c94114100ba4080803440d588440c3c5103030710380c01d1660000f0300105540b84e00b8034641c43c088408085402e5401c21440084d541d4060303002c0901484208e402003009440d0900644003121542c1703500014031200100d007044c140711035601e07001020f45000e00000f203007441540344905c240907005060070344541c44401c0d04107aa40751b440041c482c404c500031000041c1d882004c1c01c10062034084224158086d00d00205005000c40d4202a42c0b0240d03200395800040304035000100c203003c007a4003e0004000c000030f000c0da184601d4001c615803071030600c004080100304481c9140d016841c421074201c0d003500b48100c0007940d841642e1602a41032828401d10030b60404003410102c0c45214602203142ca5072028000388940410b0013554450301008058a006a03500780c0488010344403807000001d2141c403450003d400319a469 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 765186663 1250 765185413 765185429
    0x60b0a090f0b04120b0a0e07030303050105011e050a0e041808071103031219020d0501172a06071103031c050703110708070606080601080a060e0105010b160809041104 73
    0xc9404100b000e03040064504683c0d03403072038030003c400603581d40c40032242004002204042c2d4500f1550b103161001c2101c100214082e444c006401e50604000516480d807002e0381c8010300c9040048032040641c03250460f000c50f40303649420461501c0030400100906034465681600400a0600b2814010000014501548111110603016807178805050304c9014445c100355404402c41e000442848480e40f04500303188559400510b801c40c3c10340c40307030122a03082e04248101c2d44000320081c4011010010a02c4800d000075504003d0041038001040c41c10178000e005001d5000440c0801c100400c3c94030284410800905490310342c0000c0e40c19005d01c041d89080140790608103004580540d0081c031034488034801101c40546072090a840c1c030500346c2e01c5078504070780c040d64450b0001100141400141d000c0c103840b40150440320441d04004013620303001c41c1102c007542d01d4500108001003042044800081d00304502d0400100c540c10040c0442c00742c2d0030034640140c20007a210000104a030020410742e1000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 765187913 1250 765186663 765186689
    0x706080105030d09030803150d030e0108090105061c0f0c0e1e040b040b1e0109051603050c0919230901082a041112040302071502150703060b0a09 64
    0x68080580d514810350305900030138801401400800c41144c0190340c0302184180e80187c000300a000b06070700c0141b200c0c041c3c001038400c100c240c0e080d603446208103420030600740c02031007217040600000c0d14000e20240303280b800c40842d208080402000c0b041e072803040768215a148104903516801c49081000440e50352845044507416090b2441c0c032201124082c0342c001086145507a10780e5110b0303009103405080d0086d040c240c14210040c02d8240c04d403943c080d1040780b40105003401c00001e40c2c0168140d1172007800c181800c0200300000740c0350940c00c0c1d50705200115403c500651005001c0600400c1e50b4000c50031302c581084920f00c040102c0400700010660035102460f60b80c0e0b850080e00d0b1201260340c4210a01460074010448032030340c5810225040300e0040001424100f40051503105501c0502c0c401103079902c143c02c100c2415018403205008152030150301c00c81c040f1002000751901075009025840501030408a65200e11a5002101400120141640d9802c00c498060509502f0b441107210300303040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 765189163 1250 765187913 765187919
    0x20150711012607032a02010c09080f0c04090c0509040b01080d0816030b010e0409060f1a0303030a1a0a090914030c07091116140606040203040c0e060f03030c07060801 73
    0x5001e03207100d0000b21901018001d41c507181011400f50012107960f010350440c0c224801e032000312070607850746a41070980000071005510300300035002c50f0542d805410f5641140740d064074884001f01c0c5200d07240104807030004009045141c404200d0340ca40e0499500005040c0800c4100800540100c0c11b0f110500200c0c1c000c01a511001c66003488200e0b610901020003000c0121024000c0d00b0218061805050410b6403180b810f01060803910300340003d880c040d488001c02005140c980c8600403501d410b03100300301e40924206000c69607038440038100200240c2c1e20f01501000b446c000520001e55000102080c10180c0e440a0711001b5000d107100598a0524244807201d0001e00003003154641c4407064080c20451f032901088000501c03040f4100c10078840d04010307840042000410000040c0e1041903d0464840507842c901d00c2e1580042065024520400601c40410211900038007201c5100400007030a0369400d01003040503903031402480d00340c4408119241992000325081c4280e072255900d688080eaa = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 765190413 1250 765189163 765189197
    0x102040f031e0c030f0302010906050901091704062a06060603052403070b180402071202060c090105070f0312050414010c08010b0d24030c050103050708042015071101 73
    0x1e240d5401480140500b42c04c10004500740d0f00342e40001e00900000a81090f9500c0f40c03c241c510480b007040d09a59241c0c0140208800c000000d20903900700c04242c2e0525090404c041c4c04140e40314a0449002040300c103418490041518100030658841d4003801055a22100500542401d0390001c500b414410590043c7c18108203800900b020300070000e00d4450f1900700c0c5103038207a1207036521400f5112000081e44207500d0328001806030740d00c05c0402000c88140070400038100040a4041040c0100402580d88180c1c0e1085c1a030f0328584c0c1140301c160604889240640e00d24480003d107076281403c1104220901280e0203400c50891742440007404411110f0303a0445050509028142c820300d070501030003c940507264400440e170032413900c0c4c82c464511404410388001c0c24540c000c4030b0130a550303c4107000d5544c0c540649500680c860405030554100359807406200c4ea109256000d10039840888186e255075020076612689601c4212075503204150f0400c2d811600f0920200c1d40825507a0410000d024 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 765191663 1250 765190413 765190463
    0x504050603071401050c070e010504150e0406271407090204051e032805010c09031a07051b10110a02060420090108100c180e0a0e0102040f03 62
    0x4001d024000142c10008052421000f900b036441c104503091252000560080003058007030301004c900301075698500301c01c010070780c0c454408803007030880c0008003045040400c890031500b0039800741c0040b6141c03014004080c0d4408800c00c81a4032440c61501c0d141c00d1110b241c51100b4500c0100041d00e00403501c90410b00e090b40300314414150015000410a0148621800c01681c41c43c030080c04d9446030004014041400788081910100c0d880928101000b044024880c400c41100b0906160f04d80b103103507440c2c1540008499011820a001800006030014880c00407208644904510804220f090303815940c4e60360042d540e103000b1540391404120700c2a003040c2c10b4a603080e0165008085640d600e554220440320404900074018050100617811a0b680d03400b030f9400b82007540001e21141d00801400c0086d1100729100300d052240203080700545405001003441a242540b1401c2140d4440b420103400510030901c041c1d5142d4404100414024117240c1044103c9000d04103148002007200250a840 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 765192913 1250 765191663 765191671
    0x1314010501060f120204080102120708090d080637061404030f020d05150a1a0d080f2d0a0822060c020a14071703070c090914070b04030b01050405 64
    0x450a0a0043e82d4407034403030100b550084000010250400303541c0d68042d8203a8000782c5d1220f4200d140101000f28203540210529030110030540100010801d060010f0611078000d80040c2c00b032070b84a0107243c151001008020f260301050130380c8082e480c101414110400da000e0003032500103141c0d00c10000884010000b91401c1d6a0808040d030034010450742008054001000d08a4141c080c0c5418081446103807030100b481400d41c84c002050500c19038a29191881e596103207031384640f83d04090760001c40c421800f0744004c400c940d02140ea440c0000b12900c0c40c40c62911841b44181007040002481844600020700283c500c40d442e55003094039660f109900c40344182d0040201c1d40c0d18004c1180100b14160408140e0a0300350040c2c4201c0710f441d86641c01c00d1200000d00041940c010350041011002248100d9211843da90246003403101c65078890503074020701d1185d1200c5030b0301c4d090b80900707011009600009040c00c1070210340001b9a02c803900d6445400c03500c0b09407030b02104940001200c1c141800781c035103e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 765194163 1250 765192913 765192917
    0x160305031f1421060c18010f020c04020a0e03030f070512030106020a030305130b1602060108030c06010e041b08010c090b0405091b04090908191106072303131401050106 74
    0x301100a000f40540b5440000d500c0440d54003034095010116402d04c0141d0150342e201ea810750380e80c04110400300d03c01d80162001c504105802031040d082d0b607400302c3d8001140004540250740c1d0f964204048420358071040d481c40e494000042d07040c8800a000e03008004151084099034642070300000011a280824800d04000d038000d2414000001d100354883d9070700800c01200001e070742c2000d4480c4040c0d407004482c0070007d440c41c20741c00c60f086034042044900405403400294900800703481038503110441881203408650070200441c00b0400d1400a001c0000310108070f00100a50710b11180c1d02030b0004001010114440c0600495030030b1205040303605031680500105410345982c0d101d494005410440d92140c0329041c0400310f0311082074050740a48600503c4110b8503558044ca81d2051062b06540d81018082d444484007806040850115840100360900c03188112100d044d204040301140254882d40000004228040c514101c002c058940100c0d40d01450031010000d0a003219000e004482c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 765195413 1250 765194163 765194189
    0x30804230105180d2001061a070501150f0e0417030c0d0501120f03050306040b0a080f10060f051e0607060e1005070914010216080718020304030c0b0606160305031f 72
    0x410311080501c4554440d880303400094015036031680300c0c88c0441003407107240400000007603c00501c80b0074081c4003071810a008035090028070304070f1100d0311009203104502c003400c0e0360780000d801d110300313541c64510342c140c0c1003903803980d03403a003080c2d448040e074442031828035168600000800c1c015540b60340b0f0701120780e003c40301454403040750b201584c00307401c01400103510030740b0703403800079100d0b01d0344c1c60924001c0809200800030850642842403c0016540200281f079241c00710801a05501c0314001080310000da42401550601c03100440515400c0750b42c69401c08000210001088803550020502140c900b00741d410b1030110800b85802d5a405039030390b0b40052114941440000c03500848c0041c0024140100c5d248440d20030f40c40d10740c500c120340c8070003055007020000700510700d00c4011481e40900c28880071882c5203007c2c0e4025007813011340d41014003000200000940103889000489031000340c80004003644c403941e4039000f009940101c2d0395103c02042c151580805640942c0640d05507420014051 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 765196663 1250 765195413 765195437
    0x3090203060c07140708060108010c020111120c04030b1f080d0e15041d1006140a031802130c0216050f1315090204080705120a030804230105180d 64
    0xd1582200c001680d1022040166a201210401285000f81034086c0031301200d6140081c000c1c215a0441e1120007564104100b04250b51005c0d000c40306412440c0e8a8140182c45060b522211400f82e600004d00b100d4149040c0300104c907020350740c1c2103685000e021710000b0300c0d182d12210380c8851080c00050041b40c8840e01094203894102c43c10b414503405994001d0900342e503020b446d203807451a4002203c6c0703010030301c061000800c007103c0c501c40901540e040c4218081040404041c3e54841c4040b03400402d1754030302c410041454450b44650084d90014108505e0b0720440c43c801c4018540c02c46994007500c1000c2c06001003080c404008811140010302400200c1084001d0210031008880303084251942c0d00030300400c81c050403289001030003449400503195400e044442c0d10f42281a00028410070011004011018000600c60540d541c503103090100713500c0b00d18010307d0300c0c1c94042003650a40480494041204815444036208041c4100d00341130302000040c403140c0b0780c2c528070701ca0320000304411600 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 765197913 1250 765196663 765196681
    0x16150b060f070b0a0b040c0e030c1804030e0409060c1701090b0a21020307172b050a02070305100f0609060303080c180901180509070819031809060302030d0309020306 73
    0x1581d80085a2078000c07610b45c0040c4009002c035107000e03144d0000f10f40304403400d0b0018201004002250003003a59034144007024410f41d0741c2084001040141000301d001060b44032606c0e190048048141d010780144400354900101404856251020130f02c0c06803801d00004016205010707511a1a401418010415042072170740c180005c20348445007103110004081c0381c01038508015000052441540960401801c819064140030a60b00c440d0000050001242802c2400364803112a01d1a40c7c1889652891560800c0c2d007810081c1e03101030460300034011107551094060304140c0c41c149100c0c000b000340e203841c3d00d01d4904650403800040c0005517038038002410002100d0040c030416015070840707031402c403440c00003a01041d400d030465401041c6820441440956034000c080d0040c3c2402d024018650406068540d6140d480c841c00b4503610003080d480c018180034140c0110f41d95075031114200e5290b00d643d00000075019501c030480c0284640108504414030078803840d18403990041c0904501c2d101e400078 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 765199163 1250 765197913 765197933
    0x60c0d0c02060105060417150a060302030f0a2f0411030912040f0605070c0b0c0a020f06160201050a03141017030313060b120d0201150807060203040504020a0516150b060f07 76
    0x180380c1c141d101c8c0840c21084440d94610580c4500301d482c0010801c0b90462040c582819190a82c0b00c40a5102d00c9010f00040c0b00c014901e20300340a09140050201da041c5e103e5620154110000368009162001660f5aa9074030001544160302c0c81c03084544000038000205103510403446031441c0290041c1040c0710382482030000f801c14601030030a850f0541d80f01c00144070036a1041c0303140c0100c2d83c80000500304500702020740c110703406003c5445170705021000a005c1c100015001000341000400034409248601960240d44401074a40c440b45030740c50034003070b2510034030348034015003c82a1202c01141443d07000007048a105640030000d1204420032544c0d088080e1098142141d8000090740c0d604c500008100403c1c83c18803042e03400071a0803201d100c4c00d10300300d44551308003900c7c40e04115024405943c0001c1100d045403c20784005a480c440c0c0d140442e401d020b6010f9640b406600c4005450610803155059100340c00caa40d4100030b0000450100051481004c4038109005028442c40c4003064018103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 765200413 1250 765199163 765199199
    0x225030b0a02091203070c14060306040e03130303080f100b1206030703061a09060402030c0a0e2103191814040b03030a05040e01050315060d0c08060c0d0c020601050604 74
    0x110160a001e80c0c080040c0e150460130720f424403540d00110f115000c0c800fa042607a00103016000c0d240c10001e200c04041811440300800c00750041e503ca00383c0494a990400890368a404000344c0c0717404680d20b81c0380c01840e2400981c1c0758181ca028800102d07030100480f00c00c51003141c01e030100c00d610b0304d000c0c040ba03455104402080c0030303454000c6420000220712240100460081140b01e240540c21003c0c040007004480070706540e0160b88180b00300241e200c04070307080382d005c40200d08000500440c403400240907111555001c44840180701705030000f2850000c041c02019002400c600b404030700b405021103106c007042c000c01040d45e803611000c0003c101e440000308006d00000e0004103c07106113001080c41c5074011040200052800035081001c481a05901405490100e02401100104079096800003001030b08080c81102c81d40035480802800c03072100780c0113094180035074506140082c0d140e00030750800c0c00c0c80b00300d05d4180b80405141a10103c0c525050301c2c4004c1c1000c0c185030422070b40d0802c00f01495 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 765201663 1250 765200413 765200431
    0x51c0210090e040305090915010509060f130306020301060210090b0711010207170901120905060a05060d06051f050f0901090c02010b0603010b0a02010e030703090b070f210225030b 79
    0x180002c90030030040c0c01c0c1e40d44641c0c0030782c0b55160354066440520900040080c0080c41501c070f581d000b00d50980c0e10400311003011504a490070b88412580710520a203125500650624450300301001080001640280d41212815020f0b14071000105a6180c2030b0b81c4000b034014002403100c0c002402a40c0035503445441d4401c0c520005090040564407259110010070382112800e40c0415040c0480da403041d5450003811300310005020000303940c0c3e9280c0d5a00c1c0702074055101c40f40c441e00000c401e070f120409542080e9422501c14890b034100000e07107801c0b240d58581c0c18100c0c01e5203240003040900301400001c844c88005015410300303a203003c203030400070706001110a085548071400900181d90b044041c501a181d0441c016a40b0303100d45202901b11962841d01000325042886080046034000a1348022690420200c0d59a003449150604545010310b8004020002e410520889400318403942002000c5603004c680210011401070020084108031081c2d401d098600c0034070000303421001068001c4201c4c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 765202913 1250 765201663 765201677
    0x21e031611060a03061406041d180712060f050403020c01080606090a180f06050d080705011506180501091809020d050a1b140616020a1e0807051c0210 66
    0x880006600740d000000441c00a501c0304000d101c44214403601c0c2c00d001400315001f500d0700e840c00034501040e024007806030704040c458030f00240c4605030b02e854401c1d400307007948242c800554550085410008000205580700c62a09a40985000403403050304d000f40d070590003d012184002004603201d03200100381a4010405002e040966120170f07000201624260301110038841c0d10140d03440840d02c0000940c2002030504e00700b08042d40b90701e000740d5480e80d0804c03119640c80b0010b0514501605980040d52032a02d844280080d01c29482030502400041e19403401c0240341d030302e000460791100b55004602d103845d2400740c0380307581880b181c3c040c0084501c00342c0180030b03100d0303035881d050b040c00a0208181d40300d178410005462150251920307480500759009402c030800c007058022500c14018070380f0001c4c664810480302d900307540e02e8002c0c5400a014a440f020052520105450440081d0b442402c0c51449150004201e030314000b9022030386a00204000c10480d14a602005101002d20101c1c000380040c03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 765204163 1250 765202913 765202943
    0xa030c0e1f050a0509042103140a150b210c0903190308010902160204020313030909090b0a0c0203120406061706010506093106060e01020c090f070908030c010507021e0316 75
    0x240b6140c0d1f0b4000c655450000b010201d409410000b03460042064490b03a207002100d4441410100c0c000c0166044600c0c41510303017480440a4004d8001980c1ea00314012400040000f04101c410042c00115000d80a440015104008a406104c880355004001c610b401e00180002d00050380039211441001035000f10300c450f1034012504990050324000c03000080d51090505254201e030350b8000600303014004102e920300507107a180751a00301500005040d41c8420001c5600b038403c0090f2045240e01890792049810300340340100060405101e10610000c07028a04420aa00401e07894100d80016100714900304400040002c2480d22800300740583c401c0c0c21f14890300320054076281000d0007444200003020740c02c00313501800c440c074121203680c119400120114080d0701c51000ba40e41200c44c40c00803903025100d808041c6ca070980d071608128007600c0b0110300b505c1c40110540205010300095002c2c3c4815208080703422108005c040c0c42281258810021400d850360010715400d4001e01401c00c08200f10a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 765205413 1250 765204163 765204203
    0xc08010915050a030b0f0f04030f180503010c08040201120227060f04030311010b040905030702010f030615020303010e0601022b0909060b03041211070509060a030c0e1f050a050904 79
    0x21a0425200c2c2500d00d03040103040c1014071407254101f841c80020741031519003507800030f0881c1c0c40c40c0a0700c01001407002c1d450403908100c0603558060007004000b4031804501e880300134140003040b10180d000032210b92000c008041d0b00d2088500c92254071003841021954002030320003541000c403800384c111808001c420880e050b854094006144603580e00c0c4034031240c8828031800c0d1001c60031468421443c0c044200001800001115121582030078000c000d035034607601c1600207040c1540510007107099119000c0300903501000460513100141c0f61a000d640750a0012680d0b04c5020f81c000c3c140507070f0780707001d81b200c1d214207403280030717030000500c0e080f03504039207850100099505a52001c0c0080c0d0002c404e12040144c01c0018007030092803450b00070003032820419203e40d00d1105105960090000300042641910346d20362441c0610b0f00f11411520161ba24401690041d004456554110440388080c50500788003245203c1182e80c01080c088103e810402001081c032409842102c100600824000c1060 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 765206663 1250 765205413 765205429
    0xc030504030e09150d081e0d0b06040f0e09070509152107030f1707140f0a03210e0a0b0103170301150327030f030c0509240d24090c0801091505 63
    0x51f80803420942ca900c0203079041b4041d04d08002c00544210b90902c0207212141d070383e071130303a60440d50000000c60701e0782c80309080c0f981040b110ba0400740c0c21180000400401250208084e1414003041d680e082e8100342c2552407045481d00501c01003100d403c101c2c82040810244100e2084d0340303000703d072800301c20048221420040e0707010500844d8400d02141c0c406210000500100d1407104100e07000d0b00c555041543d0003800502500b42c84085204000000801d65141f81e00901c0510a20300854425007124100303425103040910086440071507544004041c045035805a034101c6008100c0109100a20301099010701044c03d0f000040e0051001c2e201c400e000300c409205201406034441214003501c001c00101a00d600c034040034144201007001e800c05444004e825140070550040310390341200d01214a02e180d20a002400c54040c0c140480f80f02e4130f6074041100050b207805078031001000c44c0d6401010051354044900c881c00b04400000410140607903821050000200241e036482141d10751f0005106a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 765207913 1250 765206663 765206707
    0xc0902091201090c05120c030d050c010603020301050c0c0d0f0c02040f090b0a06031509021f020c090f060f0103090807060504020613091d07050303030c1305040c030504030e09150d08 80
    0x1030842d5103c01c1040303081210030468645103850140c00d07c40c8041000c251345050803200c490401000050650300f0351020351040c0042c40d80203000307110794200724000700642e801040052405006e0414203400c502e000f15903260bc0301c5095114960000000d4007008002c080711036080c08010340b9644414001801c501c1658828200bc0200140b1a03045052404284200410302e4501034034000c19400581e40d01011a2002c03080380c12007056420760020128100542c0f040156004030418003400a206440241c9912450042d00d8070030818541c04011002d50f01051b4000c0e101c808c0410406011440ca81c00070751b0b105001401c043c0c03509c154002c800039482100d0b4407010044d90342c1e075803805026140a03910075402c98400f0050050f103040000190300d81c48041d1168255690001e50801c2203000c0d58903000c014540100204032100311040041c0c0980f00440d82100021100c4c94a04a10302c1c0c4881c00c0c500690074100c800740c450108805201c03613400f00100540310b040003400007410b1128880641002 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 765209163 1250 765207913 765207923
    0x6050406050f060922051207050322030b131a0a0225050d05130906150807030e0601060e01031d010905162102221a06070c090209120109 60
    0x281c2d10709028107164090025081c184140402002d01900e040d603110442c81c11414500c0100c681845c0b40782c03944c80d10059104142c900c41021503414140100800a44041c1102c1400d00072142803484041d02252031718000148050b400038040307019070034030031020041c1e40d02c1071720305049801c08110384101c1e8500468844013020740000350080c0e0401103c9000248842048500c40d071318030f02ea9225611110394035050741c20050042030074120711089440f00340081004d08000c100361070711103400c0400d05081e0260311340840c0c059804148024860b10402049450740ca002d00304a03401d001003113a5181075400080e0400d40c032040f1820b0b13051010700d1303650120448840000791607222840e1541c2001d5000c96400e2500642070010032580c0c0034004409010705406501c0c0809405138800a2856203410100030300c2c0f1041e050300c0307030309021840e440101e00380c0c030f41d00d0b4402007250541c08201d038a2007511b20007800712101c0041082a00800c0d000742030f41c05001000c05100381014000f05003120212002519 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 765210413 1250 765209163 765209171
    0x2010905160801141501030b21010903081f0e06010207050405150f03030c0601140d08031504060902070c1202061e030f0f0106170601111501050307050901060212030405030706050406 80
    0x11900092050410071a002024045103117000500c00c561203110140c000d0506488032642c00702c90740c40200e480074880319000a03100b00c0c0030300e1300824003e00c0744031005c40110b0011400304a02c010144c2d0000021045868001001420034001c00000280607282e18154824485d010400c1e0b0f85a0103118070840d03180c0001e40c2244840400c115201180d0a170507802a003040003400b451000224415055800d9881150404041e00c40426a80d40c080c1030080c0c442000841400480e40c1903151f183703150790b8125014001103032222151412441541c00090a521420400b0007180c040508034906450004000d58184000c04100781400403c11850b040041c000004020b0a484800b4207541c011103010241c0e459036041500190200c40b102d015203681d09040d00015409a1103000c2600060001105480809000311940e4800300c100b8020306200e4041d4040102d4542400c550540c100c0c0c403039a00a00700c49542c90b040b0101c1d980040d00c00e0312640010402003001c00c1407401410f0040e845440009 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 765211663 1250 765210413 765210419
    0xc060d09050c010503061804020607020d05011d030a090620071503060902090d020603040204090c060207032105121b0a0c0209060d050d110c33030903190201090516 72
    0x207400c02440da80b070309040c40014802e00117140c8a40802c0c2015045011030407805e030f2103a0001948901a000009600c0011141d040081245c103402615a103805d08804104150359501d40c5522405807180b100d00069241c9020131040d44900b0651402e0501000044148a8907481340d9061843c1030b00500b4000070b40c1403d56410603410712510004081a080450804180c07100040d926007500402920804001c0301050030b41da502d0b40001d410075408403038115015903076080039480d102030740701c181c40b290256072203901442001680104001c800d07580322894269401445000800c0162603040030307000c02c01045c100301c02110300400c014605501c03165a0510648100070391030300000c01040c098460000d030000000e03000a6038048844190a090740a02081441036250011020411307a002c0070714900d003c401044200101a00c0c02000d8000d6000310b24040f0814041c802a1614001c0764810003418007860203000040718101c00700d200105060543c0c5c2c483c28545903c031000c030130f02e082480c0010 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 765212913 1250 765211663 765211673
    0x90b0c0105071d0a030212030d05010801150503031201030201080714040e0a18210c060923031206060d020d0c0807030f0908031f1802070209060a15110c060d09 70
    0xd8a0402e1418031802024000703c2c0800c0d2421030511000b4040c00248031a00340401c2c0900982c0c0d20803070300403000c00080d81d403403010318042d11480718200b03810740f050381e40401c541c05c0200407141d0700c48980c901d01c0420f034030b95401100c0c030b40f8004151100300202044007600c80a02c0320001c200400f4214046c840038140701e41c401040b5480c003d0607a200c4038640c1c460100040040040c0880008002528603076000300f00016a8291280c4000815107032810031b1080810010386586a181e1251340b41d20702d4100c0502d40c0259481c40703281600b0041d6101c080014499282140080c00302d940381c540050b081100aa0000b0b003a0781d04c0e00880804105d0007800c015140b40d052045440c0919901d40501ca003000503104c542c558031028207424403146503c101c200f260045050010020003030740d8403408500141600401c000e400c0781904a100313511000201d085454580c11120030b41d058140801d4001d2500c51040d04c84060080d036110060080ea480a890355882c50080c020204c89520b0100e1440e40520309 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 765214163 1250 765212913 765212927
    0x6120702120706091704260f030f0c12042103120c1112040f050f0d0c060903060b090712020310080d0e2b1e020d0c17010507140a090b0c010507 63
    0x4404142c20031b1004201c40c0000245915071402401d4032a0113080211801c5814490301c201e261010744800a855804105c01400504c0a0131201e8191030400314013003c000369502c075074030030b000300b880c2100e9010000c0704c603200301040c041744282441c1d03146290702e0f42c806041c1e914100026001c00c0d0b101c0c845580d545018009400b0081d00300c8412482d05050403501c05020200e4020390b8000c0f01207040c4a0040d86a105045070000c3d040401502c90f42da58120040c0030f0101400102c030480d09001074001d050410030111401b50182d91100002e4607032040c1c0145c000e400050a201031044080d200044a034400d00c1001c902c3c0d80d190b640da6040c0c060100c24031240c1c031000c4c6081e0200c00305002c40040396402d1640c5c60441ca81c0d00c094030121118540409039205940c418019505c40c9a0032481010000428000802c441c02c0d0101c40c3c40c041e01d0b05129500700c610440c0c050b0046000d032110341030300e944c0b054010000482582422040c054a490205000341c201401110b02e50395244140520380c0d800c050 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 765215413 1250 765214163 765214193
    0x40e0903160803061c210509330c060c0d0b13020901200d180b0a08150414010b030c0c1005100503070b0904330e090c0612070212070609 60
    0x25588880c040d99000d404884035007410781e5603448624403107440340c804c3c002c079170320840010f003418400c490300740c1518150740703042410809121021550350000c4411030308aea00d8498500018000035506d240003a0400d51015050420305581d07260518865503c060940038200004900180c8600508002500324560820000500d01007402c3c202c100c808c0008070791004007500d2920090001034840c481e05960740d190020f042040010940007000d9034400c0310f95200d4103100545890700d808000500007101c5a020720710710209190030050064868660003160440290f0046a181c030081080303803802c210912246483d80750b1240e040c441c007a103c01150310094402200035050342071078444010168821148007500594581688460710242d014000003944a841c8050b1203810044201640c10403443c0245205076a426010031004107000880ca6a0210003a1441d8501000396691002c0240b00818171411071044100c41c030040c04a11002d000320034841c820108140d045450030508005100b1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 765216663 1250 765215413 765215449
    0xd020c1b0a170307020d02150c01050f25030e030c0109110411040b120702010f0c0f0f08010b070f0c090606050408150402010503190b121b030304050105040e090316080306 75
    0x88900c0024000c00303c100c8241aa04071035140c918481440070400442e070148081545d2003000c102019040b03419002507124150854010000e40d84200c1884c4103442d040d5030304c81c0000c240490a80f0500e01a070b0042c100d54808074222400c240c42c07003140307070b01391440007034115414416149083c105040500880f00100040b40076681014240b0840b0300c1c290280c0c10814403030380b440002040543d4002c1d884400504280001804880c60352600603000c0d48481110000080b03003120700d62945403084134414140d13010740550b41c0c50314020b81c032508ac0040c01c00c0380a5501d00316500001405809901c46d8000515a5444640d140c2349803a000d00d00b4007407040070321000c0225030010000140ea0107004c40340c2c4201c1c422140395042203200c12600040c580b02e00d40d9034104814450030723048000d001031901442e50107030300a8920390071840141500c071b00a610403540802c034180424010a501c280b140e56111407032508407070a28425000c00044d11810a0044e602c5a20000511a003401c0079078400d13034088000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 765217913 1250 765216663 765216689
    0x1801030f0e0d08100e04111c23010f06081c0c0b0f18010908030a0c110604030c21031b0503060a172509140c0403080d020c1b0a 56
    0x20346140d4603600c8030320b802c0c8104007000c0000340740d28089040703c0c00604070710303800c0c010035281c01d14003c40c550305107850f403034843c6003442c03081c0c80000b86080754450740690210000340581d49106d1491a40b00d5494640600c9540300c0841c22030000146c450207004001e04801000031210303400840403e01c6802ca40c07502044014000980855800612507401403803290b4080c11030355610240841030494404120155420705810000748880440614010f00da202004c01c00300844540680700b80401c0143c109403a002003000402017409117100c40d407018040c01e08943c503041680026045072106220000110380d03944042540c0303103084150b04040341d01da420490b295003403400c005085078540b846807140c0045c00001c25158800240004071000c0c03100702003000c0003e51300581d8482c048480c0140b00280d03103082e20000305a15007a99040c02050814020303440c060543d1181c401c240c0c0507116528006408100c6c04500d00c404200407000c0b2104503018051034240b035010480d144036280e01002d200492 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 765219163 1250 765217913 765217931
    0x902091b0414040f14010302090105031911010507021009080105181903030e0304031406070507080a1107031a1506031b1606110703030e0604120804171801030f 70
    0x50040350141c2e0118120000180029000500a8a0342c00a80310140742805131009034100d1a4014505803031007229070010036a2201309041d0740d21788042d00c4210a0700203410000100310005003e04403580c040c03600900d001c0c103035004600d680c188d8040e24800612900781c00c00a8031002e00c1a80d800c1808860080c0f100c000c4a0025541c940f014041c082e040d811150b1072a003003501a03481101c2e84203180065070b407156924181030020202d90341202c01c150040e100001e010034403c5040300d11003584901558248030250004503409081c241894209104a00b004000701d041000145805c18081c00c500f466442d054008400540c40ca1440c10300800b418000e1200b0403034654803580740b1004e4101e600781c41d00c0a402d68221340341071500d00a01031624041e00e81e175003510310740024450980651424404040050f21240e43da800c116401b9201e90707161004070714440d00c90740780b00e0780060103100e55016160811850100301c0c5c0c0201880106110303060301076492540c0500401c60555094001080003400c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 765220413 1250 765219163 765219211
    0x703170306180916180b0a1a0c07080114061f120c180b0c0f190809120d05040501030c090f170a050f010f050a091518020d0501090209 59
    0x288801c0080070240c50440090340b120004c1001c58044040201e200307001030350351440c112010018200446420342000740a17000d40c20060150340c202c418601122200d03400d80c04c45170310b45801a11400d07145005203040020a5a424020700c1c000040c0c1e45540c4105050880810940f10480180500e0f8410317110300344004150081c40c0034142604100b070215103648008000c4a503915211205828107660480204a40da80e40d40500403012440301142e40d2580203162442c0d40790244604010f607604550545400180c41c54080c28840700003926141101c0c4032030780b02c20700346400f000480340020000704040105690500a40f01080381508010744d1140c04c00700c40600f4042c540c0265000414003519034030380a4001c012411049030031200341c82000a03003d2115018145000e600072600d4200804110f505010344900e0716100e9200c003007901c0c80010a5000005455445c094130400f9050030412409616902c9190395030700d205030000a02400c151040003001c10000d011101072041040340361038408 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 765221663 1250 765220413 765220429
    0x61c0507060f03200703110303010b1c06050d2402070f1209050a0905010303090e131b0512010e120304150b0a33020c030a0b1b0c0703170306 62
    0x6aa00e150100c1d07002c021040c16005011490000c1c03001c0160441c01d282d0100002c0090000f0a200380d45145103c88007251465580c0801c1c02030f00c0c01030f0360801500001a00c0d40c84001244034605402040c0d40341d440000400c0c107001800f0540e80d102071001940440c4507480391503a646000c0304002c6052105030780b03070854900c0000000416001d580c0c9141a0341c0b44c01241d42d00010f00c0014403014400751155001400303420b00f0711085000c500e042c3c801154440c840d0107810720465140901d0310380e480301c035120710140e9045c403a4102052222010081020780f03543c004441c0c00c0b0305c00f80010601381d2003402001d1070107801410505041d207042c02408009601d6044410a800c1c0c03100011809001e42c00005a101c43d00d40d22a0001c21000400c402c003100306414018444125955501001c1c0d5003000e00fa61114450400558160000f000030b41c0041c40c2c0b8034144d13820400d22031a0320b022001c00078481103d684448001e900c6680005c508100300311500f107080c090440c21000c0c0500318140f01000c00c03600 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 765222913 1250 765221663 765221669
    0x101e14090c01081e04240c0807051b03040605090f091302060315041d0d08040309180b1306150c11060304060e0607031d010e1b150c0105061c0507 64
    0x400c100f4086124030404001e400e0190000130f1040c1c1440c185440c000d59082034180d04280710600b40c2a4010550403d0300c1480d902d680d064071184126600e0a1003240c0aa00c040b81c41d0f0342000c600c0c4410150b1300307000c1000d0b1028080c1c0380c581a5031010640c042142c01503100c0001441050b0401c01c0001180720352000c184140e5055a03115103e486e00546520090340d8002d003141c1040c90005216a201d0f0303054001d60815031440c054480d044115071080303c0100040301c001d008aa039040d000c101c004142c031300e040c80c1d060313640400080b00e14880000038410314420040c030b560309032500f00c00c0c1301c1c0c0c00c1c01d401d565119a42c181030601100c2d14076541c0710070000480000f0752207803c02100140900c502500250300d0300211105484940c9440c400140081a40124030001d0440d10020002502e4052044038100180c01d8001c0400311484454581d0404420f0b07160b9402c45105841e0900c9081c0752800340150510003000800c0b10300d0030300240001d104c000c1e00da04030403411a4540b1404150086000425 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 765224163 1250 765222913 765222917
    0x90f0e030d0e07080a06090c090902010819230403020c0a060e130212090703030f050c0a0f020609031b01030f0603030807080c0f07030504080609031e0309101e14090c01 74
    0x41c01c070078482c20b54200001a848182d82d406490150010000c0c190302c41c00c40c2c6441101240c0c009921068840111200703000002d0101700c04a02081035640b01200f58003072010a0381000c12290035100111000b40480768a201e4044030b1035051104054041c4883e0704d110405840c1000340c98a0440b004000c603a2070000c09010f150390080c0c54000613559011900c0640c404a01c0101c0c500f403e040c0d2660b10256444260002001c3d001c0040b0703081e200c0c0e0212400d0440ca0f20007080c3c0380c80c403511850b50b014030710f21080703034015000c109036810b40d10144240055100200c0641c2c003031400e407400140640307180c0000101218070344a018400a6044094942c01010a00d80032050f665012800f0055200b080802103d4030400316000d000c0584c890001d1003034a00c075000760b07402d03900c9a0340850b603a80103501002601040040318400c00340c0001c00a1580018100101c46a007030b010782c940c00860324848515140100254130243c60b04d502c5019205422118148100c0c41b07240243c0440d4641c0702c80b02c030141c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 765225413 1250 765224163 765224171
    0x180901051804060906020d0218030d05090a171011120903030c0d0b0f040608010902011409030d0f02121204050c0909061609030b10210b0106050a0302071407090f0e030d 74
    0x900c170751541500c1d02d03104084001c41d511050b20086500b019031151032988284102c00040000354480c4094401404018050031140e40c200780d2541e26054520764070030305602c54241111b9600c1e030140591800d58039546200755903411000031a6694501c020100e0105a108000f4008420703a104100e4401210808000400502e5800024400c8a12404250344a82040004508a1410b41c88135107254400d0325044100100d2030120315941c0070700c144040d4542c0040103640c0ca001d0003210240c041500900c15200700c0200f1441214480e00a0350b41216042c0c158401c10040180c1001a24010081100c0a00c0a880c2085010740d988070018540580000245140b80c012030043c003404025550148101116180413181e0040c442d21034400e00441140103812004042d03804500b854074150081c1458110f0303801e160701641e555000d408800201035080200c2004910254000941189201c2c0648050307450650107800351030b03111b0b80000150349030100301427201d01c0010440307000c0142c050703002c5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 765226663 1250 765225413 765225431
    0x6060c03080402030a0c030803090c09041505090a080706050103030e0402121611010203010b120115020c15070f0f0213060f1404060b0f09011b08120603011118090105180406 76
    0x21742000301c0c800c8000c16500042e080442041030440203944100100340441f102030704444e00b0014031030002d40700030b01005c5410344811307018005500000d40c490400c10442d9a40210b1382e0760b03210903a1000c101996150798820040c4105503000d0400d110114040f1007d41c18501400111204035001400b1004078584050300000340341e0042c0c192075104c18841c0021510f035a9a0303410184540c0c0f0003d0040d042c050307020300104203105014103140310510b0b0f0746d00800030030407001d0902c1140440103900030f40007030b400c0c0180c030002454062100310591140203501007201c2903105108110010015200c0c8480c04e1031001d12000b4864080c8200300c1d1440c90041e14590841808500203108503080b40959110025000c251051068010320000b0b2081e80d400d645082c11402000b80c100c1d031000001d1190000b000280040b440e44038045030442e070000c0000071000311804201e581070303019030401d01d4040c48030500d4000626140003428018003098510035084602c1e03001c401e0140b64020402422203590f81c11030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 765227913 1250 765226663 765226669
    0x12150903021903020115080610090b0402091003150b1611120703030c11100905310f0506030c0a050105180a0b0702091510030c050d0f0e0d0306060c03080402 69
    0x41e00b0301041c41c0b03000b0070156950034003c0c060410201c0010b80c42042580000b910035000540c98800d0b6031054521420340d0400400c4000307042c4100703c2550158080c4450805962070880390400b0345416140040d0b03158800c8030024140e50030b503010b2100d0003014058058503508090140030b03001d9010070004c16001d0258002010240031280c4682e5900c26244040304250f00f108645040c24040c1001c04076400c030400820018003442c07403c0500103449503204000c5424825000c8402c80d650030f00c52451004000001d081e1404003590703e9400e00d466005a21200b5140d1041d40c0e00300c0d805030090020505400049404007400e441203904000d00002c070b901c1c0d26083c01e1441c07800e591000f00190300c150b03034608503076480fa00034113411317032042d8000c2010825003145001d43c20030004019044182c012181a0705900924989108000f801010401c020b180d8a00c0e200d407422189010400044007072034a00f2062502c6400508003040c1840c01340d0902206812040020b01c0e60703031606e00074101d0780d0350740f000c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 765229163 1250 765227913 765227923
    0x2031c03091a0402090f1905070c0516320d03090803040f030b070f0206071407082d0c0a020607060608010e01090506060f060313031b0302030d05011215090302 70
    0x54401ca00140b09000700459150b03415024500881d241c69064a500e00711184c4254161004aa000d04082c403842c0038180681040c0d50028943c1840300c10b0700a80d072605800c0120140e013a406020801c8018007000c01c4440d400d0450802582c3c1405645210200140b800b90401a966102d5000880000f040611072422040904818001d44e900d45554091034506041d01d40011900d0181b29400144400c2c418078903108012844da0080c545919031190558010510a41202d41500100500d8000c154124001c10310700c141c0e8840300c00701d046c100042c0940c035080c0e2500556501000c0003520001c000014403002d1881e011280c46079154580d14044005010903480381c4019400c01031016800b0704107501521a040c001e00c04d8908a80d11842085200c00c01844415441a01030000c260311843c86442015603510038100140d5074800c088940000050b401e800300d0040e440080c209050205900510740144070100c1c1c0d8840c4c010099a40604021416000306070007070703452403114141071017009 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 765230413 1250 765229163 765229181
    0x5040915031a070206060618010c05030918041a07120b0f15070309050402130b341b0609030f0204060e071205060607020d0f05010b03070905010602060f0402031c03 72
    0x41280002d001074407100030042e42192800c01600803c000103040381000b070100d8401c481042001d0403410710403c01907800e2580390030250342522003804295000e4035030145200760003000000c0000c0743d160501d007556900d46240c09407410001c51009111800e40c0101c1110441c10b000d000110f940000c03500031900001c207029a5542c0b082010340f180f00001c3c500002442e10034069952503022a07141c00a10060348200c208900300c1280e9032030704110384100c44001d041503901c641004907141d0702c041d04a901d4900c1ca508410070664036502e4060820155609284c1790300b24403480c0990041c54072401900400117480090b01c021f8425a6040855031950703c540d003e0107200307100301c559061220000340800d03c241c0c141100c2615110106000d850803405440c010b590041c03409481854a81d10440c800c800c0510071101c66489421081c402e60f018054400030344400d11000446615245000740f070120701600c4e00c0d031390702c0b130550500c800341e2004100741c1c41408444c030403098105400d00c011802025450 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 765231663 1250 765230413 765230423
    0x100503070c11150a08370b03060405010c182106020c0d0201050709080a1707080c0304121122020c10020f0901030c08011211010512090106240504091503 67
    0x1400462500101e00041e1080c0d400999400956655501480810350704400d03000030783d0017226001c51000c007840d50308246c140e83c0102c0c2c00f01e00c80b404400440d181c090140d0341110f15035121084526400e50007904001402c03003442c008030700c0502c0c1141d09110754103461180320845140301659070a000f1123030100c030108001d92040750200c03094503c009000303100c02d507101000244024400555203000240402d065600b005010301c0000035012001200d9000c079034111002034043c00700d0411075078103201402c028101c110702151b81004030724040b00d00003c0b03107901c540304404000c0c8d0a681007908411882c401340b252000180c3d6984014101440c1009000445d010342e800080c808074150044009010800401e80b02488900348030f1000b074405d60024018045c540000486540104d41a10107100c2c90030030605003d45001028006296819402c580900b1140e443e16020000d004901781c0c911201075182c8409002041d540c40d0041c028071403807140803602900c6030b6960f618403900106450083da402 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 765232913 1250 765231663 765231679
    0x71407050a060b011b200114070605071e0e10181205010f0c05030c0a03020708040b13050604180f14011d0903040515161b030b0105100503070c11 64
    0x51078071402500301c0031402c3d030014800901c035001400310700222490003540801c140c0c0e8109480490701da1603041d911902d904000890080e05040c80c2c03d1001058010300841000c5a00d107012500a0b0050207000c4c000071086c400c3c09004088580d01480510462404803804040c503a6450070483e16490080210004d40c0b90091000034004c2d83e0100c002c40b00d40c0304000a0000b02c0c5034440b184203e6200c2401c03000070581c100000707110700c00094014142e032551030030014148001d41e1221012a0816009444c0700c610000e4818a1030049076a400010b050868001e4035107820080c4c0c40307030a8501b40001c0350002d92141c900008448554022030180d10041340304140321340c2d407040c10380c1e19043e10301030031505040c002011030807000001c001c40c1c040d594041c040c0003024502d280008510b40c4280c40300781c101d100d90701880e80060480c2c4e42c5454149041c0600e00d00a40c15030508203800c017010b9001c588034503510440c4170201e0390068140d035482501ca04000510300703000d0030843c01410550446951113410 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 765234163 1250 765232913 765232933
    0x14010e090a0903180b0d05060306070807080702030c120405012012090a080d08161103030f0c0d0501080d030e070e18100207290f041e0606030606050f150307140705 72
    0x15220240440140c1b41d0028040780c0c131180e0500d84c8500b400d031042000503040400084030240104030b415002070092040f04e1074400382032520f0b8146030364032401002c04240040e00308159a0311040c03800b81e84030310000060042e9143c00740c1665600301c1070308056209001045801c201d43e2840790f03002c000e10507101550a03030351004c10000d082500031a446d032401d500246a40c1c0b0414850b00d808492a002c6000071440c544440000942c4007000408280045100b002500c00c40806801094001e0030340100500c508181c100b80a0242e8070060418142a03101c0d060400489003118007030b54005014a007541c1106048005881c14880d501c3d640e17403031860001803660304002c01c540c1050702e00c1c5d441070007842c0e484801051902c0c0c070358425141c140505081101141c0415000c401302110345c8176150302402840001d548400c1a07414a50054a21550b603c9041100723040070b80100480040844034202e0803040d03000c1d80e10080c040a00741600b0000e0300c0700b5807100c51605204a4050640010403201ea13035107 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 765235413 1250 765234163 765234179
    0x1020f040905010806090c09220506062107030602090a030203070f410102160e09010605300a0605150429010815100914010e090a090318 60
    0x8054030846901e00c1c50040001500007000c28924002c4020002901010f84d0000401c06603c0001c1e0201c1c452030540a6444200e00c1500a48415207200341d001d081540390001c204017202e000d10185403205c2184024804c481a800700e2807406496020200503100c078681c0700410419a483c2e08001d425106159000c245158500c5c20348080740d450a401c4000c100c0803698080791034012078058158252841d06e00c0c81c00d80ac94008008107040d06104480240000202e98035909845a000e001961007901c00e01202210138058000a00f81c01d8419616405446800c140c81d00c132807501100b250302c0e516000c428419818010300700d40d40d03000001401181400312120440895200c500c1d13105620380311300460004410b10413003d81980d8003032244070380c901201c01542c45400040c10403595200e02200b01031a071b514011030b80314101d031a546198645003800340780ca507118461a21241807049820031001c0d940c0d41c03c0c0c0300c2071748240200b00118041c1c1c1d540c54184e6441c000d50454a00355200500302150b00c3c0c1d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 765236663 1250 765235413 765235417
    0xa05150d1425050d0c030209060409080a05090a09050402010804030f02010e01091202010510180b010e0d030201020a0914060316030b120c010f0504030f02040905031c09032c1c0501020f 81
    0x241400304400700c2d030703440d010003510b0082c02c100100704244040c01000507161085149500c030740082c01c0030641011f0b030707a100c000941c0301c0301c81c05000c80d002145240341414107014842c00f601c0c41c0c0204001c542000d4002a1001c5070060004080101e0800303038401403072003900051080c840940c000d00801c00c461405241c03141c0c41e44039060041d0302c1c00000601169038191801c0460350b802c01c0703034144201000d024001809010369001e05000ca080e4005d4500d49808002c072002501950005807201d03030202c2c000f0b110440a0f070005880000c5c211929589030344030750440b5084500d00c0d024800800580304203401400d0700c0c035000d030782c4121200d050160513003022a048104031800d0382c5180400203240010f844c9802036000182c251102c0465900040c01d01e81d016952440c02042242e0921454155400d20740320010302107001d540c0c07211880300030990820100303203040f40c0c0b1a02c1121032502c80c1d81102070082040c1511441090008860380300d4548242602c0d6086402c00000c0d56241e2004e4a40001130b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 765237913 1250 765236663 765236713
    0x80d090f03031b0c02011218060203100b120c13080a03120e01020a050d09020a030f150513020f0f060418150803070c090507050d0501120201080a05150d14 68
    0x4242419001d400c00800b40403242c1c440640c3e0b849004040f00b090300115070981151907031050702d5903211a80151410b0545022014a00c203910159880c90043c1d0014842401c2c3d50146111a100f0302141c01c42c0359500681c42ea03c9010400307425140d8412218880c1804540d520176401805101d00590170b040d4440c80183c010700c4001010300142042c43c590a00700e104100d80240090000d001802c0c00f25400e4120b82542c1e030004081c0740340161a030700c0300f2081100d07105007154440314080c00442c041a09025450344011004068254445039030045002100035240061241096020b86100740da10001503070083d08040c0844462841c44c50403010040208140081c550300b000c0700e000507220030010440d19290703817208144209925041c010005480090300082c2400030501c0288400f91492049500030800741040000440356030001412001c4050070102c00c60b0300b044100001d94401c00e03000b10040d00c0c1566001c4070040541007800c501c010744c1152103580d01035044c41107c0d0140450205c011 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 765239163 1250 765237913 765237917
    0x5010911090c0a1d040c18080706080f0a110f040617010803040b031003060c092303070b0904020c030a0c0b0f090c01031109030a060f14130609080d090f03 68
    0x10100c404104034050400711420041c04104200302050a0303c00d11604c4103101c00882480040a00d507800181920314295032080000c00459000e029503a1881c0c24400038025100a0700c82e040c02c00d0001050060020242c0400c01e03121400b003414450594054010000c9550410380c0302e00d100f000090790743d44103100703a0300020088021021214001c401b2903048400d4640110714082c5800781d01c01c45500020008070345504c0f030003000008609a4010f014442c400d80da280e5100c1d900385403044c1034200b00070602c10701d0511203a880241c04d4400141030400d944501d1140d81d01c60a1440009000e80702c0d19030140304500002c508120b21581040130352484a108050f1000c40d0b40c2c0d562107040d070400c000c840307000d5150b22942c000c803500e50003580715100302d149034007000e031901c948100481e00d8100d003408111030883d683c1e00d04038081c1029204000207111200540025410080b0b0f21442c18461440013130120350343d07214413a080111031000c580540c030500f881440004102d04060081e960040c0c81600 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 765240413 1250 765239163 765239183
    0x5010501090b122a0d0f0807060501090c090b0306040209120d0809161e03020904050d0e04020a050909060a03120f020c0406060f0c0615081b011103070305070c0f03050109 75
    0x1d1040b0007188402002155244070042c442504481046001010030307005c0c1c200741c410f00f90302c000c900880c0d0718501440c0140400c641d02d400300d14190044810503840051514544803030324030300c80c1d40300c00380c00304541d1001d01e11500c0e031b02c0e218000b800901c01e000441e5840340c11035503110340b80c074008038604421180350789070760312159a078030035403900c0c0c003a00d0603c2010b60500900600c010304541c0c610541c1207495928208955480360b0215210040c1528107a40580c04030f1420200c581e40a1500c1c0a0303a08103a45c254204050f04001414030300416500034891902c5400065281d00d895080d000203507081401310380b220140a20150108041144000041c05550010420741c105801a44100c440903555a00c54071001c4c582241c81d00d06c2e07800111a40758842c4000c041030000c0280450180107100043c0c0340e24050300608a01c89a92015064184075005140b8000c600000c8113842500c0d416051182d44d07039440b031070702c07882031120358010540c2e030710315114040700307018055100d0014244500c52402c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 765241663 1250 765240413 765240439
    0xd06030b0a051b0a0203190e03060705090a030b0a0f060b030a15121e020604170c09040302060c0708120c0711090103021005071e080a020615010206010303030b0d05010501090b 77
    0x507050300d03000c0b21032814010445507000d025040c0b610091644070303031034419242480141c20b00450b4002015052800140041e040700d038a52800340100340e0414003509202e4586882071022614290017444080c00c1d6504400000e1030744655500440103009258800304200d545a40001c0f084e500262214002586008072041c4182141c18510040d9190101a2500c07942141c0e5002100340c0c10510b40342504102002400060b110344028101500c822400600d03c81d006081c1540780c130201c60030841c4600191814000400e8001c5983c7c0d41040c0001101503403810f050812110b68811104000f0700040c0384170400c1201820701f0060503480d880303005581495115001003014031002804065840501d042180210b035004000a18070a8865040c00443c108066512802d0900082054aa400c4006130302d08405905100d219031160030340b286041141c00d0440001e60b11310050100030145580e031144207002d80d4412840ea41c060340d02c400207008a40e114081c12001d0281e26028a0003200d20511134 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 765242913 1250 765241663 765241681
    0xb030907060903080906090301020706050a0f0c0206101511031210090c17131a010311030a0f121110060305120405012a08070530090108070905060d06030b 68
    0x1c2c4044a07003240300c542c01c16003503204101d6694082080554159420000381d80040e0f00c07801128403a152802c0000341210318050703003174150740004004c90115003200c8100301d025035001c00b05c1410b89000c00a5070314600c2c40910162003181072910750501c544000300381e840d01c844258149611440740c2940700f480b019039400ea84019924440c0800011400d90940301041701151003e00740d102c11502002032540c41c480d01c030f41c2012100e205110031030004200050007804208441e0800500d0198000c0c22400c50503102d01c8111841c60000030855210040d441601911581c1001800b0000700d0559801a8900310100e0040ca81484102c5880c0030707007030001142940710410b0703c0c111481a16615035201c00c2c00c04180440610596144031104807410150114030480081c000c4035110302d0040055420f50382c0d208511308103a0f1900107180c0100310100300b6030310811059075051007083c20302c0780280c1c64030003065400410542202c1e0f04000c011800c50780c0010359801210850f4010001c15036143c541c0e01d40 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 765244163 1250 765242913 765242927
    0x5181c0503190e1018090c0e1e0a0b0a03020f0d200a0e0d05010608121b010516081905070c03090803090303040312090e01060c0203010f050919030c0209010b03090706 73
    0x80e080e8055000c00302d0007030440c0210700c0c1d072244000d05c50803203651704c3d119841d64084900c603107074030302c001b13070fa5641001c80e2410240100e5401040400282d180490321500180450140d4090300d16100008100303909000d00036019141ca00c486039001c1502d44185084690080ca41c4c005d01440d50011108000311400717684080390012800d5690350041800120107010805910400449482d980d41c04c0000302460705010000d000482c41d4408e9a0b5401c0c80c02d00f260401c4010b080d07010059241c00c0500640304201c40d00f41c4841060303401c20240c40d5641051220880305034011070b9240c0d80c108010030411942c4100380c14005442900d50b001c1094455076695034a0242c44942605544104814070119403c424100d02010280c030b0301840190709c40a183e59142002e9100c0c1c030114144c40c0c080c0342185001c0c05000c1040c20f11050800691408081036990b5100c41d0604a0812000007894424580300d080c040c50407940140c410145544d48072035040d4170741c1c404c480b514928007e5050200380c980c0300fa90 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 765245413 1250 765244163 765244187
    0x506040506130903091212020d0f0f121503031e050408070b0c1c03050103020a051906030b06090d0f060b01080f0619081903080a020a05181c050319 65
    0x44298100382d03069400c030003861414802c0e030174880320303401c0011382c210103917102c11207140304121800c2c0b0781d503208402a10300140c3d40d104106218614204031001680700030f10001450103450109100c40d03409802070001d10700b82c83c0ea00e880914582c008014150041c0e0344c9982810304000100100d15503003012141c60084e03006d40e80d0300f0340280c201003245404000141141c80780302c9007507034100350503546803840e418658503d4002103900e0308010000d5140014001005000a403005040412070012401c1d003168540125010b160f40d442400c00ea640391070081c1c4080240c041c3c4481010012420520414441035000b01e413458104038a0801d10b520841c0e0580c01003920039a1a1025121407013009100f20000c5842c00c200d901031040000e08010411000300320141c40c00c9411502c03130007420300502080300101074009086c01080b800c1d0308241e2290445600901e0060702e0051504000d0000f03a10308821410b089035441c4005203a03061060200c006e00100c2203490200088403c1d0f1101603c61100b460303 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 765246663 1250 765245413 765245419
    0x315060c0b1311101d01030204031a1008070e062701030f0305091503160207052101230a0608070506030c0901110f010e100b0303041503020f040e09010506040506 71
    0x40c04507501c180441e2050107100e103d40c0b0290400592070b8003007220410300106480000e008968048107034100180c44c100c41020a00e419440c0070305540b540208104001000600811820300050020f626205d50401900480301501e0425079200e40c08012a6800d41d42240700d040c00103c0310301408140300c4030032030300300501140f112203a10395180c54a081c50f008806406002d8208045502552081d603602d50000100e0303500c0780c4130304010307980040c0081181150001d65208010510440d900c500c2d11010180203428200610300201c410300340035009200c4108000306800d00e901c21200c101d43d5450740700c0e1403a41000c2280b0303692039001d542e03200a80c0c840c0b02c1e00b005040000c141d456000da0700a10342468103041900e550500101c24074a400b0445140c3d130400d9645101c42d0000107010700046856107046402402058010030000785c40f0b1085120700351382243d510702035250f01c9001e50161845142c1400c030903038540c0c1c0d0b80c4200496000d0308481d002201c3d440d06001660600e054842c2c1030081c0009 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 765247913 1250 765246663 765246683
    0xa02100b09041b0510051c0b090c0c210a021b0609010c060e070902031e01050901063020070f080a020114090309010f0807021b150a0315060c 62
    0x540c0f40c203004a02100900f410007840c200000c521504c3c3d4500c160070840e170607680c1035590040b50036080f02400050091510441c01c3c015000034507541c0c18074403034201580c034590699510741025280d01d41440300400210070407000900150051800003e4000703551541c0955014004050300b40242d0700d00b0110039680108144500d40003944141c1042603828450a000188001244039161510405500c680b24068001040011034442c40b090016140c44030f034003a00c07443d4105000202d404105016103000c11500c1e0f40740070072814200c8000742c00004d00e2185003080d08001d0320114003608050100e1140500a80c111303003101c3d504d801c1241c03a86500016454480000c0d079882d400190f00c212056400c41d0748030004042c440c401030071454000c1d810000110341c2d503e1100c0c009030102c0c00312a0b40d881402441010011305030f80124a5802940342e825000c01103141d03101c0003405c00c0e1000700002000c400003080c200c0c2c0b15601030740301410014034107404c0d90200f590341c5000c9804048103100100540b00d1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 765249163 1250 765247913 765247921
    0x10803030702071811190e04091707050c0a0608010801060e09030910270801140603120702010c0c080f010f020301120209041e081b1216020d02090c0a02100b09 70
    0x5144240450840c80106060b0384000c5a172145030881c0d6200700010b4101d51001100d40c1d0806100c80c00b02c134050700c0912149150b91106c3c070640f091840c0c881503005000402c04200101840300241c1010300814403611186c032814024201c80d4240141d1020b5840e144000c0f4010350007001c22813080c240c500085d0b01c1c00c4500310170300c10f0750b48030311078804240480701002038148060026540c01000a11003400c60962900125a00b50341860003205e81402c4003c080c01a41e07140458421f2810001040190350340c006480101e50180e0098005005048040b43c0402c3c1400c001c074081c1041090f00e0020300045040c18000c03000c0384020301c00c0c0c04003583d0181440c00141000328940394018001c803100d49150080c00ca10001001c07105200319100d03800000c0245241440c82c202c11160684000146000840c2d40e090404501c940400300c0c1c00e11000341650380031075071070040e0403000d03a03809040b002c1c243c00c0100f00000183c005854440c0980502c4101c280ca1242a2242c403103111001480d450040c2c030307 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 765250413 1250 765249163 765249179
    0x303050c0d18140d080a030f140403090506030c0c0102070b0a0b01080624090603010b07150203101205010902031005011a09060d2a050301061704020306010b0c03090301060f0e01080303070207 84
    0xc4200b07107900200b89111322800719415a0141c1001800c41c0c170045854440c900014044458680c802100d01c8009014130010070b0f070003041c0303009640381581c4c5141e8949070640462a240600001c440360780d0300000d2a401081074035109240a20b0072003078180a203e03c0d0400558902d101155225000703881c0e0103c0d4011040340104142400c1d042016061810107040040341d1594801d80060001400000d0314070f041104c41114080c40700b903c081c0860031414008500000124103100740500504100c50310004d0100c00c0d4003000b8141c5e4010111072444c0c400454a0015081c244504048101c688440111500040044a5403410002d1100340f920504051400003803050700322035000035680500014030741c040c101c035050003a00192149916580b40c035000422002c0112002701090604800784801624009240b90540e4000090282c41e91105000d0a02d18042c4400546d8150f0038800c0000f91405008800c4041d02d20318003c2c4041681c80700d8886540384011394a140050303100c003004201d070030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 765251663 1250 765250413 765250439
    0x160303140a0e1b0a0509010b09090711070501140d05040b0f06120c060309010608030c011512150f0b15071a09030a1b06050103140f0d051c060306060303050c0d18 71
    0xda4001c203c03c072540d81718408201c0921098120710f10704540021003045918100004036803041c0140340c603082409840c1d040f1034503000d9900c1035a05000d40c90400d0303d88c609c13403002034919801d00e0607070401040c94a4100f181e07400388165120116200200c2c041121401e144071002c1800018a00401d0003502040c01e104441d8001030018005558800380499142420300c000c110000700f01c800402e1401551241a040c01c04035032000c16070b680001e05410010b10020071410030383e840e841001543d02070061400016000311b0501074ad000e400c1406440b0301c4c10301b00010f44015030103015090480c0c1031703110b03905070700c92404ea901003040e61061004451840c85001e500c0720040c03940c50000000001030b0741e250203440c000c0e0070845100c010034081d42c01c80a0100071002070713440000011306481c5103040c80541284155003200002e48000340c03070300c0c0d004c0d20b00340c00203401581d201c50708001907641ea0074000c0080c6c01c81c01d814080b5001c2c86247c0e1010511078104c082564055400d25082d8034070300240c1d42546 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 765252913 1250 765251663 765251713
    0x21031306020a05130524130503060907030b01050907170a0f0504030e1f1d01090b0708120c090307090b1309030e030723090c160303140a0e 61
    0x116a4110040002810303600182003140d0701d0361900758a4400302084e1444504190700041d0007402d00f10701c240101d07104070f42d02500258030000101e680721000f41c185a00c03101c181d005983c05104039014001c0d05080000c0400c1203902410700c010300c136601c0303004000400c0d03419146200000d036141c0030022400d05505c03810340c03c50b4400100180b4140302140c203109032402140c042c1c001c03c0b05203490801c2070030f04401003a0089901420031400301c05210026010342c04004001707007500f0f40e144c488907150b4041d1904a001d440c034000c596865a2041c41c161080340d1100203210344c200030f40c070007003001141040240c2b00c2030f07880140a403817100d051040b83c0004101003007485620200d552807900c0300940522803400d00501076038480c40c0003006841414035000542e44000c03990807550442007001d20210384a440c890702c1c1258140240e07181c0440102032802801c1e0005504595040d00400f0180c05500030f14500d099500624a01d03039507404010106c0341030807110201900520002c00124006c18420300302 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 765254163 1250 765252913 765252931
    0x6052a1602010e0d05102304020117100b03040f050c06040f06390507150c02120a0512040509071106040f030306081509060c13150504090515010306082103 68
    0x42c89016259185055031929981401039a10031050b108038140c52100d84c00444c001504000c2400c2c230380c1c0001c02401a85000c5c002046882c00429001d104504c0c00c18010205a1400d68490070b081c2058501041c00074411903080c4a54800c00980c1e041100c151400c80769551b100704402485c21100796030300340c01c50246403150101402645d4010b01101e10002c4500d6040c1c4c020b00341801c41d4500b2900d00f9a264101d120101441d15146c90711036401148402e07004e5050301e140c1144d40d022070280349440d140c2d013030040c81401003456001113403c69402500c11260304407012030040e02c5248058600b0204c4032114a482c0d040140081c0105240100141441c0d200740b5000410568402c4980d040500d04d020f1144107082c90018003000010400007160800740c40c91407035280180d41e41c0300480e401c0c020300c50341c0b50120055007509805805201520000d007459070080c040c514010384c1031810361000c4686d0b14042071030000d01065030000043ea0a00028070751041580400c00c0c0300c0c80172070581005020302c0c2c07 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 765255413 1250 765254163 765254179
    0x90f060c12020a030c0305010e0112140a17030f06012f07030204021306120605060316170109060501080a0606022d030406020303040c0b13090e030706052a1602010e 72
    0x40d201c1c0741c4002d00c5038840c03541d8000354032030321074400800740d50040c6e01401070312840500500c2000e00b40400c0300c00007544084043c83c04a1200c0100b4240359920f0400b40001030130180704a18035001400561050b041c0d9036601819a6404006480c001c490180b484c1e10020412904c1c104a00c40403502204102902c00712401255a5400502a0b0340b249501c16140c20b1005820844150000b2a04000400d10b030000e000c40b5041c6000300740c2900000740b1140d210044240880100350041103072480d030301460360808243c0d40c0c5603580ba40c05041680306d084e0004080030002001d0203064400c900030b80301c0307542c09026184074207511070302c590031415462024503a5020321410b0b0140c040005000a00392900a5500c03440c0a041c003d00c1d03c00c6551003842c00d41410020758880d601098284001d8445030f0500081004a40c035203185140501c0c2c10081c501450a0140403c024030540c5004182a0707903e035400078244440700e190440e001d2620115109004044241c0056004240d2910780040c05403601f8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 765256663 1250 765255413 765255437
    0x604060f0e0d030e011a0d0204020703090f2405091e0a0503060103050d030516050d11070f0f0b0705041a090303120a02130605030f0a0504050f0304030321090f060c 72
    0x10b0520416081c42c1000c2503a070140720602a40038003a0010300e01842c0354400e501c1803143c0100e42d5003039040d4402881181d00145180c10580200d548001a1000394901c1261030744071034070301580400805000d842240c5215011411a20070f40c1201c0850802500c00f8121a40460003000460401254140c0c4a2408500400d00b914100109802540201d0007030604090030b481c06011940041c1a41d403040102c46407181c48960440101d401d000407012000425003c190000c00e1030b0300603580001c0030540882381e100705000002c0003038440c96000b00e5240328640c0300c60340c00344e581e840340e03100b4480c0ca50405a0b9100382d150546010304103554000e025680b5003a1079004140d80804100c030500035540c3d011901468801e0070303c9501c40a0003d03800c0403881e6040c00c1c07240d03804160f00107110303424450301c5800250402800b8800203500030013003401c480e141c5031607140140c4251000d0010200c540c2c206280118200d1250041c0e480450300208409100d0350207469900142101d25089014010090501 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 765257913 1250 765256663 765256691
    0x3030518011b0302071505030c1c0f021902060105040501361401060207120827040c0203220608070c1a010b0d140709090902011106181606020604060f 66
    0xb0500c02d03442580905041400c01031043c044580d05010181001020300c200208040c4000840e03654a601108000100140710403503009013088585500c42d0070300105448080d050480b001c505004542d40a81d1160384c1c0f82c1041c841141ca00344502841e01c0c01c0d02c0d12200e90501441c0c1d90070701d41100416140120800d201d41c41080d10880b00d01d11010000c500e00420000d0307414800207018220040401351980f80c1034544940e00c5c010f80c965070002e2001040200b050b19001034507800c80e02000f81081c4040410700c500651213070008215481c00007140c401d850f0719005000c0500c42503400c0c6480f0201c4640b6550b00031103100e04480300886440700b503001031401803980210020300030003101c0400765598011003203003001d41d0140031091110030505810f100440c2e03004000d40003540c02d581c10026178000f16000480c0e681c00f2441801d10180184401d0040d200ea0003055090310a0390482150703100110640b05000c1a0094401c0700d0041c3c2011000c1000104036400000d0030041c1c030117000c03908054280076 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 765259163 1250 765257913 765257957
    0x5010323090607080f0606030a0b0f0a08030414030f150705070c091b02010c02150a020409020d06030507050a06020703081e0d05070206100e0402090711030c030705070f0303051801 79
    0x41c0300e49940c4040b04020016a10643c216031160103000054603c0c01c0c004007044503030001800030000c1c02d80b101280c00e1a0b80b103070310728600c102d1002014098010f0741d40d010161654098014040c0301c868510b0300500305e060000e0b02c6100c1d60070b604000e12511030012000007040902a00071800c108081001b84003180040240d913020706000800004c0e0803040700540881c5200c0c0c00d000700156414150400390f2180c01042412113802124080b110603564540c002009209507000000c0d803910100c0d14a40c1800a0303070101003641e21450817650001e40740e00030421094503900c120030042c0d01000c02400041c61480140c811010250040314401d1511070f50100380d6080b40748000b55050f9241c0800111540c100402e0307800c0300b00900080351032800e003190b000f802c1c60001c1029000e07000c010301080b80301e44554030802103080410103413500d60f00300b4441d0580700d504c1880d09540034402d1b07120101d082a4008840000c40354141c40343c0e460003401401a101c162a421a614140481c0d02c11412401410a00c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 765260413 1250 765259163 765259171
    0x90b01050c030a020609060f0112150f0207110909070806011403030913231006030911100f0f020114070c02120106060c0506010b090102031b120403030314060d030905010323 76
    0x107085c5034a0003010035443c1c058001c00074454404810010850700070003480c0790040315084002e030100503042d504804043e200b03d281c031000081c40040d100c424004060250160007904a610241503103496480c1903889030705000701d00150300007100410120a0091240b60740400107810380b8100301410b0000b42402402c01044ea01d4562107004001010320200c02100c1003010540703405959003800c0c60b21650070304060107081c06261380c031304419082c0000d0380040e1684503c010401d61064085040003002114005160300100300e40a03d03000186006008510480d0701704480a4090b94500320b0403105e030780742940f0503600480c1510380d510030740c402030080300081e00580d100c03a0900300a030324005103401f40503842100d0680042c000b20b07503180c2e4040b0031242c0513003190003140d188c400f54084041c1070a154003946040f04400080c0041019019040041800b0100341603145030742d1010140904032104180060003d6a200012b101540c0681d000c800241410b40d0a10781c0d0019000e07906482040c161 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 765261663 1250 765260413 765260417
    0x108070e060a0302370c030c0b010b0405100908060609040f140616170a1d06040615083405030a05030705120f030a020901030b040203190b011404090b01050c030a 71
    0x15100101d10b81d44800034117103c0c1506809507801c0c072891000130302000003030703a41010024503401c2802418458038211000a810111101e8135503910f000c80b440070761151203018000d184903000100f0043c011a81c0604698650003e40002c0d95040c0800600b15401401150100d0380242d2078004540b103400c5040c41e02503018010141c50500802d810016005080554200940c0120540b50760721400c40d59034100036500008612201c40406400140c060350b0a10000340c230502c070800061100503040303002c5104605000303080080c4c84d2070000f92101c040f801556140e00340342c036402c803030100d5401c007000c241c0904e0313048652282d8507400002c1c20705145050644896001259607020300ca014400d0240f2042405141e600d014149031a09629000007400c03800f1180d4041411410780c0d002e50001d40d50060001c1c002c540e44d03c0e1151040d8400e8820282d142007032442d2450854065002d500c1800c200302905c0c03140d50800f450a0039500240406022240c10400280720b0046203840800c0506280038541d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 765262913 1250 765261663 765261667
    0x603090201171807050d1109091203070302030403080c04120b0411040c08190507020a0321050a2906090d0f120801030b22030315030c0f081506010206060108070e060a0302 75
    0x25900080c40c044064016034403943c50100c0c0c030000112500a000e171001d00a0350300119968279060490b0500500710404541601300104220f640e40c0c0c113500452240d03109440310380710f0751034860020f513260040b4060100505249295540440c08400c5031903407040c4030351503070070400e1170010200d4161348040c03400d40d021404143c18040c5c22200401d2a4905e244840c60811007440c5c035010080d5902240038001e0180110b1110492944070704080c009808900401e007405682008d540e4400280302408848085680741150451010841e098a120071600100040e09203c440c804010070245080411240340a208807400b00203040c02034940f000315295250341d4238940c074504041480301401032400e407155403500c811a680e0403d555500074020b405184c0007660b04070721400e00d40315000541000d4072600c0d055000007490a054205001a1400c0006035203408071007005c014100c49069402d540540c2154000030842d502ca0402c0342c2d0301c22510f20306084446c48240c0402c20b641d00620102c0d00007600 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 765264163 1250 765262913 765262951
    0xa080f07170102181c0c15020d14090f0d0f0b0f090a0c030308180604110f040b1c170304060c0e060c0a0b0a0905070b1806040807060309020117 63
    0x1c90546420000c502200035860b000c1041130b040c1c0b030445641e1189105000d000300c1480386840d071041045003c1c2d070002120b2000340e140d03040c60542100a100b844018416007009140c900e2040079000c04100709650598106a024010080c108003000308040e044410701360381074081b40300c3ca8040798105000e013007059501d00704909000f6141c54000c0c041c00b10359008807001000a05c5a600c2401161380520304815607403505409900c401c44103c482d1120b5100b288144014841d2030203841e01407003821120402c00d1268001030105031000e085815a1204108104a2840205041d6811003c0c403603100034101400300340c18844aa0402d8905032356440d0340b80480c1d100c8540101d100c00036508116085410120390b1074010341d07a040c040301c004120203103000210790744803110307004651015440002d0303a64040d20f41c00d01c0103182c0c00505c0c0d10040340043e41c0f00d030182414014126419a4082000341c00002d0403c00d0076000742400307c0d002c0341044075000c02c00c00c01300700c0444124000c0d07030b0205e00f80c2e040102c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 765265413 1250 765264163 765264179
    0x15300221100f031505190e100f06050102060411150a03020d0632031617300703140f1c05092a030d0810080c1804020a080f07 55
    0x420b8010548494488a080c00842d140c160742c00034450407040080360903076070f21044103c100c030400345c0326002c2800c3c02d0700c204001801040022181d90f4010382005901c14180807542a2505881800d002d07800080211380850350b860b201c81e584040c05002c0c00d4288051144401ca03590020740e1a000080d40032661808200580c00765400402004424a0082c9003078103070b9071110301c860302c041a00400510b009405c0d903102400829008041401d018942c10341e1800d84060412035440c0f09402da0240042d43c440400881941c0703944130b20100c07100c180c041c62900c460299940003500940a000d10b20541d4018590044014001d101440001d1074480a0011030516180350603240e91802d941040204500f5060014410240ba014400310f05085c050382c540c1c90000c0019106181d4041c000e90860484035500000502c3c000d21108401d0b491690b942e03580c454030707000c10700800791341703d050041c01c0c0d030922210080d1703d6002400203200c0460f0309d0b0703a2914185801c104803e080065044003c2c1000029 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 765266663 1250 765265413 765265441
    0x114010609030c121e060b040c030e070e130201050a030e01021c051b090f060415020703030206090d1d030c0a090b01030c090f030803040510020a0915300221 69
    0x4a02d207a24070400e94030b9a40c0e1781d603000102054085100e82604402c20a021307140e00407400c0d00001510405c00b070392294100038090302c03094460310f85c0c92042d03600028010803d081140c1c440c1f0748801c20346003000c203950b0045a0b1540702080d01800c040e2986030046403480300b803000300a481840151600e0fa900000103010503600010030a04103404860301e00c602c0b02c03400504652180c44e04072000c13884000e131140000e02a01aa4002c0e2241c500407156804003540c001039080d040e80d0080d004c031a10303544d07591821940c071180e4641c00c0c800140c0b41c50f081d01c6d0021540302c10948071100281507410603194900032030300e103011943c0168201511420f2802e02541c1600c40e000d140c0d4507030301d0440c1d1501d0500ca4064940507081c40000e200c402e00000140c2404401e0181e02c030031000900c0300350b50310072070000021321007030803409105050101c080e040c00b403190080850080c14815a44001c2c102c0c4c420010511000c00741c0220380400c240c00b0070a074013003160035540d89207001c8140200c0c016281080c0380500c0c500c03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 765267913 1250 765266663 765266669
    0x50f0609071e050d02130306050612060420040902090a0f05070c0201021902010302090d0506060f010323091c020313050a0f0b09010302070209010e190b0d03110114010609030c 77
    0x12212440c280344405012500460303400700c2d18103069a44030110b8035240001d10a5540c5c242d00003000c40e4011003042901d411040c087d0f80116a0300c420516418991502c444096800800c094150015018108450170700401da088000380000b40c4000c0d00c1e00410031540c0c08440703004200e40d0300c012501c01d480441c4606600200c1d549041400e045540c1c1c0041d5494442c003918203400d00c0e4824544085a10980440d0303510071014282c042581591b24089540d03043c10b4540034442c00207a199050154400c0c86000c00c000b481c11400b0020740070840c1001c44092014080907080c0c0941c9445a62020061030150311860090b8015a95402c070320151902000958000b18402c81100d0800c00894120300444030a0b9442044000d503101102c500690080c0700d050760081d0000100c0c400010120003502c4441e210b6420501c2d40c0280a9a4a4240c0111004603003d26030040e000ca404402180c81000000c0d10748001000001c0d522044c080f03c1c1054071000d03031101001941c2c2e07036018810004248020402 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 765269163 1250 765267913 765267917
    0x2011505030a060509030d090c0e090606090411121605090f0c1902010e01090b01050103050a0b101209141606090815070c0c0f051507020901050121050f060907 70
    0x4a14103000000c2e845032200080907280c40e0320341022600512081c01210303802c8031465400c01c10540030b85000c1104403002d21500d00f1582c07011000509003400400c4092240d02c1c018050030b025502da030795048081e06801c0703040703811540900501816110400802d0800070004a5400401d8680001c00c041024001c0c403840c283d001802c00d2290420110082e02e460400a000e800c08040e1444001c80c0100142a00c035011582802178100c00c1c001c55600c40740c1600d0080e6018403d541e40c0c12200d0702520496200c41d0b030041100401c0e080381501c40c2814945a00c810300e0045402e6400c0d0f2150304085240350b0070340b801900000200707000e1441107140c1c5401008903042c405105440e1072040c9890714210703000c101002d188800010b078202d10403c00202c041d603100c0c200103900354840801c04c180e01045e000b618054030640c00400640710485055490007a402450000241c0c02c0c030004440030110551119544500c035103c211a01416015551144111a5904000785403070420085940380142000007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 765270413 1250 765269163 765269201
    0xb01050f0402090f060901020a08070f060b01050a12020a120501030510180c1a09090403090f09110d0c0c1205030a110a0c02092502060a200304060b0d1a06010201 71
    0x462a103c0540742c0d02484d40855000b601c1c0c02c411382c0141c0c2001640807004004903030010311941004811965803011500070b0b86d08010a603c804010740d00c83c80341000240c0811401440c180e10788460307030002c0414405600d1310a18641c2202d0007901981d00a8008851a1300300e1000c1c030b01085445d21949413110082e150b0045504403a0311034101698141c05803504140321103103000010000c481c01c6682c0404083d109031082e01d03103405c0c0107002018a0158040f0a00030510008400c882802618101072540401c0d0740781603200481280280850001c410070b108441103600c000c114100400d030040c0c207280c0c5a0760794031301e044070031103080f1014558010b000980178800b451190743e010050f4507910b03506441c0c090840e140c03040049500d5003241d0340b0502607403002c90144540341e80403c007140181d10043c03042c0091004825100c0e500d006010802207c0c1d0310a01c0040c020030f20b55004110b1003480500f20042c100e0503500c0f08012134075414100100721707982105000130b07560709114028001c100c1703411080c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 765271663 1250 765270413 765270427
    0x102030406080a09170c300d050a090c0f061202030f06040f090503160302070803040e160e090a021b060415020f22080f011413050c030601030b01050f0402 68
    0xb50480c08003825005415903603401c140e0800c007140303589138040c032060400c06403207602196030320307a41e0201d040000007502e4030012002c44017a5507100d0009443d14940181e41060400c210000040070003c040d039070350b1a20394410300c020070800403100c405801c00340100040e01e410494041c0c8942c40c210108903031a4410010481150004d41c0c0003508400d0856010880108407841c142c040c108222015201e1f000000b040c5040c00d403c2002c51010310311036001d0300d100c50340d170300380c1a5200d000750b02c107480c42d0311580030000f4464072400422099048141c01c20a10900720600400c549400848022403c81d900042540780340f88054051451203000d030006200c0c52502d50b81c0c002002c801500c86000154004c6044240c0c1282e80c07040d52500104200c160440c0f140a444d040b00e50003192140003414001d145403e10502410b001792009003074a1001001a525040c1e10040f5150800c9000c0da0700c0c2c0140310604000c3c1d44d00740001030080d8050035182c401941060308114140c1485c5404500c81d5104100e20 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 765272913 1250 765271663 765271667
    0x30c1d090a0302190203030702120c210c1207080607080628030305030a0f02070f060c0f0801050d14030d06051207060806090a09050d0305070e180a15080a0f110102030406 75
    0x400f0107602031462201c0c4d10103880441c0c550300605078000e50004100c07c3e180ea0b48600043d5021030041d04881581d402e030840c0150815141e169160110180c010801e02c2c030031424550b041d075002e00000e0086800f21641c81040d01e0802c3e80543c0c00c3c100050001092000516200395044a070420600103082d0400010801c9241e032421f80c032004092103c0400000e80c8801103038000c010325000c0300b0081d5690500380c6440406804915422100c4500e440d40e840a0944038030b8002800740d005886a2106900300030420100ea02041310455440044880c1052031650600141c242c2203600fa402186950400c000c00c0f06039030084411501660183c00100400c1f035001c0940c94024000759000200d0342c480901800140646200141c02e604c10001ca1403140c6a00d64010f61107152282da81640300601b03481040068420f170007400920510841c0400ea5003001c1d80d1155a40240d11111f4003040340c0e0300c03141907042440e04501070b6041e18148003001c09001500c0b8041100c2e01c0c091010f149064100100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 765274163 1250 765272913 765272923
    0x9080303070e030705121c080f0f130816030906030c0207270c050a14070201120e0a061b03053106020d0920010906140c07030c1d090a0302 61
    0x14031070402519001e080c00c551030a1040700003400d00a00b0300c1180102000d201551540701c260b00c0c503000c130040062414201d05c43c58945025850506541205444900516128683c050040d5290700000c442d014002041900140005c030700e8804a05030040c50380c2070203001103003280c1c04102850f00b001058055150301107201001d85503443c0b221010760021041181041c411152030016461070700302c80c0e505050300b200140c6016401995800d02340c1d020003002c12200e0081e1203009001c2200c2020002800303481c0c0d00050701d00e0707070203400311132080798140c41c0d22069501d098100601140310303018604100e9498000c055020b80081002202c00b40c05100c1990741c0c180d4404807042040c0100790700420050660115440500c60100a02c40f4840c0780c00d0030240e414a0040060b25000703084110741040d4058030084040f202a074480303000301103070540c1c080c80c035038403c80b85441c032801a20004400164003280d404080c080418002c1c04010200600c6d5074090409000020300380e0003000c0c0d000000b80d0020f2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 765275413 1250 765274163 765274171
    0x60b0108160221090405040525060215040f020a03030801180204050913080f131508090a020114130806070f090b0a0f030e0d030b030c0a05060706151e0501080709080303 74
    0x1031260884506401c44102d001d441300d803661190604061005219000800c00d40001000d5425064608000d0007004103800c01e1085d03a025811004e82c0d0388003404c003084401d0f0b0150161400031081081640044c09400300e581045000c2018040180102030303401c80160120383e81c2c88000c514050a2000140156500500b1440a40c10031f10b51001003208002c01d8841d81c0d006061145c1e240c0e00c0d81101804491414045d9100440401401302e82c0070341702d01c912034042d0f22010080d211142141c0c004503610075080060341310000c401c0040444400803008148000e010f02c3c00541042c2c14201802032011f4010300341c900c2085003154050001e15041c40c11503289580e1401c0c564640c00c904901a0040e04c0c502d028844640144c2012010203034160700306042146048003502c6e0200540700030010425144d024050704414180864000100345910000807036014600742114071b540d4070701c108000e4580207180c080c0b541c8000420401541c205038659080169420641c0d0311904008003241d590000030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 765276663 1250 765275413 765275443
    0x20d03030f0518071401050909250f080708040819230c030a030f060f08150109111c09020a031a010506070210030c030605060c012903120d1107060b01081602 69
    0x80c00317855041c0e0040d412a0030000000d031034124a454010400c1c0e00e604141d1540d0305035004e6020402c2019403141c048805110007580b581c2c03886443c2c5040071540c44c4801031003101c48410410919142500b91000c1c03600034282550b9144900e00c0d00e14007010b00c2c140c031040d2140600c509102c800c98818011040d9080c808441ca80060601120f05440015202640c48060b86000e0141c020410100c04901c0a9194030344410032801640c0e141d01c0b020446240c044241c400400134061066403014049004400841c075590204440c0215000107411010036402119004105400032580d508000301039401440200c0c1d0701400c00c1d800d600840d6501c05810444020903550302400c8061a0103031744080081c0001501c00c5458147c4242141c1c001d141c1304014601200c42905801456414180d0540756070740040c002d400a4201005510b5954001142c11620f1030744480344c0007030b01c904072000341c240e4a00a03500882c4036503864001406551018000c185415283e0184045450b00018200604180f203 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 765277913 1250 765276663 765276689
    0x1e0a080d0906060303030e0c1801061101140703051605070c0512010227120a0f080309030f0705072111130905160801050c04060c080f07020d03030f051807 68
    0x4005003100034040100e009005903d00b11012040c154141d121044a032180011501c1c4506404100000300f0440300c003d41c069840480103100c514800c0c0d0545070820401e000116a00d0082c58001403000800c030b900f4800203039200c0800c60aa502008000f03119070343c03800c2441c602051515030001d0842203004150040940e104a000180300940c101c0300030a00080c03841001600e0028211802400440d249115401c0c40c040b15100540219955420b168010700140300080c13940d40d2000700d82c0008216401e44e020038803203429a01d0b1550010102c0f02d01c5040500502c0d07051101d03a50f00c0c44007106884520760a803184c490005200081c0044001408a507514040040d45802e030015108280d0700030620300071604800c48a05521915000361145139000780300964400d10054414040c1d0702c64032001a0782500c041c00840e84c1305009000d038058072424070b45015034070303008100900141402240081e070b540d2a034407404d008070320401c0d4000c080401c4400448020b08407080d5294000c0c043c2003810025 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 765279163 1250 765277913 765277927
    0x405010828050a05010b091e1f050a030c031b1805040222060f050715110705030d0606020d050d0b0315090708100203062107081204081e0a08 62
    0x107084088072000014403807050711010003510003000e8841560445081828940042503403002d0900f079811440c0060300100d110005260558080c0c01c1c001d40c15a040304a4407440c0e00b0300403c0ca4a03100001c0d0280d2911650349107000c000a04451520100030100f6251584003c01810780c88100022003401c4c1c84cac444c0d0942c00307581e0009010b20141e84019803152000414200c2400c80311041c0030444400008051060740d07800d400d94089400c0315a0343c0009508020100c0080c90401801d5003181401070b000844d0030100e08440c110340d0000c801643c0c19840450655040c0b450350181501030001c901c050170003004084000781650103003a2a1b0142c0c2501e5101d50801618200181d81114a03284400001c0e03041c81e49046441d004a0700900082c0e0044061f9041d1101c07040c02101e02071400580f80b40341010710031618065080134000750404c240101c810010306070104110707122401c2d250000c8156518074002c000d5240110b6006405545040c82d04004c003459808110410482d0b0400f5500780e6801e1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 765280413 1250 765279163 765279181
    0x305061f1419080d1404060504050616061103040b0610020d0c11041d0706170103060209060c25120209010306180507030f0c09090b0105040b01031508210f04050108 72
    0x1000720603160100c02c1d4148001446040040c0202246925031180d102d030740c0c07019131031020368440d5028490201e00100000c210f80c0c10240001c081c0721240c040f25641040d190350300c02080c1c60070240e4450a00d080417003800700b8000a4010b42c6c0e0880c0c8101c0b9001c58646101c60043d445001c40e091040600c44045c046405010b0580c190f0030003000003e1003000010304d0449c4004490b00e01c2100f090440c030448074003048980c0519920300c007000c540324280c00746a10b195034841c0a54070083c4125040f4105114001d505032082095405024105d08000f501d820340b04443c024a1005034400740b0034040d000b0040c409601c0303c3c1e17009410341b500403a000c1050b1400480200c1504180f001c0105180300e018030020038005480800310714944100705015405680340d141100340c4840800251404034000010880f61810b6808031150030018180418607231f6800b110343c88850041d520a080942010028403143c0003e08050000103e203803a5442c00e18403200071080281c015802030f13505112035140841d84000f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 765281663 1250 765280413 765280429
    0x28050301050c0723030313080c06040c030506070203040501120921031a22051b040b030f1807032909010b040e070503100b040b06130305061f14 63
    0x10140003844541041600503142e40e2103080242c407070407400d5402c01200d04210703c582d08007503003c0740118196140c01e160b0410807502034100300c49610041140351081601809141c4c42039026040e1110038902d9400c0c00350a1401c01000b81003190002c200138025603070460303400403400000301d40018000da081e103080004102c2d00420340c0d03100c148202c3c40703040751039050b04403c0318005c0a206c0c8001032240c2c038084c050001e000c0c0c0c0340022030440403501176000d81102d0380b145910055000d9529101030080c81c40200c1544140c0046d40c80c54000010403040e01c00019045801c12217a14844400c1e0100707000c201d869146600008210034000c00e81c680c5d455061990700c0f0500d1440c5200e401d61401c0c40c10115000b40b003202e0780240110f080c5038070b20170b000c0709c04108101240d00c0900944040c4031100c4a502c010411660301541c425500e001c0c4840c01d4448070042c010800c80075041d1207405017141442c1e89001001400d5280705940040140300d0b0480c44242c40702250410710074910010311044c0022030507 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 765282913 1250 765281663 765281669
    0x1803080d02090a151e08040b07021005011d06030a0305070f0f020402310303050a11010908070c180506030c0609130f05070f0203040803030c0f0f0c070f090b28 70
    0xc14038204010409040500000501c600c0c4d9444100d00500b040401c86030400340e0a10a001066074480068041200b0f044603030b030302004901c1543d0b0340030703c503c11013802c4034000e03004004440c1c1894100034000300b0345e10f681c6400c0b07603045004001040d49950300404e64400c2e40d20082160510740d40c01030403c400640d8040413994010b00075501e030140c04102010101504003590074101d41030100c0501502403c40c1d01064a4059681c1440c29120b16010f90b440110340c95444650b40d6100107031004141500c0280c070409108110900e05a442c103115082c5001c02c254100c071426250000340b0510355000110b500c05000e09a82080e201e50070a800209005010128a54402d0500c000303414110f5003580581e2083c8560703260b105000895010032a075a000390f00480b11070b5802000454008542c1c070740949100000c000e80c0c1840e1008194240107103400101ea100156130001c0800c0c855061465a49809000d202c0003c110138a0003000040c903450300030f1802d404040c603080c1c0f50306125260042560203 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 765284163 1250 765282913 765282919
    0x5030d0c051204090207171903180512031e07052719030b0702010903080f04020a24030c0e10390209060405011d0a02040e0106030b0f011803080d0209 66
    0x4840c0c2d518a204c1c060740c40404102c03044d4918400441c841105c0300281c402d800c090300380c1c00c00680ea40520980080840200644628110040c4200013030020040141c2c100d440485c482d4890078011518001041140c0920300d00034034041c1004400355101c01075030b0f185c00040090403074201d0724025090114541e19003003130300310040d00c001003013a40043e01c0d8030f0116403042d104d003042640c50b408101d00322000104001d00041e62600818010303842c1552150704540001c180301f2016a86401420b80303d44480d40e00402e07400da2000510b136660701071103a84141c41c0b550800c1103440510384001420000460b00c0700f41400f0600c07036620100150030a00000600c81e1642241c501003070507400c0b818230700320904d00301d21907420600043d1075400d060051504a5141c20001407110000700380c40f03066071f480101004a210317800e0000041c1400c0c8448518000e0107103440014660707910100b440402c0541400d407074140611100b10b500d04601006a040880c4c4e040f0305125115295510608043e03c90090321030381c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 765285413 1250 765284163 765284167
    0xc0b03010605120906070e090c0910021b09190e0f01020a0c2018041a13050c0315070e0a182304020f040c170f0711060105030d0c0512 59
    0x180c8036402c800200700c0040c8000390b612640d0b0740c00d0100c03599088104e448000003000341d40d61010a00b04001c0b040e400c01103070441182010b8015000c9900d040c010b11902c2e0060f440031100c10071403135090b0b942070003005040d51064520324282004010b03a945018090080b6a03680700141d060200c244240c02244100c4002555251001480103090680500c015121201c5401c840c51064035840c138580315100c0040d01e011010f80440c1c0c4241c0100c0c41c010001d891080e0815130610950350b41c1c42d01d00d44214100c4800030030200590801928251805620038042e0b8020a122512030710729403002640013840340303400c0042d070300d4241c0401c27083c2c02c89a100d05480c1c89581140e00301c4100c5508040171803003481001003644010f100b40c1c0600f07540d00744e4001c0e420808a000c41c075150b003000c0d0050b91500c05603050681d216001c070030050701401811580c8403c1e58050f10140964a548050582035a10701c1100a1115506100000352101c40420588060060400195080107001d2160001d480300c01500c0319 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 765286663 1250 765285413 765285419
    0xc030c030320042d0b0903031308160e042d150e010e03070c0b0304020d1a0103120c1707060e03030906060a090c020a03080603072102040b040c08130c0b0301 69
    0x940d4a82242c0079180e00e5400307070700024442904500c00d0040c4c40c02c0d0401d2944003e480c0c000c003c40c8992040303c541c0d8050008201c0c0040700d041d032520040003804450028044409114000718071769a50f90441310007554084240f101082102c0030030381c050300d05225175080210018000520101003098000c01d40d4026030340003414008554015002140004003d0200b04190009251a803140c1d4400810700600b5001c280040980e52002e075500510240c541d682104e0a91142d86000040c04280301003c2c01c040700501c03c10607030000380c0700b68030200c0c01d201c0180b0050340e84d40240c40e525000d0300080b2460200b8140c0501c10642c01c40014580001c00740d0381d0342d050000640e41c888100711417050040b50340a40010700710f030355403084444080351903000d0104407081d9076044440c140d02620203581407048142c00314680c440d002426000344003060340500b11040c1d52050006603602c600b9060703c182c2c40d080044400302c2e000700c0141d900840540054000345e45a180080080c2c0c0b440d00309802da60710100c008 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 765287769 1106 765286663 765286721
    0xd0506090609210f0706020d020c280b061c03020d0e010801030b06010804030e090109020d0e0a020d020613030b0412030e16090b0d06050a050f0a0c0c030c0303 70
    0x8a450102c0d1031b1580020707a081014603806c2c0c0ca9000400044021081003500c003440074800c0b0458400362601510030307003a03004000150000800da000030704241da540000b0700500c003c008800f500c0c40307041e0400030740d220b10160407070002c503d00b6421100c056015113001c038121303a40f215150400d0b6948400460755400702038001c6050007403819030f4079581d0762525602406041107800045e20f8149014045060b1a001c0900c0811074104a420101580304c000800303008036016124956664090300818464101c40e6001900c1812030030140010040b40c456a071044003584d9500707100b01e1240110039034846105804451204041c40b208100161140d0070110320304400a2001c06110f001c7d840d8031081d01c4040714004400c0e0781e80d5013081a8031410300d2040d0b400c210210300400c0251403104010342724000c0c0d0750001d0140030100034040c08051007034100c42d84109800c1600d034592600303c008 = true := by decide +kernel

theorem cover : BRFrame.Cov 765107913 765287769 := by
  have h0 := BRFrame.cov_init 765107913
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765107913 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 765107913 ≤ n) (h2 : n < 765287769) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
