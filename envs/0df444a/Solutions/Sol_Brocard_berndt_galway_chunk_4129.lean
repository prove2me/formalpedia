-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4129
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:39:11.337487+00:00
-- url     : https://prove2.me/submissions/b50198b2-3607-4348-bff8-0a88a6af5020

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 742446043 ≤ n < 742625899 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 742447293 1250 742446043 742446053
    0x1205090a0c09090b160c06050714031006030c020312010902091206040b040218060108040b18070b07170c03030109051302040f0f050601090501020a0305030910020406050c1c0903080c0a 81
    0x641c81d800a0303003468449501c3c2041c0302a024a055100d104041041c01170664180c00428541030780c0c800038401075031000070410b4103200f0f0001c00d84120b82d0100171552030604080d80074031100e5520a40c4002420004004081c1d44080305944000030034203c411102e07403c0c02102c1f4080c0d0445103c45400c034122101000f810501041518004c41c0030b400400c01c0d904050043c011002c0518906444001249051112503644154480d9109800509800c0c0e55100c80040750200c1000000c0100c84e0f1003103450210b8044091001440040c3c4100400c01c10500303000c0314001e940c05400311a000d00d401c1417004018611158200e103038040c0c00242d882e0440c101e00c1d40010116195140900b40c01a615004030601c9a10351085980016003401c141c46903030324000000b542c1e24400e8a00074108a0040041a011032041010350281d02c13031508199202c0f0f464501c0200260800442d01e05548980300402160310b000c1035059080001a41d0703060201811a1101a4070382d015031429443c0384542492500410 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 742448543 1250 742447293 742447313
    0xc06020705061e1e030411090c030412032a090f03230c0a0e1f0b0a12090204090311100e030f0a0512070e15040b12060a0b0a08040308161205090a 64
    0x1098004005845c1d0070641810240402c41041d00c07401080d003441444482c086c404c090340d900980c092040b84a05e03083d00e60407000b40248495a66050409000c592100f0420040e1480c40303510955580d040b03590354040341c2c0018805172002800f40400111104682201318400d40c11891615044440c800404808511a51039583c000e0080c1d400440600281241c035241d10403640760612001e8031080d0034900520051320540c0b40700c10620070626032480d501413081c2c21400d508d54000704200030a204038100034000303034100d9031b211102d406140f04070304001035036104501541c8075500003113040c54000301e41d0384042c4e404441740302c0900400703005002c8582c030301983c168480d1105e50f5601d5914807502e0180719520120101e56075400905003c01c0c04000c0d007103011b85259411000300c180d0350341c941754003190b41c4140c180c00043e120200024000409170f000014070740114420342c0c4241066488642d0000e000702852040760000c1c40c907942690700c0c0740c110741003660000700d080280c541400041d0384014440b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 742449793 1250 742448543 742448587
    0xf15150a0b0403060c080a0c1202090d06050906040b0907060e0f06040803030a1a010507200402090d03050309060f0f07182309060301050f01030b0c1c090c06020705061e 74
    0x75101d01d5002c0006500603d01c61f04032200c2e581c00e215051004402509407a0342c030044807403059010071200080d03a41c81040b425003d8000a04003c076040c403c0e40700d519458111070640b4801114001300c1c00007400020040e01311041541c0300403c230300103501048800d0011804640c0d22000c24000070a1a0b0414002140602030240d400103141108843c40c002001c2e0740c1c003030141880010b00c00c04000c1001e0380d09a0040705080000c4507801d284110001d4024083d10000507000541c17484807604154104d0019409903050b5022070703940c3d81c1e5450305001e40100c22990a05402c0c594800308a115002d01d242e00850301e4862503031701c422911000a1016400d01005142c180d51720072040c2030150910713050151f0854401c0d80203000c546002e0241c044504011b100050028090500250a01d8104803d40704c0210a403014030540204e2070036210040c1100f0070017070f140784401910029213103000040340c02c01c13142c024000c10308002800c0c044100d52030944440001242e4100850000c8480c2d50020f1542 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 742451043 1250 742449793 742449803
    0x9090a0e0a1a1b030717100806130b01090c0c0206131a0901031514060a02010f0609050f09060f06010c0f05120a020607030608071401020c210f15150a0b0403 69
    0x11620340010030b040308003a118203a80c02220104103000e0959440b144492882c402050b003480e00e0748407c104e031040107800b68001000d602a00003885040790406031138540c414000d8914440301c1c0d81390403444007281e14021480e004a2034445644005041100162119801c010425980d6a07554100d00c6075040e50311205241e0020002a030500b10340e00f611500e1010085100461605810940c0c031801803005040d07018070031000401c4080d8414801d420011144a0b80c0800b441480e5642c6280000b6280a440340149003409400207844400c2c00142503100f984034100500c0d046d12148010340e07921404035800d640400044900c0404a801042070300703482d601c4a0f030b00341d03a1104c24080c001c4c10070b60040d2587e810981000410000c0860009904081d961602d00000307100900c040140d140041e0810a0f50b0004d80d6034904000e46088498561b4070a003078a0292a00b5440b0201d8031511510303040f03088881e84d443d05011560b03c08017a03500e110b401c14050305c10420242c48683c08802c940080d4400c0314 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 742452293 1250 742451043 742451093
    0x20c0d050d0c0302040807050d15020c030409060503060601080403030216080313061b0801031203060e1f1e0306050a091e060b0f0603040b25050d0c0509090a0e0a 71
    0x101010740c81075006403100b0345011803c2c141464400344d1503281d075101c2c0d28801d514a00005051100081014410b00c4001c0c03001c650b6a665601525140c0c0c10a200f0504891300e01a000509401c02140540c4681016954842260380c0c55070107174025000904a07600d4004034494000004041c44001c41c000d10000041c020384081d5460402d05483c5410074598801c003031510054081d9401442c0541540d900c000d550317402c20030020f802c80c02403046500141800a843c1c0c184005c001c60302c3c04410340d45148915031010b09486000c0040c1c1100c002140c4040b482c0c1a8000700003290055002c5a003101e401c02d0041440615030f1140b283c4a517600b805081c0041c81d0031180010054580f08440000c1003e4580c640c0620340c09000581e240001800500b002c0078142c0064880b46101c030005003420107010743c040711810780810040c256003000540404051600d40400720340e030300510179100040301c01440303850195038080400001d0229505081c0c0310b4428030051800050b25462042d4016400850040f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 742453543 1250 742452293 742452307
    0x30d05040c090903090509090706120f200a0206070f0509041d06010b1c0c0509060705010e060a0905060606030c04052b11010305130210110f100b1e01050319020c0d05 73
    0xf10030200060300c0c0300c41caa030027040100b210680049026003082e1100c80001006660204040c010389014941c101200c0040001c0140400c0340c18042c0034100c81580c2243c0720b546c0d4010064491000d02078074040810801d03c40c1c99043e140581003800c407a84c2840b01c00c0d080321b901c07600d00751a14500f0703007225400c6880400c120403494a0000300412103400c03007109001c1d0645910019000f8442d1815040c0103043c0060b0050a10200b50001d4404900e43c004440643c034205411100070081c00b001140c030342c0502000304129290440589000fa0f900c4252507213000e2500c1d04020102c1d04003041078004841c01d84590710107545940e84000300d940034401d03e200c86550a1b00040071244028030120030500c8407689031000d40c86801c44501080d1203802c2c0044100319500c0c1007403902818010940c0300b4810346003000d83c188103640246800c520155060440744480c3c159124803000040d0280d40083d0042c00001c050040e08020344100c56140c0e180140342c480106038035400d00410340e50b0040890b10000b00c0f8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 742454793 1250 742453543 742453549
    0x130503120a0f0503040821270c04020703090b070c1409131b0e0420011112030705070822050a030f1709060a0c03080c0c030d05040c0909030905 63
    0x1942030903088034491840c28880050141c0b80542854048041040c00300c0005c041103440741c11910768485001d01d9859070b40110701501c21085c0e0489000d402c141129144c036150601460713214144e01e02c0748000d4941c2c1c103d480103110080d040038030280c040052030000086c100190704010300c003140c00b13060740405141c18015002c904c000c20702c0c9800d001d20051410404030466642018820303070303070000940d00b0000c2c190703610742c0d03480f681c0b1f4000f01c5420680c3c105100800a4030600800018880200741c0b00c000c544c0e000541c0c1545102c24604002d03000b8150703400c02d81c0f03030402c000d41e8480740f10704106042000c252141e01017508090642611031440880b5a4851494180c10a006001c1140d015806c141541d9800f0846820204020b08004094024850f15a549800d56101c8180a0050780c1c0380c040141000388201032100065010498200c0401c3e000c601e00000c0341d106406940041d443c200800f40e8241c0140307401003060314200d4102c2c2000c20104914082c02c0d003454060750781ca0f49803500304020 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 742456043 1250 742454793 742454803
    0x3060a060e06090409031404090911060304050319141209070b030c070602030901020909040b070e1009050f0a180f1d0601030201080c0405060a08152b0f0503130503 72
    0x400310600102400c802080e940c0e180445246610944003c40c10b02840d2409940070894500201030000010601054000480d80a811034500548401d480d07500030350140001707848290380192a5401c2000780421030703007200030380e100c079040340d89842019100344d124404503c0d040703100d03c040c10301041e00900c000203601b0020310002d0b0101038402465420402d0006040d48a560402007007140c0200010b01400002c2d815a100783c00b003d0103003c807511b8546412900740b00d08945110104d15001e80e80a0a420300040c0340001200c00d8542e01c2c0f81d1030070310080004071b40c02c3c030030445d51181900780c0204200420051000f0948404a404503001220310758010540e8403400b5200d00c0040d0090700c510100c070002038010704581e02070a00329030307a4545900080b124031454100c2a000340b00001d0030520160300c881340c1489000d000c034070311410440600410181c525000d4940d00e03d1450550240248048031644000c0184181c50035100700249540f401d055810140b621408440d2024040010341400d001c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 742457293 1250 742456043 742456049
    0x70e0a0e0d0503070c050309120c13051512011805060601020738160804051e03060402090a0b030f15010e0f07080c0906120a0609020403231e0303060a 66
    0x41c010051070314070002c1031804000d080c80304004110b4504000d1180501c02c8803c00c1c040a4a4200c0d0b00400440300c5984944104515010340c18456030441030100b5407054500503120f40f40c8142c1401600020031070180300100d4084040d541ea56030940c418a04da6045405040c4150082c200d645000000a41001460380c0400020180c881c85141d85d51544141041070210312583d011007216501c50784901801507003400032031940115003600074031220714040c200301c0340100e401302e003007044e0b001c1d03410100360445202680503030101c00410014a40000c0c0650300c569003900000f0003150b5000002d14000000e4a00d040e079401005060444c1c2c01c0340007180c1d001d0640354201e2803040c241803182c0e0f401204001c0c03884003040702c1c10f004502840d94860884468180c002d1011391540700403107000d4000182511000740151405a0000d09442c1a0090b281104d40048034242140d40f030f03c00e00718107034002612080d00b5000790035602c040820b50304072554800d08107000450b01d1380f900d54140170302c040d041d030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 742458543 1250 742457293 742457321
    0x9090c0801030215091c0f02030a030210050105060c0d0309020630071e030509120304060e0c10021002090f03010507020706030c0203032202010c060203070e01030f060303050a0c14070e0a 82
    0x101401c86501e42d688030319100320003860a01b16a8070707941040c101607000c2810095241c000d804010f01450350001e200d512245038607500700056640e580401031180700301d021451041c0c22144212040a000742c0c88454828006411185085610b40c00c01041211983c15484400a0318402580c07840c0300710003203075100c201420f1107009003030711081f20700b501201d0218076030406884034000b581c01c10302444513441c80200c1011413a00ca04261070154003800d40b81c20344001500c15820000c055103400d9088a0800982ea0040c0024603e512244406903000d1480d07950000703c15100c48600e501d00f40f0513640306240944c061f00b88136080840003415034050080c1a801c40d401841482000b0304103078100403d4000d440820b00744241c407840142d5040120403005005a0b1002c010480f189070070241080014000b40c1c1c08011400d40d0102002c00c130390182c00007a0014806001e0b4a400d54013074a201042140501c55000c20f43c002c00a40c0340c80c0c8142a000000c81c1d0742c142003481408005030040b00740145c400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 742459793 1250 742458543 742458547
    0x909030c06011d060d0303111602120d09090b040204050604030b010315020f0405011115040b0106020f030301032612100303030608030306130c030608120a0206010b0c060103060c09090c0801030215 86
    0x1018041d041c04201502d42ca20854070452076204142c00723680f042e0840c0c603259000c66152a0496408540304c4000304048c0c2c010f03007522842450090002c01d041c7c203109255200e00e43e03518100342c0d1017030081c03180181c04c94125908000c0801c0c2d59a61320042c20046110b0103028001c0d42c15031803c100300c8817400403c0c2020a0040c00741c466076031310710000d58054601c2840e140d030010702840e14040c60301c0c6600030030400845030f010901c0148a0764805541c1641d606800b224006108042441c1e5a8802403001030301603c8080c2e02c1c502030f040383c0101329080340307200207085007444841d00c0010b40c80c4071b007580c440c404500545020003c0640500461000305520b0b40510304510784200070800403034002415a41995880c00c402030201e000c0c1d40864050712a0100303c030f0030726003c180e05090700e5000340030200262180c072000040001145080380c00c24030313424016101ea64078660f074060140545000003070600400c6100801c0c101e100d8440c02030901a039640e016041d501d540103000034102e0a408202104c681 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 742461043 1250 742459793 742459829
    0xb09040c030b041106070b04021002150a18050d090e06040b01050d0b13020c061909050706050c01091a1501080903070201120b0307180b0d150c09050909030c0601 71
    0x3001000d0040366002980840385580c1c525001c85092808600d00e60b000c0310201da10002d00c000d1015142c440c80c402d461650300079906000a903528040c8844140000200000041a040341da40182e008001c0098000c83e070080c480d503403181004000075520f0005202041c080100d8034030504c945400a00c00d5408004101c103001c0020050705c1418440407200740c9401c07598440751150743c0b9190603808036500454480c10a00c01d10b81e00c0d5602921060915040c800081c6000140c6206402c0030a43c080000c0031028600801500c403030300136400e0750301c003550303221440303004a41d0003a412882903031400849050341c98980c031b40301c0403200e41242080c1007200c100200503030b81600000315014203030242841d200380710860310604041e001540c0342e5a014000d50360001401c4001d0515a0138243c5113036411300c1541109814010f41180c414406000c1c01407600501072000d800c0d60140640100070706d0800d1155480e840891a540c03003c0d030341c00d042c1c0c0d840010000b030000c0c0144a5540901080362020300c00700f003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 742462293 1250 742461043 742461053
    0xf01050618070305060f060a09030c051c0b0c07050a0609291306021c05072c0d02010e10050406110601080706051b070905040c051807030209030f0715030b0904 70
    0x1c802403071841070580d80c1020518070b560309207815106035001409240e40e41400c060052000503244801c80f02d040c8041c1010903a0714100100604103091030100380c0880c1d94a84a0f09079142d8046c08220851400304000d030041001402101e1145002d80008620300040c0d16126418100c00c1d2012041e0400780318602c0e50410010000540058106900500507803040c1003403402413007500c1c000001c24440054501d952011034204c20302c02c031655200c103040615441c10040c40400c00c5299003581c0d080c69a1081b01078030300052400321103030062500b100341180204c04110341c0c0308601c282002082001c613041010f590300a068080401c050405131542d9450f0140c1540d8406550050405208001ca5500700754140c40b96161245545881100d00e0150b8620b8040c004200a4400740c5a25804440c040b5007030400d006005400a0b504500311103c0d610400200c0c000d422007481507038540543d803c1039441e04410019100900a91100c1d04141140148050b007118880705189015008000400c00422 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 742463543 1250 742462293 742462339
    0x6062607060f0207050405010905011a04080a1506320a0302090c030c190c020f010305070807112d100e0d080a1107081314060f0d0f020c0f010506 64
    0x41d440341403000500210502c20b9080a1a9401c80c581240c80d05000003143c113511f400250481c9d110703981011151a13450004801c51049015544080d8001008040022002c04030712100480c01300d00081c0320754544030344840d50180524243c06c0c0601c05a04141c00350386400614000300e108031006407100d4a1a03001c1500c0c0500205413048441000c000149654061401c944a85060108010b40401d040f44080c01001d40c0a50690147d0030071094130045500900c1424010007250311802e034656108a01164440c1d05c0303100054203030092100c4c0014904034800c0c10810b81456464001d03607440c0c4004d5480c50302100c11441c010450030107603c00f8071550b0226680714a00c065107090b50182d65107514600c040d00380001e41d0b07941e200703000038148140b19203103000d006600b0100703203401d0035640e440c030003d03002c10780c103401451f40204200900038030361020400501c0710040d6500d0124414000807a540100e0700510341000346901700041c02550500203100e5a6070025017100d500c459000030140c501050 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 742464793 1250 742463543 742463549
    0x50309030d0801122004090317010f0315050a1b0c17070804031202030c060f040614010f0b1e0d060509100602031b01090b041217010b1617040306062607 67
    0x40050900070405c00c1e03520341041008000a04240009000352070000c100c1e00c1030070020302c0b100c44400008590741103024450b80459420510100190082039650001844d01410784508590355003417059503100e07098034040050400b034481c0300d8409000c0c10040e5032481000c19004009100f04040dc00081c0366206a800b0391740c000030440c928002801c8140e14500c04c20001490b0b9124040400c0b107040852003a1601c900d100f0785050008111074405150218428003a1240d0701110340300134080e00b0314a0b03002c2c2000340c0100200100c0704090056820300ca070720101422030019100c500c00d20040c14541e04103500054420f0b8070001aa146c050000d49030701501c840c038502102d481405100c0000d007500704888071500a008a22136050a00e0135101c904821000031001c40c2e44c00c01d400740096217440b0440d049800b2039032a03030300e4802d080c4c0742c001c92610194011600b4061040201c2d00c007400c50030152020318401e510000d003031030410400c0b1203001c00c1106650745544194040325000180030400f4011 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 742466043 1250 742464793 742464803
    0xe06010303052101270209030c24030a0b030d0206090c040911030613200105030c130b04080703020103050a0209062a010c080a0b0a1d060a05060403050309030d080112 73
    0x4401d0f108941c104000c00c800480380200100360000315410801c1e1800c001c1d500760519184801e40761840c05007007070703008068120f60f16800c010211401303814008010018040a84048503122030760b49104901908107039801e0301c1040d5502c601a0543c2001c001407212414a2300080c030007441e091400c0c60b65801c081e01202c0c05030ba145c184020411868030324106403a400101030f15038074a0315400201560082e0442511562040e9060084441c0300702c25605002c5d6040c0d40c1d031440d640e15a0785042c92a4880c132920a0300c40d0318800d0025510009001a10213800001f02420010789140001016100080c0000707d03040c0c41080310318650f40d201c604407841c82200403e40d111400d901c40340d022511143d90502c0009508116103104000c1c4c2c03040b5403d100340c1d103030740f8200882c0d01c1940620104111a006c2c041909004a601c0d50701428007002c0c10354070580091141d96220345480c00b29515400a910484095001080f41503251500b4001b2490b011024503001140c1d41c50090703008240900302101400c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 742467293 1250 742466043 742466047
    0x9150c0f0702060f0301060203072f060708070c1e08060c0912010f1a130b03060c130f0b28020705150f07081216080402120f07150f030e0601030305 65
    0x1c40d240c0c0300503140c644c892aa4070a0b1650f94030180a5180c1d03201d0384045541801150350308406400035442410501d0202d4900324288010b402800074603400b08005541511060100d08001041c0c00d5800703000c0c049807410310122000d007141c1c420702c0307620a400a4903150441010080c042c20300f6402d032481c0260803108403a6041010715124010140307030035514101414180a1540d1888500d03c580ba941d40036a01d0300c1d0010b194101040072100c0056900f44d1682003100410071040400020741a00e1394104600d0b00c4450341d8901071101261994064130f85104d0106041a01d2020301c02824442c807501d040b201e2610800b03010082d01c0d01810301072188509042d4040072a031414580603100c0403c0e50758611a07403149981013501ca541c020f00710722a4140307030750750015000c508400500801c401c101e4484020544442c5c0c00c000560700180e003024541d114000c0c404c661008104212401072079079014680c00340c6840312006008000810804c070a00d42041210f0300310300400a80a8112505890019 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 742468543 1250 742467293 742467307
    0xf1b10050d0e01020306012a020d051e06040b0a1503031d03100b030d02120313082106030d02030a08010e06030a021822050307020f011206090509150c0f 67
    0x62035500600c2501d0481c40d2400c1440209198158011402404240c076120303010b80d00e14580c00c086070f20000045025420101c007032401030501c2120181ea880c0b03c1c0c4156100c011600b1f000f00800040c2220148495008000340400d000031003a04c507030440790700c0806104c0380c0030036030700350440350100c1c48014204010301c0c0651003800d140c520392210001000781510032070380c400220700029002d4030703065504ca070007451080c80070580005039040186810a046a0035590f07a40180c24510b02980301c1656802c40401440c0c0324a10703100f500c0400409001e0140d20315050210505240c90b0b17110110303030150b6204019144180307800c0600c00307044641d42100710081c0c4d556140030034204800c03034400a41003182c8000c0541c1c81d8081c100c0c02c51182c040502010013101d03e54250324540d080c0248080d150760010001c150260400703000403501d4584c11704200d0018120a070240003281e00e158403070f029491f580c0c0140010007505101100c0e446030310141c00c10f02802c141804a42c0c51282c0c50004424400001d618 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 742469793 1250 742468543 742468547
    0x403020d1e081f090908030a050109021c0f0603020a06030519020406021b03010b0306040b071803080a1d2106090d17071e1d030f07060c0f06020409020a020f1b10 71
    0x43d1001c0d00590205100700c000034900342e21250030642c0d101d94820304140000c07940700c0c10340c426907028401c02c2e06010a841c0c1c2e503250000c0101306c0300151103590b90300d4140100260303c0316a840001010207035800145440d0140d400307102e07440b00ca10304600c000d004200c2001850b40c00280c2d19160b50341600341886408c0c00c040001e00410800203460f8041c0950410082401105004207100700002c0e114400445d1080c00a540c081585010060a22a0600c54184094400d01c0c100e0040b0b02100300034034040420000181c8140d0080740130101801c10050f0190105c5010b00451750080c084000401d00003015980150150300302840c0380c82103d50480000b90014410b88502280420352134882c4e404002c0800004e00d9000000e41c9100c40006180601c461401c000446d00301d5200c190001c0c01c4441d05100045581d00a03502003614480c04425075a004141c451000b070009211207003005a84640c14000a810001d2840010105e60003200030141c9a4410490060b60701b0801c0340c00344203c503403015003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 742471043 1250 742469793 742469851
    0x111b01140c0f0d02010903020f0619020a02010f0e07090c080c0f070c091401210c0b0307021e0f06064f1d160e0702150403020d1e08 58
    0x40368034911401c0c407241c2803d601076000e091a140603609541c049284c0000250f034804080d40d4420f00030719080d80080e54510305a020300a00b0f05c1c00d20021441c003140b5520074081d07400d203007115544c681080b241084030700304911a4081d134000070308000e800ca00d040c0880750f4250103160366040340300d83c001560404021000700e030500903001402c000c0010010360308015007504001d0140c0481c9851108403120500d03080003c6143c101d900c2200b80c003a1604110300710700c40d83c0004e45803a082d44120b040c650745d400e016520b80700c51542c510780200041160480d00602d1300703401810781402404182021280044139408007880307603d428405c42e01e080d00e4031040740b140c078844404c2c5032402d04459400000d04c8010ba0020310580600e1061040d000100d80d012988411415a884402d2403401d903040003c0d6004245d1554048141c0c015200d6042191044a1004200b11012001038201c0140a4103441d000001c800c1c6010040101d05140007054001416501d400341294005034031441c8440100c0d003401034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 742472293 1250 742471043 742471063
    0x215011e030f11190f0504060308090f0415062604050a030c0809060c03120105060a0e0f03070308041e1e051905030f0a0303180c03031110020406111b01140c 69
    0x30003007094004e0721800040795a20b81c000c010100ba5041000229880d0500602040d660400005840c0c03001071070802040310303100d40c0c4558009442d0300c20402c0b240107016a003401001c1c1501c0b0042001d610031030712103e9100101050200c1842c1c00284004036074009186c070ba0469060804a501002906085205000d6440d00c151b0040001410512030f40002c0050b2070650188010302c1c0f41a42c90300100221400f5109070000020f030204111400f030314002c0318031507070344034003505680000b500c075101c00505501c560409034500004104c88080da406109641d0b0041400401e418040140039683d240c4030521803051034842d10f44000d0001441641d400514014080113040358810070b000c0d220182c4555041c0001d030b02003480c1c00543c40403003242d82d641a1900d64001d00543c0e03450f04542d01528a40d910340104980c511801c814a0b030607225620051000c0c020300e40319800d00c1000480400c0c0361071040c0c0220f0349902180d425190561360030146107983c012958100a032104010710846160042180e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 742473543 1250 742472293 742472299
    0x406140712050901050402090604110702090f0f100303090b2b0c030b061206040c020312040303140105120705210106090605090906071b0809100215011e030f11 70
    0x1051005480d0404690090011640024011680d0703c1414500721041140e01039044191240000e0140c80c1c00d600c90504a0043c4000505210540e00480d0003800c045400301d80d0792000d10280f140e4000b9015181e0b901405441042c034100e4150340c0c004141410a00c900010303040b000c20860001c120401c0701c07190700c408408402d240422802d5403180507194040c08a4040f91030b0070100909401c00740d04a910301c0d43c1e400c1f09003100d40c441406101c018a41032000701c2c1103002c14441c03041c105c0c200d009580d008a00a0780e01243e50070020b40c0c006c1070700d0810303489288a030400da0314007010100c0200700b8500300e84007200c0c610058002003180b03000d00d00003010040c059500c0d10801084011065001c030040d58002e8400700070390f50f075101b0583e550718029240c0001140081d191508018411482003540b08d1044100c54100a20f0002240e0608500d4412401503040300ea10140103041c0300c207090340104001c1e2a104281041c0451050000490380000741618207140011303404d000c0c1c81060300309846000713 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 742474793 1250 742473543 742473581
    0x4061103041a06010f0509060c21090a171905030f04091a180a021809010e090105161d0d050f030703031a090a09020a05131d0120030406 60
    0x70385058000c140c88261005040c2d107100c0302088a5500c5030110080361940c5031611403034080c3c840100038240c0c02403924400305104501030140c00c40a188000d2030a16048011161280c81807410454a00016080603a588650711030303040b41842c00080c10b0140001d64001a00e140c0c0c4c1c50f04003107045201d0f0745c02d01c201d4000002400178800c03100340e002d00c1d2001c103110320402c0884200d00c1044124540d402915005650b580f02080313410340b007640200803010004004462880c2003d01240c10354030241d02c6004401c4c1540304010040c41d080c060342d03511804004003803006248519015080b419a09403a00d4820032071504001d0a0b00c801e040303142032a80000484920000140e50190341c0c0e400f02100f200024181007044400040c904032500c034190004100002550f036542c40c0038003c002c82c000982c0d2084401740001041d49a08400d000800c0071920007190745c449400c4908241071600c0210a101da161540e605040c01039100c55070203480c801400c040e501e880301d08091001e018200d004804aa000e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 742476043 1250 742474793 742474801
    0x31118041d0a03020f0f060c18130e160b0a0e130501080601050a0e01240e0d0525030807021005070c120308220314120c0c0111041d04061103 62
    0x8400c02e4140c0b00ea03013280e0354041600344098940c0040c1d111410190710041c0410461220708010308400c01040c059281b610030220002800b0344400121040700564450010034204020301c800c03810701c02d00030402011940b62103903261b21485034622039405c004d207000ca060030cda0b94050f00e40b030b9001200802071041d96103c120790707501d44400307100d0244110300d030709030014800d0407030280141221280130350f410304004030941c14801040d07842da24808104400074078100d40e41c1c030200350381d035120700880081404210407100d40c00300900d8825500301680c02041c0800004103000100c56045a058401a80c0400501006d480c07030f010304180100103030800c50b80411554200b4100484d03c41c000c0d61000c1241d1154480c6803005200341e1911801001d10b0b240340030110380240c01c00704a1010a070b00c00d41c507056074114203d40c00da10943c3d4070007500c00f000920449100003402400055071920182502d400c0c03410a120920b81d101030759581200b101e4000040c14000250b101d520b0b020302000c552a070f2403070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 742477293 1250 742476043 742476101
    0xc0a1209090609050919030503011a07050f0c011b172b056a0311031f0504080d020d02030a0c02210f0c0316050d03111804 54
    0xc012541c0b1710152140d507a02a00600000e9020102e054158549902c0c69003051801e0082d8940311106420059040162130300140040049108040e400c83c0500b82c51004940010302c001904a0841c1170030040b84079090204414400c8100380070640030191b5034580d070a0302c00702c4118400101581690503550241000c1e0070164200c284190700082c0044100c0800e00d00180310f070405030307030070303c1309840002003189080485440e011500007044454041708803002203000c05841c48000b194001a8400300100204601950000303406d4404a010f0301006206121110204040b807488007010b1b6100c10104c0d0501220134101c600c10300305032005565500c0d19504540c007a6109455140daa01e1401d0700c598440b80c40440e0002a510001c2246007211007c0c040800454110f004c4100c2c510b1410003d044140b01c1c02c1001b005140c803002030494a110507401d01c542003100380307980101814105800390360f07460082c0b0216040c89000c94400c841310481003000c0b90040c60b1058908007501c04c1c952524a96030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 742478543 1250 742477293 742477301
    0x60207350a0b06091918061508070503031801140c060708040b0f06031207030e10020601081b130f0f14060307091a100c080d200c0a1209090609 63
    0x6025002d52101c0e034941400744151090120752000c110302c2d4a2940382010382c855002800f0740b2035844003103207121107140c8400d411074034840303c8681075000035502002890700a014220017404202d01660030308140a074142c48040001202d14104004190307095151110b55056503011000441100c04514100341c000d425000251404d841c96000c04000848110b10501030300c0c86440040c0c060151044000840305090304080400c1b400c0c040d401c60b5251084d100c0e2110b00130125030690042c0181d514102d0741d030782021111141d40e00001c134007440c410100d84030b0b1203207226120300e00c4c4c90002d800110f40c1440310084c800301e03851103001c6041400c00a02400101c0005000e048110141c40c1120b07aa9401d4030304894a5007140381c4060b111a8032000c0518009d1800c200401460412480900c1c03103a40e002c000f94003072607403a501035644480080e8240d0070705039a400f41c82c40d0400c0d00391404000b0f00c441a81c40c110701d4002040940c2600340303522824410000c401c01844019404c2c02580c0d2150b041802030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 742479793 1250 742478543 742478563
    0x60905071a0a110f15071407060614030f070311310e01020a1b08091f0f080403020c040f15030606081002310b0a050c120406020735 58
    0x151071480c40382074552000c1403100d04940060003c5c0600705008682c0842d01c0002000041404041c10940039004c4154005007080d902c5010700041044c203080e01c50000d54030324411540664406110712000c000700255100c2501c0e04490700701005460072000030741c402d01c10744010781c4e28484d0400d84589000018060003074415a0b400604c20351141d07100040c00c034010304100c9030005800407c568101501d0b00c550280c014001e00f0f08915081089001c05c00922008003c0b400030203d44000e402010743c8100d2403916801e07185007504841c202500c000307680705080c103086440b8560f08c0d00180c488004551002c90350101d510311310380d00c030b40e500e04015009207810b114a100a000b0b01c64010310712081882240c10301e03c0c58000700c82d072412145a420300300c400402446401402d92000100c1e0049a01d4040c2c070100402d55919985d13044c0c3d08812505044078080030030070032103041c0b05c10300100760086061000c0d80e034801d81c2c40c00391807068011100c001502403c0c94031400000d03071902c019148042030034605 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 742481043 1250 742479793 742479797
    0x23010b160c08150903032e0b0307021b06070308010915081b011e08040f060b0307030819090e0703020a090312090305060106081009111b0304080c0f0904060905071a0a 73
    0x96500c07101c209481e840100d90408144001c29510700c50403040c3c0389540320052907c0d0400d20029150a0300e601d0503030003a0352940c0580d0104105103500b0040c100701c00400c100c00d603042410240c0750741d4007810555060040101e0b091315118800201006004480020300c2c404080710215004c1c1c00481243c0003440304460700144560a64030613155600c020301c001d91050b0f40e81e21407a070ba01d030313194034144270a640011a80c8c241c48000581840e5010402c0c80c01440c05019002d56480741032010711820740c850070000d024000030480070410f151500182542c42200b130b003009070351a03003583c20031982012141c00c020070b01040d0a034003000550344660312409603442407080f19000d0340c841100b500c803020121100952014180710900c8a0307000d5410844482020003003403410000000413102c3c0306031902080e000903134404a1304102005041001c1c4503c180192142c21900201402040340b00a0081c0301a2545032960081c804101080029030001c000748142410401030340c030f4202190382d1091a502d80 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 742482293 1250 742481043 742481083
    0x2040f0c030b03011401051c17030105041b022806060306050907120c06030c050c011d25050405070c02190f270e010608030d050a23010b160c08 63
    0x2c1d07820b051040c0440c0041e0b20359608100e0380b802d010000002c041e101c1c0001040007142e084400034074900321050183e0b070080c1949480f581007806100c01c80c0d414111010b20b0035044d0341091500d503004500801d00c58485025116244a0031104c40864104440c00030012840c003100001800100d510040c0290a048151144242d444046410003100b10b80050640b803c401001c00c803103030003a4090206030240d400c1032801c010785084420700312002c0800307100341002140301039042c550f8240f05000c810088040650700a8810b05c540b20350b441d020b4003590380655a100c000c10215170199044929466000b000304505080311002c0035440726003841900c400c24005103001c50120207021070704818010020b001c000c0421082022409071501d155000c0180d580c4050100c1d0300102400180180c5100a0003c296800c15000003001c49980d02022895002400014030031241c000c1e031a03604503214100b00d161558041d40d03010180c2071541c00028036903d1554000a000007000c03620013640ca02c0360350410 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 742483543 1250 742482293 742482311
    0x13020301030b0f0408190e09150112020f07060e032b0c050702011b14060705130e060f0108190212010302090601080f13030c05030406170c0703090302060f0702040f0c03 74
    0x6510707001c0540c1c0c000c221704410310402c5410703020307000a11120340c86880d004100c10f00007030204014820683d0003904580078017280a15950700320300d801e1060703c2007030411450050b07103010302c81480c0600b420041c00e141d01c400056115090400a450000c029641100e03031040141103142c1c810340c030319180e0010803414a03081e141c03140e01500c140c40c03c180e01078681c0f030034a01d40140e2201c0007081c50320307044420802e000c11014481e4000c0001d0b500c00c07503054442c641e46e0a003040340810140c01d580c0c070984545822000300320030750300c8900d4100e041c1c00d0282003282260700c403013040c49010702000c0c0d401295103101040b414500d00303102c28164104da0082c3e82820b07440d1613031300045403802c00840386400e10b1030004012802d0100785404c4c18520030b0181c84d0440c44842e20755916802c6038001d610020001c0c10542c5d140000f60b04090109401c2842003c0e420f2902100d80d40151141a5910010388250701c0418042400004d04040b2900940d00130000c115103031080c3c0d0f12000510320403500200082c9006045 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 742484793 1250 742483543 742483561
    0x90606090b09010206010302120114010b091c0c03060c1211130803030402011e0c080c0a0203070803160b0705091804150e03090f0103150906150f05030f04020102010b13020301030b 79
    0x481000742d040e0702038010350b8219000c0c450720301601000c980c015941c03420019035035840b070040180a01440d422107603446007400c2c2040300010f2121000800c8514074681c400c006000c4e440da580440350301c40004600c614139407200303980c081903482e0740410380b80c1840e4101c2010010040141089c01d0040c50110740d040e140c3c00350302e569003c1207800034082011050400502181d090a13102da01c1101d1612400038100d075510072380c003a00a9681848650f200b0314035181107127011700c201c60280c05501e0045080c0b5030a5005c42c1102c2034900c1001d07021040352004146114424005c5031070030074006d08010030030041039030f0360101404210f8059609882600640c1c100c0c0c03400d40900c001480d102e90056040c08201420400d044100403071084c141a41e4101c00c5070741030f0b40083c4000003000e0080001441d98500ba81e44044480f0260342c400800210055005210303070488196600041d1040c01602103540d00e00c0141d004140c1004150307403000c006580c1e4070114046400440c1600d100d116504c1150320340440b1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 742486043 1250 742484793 742484797
    0xb0f010b03070f110f010c03020405030609120a18170f010507140a050d060e0108070f1a03011e0806012d0302010806010f03180305190e0f060d0608010204090606090b 73
    0x22080003e0003c80342c1d20001032049030710580402d075500541d110340c00e003040000c1c02c650114880201094000ca420840303407509000703140c3d0107020352000d000d40c5007003044481014801c0c48100c90a11140000e02c03829950305170800d201034440f10b80385400c0c1208000441c0c2d074400c8080d06601003507003848006071400348101613891400300005070550505802860a480c1078201b0b0442d502e00f1580c5480000d080106180c0e00b82c006c6c100500681145070400d046255100c000e50002099100656000002c0745d14100481b0304494800c140023078041d146451054408845a01440d81d0b031207041c0021915450300030000d01c2c1080440d21541204e0601365440c2a486210f210180c00300300c0a0002503165401040583e0b0081c0723052500003103400102c800011050700b01c110039000541f001c900702207081e41c0c0c08100341c003202203410000c1401c4421000244510302d03010b200c0d4050031001c0341200310200d45800c210060070b0100d00964840c1d4481052000416103441107134001482c00c40c000a0146c0a401 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 742487293 1250 742486043 742486051
    0x1407062c1b10120516090602120d020a1101110d0617030a0315080d0831020111010e0a12020c0a08071401090b0a201501050d030201180b0f010b03 64
    0x49985018181c04201800c0c04040008080c405580d4240d5416616442482d102e8a0500a04003691215100081c480c07070560300881c05540c0040e081900c441c880c2416074200000c21a009a0307162140a03040301e403001c0d5201c00c0c034460342c00c02e80e18840c48440074018000d40758000703c082200e295101c0036600d450b100c15000c0d0030507400c2040030560451003900042090c00b07003020492891a61200346a02d400410b01c1400002a41d00c0f050107a5090110700d0035040c40e4000107006000044c4500c43c40c041c4121b440300905103c6d009441d503000301000e40140301c1190710407096520008142c10101c2880240c02d45400050040c83e2101d000344c40e20a03150b01c00d1f13480900040c140d44d401d00e2880c6543c250380c05055810b01c44031100004880400c04010445404280c1c0e42068442020b000c4424800e00030507240c141d5007021482103c020701540c0c0d0035044403000c8401c1c106015007070405138010210002c880d2400031a04110304144183e100c43ca60240b00c0c41000110181c0e65071900d0403090100307903 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 742488543 1250 742487293 742487323
    0x705040509060405040f0f0602130b040b09010c050c1806100c080403111906050a030605040c0f05031005040c0f11070e0f0a14270307020604061407062c 67
    0x20210740b003400c0070750050b0391180c4950840001d0400c1c9840340140c864020008030b403002e8001038102c074843d040c5044207004291601129003441d040c945c0311901402207205403810040140c140c80c00b40070040241d4034031400080c241c110140c041c000f00340d0f08402c2c100e6006000d4613418442200302441554591401c64002401d903041c142160f8611441245031702040da0f000f01006410b0500d850307521080c03001081e541d2107542d80d0346a06080501a03c01d9580124407131444c00c60360380c3e84650030050708000700d01c0d01e14103281d03250345a40c01e6003510903483d001a41c102c0e1502480b021180e0300301c7d81ca040c40840175103800c200c00030980c1c40b165451800d4050850907420200201d241c03032506015854005041d0b6202040a51001d0000d01061030215000721a1040b44500c104140b4503250000d00c80d8003036080507515142c415004150644258400c10041208045800200c3c460140903155407550061051008121041e0004002429060313100c685192130110086030700740c00200700c11804101 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 742489793 1250 742488543 742488559
    0xa0c0b0f0126030f0f030603011a091501050c0f0706140304050a1403211b130b0c150a02070201090503160b030604020c01051e0117072112090302030607050405 70
    0x2c1c0011102e203006904a03105144030a000302c8504500000107802201c0340050031649a18002d010103003994050f00c200c105400c2800101c4100b074480200743c0764028002065800340a1000004071441e00c186040b0b401e00d800351032118588640e000c80c01c1c908880b11a0340e581141084036111031407510082d140240191b00130a03000000444803c003411403081110140c0e420010100a5102d521800d441030110540c1c0d4542084500f04240400b190110a443c0d0f0460900d280c0340f10040c0c46207400c0c01002d09002d0701040200070b4840422081156a258240c0182103090040034400690031440041380418030400010841e4100000c2c1c00310002051030713607000250b250403e850001d510292190b60055000c000348600b40700c0900410340501c40000f0307005880013041d00e081c645801c060304143c1c80380c1001c0b001e0b5010b11100080820580e0755409036440cac00f002d210141c407001c0c106010024071207882603140c5810300d07400000036070407240250309491691b0755000e0115528031440c06125480b43c07071 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 742491043 1250 742489793 742489829
    0x80109060506120322030b090d0f02010e07030609020a0308071401050109090519170412060b0405072003271003021611060d051f0504050705040306051009020a0c0b0f01 74
    0x20403c410f1070601480b40344005c1c440d4036070710352900f4490b0444500140c0e1303005244551040f98081c08d01c0d503540101d44020807144502900668848810b440f001e041ca43c0c8950b80c042c155903580d24140c004562103a1810b80d00e01c000e19003654031240006c80c0034040d5290100004414015019100d0416489000342c10721084c42100e4a1102c0b4011106031401c0d84c1740d080c0402c601404900410140c1901100f000400380c1d1440c00000381ea0000742c0150090f41803a0600c020240c0080800098403c0400702c032405416100c400d5165014944608441c0d5810380190a0006001252080c0c924405d0381c031869201c0005030180c041c2c1c45048801300403003500c4444a408a1035819003045100e4005003094076003a60b20310108180d0b032003a00d00640c01c88503040e240203640020309140c0000d140a6805014501e41030b04042c10038050b40c4405400607884800095405107250080d50181400c950211b488141d00b820050601d00d115501b101d50648001c08103419203108401c490484149030710704104040 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 742492293 1250 742491043 742491067
    0x30504090c02070b0c0304030c050a0e06010c11041d10060b160201030b0901060f0809060c070b060607021e040c0e1003020c0a081611180f060d0c0801090605061203 72
    0x3802800e800714052110013089002d404030007040030041441c0110785030360031814034031590305090740058440c5010400c01c0008107000f80b8a41e601800c2400c003840d024403107041072201401041900c961003440c0502c9001d00380000c42c1d546120f10783c01d074129009110f0f01c20b004021611213020708002c1500c00e00c0f00e1090030790a0f91003007a80610601d4045070640448010810f080b10a80054011a012811854034642e0100060b540506884020809030070020a05c00c4103206600010f4101120040004c6c5240c50307000496011546c060103a110382041085992511040105010710581c24880a8800301d40704001075925004020510160a03c0c144c8094000798040340e088106400b40e24484400700381c1110140c15040107440c00e030011440c1ea0324089650f036090588041c0b00f003120f1010a01841c105403800c075800701641c54025031a0f2140c0f80060700828510300d000303000411144002c900d880064000c0030b08207100790014030680d103580080120b034807081c0d03421041e954010712040910603 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 742493543 1250 742492293 742492301
    0x5150606090901090b100504210201030b0607060902130b090f101503020307140a050702040b0f04090501020c100b1c06060e0103080a110118170f03041a0906010303050409 75
    0x400010600d91820100e4000b06101020907406620f005503615040100c5082c5945828031283c581c0c0340c103624150400a03508104502581c0380900c038100480c084003164081e034002e6040100080c2556281c01d100d20317103140a0016000b040b8000c282c03081c2620050340d1240240d8120300c0000308201c1301540d074403040401101c0d00400400050340d4403c0005403130103c40201700c40c0c41d2007a580240e80d80c9030844001c0c2451100721880502200c0030058020200d40c07103419110500c0c1d044502007100c840107000144c04551804806900601d40048082080015402442c2122000059482010790044094210b851100d00d11f608004020300c07641347c1c444401441c0d22400d1044100150003500c2e0100c42c00003200c240c00481d0610f0001030100c0481c1d4103c403c1c1e07480040440001d10181c80c1c0b94210080d041540c1387d00800c254000303500343c44640030880c00d407081c002c5080619601d901e1300e070400150140300d14905040850114000c00c810b0040414158140c9030180c407841c0c40c1601e00058030000f0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 742494793 1250 742493543 742493551
    0xe2d0d050c0114101a0310060e010201140c0406030e0309030304030f06022109100b031c0306090c050403260316020f070e01090e0c0d02010c0302030409021314030a0515 74
    0x3a550314018001915a110510f5000e60303007004000500301d0800764110408040e2032508a0b1203d01030041041088198200000b40c3d111841c000c1d400b00e0403032005038050400490300140717800b6880e04002a0740c90f10000341080399840d5030140015803080082c25101d2080202c01600358008010900126049032000142c15115580040c0f0b03082e0608032503000c2088001003100d8040007441440804030301004182840110003008202c00b0b9450000640d48550001b980c012911010820905071030003648544024016042c05006007024000014800e170322502017103039002c0c0340300c0d1b6240c9044281e0450444036102d001d42c81e451602c2d4030490305e821313014410b4918210b11824540b80504002800550002c10341000c0d05691541003140c01000d03100088040d14095114a02c0404181d590040540c0c16503020b08007082c4209090400702e05501c12034000454060001072981103000c50070300c03008211424070b0141a02c0829107420142c680b45450006001d50784003410900c0d00038001e51800d500 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 742496043 1250 742494793 742494817
    0x503040911130b0307080a1b210f06031a0915060627030f0d1707021c0c0506060406060503060f010e040906051506030f1602010b040e2d0d05 62
    0x1e16800b60342180080c003041d0005096900c000c001e00c01e2554021070f0341c6170440139040041c8a12054200e410790f015210354455030410040100b9407086035001c9402d03024980c1107030010301c26804c4c000c0101024014503c011a0141481c02041020481030348480340501c051001800301c0510b00507011036280c01c0900300300d40c0b11004201a8410707030003840d080d40010004001154603405810308040c14010056224000c035000150460320382d5602c114450003032003001d41c2c10b0070b107601e5440e002ca10b04502c0c17442d25605204200061006990840d01400100c0e00c91012030309155545c00901c4217440c05d521418010440520110301d0a1510300503d00383c0341c8040c90480d07a04080c9400080135540c4080040c1e4045070307030700c0600c0120f00c4540700d19007840f03005403021442e508040f00700702002c00d402000c0181c120100c4807070092040c030079000a00c40d80c800801c2130020100b441c42d080d031039030b501818240c62184402005140960740000d15048501240c3c0030300040c40c0d14442c190380c680c0c082005800 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 742497293 1250 742496043 742496047
    0x507080a0e10061401201009061b0503090d02030a09060e0312040605130e220618030302180a0303051e0d090b0f1302030a0236091002070503040911 65
    0x1c1c0d4a030710b840340030004c1a003e080140302504080024000081d006040368038102c0030840d030101e040e80040da40d1003100c070701c100000f4888007501780a401030400380c1c1406c280f4107546081498503980940914002c0000c0401d880c6061000c1d1000d036030b42d1288042d46000b0800038a0104050340c00340c001180d104801600b0780c0c00e0b10041600f08129036105400c0340d0b02156000c103120380c80d60803001e01100946044a070402140c207100142d801111048018260702c8001400c110042045035040405c44503ca406001000102c0f841c020700603402078403601c030030074082a1001c0068038104202c14110b07a010f484040c64400005804003c01c6210698250323010340402440049284600c541c2c804140680d0700c804040c04d0103c50200400e101501c0301c81c0c3d41c4012041e400240e540032841402040d070449001100c040d5070500b04c1e86600c514104030303102c0da030f042c151815551112807101e4440c040c40000d0b075455160054445080340900c000c080c107654000d100601021940d517000204021500340158 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 742498543 1250 742497293 742497313
    0xf020d08040f050106180c03200f070f06050a0b04140601111f090b1f15120c030506091003081801020f0a03030b090606030609040312020f040323010507080a0e 70
    0x2420745d0516404015480004260000350710a1403041d0318442c001c1d481e050101040e100c3c010707030360b040c007083d0402e10700480041c00300702e55400c80c003c650001c1e42c000c0c2d1240a011050900c40002e2208880c20912030341443c206048030300e41fa0ac190909420080311089035515043c1c0116150318600040c90003a20407420031400161000c91101c00807a454140800d44d07200d6890000316002e40504032250680c19040741c2d0f2091500110003a0070b64065a40079030b0242e200100880f598401112000012441e115420b405154550803591003042c0c190350408498841c00c1c00048646102d05c0080c18140d0248140044000260485c07200c07090144107e400c1800444982810308011030f4007100440d41e00c08201005040c50455242c2c4503004175689421131500c00301040540c0402003009040100202e490700c01800c099055840c200280c80807907480d16141c2c986005a090500c2c62840d801070500400c64040340140510781c4900d1050341c681209460300030351040600100740403030381940544503000d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 742499793 1250 742498543 742498553
    0x30705040e0619060e012904030f0c050a0503120c01150608090d03180b0405121b070e04030c0219030209070806010f0e010207180e0a0302030a0f0f020d08040f 70
    0x40301050300042c02241c202100200310603410781c02c2060503141040070401240302d40e600c0c074604549140360f2408602510510140c070415185900280d0002c0c00f050101c1409090f24034928440d20030401c1c21091510340d8108124500c8612034164560b106010055080da50f8074007800ca107000200010680c2c00e09a074419400c10a0b54000c100001d034007400f000102d40c410000ca80750a07200382420040e0b11200c0c3c000305903080801001500d00480b200c040350804c03004110a905044160103031503181c074850555040c80502a000300c0403544100c10021802c5100c0f8443e05003d03a50540342d044809515500f4001d1042880500088100c10307048000701684071b420703600b84610000d5665500d289012000585400084221641080150920300c400360b600001c1207002c1e118a20558940d40401c6102000500344c40044038015018008041017010b03000000750140008503124040320850300300b000c03600040e2458240d40141d02c140022402e40f4060303610241c01c0f44c0941c2008a120b00b20b5118 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 742501043 1250 742499793 742499801
    0xe010303020f060f0f0105010507110306010b1804020414041119020c040627050c0706110901090b1e0f1908060a051206010b160203060a02030601030f060501080703050603070504 78
    0x1900942c00490b0491000002031288551042040000a0712401c01072049120369505009240c180f01001400d4401e015500da591205200005d04440403580c4440c041e070940e0f00501c0015400c0d20003000340c0311140c0b81074000c0d2002e82d41c2c5009081030240520080102a003102284e0f0f0040500030080b6004c1110680c140d164044110340080a01080080030701c0112440c41d40709403070b070181c0036410406101d114111845284454240480c45454280c05c145503817242010080001d440e004400812008a00240c4000c40c4240c0b03c0c900050303980e0348441c10510810000c05c1034980709601e18000d086020000d0040c0c00782c903866907414903406070401014404221415808100300c01e00300803140c80e10740d00030005000c0c1620500c4071146d10300740e400da44141c1030180b2200e902010510b9a110315881050321a030903001800c4502c10f00b082040c0b14001e600a031082400641003114100ca0101c190180070101e9406941d00ca41580d01e07101c08030000e0401038001a40b6000358000007a155a607809 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 742502293 1250 742501043 742501049
    0x1b0503100b0f0603010302090a050405190f0c08010615050309030403020402031515190c1401060b0a03061a0d0b130e0106090e07030203190c0801050a0902030c032a0301060e01 77
    0x100020036404103820041401c2c0c0b02c0d02e0a501c541c3c0104014070050310f40d02c02e5640c106004102c0860030340c58601c2c1039401c10001c0c02d01000ea00310040c2c007000c08c1c00203d00c0c042c00c002d40200d619500003510750710703403600fa20507034046c4c054101c00f040c01c4604038078413410045038070415401c00d036410962240e002030300b80d030320503940718541c040011010314031807030140d40c40342c9400c295584252901401214403042a1540303404641440701c071520540c03d004400c0c40d1003445031101c90007002420703250702848440760070184100000a18001000c40c0380310310440b0b50300c0711601c0d0140107401c0c03900f4400e44178090258510f0050f007004982e41e0308000070289008440d1004600400810b00312b05046440003180c20700080f010440d48042410009a203020a060690b084000100c01107140c1d5400d0202c11500d032607000050940c40c201c204020400f45034450b00d0300c01d20803400d540000c44008201582e410585465015901c90b060202c4800782d04040030030070004015001092080c0c1e034101c1d00148034001d80c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 742503543 1250 742502293 742502323
    0x6013b0106031b0309110f041b020601031e081c02070c09020a0e0f0907030c0215070c020f01030c09051c0614070311070503040b1c0c020f01050c04060203071b0503 72
    0x2c4083d462036001140d1840c1020b503290402007035000362503904d4030310354845d0f449006019100b091049074030346030828041d140000c2004c3c421907031060002903441c40248000e90b41c007440a44203200c40003003080e80c0b811203500203800340c0c2080e00d0260b604010305040b03800c007920300c0c0d400c01c8000002544000344400408100e003006850715941c0b200940f80c08904075005101e0021442c0040c0c3d02d5a482d40c45c960820310750300c1c2c0001c4a030301600080e032a00e40111201e4800c050140100002d80303a0200d80d44240f507109885c8040004a880c005500740d440714003c0d04040b403803000f03050080b414a600100140f61a1a0002e003103401c150b00c030501201c0781040064818440e800401c00501c2e0075000c1c110100c036040e10300301e01e042c5281d140c0c2a1240103900035a61541c3c1c00144403d03402050700c50010b41c0308803181c001c02228140d502c0282d901c05c003425481c4c800c0c1d404c10000900300740907001901e00300c83c00f58000e0341c980900c3d90703955100301007401031105031403e030b540000c0390302d4404101c100c480c0c030800 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 742504793 1250 742503543 742503551
    0x201200a051e070612020c160f0602070902030405100b01050d020a03050105040c051e07030315060206060315010f05090402060d06151b030e09061521010806013b010603 74
    0x41e4129040404500350358880d83c0031480400c6055840440360040003805c00c40140c030380036610314070b504000c0001c11981c40e94a6200e004500c10040c8406a000c80b0b0300707074080b66040c50b544e541010a0f4001103130f01910707540109842240030852a001584034090500d4100d1410807036441c3e42d801ca8101042c010b0000c1e5841005200741c0c140b500c00c2e69200c848038104582414481c035199001c41d65008244500803002003061020503000e500651142201080d92401080d00c0d818000d680304402c0710407038802d2140d4141c0c807508907902078115050b10303050010580302605203018880d001c2c902600881e001203080000c0040e0200c58441c071006000e4269544c4950091160300400e000c507045080410b0040c803810f103900203504407104801842040d1054292950b9101c00150154203280e401c0380c082d4000111003840001d9035060710100001c9003040380d2140d81741c800d4582d035002c3c02d01450412061010454140354200900c00100000411542810b466600c283c142052420303400f25000c2a11 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 742506043 1250 742504793 742504813
    0x25020a170d050903040b03310605090c0405010e0628080c1002063304090b1b03090604080f1e040e0a0219030b0a03021c1e0f0201200a05 60
    0x6600550783c101d03251100850030117040030205883c51102900d200d0003924404030b03076052035a00d21902d405c408802d00e40520b1502c2c641c10048003800701280d600025000e004418401490b0601c54035050340c4401c406c9044680e00c19003400b8806591300343c4003800d0341200d08a41d00c0100c59200031005400103502070a0031365069018400c9000d00d0180f4031040d5001340f420041010725601e103800c0d00c90030384044d1005c031240f0014040e0342c0c1c00403500007c3d0000d04042100f0107000c128900140500040c0d00000c210120010303d6042900040e034281c5201d820001c045408128000d002e080c40100d603400180c500004140b040714248240000c03804a82c0b00400c3c10001401040d01c5c8641c09038240e6001d40c41d10b9042c000030070400c01e0505c8008103065640454115036140c02030060050b540c054000a481038510b9085d07a0501c03180101107503140c81098280800032098181c0c96411a4010741608101c0615801035802403809041044d584014600031000b020082007510a0f0500030790190005202d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 742507293 1250 742506043 742506067
    0x50f0411120a0c1701051617100e0f01080f070b07080306151305152a10110403050c1002030f030a23150406060e0d06020c01020c2425020a17 62
    0x880200600d001401005c400c5034059085000d04845a81e500590a00e954a4100000300027080340c11070005403001000b088402000d0740c100a05881070082200c00550f40302d60751a03510b00042c003511503d440280810000194048095500448014058224010318609107071980c1c01c03030300181030301c103031100c500b003081e4140303071040001c00028922200c0c5801c0c500310351154030144000c02e280c12141003491031080c0260601c40400040040f130414001c08480d01e501039a2900300303001c15038090054046a61003480d1403500180f01c54802c0c0c01a40c20074443c2c8507441c50980006101c07601060300e8101a2100762908604103065452582a07078002d4207000b1b081c01040c400c00c6520030f010320700c5d0070004c6c44040e82088104643c03000c121010140c11503640f60590180c0210a0340c016a580040ba61030b8000d01e01192000001d40401800d08500d00c4030b9000d901070301400d41d12000c00800765004401440750442441015055600480342401c820f80d232151610b07070800e402a88440e00104a81003500 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 742508543 1250 742507293 742507301
    0x60b0a120c06090b0711130e0f010b0a05060a09170a0b070c1e020603010510020c0306181605210115030311070f14121f020409050f0411120a0c1701 65
    0x41031180d00181414116036550381b00031101004184510300c2d55001100207440d0b80c0102c1e11100a49050b10082c0b0706c80342c03031540a812a54003851150240c1d000100781c034103044080e5443d5864554624805600c3e040065201e50801d100055090107241c1400d0041358844040138001c0c0340300e68851a007511141010002c580d1109083c0c0b01a030501488030001d030340c1d1181900c2c150350301111065000343c59034805901d0011040200394040c011501004103101c003070084e40d80d5070441c400554030310200c007501c0038170b5440040c0129503019a0083d030300c0d1303001c59030603405000c602030701e1000140d11003600c1c41c1190b0754602a0b200702d00094144658003640d410034400e040081c00240d40003280780303080c0000011070402258032a0b00614401411180310301c3c0412141c0c680002c2210104050700c0c5400910f400380d44207014450000f130030080450310b0200f80382416031166400201310070712804484104004a019881080c1803480341e0412000861011003118005203286c44c070703031072001021400c02420b603 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 742509793 1250 742508543 742508549
    0xf03030a0323010b0a08010b07200f090103060219020a0c0b1b15040c1e050409050106050d050a050c101b141b0a0b0a080103060e0102041802031803030c07060b0a120c0609 75
    0x55040c090038000515800c520f010081c0c408800b51000c480390341c04944bd01d80200c1d071813584052410f0001062020701e900038626102403600e840c800c1440c0c2401680e85034800c650081c200007100608210810030480601000700d02c0d04101d030700b04e1380000915440e103084982c6030070205410742d080c0010009103405220003003580314407080c03d440d444010700e141000e89110f01405240c0f01c1c025801001804c0d8091005460001c03c1c0d0800c1110030b08025507947d1031850300b250540700301c503000412450f2000ba922032441003a40c2c0e506082040600b0051802400502110708a0044c1d605c2494102e050010b0907150341090240080070b80c690082141d26075440d80180c881e15000c0044038101d550003102241901c0e00200d000c07030380c0c0d5000c101041c0284269404802d22038042d480c1180c018140703400460082c0401c0300804030b44800c0f003e11544902c82541c0c02501008108114070019103035400c00140080020b14044900790b03541510829a4450b030000c81354104107000902009801600d40c00c0030b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 742511043 1250 742509793 742509809
    0x4030e0918060610050a050f040f0305031b03250c0e1305010f0b0a0302060f221707082d030f0c15100501080a0b19090b0f03030a0323010b0a0801 64
    0x13040d130b0b00450140903485000584401c0200000c0d1810303038104104103d50040000440681881c0d549081080d100c1d04950303840405010b003c0d289000f524400000e880c504c50010000444010005003400400003582c03404030344c11000d021002820540e02002c00e8810261000c400d501c4d1000c2d40b45c0542181d60780840341e0000752803c0c9441c1c1c85c0703442d820303040c40c2560f0341035540741d54890000300c1c101d0040c010207132440c040c07180c8604001c1c00300c00d2a40b500b004854034951465158644501138581b80c1010303024104560b40400001d0b81d400a5664441c10a0034414503050309000d2004619819a401005442e081d4a40059008100b050401020b070312881804003000f29424009000d080d400e54a1007402c1c10089464089504000daa078407a1048400060400401c00306d0040b0351480d00c0362501c68002d9852401d4456400c0307080c440c2c1c0e540c01d1500010051443d144400030241c00420600040780c403030203501d00b0f032030600403190220075010384042c0850548400802d036004246120581003066 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 742512293 1250 742511043 742511059
    0x1e0109110319091b180501260f060702100f0b0d1e02030618070e07080c0d02040e0403030c020715050913111206090105010507080a120f0603030c021e03120304030e09180606 76
    0x198015110103181e640b1541080003148ca680302902c0d11300340848a00030b00c10700680f010310452075000510005a242c82d800103000c080c40c8959000c2c01c032074501003a182c008002d01c81800002c0c4440309600c8240810b11952172101405030042032410f0350072525510300400580c103451110100300141801444ca0619990251a181100604402d07000d0b2004402c100081404001d40b0380781d070180da0180c01d00001b05555482e050400901034090000c0742c00140c01401d4003c50080d107000c9041900e05029140d00d0314000048050044d4000680745074010701daa074a000404881185000706098036100000c060281065010803c20003810391080e0306000b010444200040c400320143c92015185040840c241076442544002a200300400c645d1080e240c02c50100404d0b820004100000b4000d580b48007114034000801e01c0913100c44104240d26600040c0e00b058419000c3d00250740c0144245004000440300718003003524044155030000701c01916001e1590b00034000c0095542c0090110b0f0412 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 742513543 1250 742512293 742512299
    0x1e0e0105040b01021c030b040c020309040c14040302010509031002030f041e110405070e031c02011406061c150f06020609010b1c02030a0b1e0109110319091b180501 72
    0x41e54a550400c5a58005001d201c085c212503800ba81c804181010007800600c80041158030094031b0344c0c450b51665111b985040314006500b0320410540b5170031881c0400c21840c2070304540054030280c1140d0300c480d0b410b03c140009162654803c6c00518050f100001c41017072241018604007102c000c44901c0341004031500300d42d42000c501c07441e01d0703c0d031a00f01c03d80b4009080d0f00e414004031000b10400000942504c1490420018402d2101805004260300e6000300b0224100360100381032800b00780e034200c0d030150b010b01ca040d1001c05d0b4107800b8107a030300200900040b0510340121740040d520340785d4090380c0d04a105410070411190140301c1c056020007948020400345010b0000104c039036440320281c0207404840d00d084011501d082203520303419a048903c509151030410980c00000c01c025610004030000800002103078030240c0254500b6645040d40c40c4d040d5030b11480d0510754010941400c0b80303010744826450300481c0c280b2034900303e28104c1c0401c29035010305000480784030081800d10702a0140c9884010 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 742514793 1250 742513543 742513547
    0x17090306040b060d05011a0301060e060907140409180c0e0f01030b0613110318031e0d090218271c20010506090609040b130203071e0e0105040b01 64
    0x40c99116902524a0090351900c0000c505038401d0030308014410362030400004062032030751503c4803140c0000c50081c401152601b036005226270b025140c0700d03041115080490f1a55003d040c405030452881c00ca51800c1c60b0761a051003003503a054003050407000500c0607100d014001080707851000341c800f032440c1440724184914007007201b03501440007034844055040402c1c1a80d880030125601451040400c1c4002c54080d04000c1b8240c0c000e480d41070071600c2c080ca0f85800c058011041d00c0d4403178a01d01d82412a007160782140c4003154490024000d4641d80c0d2a054401a5210204240407503005c0c1500460f614140c500c080001114847e0308603510ce00d030f0304240381840c0014403c03901c02c0c00f501000d085185070f011306a54001d924039070340c1e061041c0d9900c05410507205511030b9100b62801c4074000c81d644c481805101c0e05800590f400341503240c8110008541904070344090036001e1001c5c044600e00740c3d4900355100c440c0700c9801e140182c540d2188080042c90101000f950241004031000c220171a0102c0c00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 742516043 1250 742514793 742514803
    0x908030d0b0103110a120c020606010507060905010b100201020304050c0a0f180902150d0f0506010f0f09180e100c08130812041218030309050d06060f08030304170903 73
    0x2445040a45808000e00709034400e400620b1032000e5904c0c00c548810100c0805031001400c100d44402e954980680b04204520004840317004100c1a1203040c601542525240b000d00311041c41660ba564850401e1181502e900343d0700341e00001c00394001610b0741030500d4002c0c1003090046915109400089040c0860715070083d0070340c200e0b00080507400408240404003005880308a0002e07500030206a4011108030300c5074001c001e0b03900b5450080115894101c58041169070130750f1503038009011150140001c07405445c1607042c014403410078910460751034902010481007942d01c0b40d00c0c1901c0b2081c0d040c10010030002c49001d03081d10344040c8820342e01c01d00c000341010390042c081c60316041500e00c0001444440320460742c0304504049001e0580c540750518290145151200100080c8601d0f00c5110042c1d000d074008054a525a0300c0d000198034020030001a80e845560030349a4540c0c132100069084003c0c0b0b106c40c0181f1802002d50784030b14140c10110880c550b01403030740303c00c0e08041040c24007035680461 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 742517293 1250 742516043 742516057
    0x2030601080901050c0412240209090a110301050409060b0409080c010e0703080304032d030506010905040e0a06020d2a090e0c1e1b06010306110406051c0e06010b040312090803 77
    0xd9500101426410f00964007a040298902d006131481c00e0001c40f024241c000305510310301550040e11584483d541c4070704482e410dc3c0c1803496400140010304c11464540c225051281c002ca0000c6030f00b803002c50002e800c0b04d0101c0e100311080d030310004200e680000280101c4880702a8007001c3c104891440d00c0f0b20510f448004c0008041082d00440e0064444c20205240c2190769285084500d601300200064000e040607a40c032400700e286108001000c0c42c003401500e10881c0c2d01d00141100301081c3e80c0d200042d4001e0382941d06200e40711a003080007482e41c000300802110620030a5615207080310780151924080380c1015088001130000c100c0300b602c414040701d87d0340d0842d20b504028540c1144c018519802400707900824089002c4114400000c000b9007581680d020320b80030030088605900411040c03186119071004070350f0520020295001c141100c0920301061070003c03034907091483c65242024400d810030542010081001d00500c81d129054071107400c081d081c6500024201410a6038a00440f1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 742518543 1250 742517293 742517309
    0x1110c060703091208040306060b0301060c15020f0706020d05011d011a04181509020a09030327150315060c1412040828261201030602030601080901050c04 68
    0x1180c1007094455030001004040306005a941d0040302d01d0205e04980c040c0c441940c500703090a07400305026034030300b045074101d500d503490314135440447c1c2e0b5986024031210580b540d00c0c039501b8020300c03294504240040020034400c0d040140d451140d10b9030384040380e00c181c00000030100d001105500e03c20814440b83c0c10f640440108401019201903a020326108680088540080840682500005581003c092240f028200314111a103884480c4220b0060700d4041f0001218260b0070000f0901035200750b03550102240072002182982c400808445850f41c0c031a0598189841c061055160703d40300c0d0300501e100c00d92240f55a80d1606000802c0c1105107280500048005c00d200b20020324100714800e0102c0075210901d446940e1009020344659040364424988074040304034031443e0310004140c103480c0354841040c2c4141064210089410705411855a80e100380404c03994100310207407507080c1e000354418a40580e803490914001082c0b10700181c03984420741e06203030034480360710900d03000e96042c1d807045 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 742519793 1250 742518543 742518547
    0x10c0807050a0615060806010c030504063e0d0e031e030c16170304081e15010803070c0806070f0302181e030f060c0702040b040615080f010501110c06 66
    0x6400d160742042c0007200000d110b14903082c0050101e032080d0150900301e402030b48480090380c1d40c0e1001500c44000c0700400600040041100303200c0a4000c0c02103038426202121340005402c102515050032541c1040348480110091914958215041100720500400c0386004004460703101c010035075a450394400940000740044001190303100030002e49050f820114112060003a034104200000300d0103014021400b00b03404c01403041c100e0300004480840e01840b004007120130850210341c40024a100b44100039020352840081713000c03800c580f164080c00300759001d90f03521102c0f407030402e6084049a010101c642c001c4010814055023202c180c000250160a015940b03c0710310350035500140c031242e8210f034441c105410700c2c29055015061003440b90030642c02c44036403400103405507681e811f04071a00c12810a0400189005052580005124a0000d0030104080e520750060740700d90480d000301c60b0001600c100c1004894040d203175074103004120a00b8a184603030400d207005520b031394003070940038052000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 742521043 1250 742519793 742519807
    0x3021203060427050606011805091503100e0c0d03050a0c14070b04050405070306050d110409060203070804030905010801060e091b031602010f1116060f020c070303030e010b010c08 79
    0x1950024020700340e403180c001c0d4003010070301c3c000c0b4400c0c641660140c030180314a0700054000e5000c0d800c51026079070001d00f52070040c0e14100410100120082ca03850002c2100b200415854a042020211140c1c40013408142c122416581c0c1d440c0c0f800b00c5401c6803040e0603800015011039041001c4507821041d9180110600b01c480c18010b10882031000c3d0700456100d800800140c0c07641181c0035009880c01140d0600c00ca440f42c18040302560b18501429900c000d80c44028030004190316110314100b00b010b04003207040012511400100c0c0c100b220f8100126891008100030150b002041e10301411003424400882d50400400602c494080c0d40c88074000c2141c000890141c000092440d141500b1082215540749000c4d10022400000104103001543c00c04448258800305802026a161541400c00d82099041c0c00140c00d1a4400700042d50200e680300c400c04c58881c40d60004118410001d801008007515500d402002c480b094241a481645003403104141c980e03002941700d440c940c02031610741e205c1030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 742522293 1250 742521043 742521049
    0xe06120a060b191b110105031b0a1716020d05211518191a1509031002130b0918040b01170c0f01030509150415180302120306 55
    0x100c0c2e0300000003000012440d20746144868160410301442e0b03969440546420f00c0700c1d0314001602803c02031485080403515030065100e038000e15406207184034000d440f01c02c02042c40321207902c0703100004006070202181e08440c1c40c9203545550003d2480001142011118600a40360071130343c0070340010031100150926100c03616001e18003210184035038003005802c013124100c0600e4654607910780281060054000003140081b01c00b40b180301c8101006441c0c192056600c1d00400c0e029000c84d10000000ea455080c1e920350300c00080015501038005595102c004040500c1d004010700d6400400f801080000080400c0310f0041c4100c800c551012a1030310303074140010362180e118885045002129000700801d11090280c2e65040318008462061146440035445031544419405c3c241c000c8020600c040d804d5210341c0c41641c2c0600010140e070308640241d000c2500031401568140c07504810822400344841d41c500c6160025070350315210100c1c002090381d000e503c800303549200f11040745012000418a40b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 742523543 1250 742522293 742522301
    0x90f0112092108091c050c15060307270c0507060212040b0603070302150a0c0b1906060c020d111309060203091501050315040302010f0908070308010f050a0b0c150403080f070e06120a 80
    0x40e14075415107001002c02c0700e4230b1860900c202c0e4402d20a100c0c2e85400039096040300004480b4030010002c088104010400300381c00340c81c07241c40c420100300d4108200c002007105c52001d4014081030b0250f01545042501740500394501c00341103188250030120381000107a80d540f80d8200c1c1400068400c9868120384001680d661a803d640602520381d0350080090600041d040c2e00106510001c00301701c0d060325010111645045690000d4002e10140640004240081015008800001c01c9001c410442308020400e0311190342d021266a900407042c00071002d820320048000030741d050b424192a61609000030341c0c9441c0c442000c04100d000340302084c1414030039002140781d4007550200f0711030303c0c1c0d40b03107080003007944800f105500281100c400407900040c4010807134210f80005060100b402d0a08584070b60a60205019880a2003603544038400d030f84100c0c40c001d218a010340c0b00c01c0c103549016140740c1c44003000201000c0c10044658a0b050340c40c0d4900d002c2c0c0c0c038400100b0140da10f8036640c1464180c024 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 742524793 1250 742523543 742523557
    0x31009051906060c0302060c0414041509020d060f170303070f0e0a0303210b130f0204080d05190309021e01020a0c090c030e070506090f0112092108091c05 68
    0x110308210340460b00f203030401420420780307219508844d580d42c0c80503c403802d24015406107c640a265880c0140c6600d0242c02030328081024041d940c400d070b9940e01d01d5070100e920400c0009009a200c41c81080800000c1d0b1045000b002c007214507030421443e03483e403e0b80301d01c4001c06100a02113005801c0c0c80651091004880704140501002e20b0303e52241000380c260445064200b124081001099455015131701810010001c0035107004088070810442102801d00150300214066080c440090f009908200c255101c00450710303010fa5511507036514460300b0005103024018181040210001a1662030080d0700b5914500e03403450001d210680100e0404001c0034000d0940c0c0c1181802045202065001144020994408201d40c0d0780321b80d6a07548400303e82c40f0b9250b110b0701c107010307070502c508010b403440341c520300145402281c0c81910b20006003100c0c41a107003542c4074446103a40c2281c031340d042c40010311811600c2c01c1c1102c1c00c0c40e1214202c1e80e41e42c08514030066202ca10700c00100098020003e540d42 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 742526043 1250 742524793 742524841
    0x3060c050f13090e0a03021c180b0306040b0303030903041214010e0d031805060a02030406020f0c0f12030f0a2c0a0b0c0708030c0f0714031e03100905 66
    0x55000304500d04002c141c541e0040c070310300e00d01d000c00350b5101660001c0c0702030a255168002d041d0a1158a1072030000310358070690b84052124038031045440b9080148010040d1401c00e10f00b5480382440024003044607140f15400c5d020303510400900c0500540001610200d500d00e00d4200c0900304d251610402804009a4883c01e03503080c2201c0034003880c0c002c50700d5001c0421a0364100000004056540e1074212105400381c0035030406070206d01120403907002958454014040545450300129100c402a880002041d2464000c2200c501c80d0b000c3c113000c9011600c40d171003202400c1d4280b4072145003c4440c00717030105114582c0c90710300140340b4640305210b20152001c081b8551381e420400e20105d49481c0c1103031080b00e45c4228070001401115000040c0c600c131a0700081c465041d0360342d04d421001d06901144100c40808014003201c0001518180081c00050901c030103162a0007180364205000c4c0000b00c24100610700c00c0c004c0256510004c02d000d000c0344c180c5c00020400e034464100d40401030b6130394882245 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 742527293 1250 742526043 742526047
    0x50319020a260a0b0a0510050c010902120303010f0b120a0b010c050712170408190c0e0a02180109081b01090e040b010315050c030103060c1215150e0a03060c050f 71
    0x84128210b1818601c80c0d01c40c07400070f2201300080400c02c058528a40609580011041d0301c12485038442d03009000d10f890b0b48000003d040f001034000a161034490300041210b03920010042c4911544198120014011300f0452420094001c1041502e8a4024102100745e50382e9462100b660384280c1010886581250940d90707181d4440465520346256810107562049800c14050101074203101140e0850705010080c018401c0000307141009404485d10a84d2014801c060204090f140020700d14090701d905140166925840307180c0750f04011141040a05100f07001a0401450700e010454201c0c0c45400551520740c4060800142e0321140d141c0c20220100e9000e500f048200100303003120354141e034041e0a5405480c003030f00e030700705043c2c0305e04589a400c1c502c0c080c0010030000740d45070000d805540960420440501c0000c1c5220b0482e000b030101c850140000309030410261045440020355081286800c11031809404081640507401e4400146955540d10034a111244100185c44480c15801040340d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 742528543 1250 742527293 742527347
    0xf07060c09052103070605130b01090b04050601030902030a0212030f0f220f030204090c08060a06030605070c17090102031603050909070314180c0303070b040b07050319020a 76
    0x1000e020082c001d45001e50710303507007801094800034000c2d81d401540500040d880e00200e0b030384807806000013528158429a201d0400e00007d25120440b1f070181c000c91200203440d030701e5881040143d90300901018103142c5004924000f503180480c041d05d4640d015240c0c000072541820a4030318505c6600240c521040b408a80ca5182035505c000802480b0488a0414040e540000500d95134807c0342c0b00f203440d0070918200c20001810681c000000d094018104421110794a03030030a810044101d035001d842d80d940301024010000140b040c2c5400c4851841c1031a1304007a41d5540e800d64810f50347e03010a101a0100348480701740c0c2700700100d80c2c07004181c40600381401841e150140458118032005842010305100156600d846407007902030000f64590204403c2d1107511180c3d01002603e6841c031440d00410b003600b911501c0c108024007410348151042d10551510b428261084200a029802007200401c01d01400002125030303840c24036044400140d5840b040030041e1048607601411102c8441000c10340 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 742529793 1250 742528543 742528547
    0x210060609030209090f031603181706010b09010c1e0222050c090a03120311040b040306050105060a0f1407020d0b0601020639040b3007080103080f07060c 68
    0x481d04a07032007625041041e450380041592a0b407144522800c0e03a80c400c2c4200e02841040d2030003140c003540207003010701626544007400c0001d1400781e080544403c81050b00b04941313039401c100850040c07600c0c90f0f075981408900c500092524010510190050600d10100545c0b400d40c445002070156004220380081d00c80040d045403030014144114008500d80000150110401d10072143c0000004100400f03c500319541e030031080030201c078a5001c06135240d040002a44101c00148064500c05214035100c0d840e500d44142903840c140c1009001e09000e005088949030440010038880156003080c1030b0f2052110040b042900810784080c2d401101000280207100840c4e9105000d01030a81c25200c842d40c074500d00340541c050394002c0308c0710313940c014030031701c00c0e01d61340f174001c042c105c8a03006a1602d003d540b445444815080303201d80d040800302d2010020060741101c92011400810700b04038590b14503081e50301604040341488080d00d04240014078941c403902100c220740c00382d40c0c440003c00411054000c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 742531043 1250 742529793 742529807
    0x50901091a0408040b0f0c0f0f070504060f05100c06021804051627090e03040509180615060c160f06210b040e15060a1d070c0302100606 60
    0x351041d52007466060040d00c407020a40d445640c10a01207480c140c84d0641c004c4c003036800444014002582800b80042c0c196080c01085402d44070b100080020f0490303805260304040d0030790b11a5200c0c501c0c004041206880090b0340c01c0480d01c08485120480c10702c0401910100c0c4815402040d2902c0091034290341d4106d0140c40712485c4c03040c0c50801844c0d44410400c00404400011030b4086044014a410004c208000010000c8116a8034501e41559a520442030b20344045206005810102c1c0a11850a02d120030b60750040245025000b10070030081826112203000d4801c0f6099414404440c6181e29144201c400340c4281c3c8040310a0a01d501d5560300300c584081c02030310407500c10403500060b10341c1b0485a407503041c0943d5100e0f0240310411003000c40203140141103241c11540307544a071481c0410600ca1031603000b4130000a4266031a00e442000f03180c1c0030329001078012416051002500c418900c250f40e40c42240350030000b40c0c21a582c00d050b8584a04142c041460703506014000c84c0720384c1e000c3c103 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 742532293 1250 742531043 742531061
    0x5150406051602030d090c0810141f031b030c0e04030905030c01050a0e030a1407080c0102070b0304110d05010e010f0f18080a030e0313061101090c0b0c010b04050901 73
    0x2080181d61502c4440300402080b402503040182e00c00d00884451084a612982d103032845910407014560340c50310040d0030104103120090865581e4409444030404403120564403c0d02452054100450101010060800c902010f04001d0317100c40b4900d880081c031701c1e4a1001e95000565521080d07a5641e0758032080c001250200d0000c0c80e03041c0001503c0c1000909a41c11a805031034640c188618034004403168015002041e51620581d0310140104e501d400c004040b011055000e000d6a41c1441c9a1a14003010441c1050440d48000d1040041660708010f9076041684101c802007405001d40000d070f107005070480081d01d00d5103131440304290003505510031b01403501c044d01e061002e440c200c981c1c94101d4264084001034804120790940028000c44000e1041c480e0174100001c1350a01c05d5001840d64214564808105150a00c203024036a000600188021000f00c002d000e80040350b615041003400300e00c1a10031090005c42c0d00c40c0d60b40002c0d000700c0206080a8810005842c0194000d800303804204 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 742533543 1250 742532293 742532303
    0x1090f02030c0306060a090f0b090403050a1812060b0d051615050910050a0c12031a03010207170c030408100203040218010f05010c08070203010c020f1b0904120507051504 75
    0x82d0703004556040110319144079200007410342006030f1414001c1006020f0340d401d00007096544013242d00041c0d40b0300c0000c40c005e60013039450035120789503480c02400c02e0f4800032030104080d4101c0030810800745000c80c05002541d02030300c086140c42400004c108070320740701100180300313006120844100042440c0030808981541d07030341e00c010940300f80040e20a40b0646041a80200507904080d41803805400105642e440c1c2c9d141681c05c0c0c50f583c3e10744002860b4881c05c12800252100380a20040004601c0140301c1c0b4400c4000b140703050f20a9441102c1580b40000354000740002154013040c141c000d1083d02d00405407002071f11b601450b50800340c00294004c880032485003081d105140c03154103142003c64142c2d81d064210740d001c03d040400544030200302d600c040340c00b24170401507034005032070a00610058807540c1c0c00401d00b402e0201105d50400e070b0070056040c0c0c2c11036201b80d9040340d03955510425070050340088220640e541c04880c02ca881e0b02c101003000d040c41c03180800d9074003072004010701c080c820350081c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 742534793 1250 742533543 742533553
    0x32a1206240803070b040f140c03060703180b040c090204030309080709090203030d05130807030215070815061308060f0103060e0703120e12060a15080622030504050301090f0203 78
    0x8444044800322182c05060034942c428001180040d80002889030086d00801c116408145240c0d55507000781505012445d482c0c0140410003140d040800c86030750040c00e28107040c000488100004481c41c18100e8001c0c24164149010505000020750b1340c1001d0010b005003995226140e04003c2c01d654464810250580711b0070710000b8003002d0034401c040c201540100a140303000d00c3c84240c00c0140070040c2510f170b4101290407403e0001010f460003000c00c20b210750080c00c20b400440c0000110404004c0c5100c040c400c02d04200206c04035010501a0001030460b1a50b445d8141400000380f030f0350403034010075040e10486041c40404c0c4904165030307040f60300c03c0d4018000c13051945100740c0c685c005480010b02e080e501c01d1442c0c25040c080c64000710304641c090464185c442801d6207442c944141901c200c0c00060782c0c5c0c00c04044c4000c13100000740c00350503101c00404642c100400400e8843d5a1200f081c451096189da4281c2010b01c500111402030100800910000a490410381c851041e80a4101d100c5d1246c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 742536043 1250 742534793 742534841
    0x603070c030e030c0d0807110306161106100b030c0906040e01090c03090b0a020a020a02041a10020304032003010b1e0406050a05060403140a20100806010206011a0906040308041e032a1206 82
    0x40010337000d100d0304030315a00400040c5001a0645103800c050103102140505009500494583c40003070310050444501004072949892600c000b11074078007010b441010b061145050103e102280d650341c0054907c20700503903072501c0c000100e00b0060401c0e0700a40c814207215081580c0d014000741c0b9444010101d03400116855031100130ba0b6070f0303c03d0380b0005241d541400394440700941400840490b0b14009000410324008100025101103041400315000020020110001d81418401c99020700000c1d1002c904403802c00001170380f1340c011403000030700301d0f042660340c0e10311020305100810b240b40e40030405901c000c00c400200680030f203042c00c401e400b403107041601e00c00c0c49100d0042140640c01c182c001e0b12007039003404601c06e0040b43d250700c1c450500e14104120103442d1500d00003000107501520884d52914101070b95600d00c003d1810079816a00940b24003480071401040a0076511000300000d006140c9804500c4843c001240d0711542d140031040b9051002c0c80256006015a4440110034840b0026 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 742537293 1250 742536043 742536077
    0xa051207050a030c030507022e030207110f040204030f0609020108070503130320330f0c070204060909080d1b120f0b0603070c030e030c0d080711030616 67
    0x20a00d014020b54440c07111000407a02410001c085613000e0320341546000b070140c02103602000c01803506041c400741340c0d07a4543d01d203100085000d030b08401894198940122a2940c0c0021000a45040d21945011820076096a1554101d5001b103612404ca00040c1000d410800004c101c04031080c2d010410540005411710322920440780300348046421003080b149a520300315940c047c1e140c652800e10708103401d000d09411041205021400014074201c209051401c000d070441c24400102d1880380303a0080c18403854003103c4404c980c0c082c1d420a138940c3c40344c02c00e000180c058270302ca0344100d8a00b0f11b4500c82c101031018140c001c1a20285049080c0920704031052004503148074080f04a00140c0282086580302005400180c01e802d500b040105030040d140c00025110f91080c0c5608000c0f480000343e80040581094034102221800c070301800504002c85c4c08200000321440000b880084005824400c0245008011070550700203412a0318034030786540d564810402c0041340c80e020592441107210310700 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 742538543 1250 742537293 742537297
    0x60819090507031703060915040f150f0b030702070e1510080f060901030c0b0d020403120906180510030c02150c0c150108030d0e1e07030c1e0315020d020c0a0512 71
    0x5903019048480c180d981c020b120723003111075141065074080d0729840761092020070750040704510740151444450381031418403038219001c000c2d400741050040c01e2040240294012580d802250f1600f0008130322603a0300c286002c95001c2104010b0340c00742042011944003507001e50b06520600401c49180f0403500c030b210401041c0082488003c19401d520b850030b00050300450041c00107441d00b19009428141c5960701e52100c0252501d10794000b0324040802c2240c146d21034032000b00b900b500e68900300d810781040c2c04502c82e43d2415045005141c0c581c0740c1c440001c0d10070080c2c01103500420903000c1c03a905040070a094035902c11004600e551180c07400850004403120342490483c0e543d00020741c901010b41e450b0f413000e01080c0e04000b1039406224201e4a4103403509070f03d5849502c0000c041c1000070b04615005540c1942034001048010100740342075103688000340100240c035040890f507103c403c0650b03d500003900c40d104080314518000728652030b0303040c00003e03c514aa84144240c0300d4811860a02244074 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 742539793 1250 742538543 742538551
    0x2010509073503190c12050a030b06030a09350703091d040c0f260a020d0b090105070f20120f27090c090102191209150504060819090507031703 63
    0x1b540c003c0040452540c000d80007010803d2007414041a180841c00004074a034208440d891841034a07003a003201005109854407465070680d04c18840449020030114100b1507000501e035030502800990a01414040c3c98828001c5c07500c0714400841280408011100003829642200d10b12005e01c030105403c400c12600b4015540c40d5225020307440c07400f8641c0003121a00c112102c10070b0181c01000d85c00741e118010070443d2a070040344100e44a0400302c4180b421103800074002402c2000921000b52000c0e404041d05218400311112000b410011148040c11b00c00c407892401c211100c00281e00c01c8194a50014041c0c043c0c60791010b80300030403401060040a5503040d82d042e44040200300090b84801070038060600c081d4184116070070391555040a00010303d0340241610340f1030348074180c03a40c1c065100815401602c0c8480e88103010301250316016005019601545062154000000361800d48011590003041c0450030140080382181c01d1040d140d030124002942e003c1109904100180a004120f82c02 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 742541043 1250 742539793 742539803
    0xb0a051b0324031b190807060c1b0605070f0c24080a0e0d110307060f060905092b170103060516050903070902160f2102010509073503190c 61
    0x28500034100304001042c0c10176001548511103400412410800c002000c0604001d481d01a41500c0905201e00101d42e00b101404102d42408024004140e00006441c4a05c2c3e0003481000749001c240f420301d201c208581c00207480507072440400c03001071800c10038541c2100c01d9600c070407125844003202c442c161110225801c2c000c2e80241d001100281c865201004548015020f60b81030070080c0d9a54800d40c1e103843d41c1d5200203900c4420a114a031f030740e4402c042d0000c40b41c4005298040055109100303049030610b1505441c0b6100c20000340f01070041c504520070308543c00a01d10191707102c0ca000c100070312042d80c0c2c2040d403140c802d000405003400b841c1201c3c020f17903001b8001d04bc11441e000c0f141001c1c0d4000240c0410710004604c1031030000d000d10844440c030038401c40211002c2c40092005a1030395061600b18000c5a0516060280381d038008a242c01c00c3d54907003030b09481e64001411250251181220701c800041040c03112010055a01001502222003e2010050180d4110204640c649000c202c0501 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 742542293 1250 742541043 742541083
    0x30e0a0b06120f06060607050304080f07090f05130201050c0a08040e07110a0f0b15031b010e0a050904080901170c030601030b0609011e030605040207050307060501090203040b0a051b032403 83
    0x170303561500f4400380282e07510480c212403901743c645046505010040e82e248409a202103405c5c002044640201c101864520008000301e2400b03150704102c03410202000780c144400011550f210038801d01004500ea40c100c15000e80d02e030f6840080340c4044104441d00800510300c640c2d000c1c1011404103141d100243c200b0303a4440095143c0d00c8241c4480d10242c480101c0112141055013144c41c01d10007072210814009c0c01c0071044c040040050300170340c01c00d1b109134894817010304144a9540c0d42003402e41c04c47d070040011a02d40c000315005071113481802c00208141000001017002e4584064011485030b0000e07030b002d12841d0400c106014480c00340310001d82c04501c484070401301f020f034548040b400c416010319008c80d103113640b40c01107402c981c843c0d00152615080014030030180042401500c0c0100a01c01007149185029103030310400303040180408900075111404100d1107044032a0018050342541005035484c01c0c400c07008440c400c987c1504020b030310345062000c500d5207404286d210b490b1301c0d941c00040e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 742543543 1250 742542293 742542301
    0x418020a021203060415120210050901090603020f070f0c090e0c06090d020d120f020c1f0f0c021305040201110c060409181203050603060c0c0c040507030e0a0b06120f06 74
    0x1200ba5040180520340007941e884c8002040e299407805040100910443c9203415a0180103018241014281d5201070241c01c200840459a0142c0701c1021a0300380e00c0c0043e03d401e10894082420b104428020709118681c103203180900800d50364050071a403180c2402c1290541e02190503807141c07170b00660650310850905c8007c0341401c02007840d040b0345c0d100814401030003155948009071250b041e05468009140701c42181203064040261130858001103030000381d2507000231f040c0443d5245070102d02d0100846c0c1c031a03050140d030040c1210410146e00805000c03440c26000548070081c40120f4041c0c1c001242e12080100f8100080b4908403030100280040c0e28260a10b4900f20180c071400e20001510484c1c2003220021800299500b98003802c103607000b00c2d07141420341c02c252510a000e015400700c807500300a003511050b00002c0000c0881c0c0159801300395641c0b010b00c15030052a04400c40c03280c9008184c036000401a00110141c820902118003030064032403aa113082c0d40e80156400b10300c10703074000c1c0046 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 742544793 1250 742543543 742543573
    0x6060904140a0606080c100309080945010b070b150609120c0103050c0301080303190209061606060b21090a0804090b0a0e04050d03200f0418020a02 65
    0x750320001d0004994000446649840071516683c0c000c2040c3d4005402002162920040006038044a885c09001408043c1c40307100c80c07442100b81d011b104400781070280d0000e00306200828102c081031840b004a6242c2c611401c4098034140a51f51007420315100003188050805080d1a1001d4107c00c40780c0303040e980c050702400c50208030701c1d10340c0d84803034140040321503580c40c1b40c80e4040300302d494000340c003002d1036241c005015104082c0000100490600062140d03400000c150b0364805807034401420300e0148901e00350020710490420580010002a40c4950340c0300c90b0100031040d500c1007204102103a510040000c0350b0013200c440603600c504654000c20354401000040e0f0b00040c002c0240e031600c1c07501d950340c00700d00d50083c1d101554182c0c48a40810451806104400082c240e003903044101d89003da595689034074010311040b091607030301c0502c1c1e000941001e0a05841c11104070016aa0f4041d81026040c60b40151007044811019100e90600031007581c026a01180410b070001c0200c41c44001074 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 742546043 1250 742544793 742544813
    0x21e0907050a0f0f030f09030908060601080402060d09031b0b040c050415051203090613230108040f033e0c011e030207080f0c010f06031106131d060a060206060904 72
    0x21480030103403960034401b880505480340182445c402e8503210295481c0061141c01c0480050904d030500880800700000f5171100c0302100d110340b9002c1000155080d281c901950320200401c05021210524140320041054184600b4080e40c040d40c4114800d50741d0390100410340705074030b4403d03506003402a02005681001000000301c1441700091701c0c141000503000c030b00c5075000202c075003941001801003003204d55064501c07280e0791900251000c04128100f8006419624041d000520105045190030306052041d1110005400d810706184010220602c4091102403101990780c44c1030641204403070884c0000030000c55216040e16500c03455a8800381c5544500c40b01e0078400309040c0c00300408400201c00074010104940040200c5444511543c01242191782420240410768908001400880c0100c0034a24804500f00c1c0d48a5503440320319485400c030a180d034044128101045940c84000400e45042e922601d000c1c0c44d94403903190740e880100d0b0394804c2591101d402980240114021030f0254030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 742547293 1250 742546043 742546067
    0xf0d030911030a111203250212011112040204022208070e0603100c140a091d13120c02030133030b0106030b011115060f03010b0604140d021e0907050a0f 67
    0x411b580c10700c00a401700c0d0301d546d1100d41c45140c41a40e10000d00d803c62900103401200c1400e224000c024500c00c000e6841010301c5080c1c601103e0018a600040c11541d0f65011105800304007046880103e5a800000000c00c000f4000ca8125000e6080c020407071500d40c041d4584140001070061036510814200d040c024081d62900c901088201001000400040b03c0184a80302c0c80381e685104661a0230740c1448101801601600e1001c0c84009102080407010901c038645900401c0c00318081c02100e200f521681c00641000b9019402c06c1141c5580320704011060342d03103480913407216114103c441000075040c0e10b2800000c052174a0040148030b0107100e60b0051540e000181401345c0001c80ca404041d180400d11078030010750000c00e0040101a04042c02c0000c080340c002c1c3d00900c06001045c0000304140940d004840755602010326025299550300d00d0b80700c10a8000d07000c48000d04001002e84086542865698040d01d120000b00f220b40e0312410440306220313603d59801410082924048402100703d030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 742548543 1250 742547293 742547329
    0x1b120809060d06030209131a15012f0714090903070f0302031c0f0c0e060909130206031801052d040c1701091103150c0c0f0d030911030a11 61
    0xf0700100c0103894204400d800303115404030b0958210042d24042c1038a50011094034480001d010600c80509184080c403860b41009090a002c0308901c515090b1240007500340241000a50100d4291005070108a80080d80e441d9600b079400304a451092041940054403602d07590390040015001280702d45880782c80b0144a072050368a05180c0421819100c1c00b004001c855190345d4084c00c491151131031290300b00b40201da0405071601c00600001031424001c056409024040803400200c2d0b1588100c0011007080d4010301e001d0b2a41450032040c24500624071020940f5031801c80401c81a4084075050385811800c1c51a540b40540d440301790300c1240a0181040f07420340900c06011032030144208003296140201300000030350307440d50705128241c9000d400000303005e034001e6030070300002c0c650000b41c035540f01c001047d00035551010b041036185410702c1115020040e01500a83c00c20041e0b05421007140f4500480300206400604400c05880300c481000061550035002e401c8020707400c00708426210075400c8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 742549793 1250 742548543 742548551
    0xd0b0c0c0a0b0f010e0912033408090d0305040f1509020a03050c03070608040c0e0903070c080607090803090307140d0204050411040e03040f140402040902071b120809060d 75
    0x50b580c041444800b41c40c0341e00709560060041c003c420b00d405a1035849031280e002071840020799100d0924a00c006001c47c034107074140010701405009680f100d619150301009003080025040100145500ca040e140042c05020354250039885a12030301406000301e812032481004240c032940c500c0c40410402c660141e01d00e45071025140540e0350742c1a868011802840540505284a0101400c08116400003402d211500041c8000300b64108080c0c002d40d030340c1c103100e0052505c4412021b4914010004010807180300c056002c140c01a0125146010780c440791a03d403412503c0340d209640364007901c445c0c42d4050303210780010012060460190301d03100c0341c0644034000d075903e940c011a083d42c4007224140c54190030011188058105441800403000d0a031019608041c102103a5400c40080780c07251100198030031146207802c2d6520350442d0000d001c127500465a840107442c0074160700e0481102012805400070b000515038540b0184164034540c01866189003141040402c40c16410a181d045c2c406035a03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 742551043 1250 742549793 742549813
    0x615160606030f05010905070602030f120702030c060c0a0906030218040902040e1e060709030c030311011b0210060509071215050a06020f0c1c0f051c03020909060d0b0c0c 75
    0x72103c412902c041c000e400104451440d4105585010140d91110003154001c0101350554010881034540820f8240040742e66915104012499070003a010710141c54092403090003514007521005042c212290340b00d00c3c040503511041074049000d180e0710305441c1525007140c0d23030b4245081c0e413290340d14520040c400268000108080c51810020042c040d0761003404c2582c0c22801c0c0000c1041c3c9601c5101c40c82c0036004141903903540468000680301c01014003064030507c00650101f908848445021801e07540c5450b44132610081d075540e000d94040c144030745004008605414034900540c4142c1160300d840c040d103801c2c0445d1100a140d0b00c151000c580740350395004101590740e8091040207050507402420a004025003060400c44040e002038850300304030500095a070214951025120340100c2001d00c5841541803140c2004500d19210140921003001c03606442e41590140c25414010780d40344007190340c0c030010b021300f4001c1520050855901c000c0040e4006081ca00184041100c00c070075141c0c0744003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 742552293 1250 742551043 742551053
    0x11190e010513270e0c13060803120a020f12010314061b0a02010e01050a0c0908010b0306070c050109060c110123011406070602073f0e0406030804090e0105061516060603 74
    0x501802c2c0151300340c01c280701048081c9419820101c5d1404a48401c1041c54a88400e507a41c83c400c0f000100300fa0350702d0030300240e41d08659505aa1841d1360300c441165860180341d102d00b81c409800d0000311400907002403060b0b044200000d84034030070781030000114004040228481542d80100300000119900c0e0305401900301e000307001e5a8081c851412022440c0c1c00926400b0b806103c0c0e0340c10800090b890003002c5a20341e600001d0441c2c010325a81890f880303444450030005d0140c05071a40c0074041c070341015140c92a25034400718140c0d03034044000c001c200d400c0c036190302806c408a0714010701403030740c0f61b1000620000051340e0041640c1c81c001426503250030015650201660030100084c0c41740c42c1003001c000ba0300c410401c0d511402c2c8105290501c1c8002c411403e02c251445228284020001c0c070901c010240d07161540018040c5820001c20340e1100d960b141018090001400080015401d04000c91100d0516100165408a078001880d04007a004850b621031907903030070029188143c4a03000000820 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 742553543 1250 742552293 742552301
    0x90b0604090e1507050c1b0607020402031303021207030e0f18090c130b031f1805010b130615080c040b0a17070f090b070611190e01051327 61
    0x40005805080c0c415110583c00d040c0801c020816000d00c00204440f8002203000b184220549480f110070303c0c00d10390700f080820514011144000c3d040342c07000040c8005e006200705011080c501c2907003140e05514050a400707042c2e002d0740710000d02181400001640d0b92400307021300d11101d80c01820046643d411006225080902640d688103140c002910383d40540c00d008410403640e1116080a004180058000c42d03590780c24250b8080c01d24440702c00c07030208041c6582020b18068801c00c2d9100b0b1050031410514024080c03140090b100303050841a18048a40c1c0303002d00c104a9508101418510210032025a43c141d0002c01400c0002c1d010031000c90500c0d00e68000c2c04044a503643d4901002d88207000c0016001c0e8040c0c062024082c01c0d4443c11500c0e58441f1010094644d0354040f10f88428043c40c00c880505403895002403014404640700c1e103190380102ca1120f8409003651604907030201c4000550b00c030700c40d60740e404454042d40c0c401401082007030301c044201410181042c010240c00d11000340129 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 742554793 1250 742553543 742553561
    0x61c0e01060f0815191802092409040506040b1f0311010807020c03120a020309060403290609070309140a0308070e04180f050a060f0504060501080115090b060409 71
    0xb80201c41c402c3c001c1e084204200c6031101211550b1580038107004105401c07005a01400c0108580c94140780076058103000304e07010050741c0c042d1071140181041000c4a0494200c1d5011b40600d02c00b110380e0b0000ca00c0c1038051640a0313070700320000e4400c0340c413607407990341140708010720030713000d1f020404803800c0d00003903032a8a4030003075010350005007a14a89034001041200007070900421580070419000d9180d07004502c45510f1910b40e00c001c1c3da40d5402d081d003a03013140200d00083d076100c0d0000c1000070078040450341c4c500180910070554201075480945400c005c10041d2402070308032044034002214039019601ca0b013103082c0585903043d44441795510403480c210b00718200b1800210f0340d00038002e050f600310648000b6030000b00e405200e0150340c0d103516100c1c0d200000010380141c81906481d0284102400080c01c402d4101e5420b01019107032003071038400340c01c044c3c404a501d103280c00300000786020706208241c0d48800303a040d113070503140c5002d104a010b00682c95459500c204204000108100107105207842c0c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 742556043 1250 742554793 742554809
    0x61213051207110d1a070908060c04030c05010f1209080921010615050f0f120907150305190b010e030d0305180d02030304060c05070204021c060b09061c0e0106 70
    0x642c4000c0e240940c1111100c580302030007400c1c020140b60001d98101d2206185150403000314095a071188003c075a8259103074000703a214092582444282800000100180c0340909118115036684500440b198403090520340c0018141400c010701403a02c03a00310540b154016401203040814420000310110f003202147c0c1010300d81c8401e0384180b60028010300c4020810451252619070000c600506580306070114111602e00026000e4003480009081e03480c034541c80801010701c1d1405035010760b0344003424080e000e811064041e0101d40301d07201c0d0069600c1010442844c9042d4072040440c031020f0140d1103c0386050051030f0054503104d07242049002190a5240e0700070640d414105008008a1180c1d104090180c210300100000a60000220703504280d000c2d10000700805d205030304644030b0040000c000d500c0b9000182e4a0480141d050f0000c40c13031806410200191681d82c1c10003a180d114107400b05401c03510901815002c3d100b078070070342d800001e4144400308600c420003900c10b0031140250000e6030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 742557293 1250 742556043 742556047
    0x40b0f0901120c0e0607020a0f0315203a0b0a050303040e041412030414150433020403051c0503060d141009081e0403020612130512 58
    0x8040e40c1d000d01c019208824042d003c102e840c2d004200140b0040690200d40d01aa00c006514021500c80d400c082d001004d024400300c0803640c480c9400b10f084000402c02441d0207040c4000030410804007c00d079240d071048041c2c000d20b0103000000d161031400e0a900307081c1c008000400b15a42d5103145200f0643d46541ca440c000424070b80c200200090f100c040d03003086000342c0c001d0105000c1102c0726400d15402c5030304048500e140b211440c07091031802d18482503480b01c0300008010300c000c0011a80c003d580c9000020261902100080041c1a03501c20444000c0d0030503010121180e8800c069410081906a07054100840400740b00740790000d0340d00c035500480d6a40d10190b0350321584410030f0400c1d034a40140380380c49403541c10007a0006484400014014050082da40c0034071492010802000030f007612980818010300c45a03050030b6029802629809005480410a01c4259215041240c0559070300902190901e0189c0c1030150000e0002000c0e10346400090800d070011640801294041e2407104c940d0f15 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 742558543 1250 742557293 742557307
    0x20f0f060105150f030703021b0106120b060301140f0a06051f03061e1a30010f03020102070308090a05030a05060601200d030f1d0a0b0603030f0f0f040b0f 68
    0x11a0715503011012000d1103c0c10311800b03041031324007022a900300580345000350f20352215078504580445a1f190f0074140b50700c1e2200002d110711034039003840d554174024080d8211507600c00080c98240c0f0121181c00e0059082d1200150b080d001c10418940c000210003c00034070141ca9402040030100c481628801400e480c2c086680785541c10b00070b4602030300c1b2501c07051680004440d0700c140f140416010f0030550901840041144a00c0d1504bd101c94a4120382c504841c08916000e00002c1245246041c2ca05d016510000c10707024003a04203202126410307402132800d1480e54480d0840758002501050707100007401c2f4000b03032540d42040340140050158026040e1380c2860400541103010300068000413020403c8542900742c80411041000c56403418041901103510201c00010840f00440044000a40c00808240d481c0025000b00040c481d0109c1e40c40c54440d00c04050743d81c0680d2800d040d08000030401400c03c650860090a000b401849809041980341c02d01c0d0041900945524502070341c01082c00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 742559793 1250 742558543 742558549
    0x1704150e03061008120901030b131b1b08031b1b01181104020c160f06020c0301020c030307200303460b0f030609061906080c0d0201020f0f060105 64
    0x503003040c10440d1030084180b80c070314501c0e2a6000b004100390050000b1580340e0b440d9020360400442e403032000302004070074ad0301096000010309007081d0203041c010038800309901e00d0f402240400301150243c02840d240c0d031042d1b0f44900081d80002c045e00b8880e20a0340151140020440241c5000404045111315001c041580f80d401c540c54070b0500c14a485d40300c913140f80450f25200300100c0c805015500507035140000c8500b1490000305040d240d4071070f0312000c40010441e07002c0e80301006650300d503402d640d03960741414101070a034050040240b80d90f81040000c10003260190700490034400c41c24801c65090b02d10f0804245c00c40c1c0084410f014001c1c0110040307940c41c18a4180c4061240e0440213800d8401003040c140c07900c502125486d804855510703410350045070b0320092841c50040d801001c4403082c1c5009000301d03031030b01e00039a14601508401e500c0f404da4440720f40940340a13141c2400041c640349650404101c44104601c5007641503000c0e2040d010200c400c217001885540c09080300030f1005502d86818 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 742561043 1250 742559793 742559803
    0xa050409020607151409011b03020d0b031c020c010504140405100e04050a1101021f020c0c060414040b01110303041509150b0111071d15030a030305040605130b041704150e03 76
    0x46446e40c0e450030280202c0ca00c50b69181c0000140c0b14580161a284071043c40001481c9142406070705109100003e40720100510180811004590a03074100300c1c00300d40103444030300036405100c244807412080d00b01c1c9400e1503400281d11454914040b0072041e5238040e00441c602003900d042c0d13500e4001070740702070500010200c4d00000d0902071005000180440c0212210342d019042882401500012130198101c4204550840030400030704595540e9603480d407800700f58103000c21540c061428402e02007041d60050490302c4d0f0203c5c2d03400c0030314607540c3d8a9540203c00704010100030b1509646e8001240450106490340c4035210305031100054800b02c4000241c03184a61900f40c1d042640898030905c016032204001c1d4070344a0740007001c0c60f2152600d0100e2103201e4035884400740c140c402c0d9400d00f030a055040e0050b500440c0100030407c165210b209424851556441e00541046c69010228001071040c01507510001c1c0b8030400f05040076220070035140d50040580281c3c0009000d480394416510f81401 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 742562293 1250 742561043 742561051
    0x9060a0f0b0a120f230c0a060c0b09120f12010611100c0507080d02120f0c040306090f120f08160c12030e011805060610021f061a070614060a0504090206071514 70
    0x91f490140503e8024014034031030688100500300e2011502085100754204556004503003aa500740c0e80700c0d40c00c624584496000701035109410700c00c5000001d00301d40a40801c508404940d4041e0101082809038a00503005180c001c0040010400080b0082882c03000645400a02c3d00000341c0d4400c4207124202901c01d0203061134a1002c00c210034000e524400c40e0458048a038009000b0440d4016400c0900c0c0a0380790300c201400071b0200101601805902030045031358200561949007264450a42c105d00600981c44480041200320302c450f408102d0084107032400c4421444c001c64071740c0710307000054255842c480541e02c9503402d28099000300311301400a107034051400e4801c00031003820410000d40e07800740e003410082c0004124244110368045904400c0c0500010089640546104c40e001a4154805081642d01500e00032202e442c041d0780c180e03914000c80d0024226858142041c0c1004000e00e26031100300e0340850704201c000d00090f080c410880f118145203400007031500050342500c4c03400c48020 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 742563543 1250 742562293 742562299
    0x50705100c0302042409050f010915090e090d0f050313060c0f02011a0306011406160506010f0608070e060c010e2d150c0d0b030609060a0f0b0a120f230c 67
    0x340178101500d900013035500c00c41c2c000b01d5802000101c0e940068903034180c29000b0108150030000090021a0400b10850483d040880001144e6681005445d01c07807201051300310000306013003130031114140b00300051030300250170b19282940c0e4501ca668680440f141c001d80c00740031a0500d0f1000c2c0d006502849020350202501030b4410b00300c010b590009483d1401406040304c00b4103011036080090300d8201c2540c03010402c03c541d400140150f800d1050303503404244511500103058030000300700b26114110b140e0040c2d1103a2240b18000f007004041000c0c42e0465000220030759602d111805032004204150001c99240680b10341106c4402e540715a0580303401c4211002c0c40c0e010600302034401e01075407400c1707030311400c0030083c25107030f440766040e00c4040c0185030f038050740c10700c1114184143c00d04046241805090001d404000140128080c54241c601d00d03d00d640e07000144010802c40d0101201e903912045120319003501d075100555581a0100260000d400c41d00310600381c501c41074070410015042c10000031 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 742564793 1250 742563543 742563599
    0x7030501081b06030403051608091c02010503040b0603120f120105060f0414010e0a09020a0e01110c1c0b07050304060f061a13080106060e091006050703050705100c030204 75
    0xc1c0d022202c04800a50a035000711030020004050602c00c40686000543c243c0751503074120044d0809000c140c00500c0a10b11803402d8004a122804036568041e1f507155040c0c44d000e01b0f55032191602c54400d03000400d101e4040c000c1031420705031590344c02c0c01070494605214402d51200588900060380d50230581145018003402c20a05c0c10b5501410181d40465017a02d07004060710340c040004035011508841d000d034101200e201c0104106406402426840e06240c0c1c2e406045420100110390140c0c40910030400e640001600c40064100401038404413081e5401000341c0d100d140d13941d0308a08108548500009001100340310800600d03015010080c0c014240620089082c40c0104120a00c0d035a014105500c0014049001c2101100268003c000d014000c0000c04e0b91440054030000305001d555100f0203546000508000184400600742d03402a99010304042c5980d90a840c0e5a00c181c5054903a48150b6800414440c200d0203408400c941c0c036500941c80314905001e8800c001011148800e8540324 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 742566043 1250 742564793 742564813
    0x807050306010b0d02040b0d0534201006051207030b2404050a0209040605041e05040819090f080d0e10030204050d21110d030903110a06050703050108 66
    0x40000c61905481180f00b1040e80d0b07800e5400044020b02c640d0b03101d25801200855441130314205588000d1007000d640100600c41907062000362170986410201160501d807007588a1204c038070812844060214410090400c20407031000380d4a440b60b00038500d010135440ba03109201c5414108a940303051010780008000a03410360703a9181481e40000d044c0361100800c3e48101441552403201c06008210162041059045c000d0071900a5481400c601e8092410b2080c0000c50f41814032484180c414541c50300403280781e000000300d01501019000b601c8003a810710004000054001619030f5580d81500ca0101051410008042a94050340301c20501e0b0014006554002e4001113055002017044401441c2d0480c142000e030000d004640003150001842d8144004000c2034081c03c2c1d421074040044002403020003242250204070811110803913800c6880802d002d140a03411442040d032103800c2c03400100784124481c9252190501e026900c00c1d894a0501080d030303805100b42405030015002501103018 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 742567293 1250 742566043 742566049
    0x1e061a030c19030209070912060b19050d12050f0a02010e060c16030f0201060801110c1b0303040e060d0602030a05160e0319051c050c07051e0d050a150213080705 71
    0x1c40e1001030702030591880006c80080c0705003656009444400f0489030050040d0601310000c0c030300580034500440da0140301950007d4001260f60441340014105440e0003010796038640c0080c03034080070710b06022003441100c10204036003018000c405e8090b8000031303c0c4035441080e5464100c001c1d143c0c2d4000e17030b402c1103244540120400c134004105c0c1c1609115031080d010b407030100d00403c1c0560204115510300242901d01400031030092003034041c0350041700c03020000c00c038442e40d00755002c40003568154002c100030803074510032800b01079100200400b4070724007085549804090b0390088488640352540e03141002842c1038172640f142e02c01c150520340f11a54890f83d1022030381d1040d00404083d030b0310841031103400030070108000b04420400000c817901d000403102100a03045411074072000081d4080c60381d02284504140504144401c1000d2203081a03001210902625010424041e07407140150064500490b502203d00380300c4024003c00140d0760702c2a071001d551404110b400c15032254104000800c810b40d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 742568543 1250 742567293 742567339
    0xf0f0903020d23030a0f020f030a02280b01030602030121020907110703050a050601050a0603050c0f0901180b030a150513180c09020d05160c1e061a030c 67
    0x65808642c06101115040c03c020030f1495500160455100024110303400d00d5000720501c192981540803209050000300c1066120302800000a00582c0803004005804029000754560003103903488840226681d41c0f51000791010903003040d1085600080100100822504041843c1c0002c41050f503852804d0b81c0082e200481c05000c04080000f852184481040c00b0300102000310fa100007243c1c245541031410a4807a0b20903c0f860748103920300b010001d0307042c0c0a0f00800748a0001d00c45180c1c43c140c503004204500b41c001248082c104142c80e448020381c000742c00081070107406c103072400e0ba84030700e0200c08035416100c011008002c00180d0780c03030800c070130344918950081d2220782c2007003c00c074140840340c0c814a80700c900c40058410510103000191a2007168020301c03207020000f2060040341d440700e6a9812030b415401d1003900041050714900c002c00c40103081503000d080d4401107c1ca0303105e010b0300d8040513035505c0404e699500d408a01404841d00c1c0411014012001c2600d40c050381c814160880c003480 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 742569793 1250 742568543 742568569
    0x5040902130203150301063c0302130e030c070807080111120417070602090319020616061d070f05100915020c09090a05060106020c0a0612021303030f0f090302 70
    0xd582c000c80031070031031010122000312120001e0000c010045e501c40d150024042c4c0c01d48025004109002c0c46425030490301c50016424140c00d440d0b8442a1441d0309218000440c490b804006568440110154030000c5c0010000002c00c0307402000510f0a204086051000c1513000b120a6854000881c1003035031008241c07203041170110301600382030359141818103c04201e507880c948001000140002000540e6014052042d000c4e1f04803125800b00c1400030140480350040130750301039401c4c440c0c00e81e03d0501c0e403501d82c180c1d44a82404118090304c80d68040207500d100c0100c6195800a200034400c20a6100200005041c220b48050003448801400307450f015171406001c0d41c070b40c1560055223144c0c1c002c1120000b02c1c00094000844c61178101c0d400d68403104441030880301ca00800d80005010352001a50446400c0020954a802441d080f0f099507400380070503548003c6074080c01418100280d00c40703a00c000718081d0b2a81d5400400c003000051031000c01c5000c1d401070196042c0144003503282c11000c5404 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 742571043 1250 742569793 742569829
    0x3020c01140c0d08090712081201050a03020603010b030711161a03130f0618080d421508090708010203070e0d06022a0d110d1b0b07050406080105040902 67
    0x11a00e6a1240f01c0c01c01e106c0f50403c812020b1800e40c64010812030174028001c60764501440c1104d070b40c90b4404c01c40340080da84400ba51018092005200e044007040041d600510241800c0340c10ba412561943d09080911141c01d0b516001d068040180341d2150321042c410104041d212451490402114040c101855401070031308503140f104442081020b5101c1c1e0545c60540481032010526803406010307550104000d040303507600b081900801094140c8100d21407811050562a41c03000d07001c080ca080c07109543c0c2c5c09801c255003042c001540040303080038030490320881d0398011a80c80c3c54021a0f04d41143c5920150650b8410810464595841a948d0254420441c1c20b020220318600740100680500e92413400b41c00001e103a08201120b96140b0144030107091400c0d200107c1c1d8002c4e080d101201140c00ca60115003201030110300d003d102d1074100750100c0d8103908072a4007082c1c039207420b0100107088442c1004141c1c001400d00a0311b030446075113401020111018041b2468070745c08905400e071445c01c500320f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 742572293 1250 742571043 742571057
    0x15240228030c06060905150105070210050d200304020f030a0b0103020409080d0c020106030213060315020304331404050312250206041a012711030403020c01140c0d 72
    0x2042510400030000340d80d0f040101404015200d12000c0001d0405031060315004a03482d02c0052994001c1045d03e000c540c0003050201c9016a40c901551254000d0340c030f00c10003c1e138400300c040c030200312404800502e00005000c4c80e00d038680392043c40281608860a40d00c240d00040c1c230300300090709480c2c1e6030341134035070641b008100c54240b07180407003079809085540030015041084041002da4150b1116085a008032110f4481202d81260001107400600015111520502e03102068100e283c00840e0400e203c1d4240414446100308440c0440310801900e0170700349800c035001c00da0500540109031903005080c407001100c0c1002c0d82d405a50384240310100105030b600700c001403281a010b04603400464100300340d0300c001c02c0e051800251603640894044400d405c1100460b40c200c84030321a01c605a036150038805604035003580440359458078030085007203650f03203030440c3c5020304180c1c00c09036000700c0c80303600100300c1c8407000300c005050208149a41852580c0034425801c0c02c07000000c0301e49446040d410018 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 742573543 1250 742572293 742572373
    0xe04060b070507060309060b1e0a0b0a1b08040f0308070b0901060b0d1d06010b04060305011406040509040501091703090c01020a0803011412010504141c0f12152402 72
    0x48041c020044088ea40301d5007010418414821a409001100d01c3c00c0310032284203a1101d52542d15401190f00c03e400060115092204035a0b01804030b50704035010300c1c007031230429984403c283e04010140d0801c564492002c184901045507650b40960032220000c002e210050429407511858080c0d40000381c01a0703140c0b034208900540c129402e041c3c161000d02900c4080d038403070788044042e50291141c600002c0c40d0000006400180c40280b0340c2c7c4c1d00c8014241881c051070320040200740c1c4409402602d032035503103420200001d02c85444000da81303c40420b90030b40303070f280408c1040e082483d10105581550020100d29002402900890b415a05c40c00644840c407001400440c181e1914410310300c036158a0503050005101e9401d5241401c14a24000c9908503509290100310b403000150908001c81c00940d603004080703000e6a414011224401f0740041e10f281050080d0180c0348441d80000040020394044903206072131000d10f103d03100c0950000b8190803645104080300c60008100d14007002e1f400090301 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 742574793 1250 742573543 742573553
    0x702040209040b04090308070f0318080a020f011802010807030b01272303060c0403031d1302071b170a08070f0503030f0610090803160813060e04060b070507060309 72
    0x20450f452020f0300400c803401491401030b050210646d04640403c030007601c0e02101c5031090040810018000b0842d00e0000b85036602c41e625500000700f80b006500035541075142c000c50911501d60b84540908110302601c8250001421034400585020201410007400303040a98010f04410040c06003000c80034442e01405200d142400740c02c0d0046113104104941088012011080f06081080c0840c140c1e00320742c03038040345031b00c1c244030380d1000a000c1490000c15001c001c614246041e40c04401400203101c0310034420100040303902c002400c81e000700da0880201303100b0713620004210141c20600345c0300011104000442d5616564803000a204038000140102000b00795000c400300d00703910804403505d03410400104440e200701150654000c401e2515040021482402c0c1d1000311400c8002a501c1d02c80424100208502003c0c000c2d1042c4400704004030550700c04a2441c00200a9039503502c240740380050401c001d481507544800010801408a10003159020070740408a5140f42000140b0341d00718940 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 742576043 1250 742574793 742574801
    0xc0d0f1404031406060d051c02070b030c0705010606021f0218040e150f130209040521090a120309060f030f09061b0f0f050a050d0f020403050f0f03070204020904 71
    0x12604000c0030400008002c10412650184043c410564003244d8900c4107000c05180b42503001380031540000740f00c00c004510845026a0305a903803041d1a00541c0310740a10050303500030340307140007052740002e40d00090081c00c1c030400300900f43c148007a00c0302d13480b08007980c5c0c1c0381d4803484800d40e49076034002610745202d90764020701c40380444054000c0c0030a031710010700310340c0700c4503a00184003290f000e40e00041c10362009070220a00c500320300560803913050301e207400f4020400c000400446152284009c0c0c0d141400c100700d00d082c01003880b2010160f8888400c81440700c0100b407031340104210360522400c10002500aa001c60540d003280c608040381580000d4200c01806240e0103541c1d005240c0840c403428031040e900640b03440710303184624081c2034a1000045074240010202900003920145103200c5c043c0c03080008011501d0380b40f50445c1458403c1c08400b08031800588040c00300e503400a002c008000083c444e00054a00c414090003040d41e803120095228858803d00074880d40e400200d810060703841ea40 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 742577293 1250 742576043 742576067
    0x50a11010c050331030e010f020a1e260a030b1f050a2307060c08040f1502070204050a060825050f0d060216150b0319080c06090d030f020c0d0f 63
    0x1000f00010106040c050699104464a1b90020b102c46081da44000d000049010701142e00c0b1005100e03400308018040101c9070090400c49680b184040380c0c5a1020340980c8040d4000d030a040c2155403030180100c05411182c2c0c500302180200c1c3d00c2d6004030002411000464140c0a2508001d41e0b102c100e00380032200ca030384071082040b51a40140003440500009806003000314402c0c80c003045051000c20042d6624602220010402d148400c8070200044503182000b110002c940005410542c080c0d000900b50741b411600d60b400300390381e014100461081001507810040d808034003d20000c88200102200314118010a400383c003e2402c10900340d200c060098540c103411803000c5494040a01d80e02c032040040c050b06840f045900050910348290703900c69040c1102005004241500b50012416000300d40400700303945148051001501d5a076050000070f125569950181542c541244002b5003101e24015106082c0e6106111000c6851400503080d0360000590030240010310640b40c00703c420a141035 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 742578543 1250 742577293 742577371
    0xc030e0a121b0309140108152b0f060605101d0303040b0c03090a08071202010c0c090501060804060f0b01080c0c0f0d0f1103030405031b150403050a11010c0503 70
    0x21140b1403d055100007401c094481004c0c0e0b02c038110410900440e08090255049981552844005e403540d190101440020842d0002c1d091350074160482c0f00185c286070100c1c155020700f0500162420000c00d40f0071000500300c120b9140c50740d04840c40000340912010340e0b400ca01d010783d01440c0389483e58100150b600410715440c4c095a214031094410b42c40350030092066000701041d46001c038917954081540825901c048034040c0a14100360011250480d140303509070340401e01c154003c2143c032902d000da41d020f410107494004180c00c0c1444c0c8801190304031240c1d007851520b03003110601c141ea80030802d280c010841c00c240c0c58072109204959030920602088480080c4039a1440c1c0a040380c0002407000c404800d9210317a0a0450351100c8291640f004480045c42e0350004c0004050310111304140d03007520282c44040f945900840c202c5200c1002d0155020b501041020450310b0070981d01080580703003083d40c60020300c0150450000602a4000605021042c901c902407502c01900c0b181c9442c80803400746 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 742579793 1250 742578543 742578587
    0x30424050709080c0117160306050d0f120311030402010509060c070e0105150f0426010e0c04110c07050405070314040b04170a0e100509041e0c030e0a12 67
    0x540c1c0607150032060301c200400381c002c481c2140800e6010f008894848400d050003800c2690301c0c1d0100f4002d1498002004090694a07000800d1940761683c840320801d00c0380c51220903031101c0703090580c2544040c5110404050400d240c0129042c01001a41c2d0015428241213403500303800400602c41c0d005041103039101c2d108003040080d41103000c00525040700e109843d414801c910340c1d170441e40c40f44103c03c10142102c0040004001c0071100b0194043c40100071038101c02c0350126295540c0c00d54200880080e0503078816080e01d05c0500c1d0038814106101070300707021540341100104690b500e070880391207500d2150340c1d00c60010b0855400380d002580e65030208140c01003c1e152900c1d10031050ba4040e10144d521280310303441607121401a40071940c49869585400c1801500c03d800c100200c034800640c0c0003001810300c1070b041503440301e0046203507652020400302142942d90405004841c4200309090070581056031000f90410081145940c0036000070540d036039082240000e030f894040d00b1380c000002c4104 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 742581043 1250 742579793 742579801
    0xc06120b04021c050a0b03060126070e1f030b06090a06050402120906061804140109140a110901290f040602031207090e06040903031d0d0801050d0803042405 69
    0x6a814140d8103c4280004104584480041800311169480c15582541c44800107114183d540c0f41c85800080c0006112809110249502400c160869100c025106080350070f0141c0d105980790072a0000c13075001140c0003032510f1501e52070071140d4058500742c0a4024140455040c07003583c1c01080140002074015036540b0f00901d019095020b0864610009024050114820340b62102400b900c1200d0756102e804030b512151202c0314410400c0b55200c0031907584425080001e2040402c0a4a0103030304009400100140d0601e40300310740c21155980d00c2854400c0050114440485540c051a400300741e9200d181401c04c8202d081c0c41c8180000ea4107011004640060001d90000040200e0000110400d45540f00c080701612009414014100e40b40c007100d002521505066000804c01ca0003450086800107080704800c03001c41c040750500c50250807000041c001c2507040400c0e11300402094418202e0361a1545608601e4040540000c208414258001e03503c1c7c1a40124241902c0d11709008006c2824 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 742582293 1250 742581043 742581067
    0x121060e070504112d070516051305010e0711010204031e1b060504060f0c0f0507080f1504080c070e100306060b0a1e031d070e010b04030c06120b0402 66
    0x1c0c42c41034600c11401c0c0b8210b144801c42c1c00040d40c1039025040000451080c00c40c0d102d000b4020400d1070109482820300200c808600708124800540300c6034184d111506040000f804002142c00141307200c0d4609107401000460f41c01000a80d1060584c0340c110110040e0800b000d004e403085602c042c00c944a034011048096900c000f8100c02d0500c00c03041c1c038511050f405024042030849100704408281c05110803c070300382c0a9244580e203450345190440c40800d5555444915030440c00065031158045502884030307060412030400010080c00051032460103450501e105041e0081c802401d82001107411409182e00b0403140001d040c3d802c9104005203080c0b0340348040030480e4442681c1240c1808400920b041d00760044a001c1e0074a9519904000c00c0c1048100d580588032030110101540d0300b03000300c00410310804144911040d54080c041d100c2c5050791441c1c07150010f0708100c0c00d051081100300b00089621030301c04100c9641c0e0503c03507841c1454222001c02402c0c60b21503107400a00024a12031500 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 742583543 1250 742582293 742582303
    0x50f06041e110301141207050625050a02030c0301022b020712020105091b181518040b0702060720070e040f0335040203011d0a031707080121060e 64
    0x205e90041030407441d1251401c21664800b0301900807800d800103401400b107806c2c040c2c020f10003c0f8051a1080c20300101100306240010705141c142e07810b8200e0304c1403200f189018000440703c1c007000c90003541416074548803460b0055140c00f101680051001034080100040e0301651081c0c2d800c0005400300c0c01c3d01c81c101078082c00e01211001c0850290541c040d00d4280950840c0a0814000d0403a0b50081a245401c60142c5000360000e50610f410b1030707002c2e143d50344d600e01100d0600c80d220340e40485070825140455640c8405404980be64014104003c5074a074803041c0100e03800802c20f90081c128105910b9181400c0680d0884150848801d0401c02400700080000320100c5c4a41d4450450304801c0041c500c0204511100c50508140d06a200e40d0301403907024443d0708a800100001465820210850020021425004131680080318507005041c2c01c840107001400c1007000c0c010052400100041148105004888020050303040d43c0c80c0d000807280041001c01d41c809010884c41305c10f059116591 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 742584793 1250 742583543 742583549
    0x10905210f070620060c03010b03040609120302130503010603051f1b09170f03040510110a1b0902040501020604030f03090209012916030509010210061e09050f06041e110301 76
    0x340e5130540711104444001a51510424440003401d003180d0824000c1e1081e5800035005035442ca0f250060740380402c460f2440d0490f0200c8075180182d44400c00080316030644503940c8014400e915000d01000407501c04500640d440c4805100010782c0070703140b01c1440007002d080500c680b4400801041c184a150800407540603240081d4244824040010300103030780301020070342060250070501081042d410302510000300e9103060700300311a201f031010b00c5140ca0a040a01c054488800b10b80a0804074440c0140030805040301500070743ca45420100042d545400c064001010401c0029041e13a409102e0ba100c0d02e0515070041810b4030740d5945030102c031030500341c0d5102e1401d070340380c1380e8413038121302c000e481c102e44a90495443c0b034904080207840546080d0030001015065005450751102c140d40315109100c0038190302c0000b0b41c2c0080d9101450212081946c2211284925110900c180c2c4d042c2405426880b0208030750204803040c07065030200308411401000e038440d50812582c00d08541015010b5416 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 742586043 1250 742584793 742584827
    0xc0405180d05041d0618070c0818100804080f070c0806040f02040b0f01080402040f021b01090308393907030b04120201020f07060b0f010905210f0706 66
    0x4c08103590303a02c40850041aa8140d601071054800d0111030020074442e55440201c5082000d00312204e42ca901c403007903010362421a2810580a8981d0082c5000b15480c10004800e2508034210f10349540d0314a441d1003490400c54060300e0100e5450100700303280c0555000341080b1b1064880c14141403900009022030060300302d11031810002145401c1c1840f03600009070210517560b010064840d034082c800201841b00c40c43c00b03829000c00c03403150001480104080314140000001481c0886410f00501340d002c080c201542041308246010380200d6a84005180007045420342205140004505000e83c450101c07003002c1c5084411200c969080c3c15000d2181491001c8020901c0301c14041500da00ca0409002c024100c03400313500410301103001c03030307541c003204980c1400014038014500101000a82041400301c1e04244c0740e10050403541059150003d17850402c1c00c014a055040800290040707584042500d0b40030000340c0c1d41c09002204112001c151400c40042d41d60003501d03400010b00c0052000b800d258 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 742587293 1250 742586043 742586069
    0x2070b0c03060604030308060409051c17010b0702040c0e041107051204061403040f021c0302011b0f120f110a08011205030a0e01021c180b0c0c0405180d0504 69
    0x44000d003460122072196000400c520302d0726007140e90654150201410b46500f10b50782d0846480001d404005c0d200300c000c080e00e04502526242c040050000ca2144411440014044010420000c2d40d00689590039070444010074496240c1000701d5904440c16205c5601c54104800246601015402020340c503001d5410b48447c040843d0210fa540c2c401da101e200001030340209805045402f980146410500c261109003a20256030000f90100103c101c90703d035445407100300d0800701602446680150074020700d038a184827009000180150424084030414009144403240482d01c1c0c0c0d0380a011443c215280400904610300092103440e040009503c0204600000100d00d11100400741d060141d070240041d8941181502e00302e41e05280300d86060305510441110a81c0c200c22040402e020050b69036441001d41400c0f82ca9040b140420360282c071840c40300308403105030044007003008041090b058802145988950203200c800e00d90044048041e0b004420a03a0750b41940980100201c80080e81032070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 742588543 1250 742587293 742587301
    0x106081005040905191a16121505120f030c0c0a0b120a1d0607020f0d05090310022a060703060e0906150118081c1e0e060409060902070b 60
    0x8455803054050b0095005505102c0e42640c0d041e100300d18540304041c41d135044180d882444500c6d010a0b500d01103242080c00c030710341995901000029481d00140702c14000e032002c40750100c14950203801b42d80d001e5001c4040203412200c0c108090580b03441000304a07951101941c00c12512071510400e40d612840d084840012402d1802c001ea900082100c0d803c0300440d151030901c0c000078407203c40554548014101d80c0f80c2900010b00c0f80900c0b5220540140c0305a01c0840961420454a84141003d02605018003849a20700050f282d1000b0310a44006a948503c40c016066085501810003485000441800004c1d100440c0c0750780690300c02d450500a49403560501800b415003100d0100d0141c1c030038070001e0350b441030107181204880c8040c1028080c0c000c0c1c00f651a510651107802402d03da0307004016000d00200d6504203510030b100103141140036042c9441215054181480300d2500f00041c2c9150b030505581c46200300e0b070041407004004c00a0550b504131010182d0408242a14800e50420001e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 742589793 1250 742588543 742588549
    0x12030f0108070f120f080a11011521050c06040f090e0a081206190f1d040305160516090b1c051f02130303030e100b01080c09180106081005 61
    0x1582c243e46810200824903402d10609480c07000c00703248241c4e210950b80c030a00c1e000c42c80001c000c00016085036600460064800e02d0039094640c0098819142c0c800c8d01c104008040070134545080c4c043d4040b4102c140c2132040c1c03c10500d0004810b00980d071041001400040c908210301c0075500300c5114000900c64041e142e58415103c10310142c02610302801000301203601544042000d034460303401030495015040c94055603c82041c240c0200364030902002c814400c125403c00c50032079043d17070151880401d00c1d003540d0060560061480c25004103080d41d500d002048414001082c080102c4c0a00c0c01e80c4540d1903089130040c042c06408a0b0182607030f11030208912081000681ca0700f900040101028042114040c1580c0b00c1c000700310704026802e00c844060300129925400055020b6540815081c010044190800c0c1c0c1e1501d450140501c1c01d040511540d07001070b2191351014091001580340c49800c40408c101450094000c0b4035a001c01001103a1b00b074100e076038580a40003604048800a03103d03824 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 742591043 1250 742589793 742589803
    0x12060302030a021011061008070b0301050604050f030a0803073c050307091703041a040f26032803090309120501110d0606080f04030f0f05090312030f0108 68
    0xc0c0d00354000d00d00311805810625816a5241c5140c5003092400750144600f500b021000c0e1003121031403881440400c840407080040a014018040499240d0352501c400101a84214800c40303020703102d0100203d4081c3d6051041100b110f40041c0306076500d10f40100000d00202c549284100c2c888285020108181c0207006940c0c07060b0211a40c0a2945000c080c0c19121500001c0100040110001010680c855840c000384102c0320440002c50300c80e810314041d51070007440c0c000303500000f410503c020010746c1460fa1401048a086550348200803043d460b140d591107413078218500c0188000202505418440d031724549400440c4801c61982c6008882c088081d15594103000e0002403400c0414030032030a1800624200c40d02c038800014810700c90002c4501d007604000e14009a4a17a00c3d6000c105c20361700800e440c0d60052444444480500d010313036028020b064030607800c50422151b06804c07084240a071007151050800181100d208080f241541400c550080b00c0c40c0000100c5040001212000016 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 742592293 1250 742591043 742591049
    0x8070515071b020f15030103060507050a021002070503072108070212070b151005030a15030206180a050a09020414090103031710091e3c2a1206 63
    0xb07a22071103440c60320040491000c894a05a901144142c50842240e40780705441800348180c05c002e40d1a58034508000c0c1c00c03100000d049100b8020b0421400e0b44640c1d02040e131080540050f0390041e12524142803017841e40c01940001800080f840e903088020440b03442c8100000b6038150340d000b10076951540708980380c0300904075000f008e1206100360b0300000c2e50f225a0940c011594018840306014200004146080c0c4040071004280000140500d5400c02d0003665040d509684500c1522807540c2d021841600c1505007103030740c08900310f00b402240d0f039031000700f0300c0103110090a180c00c42d03171204002c10080d4001c4c441d101044001c5124104203040034144c903412a60591200461901e1080000c8442034004014900d01c40d1200e03004140001d69114013445503019800b0142d41004003400c0300200c1c0c0000c0351080c400c030ba080d584480c5007181580c00d810101c1010004c506100e0f540d04c800e101900e0221b883d510140c000c12480d580b00341c200d5103661741c121401d0b50703003140398170880c2621022206180 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 742593543 1250 742592293 742592297
    0xa11070b09120a0c121103150103021e0a0e0c0c0a05030a03140103021c05030f04080703020111011b141c02221401030207021c03170114030304140a0e01030807051507 73
    0x156040190707034105c50000b070035a4000c0c4c8030700b605520f090b00040c2c00c1941e081d0808944140d410018805d508004a40001075030b00d48100030f0680e0800000580e5142c007504c51072495021000024582c0c500003425a0503081110046a04204417440c041e510b83c0c100300c1076040020700c0c0c0600f4607011a07840c0400f038101c0b600509540b041c980015403050300d1114920064803548010401203194680d2000100020701160003c1d084450840c400100b10140b08175a5582c40c0c1e0500d0aa0022a846049500004015410008981c1c1103049040c402802000180038504103661102c45903040203400801d82d03606510380da80b581a51415050415020034040d04040707448600401480d9400399000b05510341c0020014403000f44403400018a105103008114001082d080003401c2085c0c48240c898054601203040c80c080c407500078003107550f1380a00c0c0b049040107280f00044110303d44500d403400024040120007081036603140d04085405078002d0b0000c075458400d80901c1d50f1103035541c1c0303182800f507032081d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 742594793 1250 742593543 742593563
    0x3070305090f010212070c06030b060f0901110c060c01060e0711070e041e210302031b09040603050328020304230f06191706090c0a11070b09120a 64
    0x408280000305900401c2c6a06602c00c450b001c5940c4101007001d00030192061482e00700847c18110b0040586c0d280e000c4039405104144643e2240b02c05080c16500f412800b8a021142c010b407a4541c0c42c0307407804071995207420120000d404106201e040d044002a40d202c488200303100d8849981c2100d5000380726500c06401e801c000c600344104009194000d80281c000d4a64003103100c850000000003901c501000c941c00c24180740c105c22000310101060340c1c02011410114207526000302800020f00850206c0300800000242280c55039545074014005583c21000301c03074880e9500c450016101c0005002c80243c61403104156865501c004111000e5441400c0302c2042c1030314216849140c1c0311040104c9500110a008902c41600c4180c00360034050211310b8a4070036103a0b034010152900e54a03030000b0b4801001c0d00c0800c40d40b91103550b0550317080504106225a603845070142194245071500008120b80a954000500c43d84500040d00750100100c3c2ca515400c0300d141c01032a55211014801000300000b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 742596043 1250 742594793 742594807
    0x924060f03080a05162001020c010305040b060402161202010b240a0e010c1b1a070503120601020a060507020a12032009040207021804060c080403081314030c061803070305 75
    0xf241000d4204600480005002d41040359500f41c01809000306c2c0e0140c20741c110b01200c400e980c0c10446240d12030000c1c01d007000300b820070b911020b0091000414490003103400091a101d4807442040085000340c21500718407103002d008800a020b000c01c0ca5082e0710902850b083c44a1504030b03181d54426503491150300e1482d0907909101600c510020f40100c0c0d06004000070701501082d602420000c4270b120900d0352106c020304082c50552913503400e5101a2000700b0500030440010400400c031038125510986409250b075408004074a0650744c24002000345080c4028824210740000b5804852032003102c04514407014500c00700c08481c1c049507924984183d0124512281d400c440c01406001d001034005032406000d500414850140d111440f05030041c401d0402c014080c4a114103d0098003c1c41c0c0082c16042a032401403000c0c0b40130381258183e602d0850355008204122501000c801004c0381942d44400120f60b8240e05c45d40121400c081c2203c05401d0647c05640c04001c41e40255070544855051140c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 742597293 1250 742596043 742596047
    0xf0904050601050403050303040c17120d02131d01060f0f08061002100e0a0203070f121502091206070906020607121d1c020d030908030402130924060f03080a 69
    0x200140c03100b41400b40411000c40400d0303051006600c214040c4000d038540c00c1c034100c800c9051041c441c404802d00d401c810904114000910203c8005050300300c4050785982720040c02405c404d000e540112040e44010404000c9003440c030224904a0303546131101401c00c01c4184094458007034105501d8002200310001602d203150401200e0741c512075910440d01d401c106010315504407034100183c4000e582c0508072210451a040002401411062160076241460011840c0c014551808000c0c0300b40c5540301861020885a816170300e150780014807040d00400480c035140d03150700e8150740c10030008804200104105000044480c068802640c0e10500080b000000ca0010100541080c1c640c0c2c12203444000311f00000c00c0200c4180000c5040c2900c0d41c4c0b80c0301c00103450491250001c4d0b060504205c5c103140402c000c8030540754441e80548100c0000c40350680b0b15401041c04050090511025961103183d40e5414642042d2210381208100205074440b050030214010700c1c4401002200200010f9100034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 742598543 1250 742597293 742597301
    0x3050c01080114060c0a0b072109030f0c0f0602040b070201030506030705130207030513080f1b0a05010f1209080c01200f070c0b0309030d06150c200a0905100501050f0904 75
    0x650460b081d11b0202010742d880f042030340001e4a0040024401018030030284c8042c00f40d140d0f0806096100b000002200d80c1d0180100440306c034480203001c12482c0060600c107101d40182071407944858110740d2240c950740002c1d030f181c10004c000d0740040d00c0c00000807021304000540c88255500145501c2421200b00000e402030f501c5441b04604210050007000200001140c04401510440c0050a80d0f041444d000c1841d2200c1d20980b404580100480740a4031b86643c0b90b107601b5254217290140802d6544842070302c02000350b070041c440341450b1003810b83c00c2c0121a40500b40402da804021300c014180407100304100d580102000c7c440d45400c00c8040401c000c000d008040d65031050130312444403a82d9100c03461150301b01b140c1341034280c1c10008042c02c900040e4442c0c0740250510107440c1206091402c0020301160140400500d0035410704052050400080200d01042c94001e003a6000240c41344001409400146d50220920f011424042483e40c042c0f01501c26400702041d2080c01c0203e08010840a0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 742599793 1250 742598543 742598557
    0x10612021806032e0806060d1101080717071806180b0d0e0304030b190507020c0103050a180c180605060f03280203160203030915060f030a0b0103050c0108011406 71
    0x1a100907013419115410360f070341050940e59400e0f60300c00c0a00e8096418184030004241e00d124403414850f0380006003000300040c090b1102803903c85056641c880d0306031555004c40a4644000400c079007000200d035800501000003041038401e01d4840c43c1d80b92400d40300c5101c25124202005000c000c00c3c0842503400000e01101c0e0007041003c9003044d08104860709651150f0800d03541200890b0030030140e207010b9502c04140404503e0104554501300340020740712090302402604240d04c0e44046048050a03802003031000c0c03d0748180070303000d44203032600911020851090300e5070300ba418113201040c031185104074801c80700b024104515101801502d214181e0004049403c1c2d444107400f04804070007842c82d0884400300034030005aa070300b0441010541d241e503c0c4150011940300300104a0900d40129138103040b0503000c446a01503448120020b100c1c0316101d0904e940611840302003005206c3c020140c3c0d412680501c0a460080d00e2100044500da102405802c0344012407640300402d6050104c018004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 742601043 1250 742599793 742599811
    0xa0e06040308070506040c12021309020102070e161103090105040b07051f050105091003050c061803120406080a05040c0e0702010f15090c03180201081e0f01061202180603 75
    0x38007601c994441c0c049030014035050780c407544002d0404c01000358005050014204c0e000480c59030500c6a800542c2050850b000307804c02c40c0d00c525003441164020000b50300075140c2d11a80180500c3c00303131203030f8500d2012000400c2c005241000f0b004800a404002c0706c45180040c2d480354038050074004081026488684120b605105190100c43c0191075200f00e000200d81344980172030103524181c02c00c180c2d007a000d0644902e6010114081000980002c0c0b0750610640584655440700002e02e2040072109220310b116405015a40c1c00e002e00f6440103000301705441c803070784541855444614018044500485000346100c12588040c001d4180c42120705602c070486200200e031402c14002c03908250f4441c00c181d220f50507804581444081210b01844104010501d0200110045048401410b00729100c0c080d05001c509404200c0743e40c00f41d0805078502c02c60705248400d42c182410796141c2d11400b4899000010741c0c0400403600540d071070003101d10415510080c004501315100402250790b00217054494 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 742602293 1250 742601043 742601047
    0x14192f031906081b060c061803041208030703050f01120f06060b27030316110111030c1b0607031e020304120602071a06030d0302030a140405010c0917030a0e06 70
    0x101001c41d90041c00007a003003a00c05400f02e034504044035a80c4801a02c5860320400052046030b41541d400180c447d03004810010826807410340780840340c2584282e4210240c0f1a01b40040c000030300c0360040080d0300a1140e56810000c0b542c0c0c024440030003000a0282c1040e2084461903200030079010050150f0884c0508000034000b0350754024062503600c401107100b00c140c82200311191007904070209030307000031058015616211510213007160038280c0700d00c0248100f40140f1841d4080e40710b003e41c407240c0300504c0b0480c1c1e03503850421002544c1d450b02e41d80c01803800907070507500d00d03d504180c0d05450400fa419120813544046e44100c900c0a81c0003c0c280a045100a0000191800b04540035240301d50148400581e915600c0c2130106c000701c3d030140c107480c030809900180b007041e480010340302507036243d180380051b01d035210707a0a03030310140203900000b47e0720103400c4060006100c01036102d5100d1182c2901c512000e1540d45100741240300c41d20117510500e420604c024143c039800303160410402500240710038 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 742603543 1250 742602293 742602331
    0x40f0807030509040e06062d0d0c1a03010f0f03030f050d091203060303120504030f0c1704030605012d06031a060409020408160509010302100314192f03 67
    0x1130226026081c462401b07a00050a204590800c6405498402c0e407810201c540665241000c2200100c0b0749403c0780078880d10b414910510905003042c074007400b8001010f241d14201079036007003601c0e0070030701400170002c0b1403440c00201c080d40340310f0030300880f0743c0740e224800007061203c0141c900da01b00c81e8015140c00c0e20385480c40c0000342d000b121043c01600f5078800143c074500f9814024440d02a40c00400f110038500700c18040429004808800b0441e800d10705003aaa104c02e1916201c22800800040301e2901c0c003140110070009142c002e01c0c10b0740d00d20103040c20a49050034440100c0d411316001c0d100c0d1890414800c1c00218802e07040702082000450b20100905100000700e2050b03405640443c0c80203034085800c0c44403c0e810301c4a10340c8228016804894203083c100010303545081888000d03caa45081190b19080d13000c0d4200e09440030014048451500d8401c0740d02c1c0920300c4920441d007006142c825841c64a65000150070031080c06032051680d1040541180b4526900180024000d110b800d043c076 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 742604793 1250 742603543 742603549
    0x70909020d0b0c13050306130602070516030317060105030f0c03092a040b01090305031206041806060603060609080a0b07020a0203061806010b0f0a0c0201030f1109090f040f0807030509 81
    0x3034010740f115800c450b919644000602c6048420b604440d100360045000e20000724030380d001c82115039030001001643e40e07405142c280d14000d00c446400c1800d0503003101c000700b4143c001c002e02014002e01807500e1095030300c003c011129440b00310b510740445421240411001d1889801a41c3d112100804486400c0502c0c07907041501000040c1c078010002a045034005182018041d03001408001e00346155158155034846480340101c8911101c0c0000100000b14150703103036041010058801e4220344441c19450030300c1341c0546194082c0c000403030b0410f03400080300e9103c0c18840049610301c0303010302426201c6565a413138512004c0d11400440c0325045000c00584e40c01d1140f180a1101145801c10031840d8a503020708020050780901030409003803040e21200301c010001c41c1d65804c690f107400c0010004a00c0184d00810100c10340101c001e16145440301703803850302c00080c500e8403802c8984c0d500540c2c5440c140c5038120000ca6000785120301200403940006c8010002d48103462090030402e0414007181c000c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 742606043 1250 742604793 742604813
    0x20c2512080c0705061213170d05040c0f0510081009060b0c1b0907110f120421021f050408010c03061d07080115020307080d0c0906020a05070909020d 66
    0x6030381c101c00004a00300c40400800c8250001d200949040e42015262841200d5501e401030008a401420741d801004100310544800050b400750004a92110305800c0724000a220884d03080b10040e404071f1020680400ea45501c0080341c038000c0050200560924044030140009032a916030850707920b401240146507402920040d041240500303441e09a0000c0051420105400d50000c1200d203e050305629113507500c149520002e24100241074a0407000d48510700000304424807500e0280c090941d0000c0c008400030070440300c0440150341e10903014030f40ca088804184500944c040c07442d03207101c5141c040104000301c4142c16400e22a0826a0390010b25007913480110f100400240c3c1d402e010b200c0c5c12500304c8602c0070f0015007882d080c82482e0105c0060a40301060041c145900d80030100905a644204100e444080c0e00c0b2015580310701010000d60040e00082c40c040c40812010300c4041002840010301c2d40d00c4580160003400c00f01e203400f0b01c400c024400100140d82001ea5500d500d80132980c0680 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 742607293 1250 742606043 742606079
    0x4121103030f090a090603031706060c0105040c090e1f05060a030c090603120c020a030303020c031c05060f09070e0118080a151104080703080a0215070809070603020c25 74
    0x4690740d8640350f020026042501d40044510b6864045d081c40403991102001c8a05000e205075800315841e40b00018000d801503911841d9198241000c00c810004141405030846440764818003241c500802c11039180e650314020006600c490248401001400d50049500440040c001031105074981e160519540040c2c1c11078449192960410010440c0000310840350301698909046601c0d0705900148132a44184400390805801068501055000b8030440c1c0c0c0e01220504000a11560b00b102e9a0150908031a42445084544613152060a007040d9040c868100e9541c0c0020140e412001540c4420400c84a12030101c041000413030b1000c010004125524002c1c030204881400406030b00d82610032086050103248814001045188030015080081e00e502c10a525100d030200c1c1c0040f450451080922a454000b16040c0080070350424039880c00f0f181d008054403031844e1684c2e4203400380d110741d022603445640601030011307250450002240b0031120441031210007a40d10f641c00301001c50170b95 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 742608543 1250 742607293 742607317
    0xf030d030c080a061d1909140609061003120507020a030b18011e0917070b0a0b042306120102030a0f0b090402010e01110a0b040f0312110412110303 65
    0x1035020291141c00c4200709510003c01c25042c0012801d0101c1400c07401d107030100c09200340201c40085031000003251095001700040c10000c00540c0403d0902040c81001c03100001464080e840200700d03000004a000c520906803141d0b503002c460b156039212a43c0a69807515030b0204201403041c14010303910403182d440118018103030100141000385030b2561510800c64103005903171522140c1c400c101c1d94000040300e801c1c144040060840f40070305280085103603140390b81c3d04003d0001284000c100d01d495603140950a40c450400000c0c8421041c0012224500e00e44103040042e04004640010548000d941c0140054461920b5440c0d10000c0c500f660001d0340d801c2401034880441c040b44060602c5100e2481d0411100b00e0203900b0103070000b80c034800c0d9103901e040c104100141a400004420000c0300b20301c1e540224082c800d41742034101410403181115080300007500070421000c100701980608140307161201c1d9042c2c54503180076a10801d66250801c200c43c00e05d10300000300e0301503805001400e80e01c1910 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 742609793 1250 742608543 742608551
    0x60d150203070e03011b022d0d05120c1206040f4104110415080304030b0a060b0304020f010f030902090103050304051915050a0314130b06010201091a060f030d03 71
    0x11004041c04d41d51480c0200040361b0440c80088a126400202c1e044d00070a0b0403400000a100f0a100b4040c0000507688403220b80300703d44543d0b6000340d026005054030294600074418a84401c0203814003842624446012050b40101040040c0b03030a912103180c600d9121720005080c0c6007803103001c9660604185100c0348510b4000904010800c0d00ca500b51141060302c0d014005181030340c1c0d01900180000e50395401555119000e1410200a07032440001c0d06e0120102e035115a5a4580780002c07100403168030070110f003440000035103601c1c00c00c00d680c021031b0300416100c400b04440300116004a40301820104040d203c9440d500562117510442c2c2c003950103038000c2d60351035081c20203010801c0c003245285124075485c0300003044410210002d401c40c281b036a01d070050f90744044100c06c402030220544000541000b42061004428103803042400d9148075020303403801903440c0300c016400c0350358488002e0400303125002c0d081d180c980002d40660384208000d04191003e100180841c1c50804d010844a010a0340c07 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 742611043 1250 742609793 742609817
    0x40f050a050903120f060a1205060726040f0309120f02040b060a0c15110c010507091403030403060f02070b280506010527040c02071418060d15020307 66
    0xa54001c5940c07115a44004600e00402e0014105201c08000d1590400c14400008100990703102407200303000700030b54009041c050020341011612540d0903075031a030104403078840904102c3e00300b440741c4d00340a0242c6101c241564035615034a48024400c2c00c01c4003006040e10010a0740b0040708040380209004120019031401c062040c44111070820b180103100c1c03801032000110082d4492011011560b00c014609130714a0004042c9001c1c1003060140554281c0103e50000714010560040f44940000c0e90ba051415940310038002d401c1c80400b0017150503810800040c4040340d9607402c80803c1d403681c0b007001498010240c40e485002501600c0200351044208455566681c0b510044640e000665130104294201100040c001d0300c1403006003201d000d500c444d88540b4240d40d44a0860b5410040c0041c0985c4180580080d00c991480c003070b030001c594084200904030705003640030507015200381c0010316060321b850b420000302130341030301040b0380f03620349038075180c4d0840c0444c000766000342d8864444c113a10f07180b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 742612293 1250 742611043 742611061
    0x409020a08160f030507150e030303040f110904080a03020c0a021e090c03011d07030b31110306010e0a0b18130e0a0212070503071206240b0d0b040f05 66
    0x289a502800403882c0c1c1c64001c4c8081540454004100c51404841109101c00c042d81640c88680748411765516010110403c01849401046030800e07910a445814604030580c040108007182038901611003c0113000b44041c4500030340c02040e5800781c0d00c080320b1010307005a0002d9521070400c8114140681c50032503211180c14600c40039500000149541c074115814108001010031581d0b44e0f80b070b040700981d0046001c223406680f241c6800785c80506080f51b0400b040449203e106034030b14501c600c0750f006007450002d0210b140714035140070300441441031540d00e03035400449032005004d000d550320102550000880c0000203000388911140c44408030780206140b8100002840c1c104c0c2901a0035003805180e0303212050214291a51581c103da481c444408038081031490040180c000940500c11000d0100b021031812040d110464402c0c00700740059414200720000380410050884104906240117200c2031440c3e40150181d4520300e48001042164440084c1c1905c00410807400c0d003d44d02d00500030200 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 742613543 1250 742612293 742612333
    0x4031401060f06021b01140d050613140c03060a0e0106081906050303032701020d0207020f0d05070b07030e0a060e030c04020a0e0904050a0609050d0e010c200409020a08 74
    0x2c031007440c11101c00b070318000c0c000e52a03100380f02044042d07080c0c0c01400a5503a0203440c010f005500c00780050341e00c0c5c030300c01c40007900217110990322a48501d071000c443e000c10f0304142c05010315044032402e070014039480340e0301c01c01065000981801c0e070000d244440401c4100002c0f10181c000c004503920301c11141407000e6080841d90702d00303105c0750b80f540c1040c8043c00360f52000000c43e0740040d80b50070318010024a2182e08245540c0a031002c440a50000503d41401401600076200300c0d4002c4400314200c11100040040149828074010030755044000708000003000c02010707001c000d01034149007401c4030310703000020801502c50304050081007445c00388c40802d06080010600f1100240c07011454540c0c00315002c2c201c240b5035516a84580070a00c001400c0040910998002c213600150501c01c540c21858481c1d00e0300300d0703080350b00000740308140c40120547c0305000508007507400801d10401c1e5109a00f05040f200e041e00c0030700750440c2c0c541804100507122000802d00600c400000b4014072011000310140030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 742614793 1250 742613543 742613549
    0x1e0307090e0c03010e0601050702042d060b041d18011b030f060f05370510050405060714160306051009021c02032e03030e09090a12050702060403140106 67
    0x4080240018084441007003880e075000700e03003400c207251a541644000741c01b81007100310058512036103e0b040c20f464042e9903110011533101d58024455541c85500c034170801c2c007032403160412501221103582d0a901120304001c0e0816035529203500b100205200a80c25218a1601e80b00001000f0980b041215854420351141c100c41550522100f03141080c0d1070021092401054480c50740010143c40b102c1c40d0a03007101860945003601300d4250b01c444034041c026280ba00c01e8070f010b6000c500903600110311403c212800e80e50001c2c080c6090100d203480d501d804511031300d0110441c0c8103d40300c06410301c0c0c034120707203a009501c981004101460448042c6135082665404030480900510101008071181d40c50402080040e490040e107a82c3c819400f5807071042101d203400141e442c800b800f000da00030011180c6080e0790083d1142080740d4212b00034070039440411160343c81e46030003040184000881c0d51080c1e04202410f49040b0307003851281d0700000c01c0d55100d617104440d44040d00d401101800c1080c0504001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 742616043 1250 742614793 742614811
    0xf0b0c0409050f10060f0315090c030605033009060309061005012f120d06080106050a1220060c0c030d080603030a0f0c06090b06030c06031b1e0307090e 67
    0x81070130b01030301041076541d25000e541c0a1060b00043d0b1031036603110ba407006000341c141c0701c00810381980e1820560f000b01185c4580a00103428038202180e00d060020722680d0403800f854880e0300b1144819003101401d402c1c2020260010300c10801c183d00d030350351034014500800340310b00070b44654240340000303035080c00007580072a0505c00324114600b201194800d50412482c00c0314140c80110900c1c1c500d49080a04402c141e4600c908007088000290341c00740d001d002503071409002080300c1510390040014940d80c0d486120003408901e15603400107481c8180c0454180f5045501c400e20b40f030300c500003460f240c0011341004240c0d40041001400d40c98100040c000d400c80900744990503042030b101080d101d2203280d243c501401010455164850b1003000030803182600072508200540241c642030544800c19601c262003885400020b00340c1d442c0201c220380c020b848801c110200c6465803002070800d50400f80210444d00c8041101400100c405002544115503e5485140d580e00700301c0410781002005d404990 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 742617293 1250 742616043 742616071
    0x26070f14130c020c04050a0204050301090506010f0b1c09030207090f020d061d16020708070e0a0e060c190c0204020f0c12030402090105010813020d120e031f090f0b0c040905 76
    0x20000fa0003140150106806503000718040e95400425800391096a115035010761030b101c03500e41400008205241a5110360010b0103503103035100314000c124011401d41d0301801d21011a88848a54503034030851010340700e0300546080d0741d030301c000d90011120000000c802786034002032002141c1070b0500c1428080c043d40d18090a0105980191410003100108600d110002d000c1c000180c1500810190303000b41140001c0b1241c868551b043c0011801058a4100f0749a003000000ea4174010041940340c401c1c2c0403d2655418a50103507083d401000d4481341c4c5205010700d41d1059405030716140001c1002c0d14083c1c0700940d43c1c00402d0a0303246000c9c102d451811403a0030a009100040e80e5142040341140d0003440e0070354527901c50040090b242c022035400254450301d0002c25000300601120642c40c000960786540701070130400d60505890350511b09800c86e860440d400038141c0641c5030b80c40014840d0044070310a00a0119035038010010000351503400240001007410421601c180c080d00d58800c1400f85004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 742618543 1250 742617293 742617311
    0xe0705030709170a1a1618030204090510021908070c030c03030c050d09080c0f03070b040209060a09020c0606040c020a0b0a0c050405130501030210213303140726070f1413 75
    0x1f581585c0501000340b143e5116107000c024010104102c81241071525130455a80d01d1000309084180c06610ba44400b09091030002a03110380280303440c544854140e02c500254406c01e65040f0010038440b00d650b01409000d12000c1c103480418464210b0300340c0b041a9041d603c20700751030309a140412850790340c00c1a03401041104009a505003183d5040755040d926407c0d19202c0400054508289800454685201143e00700d00b12400060076802030b00241d8040000d0350407400c00f240c80b5003130004054603001d060f001282d08000241d2041c0d0814441e40b411600382a1a00d00142c40035034036504820b003d5442d480140709501d01b481c1480c05110481c1049800145840c0b0024420b01080381641c41f03803039031a1700107210072043d0802c070a40591340c00c1820100350000c43e0440c01800c03c4d4041515180380c0d14440c00ca04140009030030040d180d61401c88000440001c421501d076419145410402c2d02075544000b5190b0109660440900a486203132a408250001408540d000700004040c0e00741c14280702c4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 742619793 1250 742618543 742618577
    0xf070f031b0b1c090206210105040501120f05011d030304140613110a0302060d0911032418010219030e010c1d0f0a08070e0705030709170a1a16 63
    0xd03050146480310140e01030303c00070418402080d9681c00030b904444002208080718090115817120b00002d29920505a41c1b2481400700700c4400340240031a07091010907480100e54070449000300148100c00200e2080035000d1041c5110101c1407060300e1a90011003440104004061180e4403180040010052441c0076225010000054400030f04046001100003206844103c0745202071500505129580c4810900341c80082c007031000705a0300c0d038641e844924007a1a020039007200c0403441c444004070f0b658002c04821408000500080d00311000200041800c0d1400c0c0090914107400c1003020402c2c1e55100c90203400c0d60800d0100b800329914042c880446140c0206110500c80614504442c00840310004100c0c080000105568003016854000440400010b0a8003c0e2034201401c0d0100b520b4003802900c2d140815036110300800d02d10030f01072001e000d4982030310981c158204121354100c0b020344c44043e00c5060f46005091600c002d001000404940c8101e111410046454000d0420f0140015 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 742621043 1250 742619793 742619797
    0x60d0c020a02130e10240f050319080906090d0501090f02090c0a0c0303020921030406093f0609030e090907030305030105210303070306060e061809090f070f031b0b 72
    0x400c00440e0b85101405100b90013185002c2521400a106d2840e261680718050003200396209080c8244128803905540c03504040d05044070a502012440c1401810010031845d0303082948540e0f008504001c826010130400d0050141440c042c901400e0740400074010b20000c804c004103051b0802404001103200c0c9075115002d4102d590305890010380311903562001a4030000443c00c0b00030602e403440c002c0040c3c01400300081040340d030a034540b0f1038660390f03d10303028503070350004038000000c014906582082e8a113101300c9400000341c01484140d002d0915a100310440d804034509034001054031900d0740f10b5080c11441d0942204540d030081007018519600202103100500030a80a83c1d111519070000002303514401000c02d03a07502c180da44a1628000c000c00030300141c030550b00016481c034424295401c1c11412108543c0007a5041d101851803501441800d0b5030203403403400b2900c01c01071880b02d656030520100c0058520a0000880e062031810003600002081c2c2d1000103403000410104840079100d41 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 742622293 1250 742621043 742621063
    0x20030411031009050d120e0d050301080c0901060504140105090d0b1b091c050c0a06120515180613021801030f020c0606010c140106090603140d020c0f060d0c020a02130e 74
    0x281c00ba0400140246c20405004c1800b4a08028482e244d00806007541090141d4103941e080c00403141542c42c000f00300464107500313101e01c9001c10350802c4248a40e54211120b581752407010704010340340c002e1350400300d070000410800980e44a880c0805000c7c0541d0080200361400340050300d00c41c1454191400200c401240360114140107a04030098806c0007400e01941d8400704008010404195907804080c1c0941124440090018500400994410000c001c51108500081c04005190300030000d0311500c61009416a940a2074200002c0304803070603400200111450fa9140c41a440320260000d416074a81b03ca24024440c0140321406c450304000802680c0300c4d0b000d280110800215007000901800d1403003800c2c80300d5007040c00204540c0d686070484030480c1e02c40d03518800a50700030000e082e01c23002c11005180040c1c028071640021480c100465806003072008000d2490840740c070900b00103c600b00034a00d800760300402400015841d1046003e0001003003100e0504c0402d01601c40940c481030304007 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 742623543 1250 742622293 742622297
    0x24020a021309051c0f0809060f04030e0609150414040203010503030a21050106020d080c070309090b0a080627030301031523090f100608070920030411031009050d 71
    0x24900b64184201048003140858410340c6000107100704410050101500001c14400300d092a00032401a18000440600c208090102c14400c6d444640e4102c940d40480310500c0d61110042c0b2141c119961405141a00c034620f0883c556a140d01e850000300c00070710446035407407080f841400100a0358030007104496541070149006207004c1c034005a83c4101801180161100614001c00440c010350001f424101c0b60707440c1d8562421555071a080c2e41440e2090180040010300d440d07404110020094001800342c000c010f015034440c5455000052508004035070014003180c100c0200c03245040900c611080c80090300000d14034643c1192101c40301c2c0001d08814054255842c02214584010402600f03500b40e003400c10b2520f10304001203031035074800c00060b01074940d0003003024100d41900d19219803022250301c1e001801c81e407803900b00e49000070041d807014a90304072500b41c5400d100040800c000c601c01ea00c500d003102c100a15010a2501e06040c803143c1030302c502d00d04182000880c10000302003041005034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 742624793 1250 742623543 742623551
    0x609050f0328031b0f020f060f070303020310080d090605090d02100e030c01050a1d121501060f020106050a121a010602011409071202090a11030124020a0213 69
    0x800300349401d9a240c61500084050342c40c8203240c428108440d50914007030382e140ca05501040c00705103000b08070804010242030700c1c40c007200010704000e0082e00b60490000d00203814200150440303202075002000480000b54000b04002c0801039032800b210180400d140104007101d01d440015000003602c0c0904818050702040c0d04805668160f4900c404a501400400544202c11406808510100c07401d601c24018403128440c113512400548404440756503883d0124000c2e044103d43d400c12500c2d040d034201501003402c2d82082c00401001e00007507507081c00c0d158590b00d85000200602c065850080859040240800003a5108a029800d030b8100c02c1c0040b803d10002d10b0a46c0d03018511a01c422400d8041030000184039030194040c0e000d8a004903035802d09a0386c1d80402a031206002e0041384281ba80c2d5030702d0003000d4140071007910b44c0f2200d58040081e8268844510a07031a4101340d00c039850003110b40004003c1e2180f04c60f92039001880600040000034890303400906800c00c0f900c100700005a403 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 742625899 1106 742624793 742624819
    0xa060506090a1a0d0305090d0c0609090603120f0203160b01051216060e030f070f090608030a0f03020f31080a050d03021305030613060e07060905 64
    0xe44041c01000f000300c8000c200c481c5003074407801d604025081c49a401c20742c49010b680c1103824098005101d0903890306c0e40081c2210080d4100c51f200324104a02000001d0030f4465805240300d0354201245107111000c001c0f859409402e50060915405895000500c03840d12001070685405841079490040c108240607601d40c6001c0606011410602041056520a041840031036200030150740008d01f22a105901c3d0069540248020044a1104000d000031620a1342d000b020040061401c040030100007401c52404076058009240e000605190b20703070051001c40701c502c01030200648079110701c00e88c04c885e0550b100481c100b40030a4190040307179980340041c900202c254084020080c0c005d5400e0200c0c06508000052855a000010040b5446d0b40601c021441098003036418105003105041c001c081c2c440030b400a01c0c1c40d400c1001d05009480e846010f60090b580c0c103940190f06021 = true := by decide +kernel

theorem cover : BRFrame.Cov 742446043 742625899 := by
  have h0 := BRFrame.cov_init 742446043
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742446043 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 742446043 ≤ n) (h2 : n < 742625899) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
