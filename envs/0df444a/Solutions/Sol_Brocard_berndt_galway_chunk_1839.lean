-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1839
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:51:46.391309+00:00
-- url     : https://prove2.me/submissions/9ae685c2-a5e7-4758-9345-59d8affe6084

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 330575539 ≤ n < 330755395 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 330576789 1250 330575539 330575561
    0x180417030a0903120c0207030b0903091e030f121c060e0708040303060503070305030d0b010201110c0105010f06080103050c09091e01090b0a0507120c0e040207030305070e03060c0403200301 83
    0x20780c554640040c0b650008212404c05404a400d2040d0704004500950b02e4200c1d000140203030320000082035024104000f290414080039000d010b8021000146801400c40d0184d102d00170701501c0b86000140b40085403500d4942078000030503080450390801172401e0a1100200c81d40c0c140c1d156008181c001003110705c1c5201b5101c035034a4034020720380b03864018107645060f0b110034080d0307001c502c1c2440010804000e854400707441c40d00004000e11180b00403409045440c600f002c0b40000001c8901030032006401c6107050b607180500302c1c110f0a030341d808210f0ba0382c8000d21010b0b003039800060010322545815040b45170030007540d60403107021408c110035814421000c6400c48225179507451402c0200f100301c0425941c0954648030410447c81c00160203800002c900079840d103c81c1e522108640214001d080d20088880c01910454a415882c98007400a0105072170a01c00f10f0b040111440d418900050710512030381e00c40802606052465503200c1050311010035155407114450000701490300c0902c01d50140030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 330578039 1250 330576789 330576791
    0xa0e0402031306060503060601020c1306050604060f14130506070302120316030b0607020f0108040c09050123030c0f0d0c080d020607080a020a090302150d0c0e04060605030105180417030a 82
    0x1d105481c0c901e085611945c0102c0c00303508160f04020050b80c011800b40554441620f440748054405a02c0780020a81500040c1d40030101140100e034207030b80175440620034160b07511404500c1112810b81c000f180a94210a8412204c0078002d120604060f0090041d5a2003801200c600b4403001c1148122034000f102c0300004d100c3c0103090207134010303414011455401001e81d01c4629014083d0081580d140c013042d126814420480701040800c200d00d86040c0041619403000c000e996103d20714403a081d140c580ca0450007044548401540307203000301d44101003410060200e414590b121041c40441d02105600381e80c5048944000200d10005020107040340085034058070162404941c00317401c010024003440407a520511a07140810b801910041c140c030b4044480145000c0400c0c401c0041e44104d40302c19400e2402c014400f400a600151a00ca4440c401c84051213071075151182103500340024400e6503403211082003030980964003403020f150024014200c00c2c10004400564403019030090b102c0154403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 330579289 1250 330578039 330578071
    0x3204060c1110021c060b19020a06110a080c1204061509060b090910080c1c080703030c020f0d170c04050306071205011a0d050c0405040e0304082103010b0a0e040203 72
    0x40c510014001380703110326504041101508001300348085008605c43c541d01e040700c2da5000810b6600800500d60b00e968050301c14018100b6204810f140b5810145c5c200e004030385264003286480100d00281c50300050b407003405070050741e100d4484c1000381c4050039030400da00045010110355643d4601582000e0001412002d9649141d80c00f03015010b8401410400c0b020320340c2c0b000b440300d0b00c2d0201d8610701044080700c0141070b8a03041610b80c080f1f05005003005242010000e4481c0405406400011344960a5000d440340345150502c411780315101d001c40b4000081d5259030010701c18511605864009085512250905031240c010030318202d0140c1e64403010941c6600030419444079030203518050042b001a85601c2004c01d203010320103011748070350700b980c5544450001d001419801c060340d0061000820134419107204081741e903201d5000e03000e0308542c1d000740201b101200c0c1d02c00525442000307a01505030300c0c503860400784021a80200c084070703041100340ca0340d285d032a9540707001542c0110300d8504141c000c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 330580539 1250 330579289 330579307
    0x309050705030105042022090b0a0b0120030f040e0907050d0b04020d1401061403160510230a1e08010303020d03020c010207020607063204060c111002 66
    0xe00002640300c54401e07070601040100003103c60780c000c0a45c05c3c88507844149190010001580d058612500c00c00781d080035055541c0349580c0743c0107034942d2402031071104610703100c0c2124601501c424003000c0d40841ca68103c0680030a1965208ac40c03a020101d081d070341003001143c84942eaa81c0203a100b10100510300b0180080101c040c0a0b150003000f007261901d9204c80300e030b99070050950005102911a51601145809000d48051403c06282c3c3c460020846141c44041c0b514441c1001c0d442c441c000d1003802055900c80c04074038074110990724010110140342d112114222000222410001100e0340c0070b450321180803030490041c2c01c05042d036448a071030140100354004521181d9045000400131034600420207ea00400c00c0030b0b1804082c60051b0740c0300341c01801c0301e0180c814034100075089000000d0020078803160380c4c40907460030102c140c0400d481540340501154003400803602c440010356580428009481070384021524800f0f42002003112580b5075042d42040482d40105010b983c0000d10201 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 330581789 1250 330580539 330580543
    0x2409080706021b0c150a020a060f0510061115060d0c140f0405070f050c01020403020607121b080f13081902010f0207060c0f0201020a051911040504030e040921030905 73
    0x1d1084510f900800030300c0f090000142c08501030340500b04075508001103298086100380040980d440c0c20070018403680003101031100c014041259038140c80c50403d5804980c4c03500c20303540740a40c0d92505004010f00c080000c010b01c3c8058010700402e070f005d0b03000303d207a02c00607841e10503007001040b201601c11000c145440911250754007007a6060700c03651411042144413034100ca410b15002c200e51400d1515002d02c1d000b001e00a200741d4101952212001c901142009046155440e40220740d9507590403910b803400e070419200701400e5004040136028070072000700e1040c03440640f0817105045000e22405640e0b2608600708194848400343d140d0f9030900b90010345d41c108034a2400b0100d10700c010725143c5c2c0b5001c0000c0c2100d0704048001c0c00721032204841c03419a84204103004200d9080340556400c4024000703000c05506601404031a10661568840040c1c9004d00c0380341e103e241c15448419031118031008010062900e200104d5a6071003d9120825420700708a4095101e50a51000200700105050541c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 330583039 1250 330581789 330581827
    0x703060e3d050c0712050d020c07050f0a0b0d0b0a090e010c030b030c18043002010c020c01050307110a05061e010503061b0c070509040f1a04240908070602 68
    0x2100e85082c0000d2002c0078000700100d61005810002c2000754800c2c00380212403a100e28110f280c1a42e0020505054400010440d50200c6100f1203059601d4401001407101c46e0160780302e4069030b020188405803030400103800c506180c010080082000030303101d0342c1d90400ca0b0038070a0b100c43d25a640d1007409100300c1e0540309506603000120001c01883c002c0c1000a2a5010b422105212000b4144085404c22a07588081c0c03403181d03112401121841c1701c440501c061541c2178210000158240007000c0d0140c2d0000c40d40d410343e000706039034652656030703501d03410303152000b82c944040f0561288407450404210309000c03580c0204d031100505020039a211001405401c07040e0800f920035000f42d4284410905041000301c2d0780403502450300e4441c00448025400d00b042d03507000c190094825020803081118242c203d160052249840310114000d0f2101c410660750103c0380202403208401180414031402911101e0030b459219003c03600e040e944d59001040d4000c400d04840d05900840d0803104600d014250f0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 330584289 1250 330583039 330583153
    0x207111e0f01030207080d050402030613170a020a0615051509181e1026101805010204030605090606060c10020a031b0f0e010509030703060e 62
    0xc1085000c010351034003140180090035210348000001150340781d00030f03019a461140c1020801da100c440c11160b0a010706000c50b412440f038054140060b099081c0044c41049558026a6141c0340b041654407024156001c40f500206520402c2e6030b510003c0c0d658000c42c068904100010300b50b8529000170721808003002c03c201e04410b41c0c244000b0419440b998000080e80c00c640706180c00c107450b048003108100c1c40360304030404045a03120400414415140c080c0c812588a500c8482e0311b04540b84458245803040c07661030318260008071031154003100c42d4104060b02950401c450304858031503503e440c22a40268001c40340d00d5220740030400d506c0020b10142c1d500c040d0941e1040e152401c15041c2d292285c2d02021480b1006034042050565544240d1100a42164142049000d031541c80c5000c3c0c588903801d6a107c002030b0000410b0201544500e0a0341c05d1070070040d0003411200d007559130b035101501080c0700001c1c0d984038240300d2466680c02441d01004101101c800c1c2c07a64183d022283e8840c44110b1000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 330585539 1250 330584289 330584299
    0x9020c060609060a05092d160e03010e0d1107050303070c0b070c15021b04060f05040f0b19090b060901080c0a0201060803030c041403060c040315020715020711 70
    0x290206001151207580650101c48486480d51818005880e410080d00160340006c0c1c03460800c4456250700340da40c00e008840a8200d4a507102d40071751124003800864807171074400e0000055101c91402074005460842c0c009002055901d104a0258a02000801d000300001d0340c14181032030220050200502600c0140c000d1880c100240d01e80ea464a12280f0601c0384040000804030203101441c85580c020f45802d200d0b840200c05140c400035501d5019115001c000041803072280d1044c034144c440c040848117803c184010846c50002000b0041640e40c48e4904516200c4540d500c955540e9110304206001601c4101034103400c02c0541c5086400300041c2c0c902459040085080c80da0b00400d4441d407100b420707801e0a94807815210100e000d0111540825000c1c0320110520500c07007481005081030301c2000040a905104242c1016913410050300d0038284120200710500115038007041040700503401d064054500389032a52040038401c1c04a0305038111903400f1403410304204101310f00018528040754 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 330586789 1250 330585539 330585547
    0xe0c090606040f1505131d09070311040908090d0813080f03160212070303110c06031b0903070b0a1805010e012a0f050303061c0308010603180b0a150902 67
    0x59800115110783c011380d20040404501c502106100348101c8000e1170402207540c9106580d02c940c4565902414025920f06260302c00050a142000852504680c1c0140c4080701900802062000400e200e80301582c45040821405105131151542c030102c4603c15806a5900d4810703d50083e811190f41d0050b07405074002104003000e0039000010303a4040c0c6420303104103a1803122480052400c01201c0080381d0345014608000040c55003046210100c409601c09940c1c0024a80c020009941301c11101c0c0400300e004660102c00b05804540505410700d0702900712000c0c1901c44c01f040380144c000c281d10f04001540c1c504425412800c03091000003c00d0207003000c00d04100070400113007003502c2000c01207200c2c1150042d52480c515050010040769274120000b81a200c005003000d94807035108598035030060500b083c403002004141d40482e42d80640640e92f4103460390a265088020b04009a00407201d1100d01450f0307000728840410890044510501c00180007e030080303a619100905c2d40440c1000348180 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 330588039 1250 330586789 330586799
    0x3061404060e07030b010618090c09081029060403050a0b0405010c030624090b0a053001120203030910200609030f030613020a0c06050c03040f0f02040e010e0c09060604 74
    0xc5191410b40d000383c1403509004080c00f200e230050111aa2112803d00e08206548000356000001c0c0c0e800d45588500f51400f01140904510039501804101200d04014412a003019250559842c8407884009d081c203190654035100c0c14074110b046a41603a0054044040c0010081c0900c2003c20201581c141031007042c0c64400b8025801c40350400e4039904413400858005024414240c031b0016040900070241c8915403107000400f141c201820301d400440d2000540504890480015060b6001c0c13081031115980c00c0007900702c0c4c10140100102d13010b03c014000c88015941760b4a03910222583c40c1d4511110101395085c0f00c016040d541e0006009400c41c50034040d0104c0d0101c00c5451410004500c95034940324078012030400501d496034492683d00c0811041e48255200050211a034040c0c01c05100c1c684030717010341c004148030642c6e0060401d4012000500014440004150340500080c80003d000b0814003d881c02c2d910110b07840718454000030411003561030115050b44d0080404d03150141402d00785 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 330589289 1250 330588039 330588053
    0x52a010e0607030c0b010f08071d22050a080c0115062c0307091e11251b050a060806240f0a18120b040602030c0403061404060e0703 58
    0x201040340d0141000180a200381402030b609511241c2c0d00a152170702079030791640094800f400034002c0340460f01030402c0010304041d882203101c50f00640c451201c8000d032110742401e046110405a00307401e41c1040070110000c11005d001000c101c50080140b41d41d9810382400c0582194111650140740c94031088007440940da2022403403081c4140340000c2c002c90001c680b03803c0b914245502c0c12039894490800041035a08413500440c005401a07429504252402901c54041d280300d8003180d00d44032402d00001114244442c28007000340d00307100031420484129214950860401049480c07403561200d4100402c1c100b80c031002d0000c001d00e20301071019042a200044000c40c846014405641d0100000703c100c40c096011500c2030441905481e03514107510101609140300e00800c20302005421000007582c414050400031216400b245d61052540c8a0795054001d42002e84824210401400080700240151040d204141111818100700f407034245048015544180c14821841d00948401c04c0000c0d00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 330590539 1250 330589289 330589307
    0x18090c0302150f0f1305100804030503150306100611030a051c27020109051f2a0b041214030a0e030f0316090801020a020c04050a1503052a01 62
    0x3040b1070b030003003116080601001c00d0040d420b90a010b940001035401c03100d640c01000b002c1213004000340942d51955a07040041407158407002070085003101f800100002d201b032008583c883c1c20103050391282d85000001c0307842c00100b12500c0c8205403188100b13016241c2c00104280004810500451030001c03c108010710038090340b10f0705056284c1039110200240b00c2c94000f64900c4102c400282050030001003111440341e185a0160701181241e9804202030921a0303401100440c11420504a000000412107000075509081e005c045a40071480340d2010303109010440705030085012012509050401452a48031070100400307000300c00305510030100358102a07a912000000c000103040300318407a864251312030301303052412000d000410013001e282007425600080c5a81c0d510060407a4880a4443c02c078803036510201c001d40d1060305585290314054000a6015059400100b40f080e0b09582200306400940c008484617040005a2085540031001201401c0b880b0030701c0c9804080000006015034403 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 330591789 1250 330590539 330590543
    0x1050c0301050d151103040c030b07020102030112020607050111030711010608030310030b150607080a0f11190203190c08100209090c030402010302120709081e19020d080a080118090c03 81
    0x4803e05080101076194081c040b024021704030705550349410700d00010701c54100d020840b04120a100410f410038414420359058541503d55101d82c4140e640030400c2e203800c900d0303007101d842d0348a55070015070350180720245014030815260324142103440c0f00c41c01e080da645600000020b52040c820001000f04c204410400c9075042840300c2c503161110324030702201c5004940100c1d0400000a5010304005079100107101039030041c2d807280083d100d00c110031582d03010a10a490f10340d900009104020355008607240350380c188001d04441e07131840c6014021500300032880c41500c2004821070100f11071a0b00f03000c040034860200f102107103001c820b03400107070345c2c1c001c094080c200d100c501100040469000b9411550144019511100c052600e644020019640e501800a45014130340c00001c0ca16001c24595544610b01c201030201d0240e080100b03440c441485d40e051740d114800042c204041140d0b040203041c042620750310806c0c1581004204402c1c02c10003140c07900403615201010010030300184424003525 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 330593039 1250 330591789 330591803
    0x31b0603040602130906030f020f2d031504060510060801060f050d02090303181005090a0e0a1d1617100b04021c09020a0e040302030a0c031704110301050c0301050d 72
    0x2088600d100c4c5004225600003030401807520a0100502c48500c65030b062086c8208c59111b500c140100c1402000103000107500040c441d2114501e90030102001c444101100107000c07100c000407aa002258800b9090718184c0300e666507a014043c40152040c3c007030000d4095410f140d407803035140a074006d0004000171210001c0000c081003000b0b0048541c0c0480e88000c4c0000d00726500d0301d081600c5100c07218807844900e40704007492480042c2450003441680c4a00400812072200580751100328040945c000f0050a0041e9a5031000760401d0801001c50f030a0240381c070020096804500341c4150030b03654941051503c0b05070800d8090407001c0c002420034189901e0280800d020301808041806030207522024a641030070346911480118580c0e01809000c0d000300d43c2007441682c0c0e1001c1d2030001e1001e960280050f001000080c120901500350008114402c0c50820b42d00800310f01b02e242078142c00e890407070702c0000b26680244189030034001d072034100c8000414103103154500380025101d08100e0a0080140c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 330594289 1250 330593039 330593047
    0x4021507051606081009110406030207020301020405040207080705010b3a05070b0c0106140109030206031f031a06040c20100c03020309100c0504031106160809031b0603040602 77
    0x88180300d841e480b40488032031941c04a4480d08081c01074042220703160f001e034200c0310700007880f603256005c2c0407144d03006c00b1b4070540b9090903c4000c41c040c0d404508141e070199020800014981c0761880280b8070f040c01900115100d00151610500b5100071401e40d80c0702c5d001c00c91701403030802042c060703880f039007514104104074a040e555090b43c4c3c0c8440003c00904607000d000e0b070014810444034010004c04504600030020140c0b01c6030f460124000d0300711460f00241901c0d40a0006080401c01035070841c0f44d031b411004070540d8424441c1c140d40901e8004552820550700e05010802e00e1100c096000710f000c079403e00c0282e0314040000d0034003010a0050400c00000d0f0f0001a1003031003409500d6001c84078038024020f11a100303401501945c401c1d94419a940b05120840d11040d007548102d0903c100d4070355655180a183d030300c840007005060314450381c1c0800104144464a00c0102034209038511455805480d02c61000405040814502804644039109403d10a01c1c2c1c0d50081200d51041e40564010f0b00c07 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 330595539 1250 330594289 330594293
    0x12060409060b041d190b0703020f161101143405060901090507050a0b090d0c17060609060a03050c041a0d0809040c0e0306130303020c030d09020906010804021507 71
    0x646851000660400d01d0003106100044c40a180c0d05130815001c0100d0390a241d20480d9584a01e03a01d40300074048040070404190309a02c41d800174040e108400c5080d5081c040d008100d4007425400c0e0703c0860b100d000800039658030f56000350602840e41c265038030090400701c418001801c5101050702444840390b950078008440c0420040004809070000100c9203586002002c01d0f0003001441000c3da001c2c0320301e010000341403403d003440d9001d94041038080c0c0d0401c1e0400042c422a9000d448003110610f82010010031113400700181541001c4191000b011b403420003505000148102400e51340c0280142002407000c620000360f000e540850076100060103015105c800d6034030981400740300d5440900e42c401402170080d00d002910b0551000c4070204034100813088152007020032140c40d0368242e049803001610702c1050300d2404e0f603194024100540782c800246042419540b10341081040160f540b9070013030139410702118043d400701003030030401c107242040d4000074503003000080304504a000c00240c44003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 330596789 1250 330595539 330595541
    0xf080613030c391a090117070504032f0301060f05090a090206040e011508130803060301060b2d031308030907030606030803041401060501052d1b121206040906 70
    0x4507040c650301e0800554050b00c083e080e4245000d124600c0c3c0424400d5204400c203410800b15840c4c603205849441014104d414240c081c040010003007024000240400000b041c221000a08031030502c0b240c4251651071114007140c0200000d9056000781e1501e8424000560361054140c1070702c000302e94040c51176480c404000098620100000e42100340481e002506e078444d00e0b8141c2c141c41e2084c44035803a640c03c3c40b004841c480d20442e280040c0980907001580411154030065070446409070000c6030707150b01c03000d41c080f060380f120303900038540381c01c5000c00e0040e5004070f03601c19001b184055149155041c1040003010484003180080d01049002021400c03409c02042104025540a01c040c00303800d030307030f810600b0094004079000d0301e2041004080c1e0054003810b22450059075016110982803106c9101c1e05c2c41c4190b6400169200001c04404a000210301000601005560100000d1149880b0002c3c0e5080c0b08428080a0115809004c1c213003159094800a6921440c282c8000940d074110742007200c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 330598039 1250 330596789 330596843
    0x10206160f1d130e060f0f0c070f020a0e010f0b07080405010509210606040e0c031209040e01240e100302040f1e0617030703020a080714070f080613030c 67
    0xc1d400a18074a050183c2d401c6900302e40c84007125a01070742d00c15075603460807481c0484104c0311101c0c0182c0400c000b4a14010300c0002e450120302903c00c090844243d42d02203a060383c850b40041c488120140d004100c0b81984400303207009820131010700790030405140e484a0b501c1c000c600886060000116001400742c072502c158140380000d076031101241c840c0100103103807524402d80380980128180701c09056a06000a5202d4006801800604d4090000360038284036410060002e9400b984271000711203500c1e824060800c8e20622548185030402c1105c0d03e80341c0c29210ad900040359184014101701c5030780e03080188241183e13010f81e8041041c0c040080d00f8401411501c140c02107034a81d4544080080c4402e41c4400e00780c599038035042100a0307400400aa4a0182c0344000300181c1c480f039440400520720101404190744500a00030040d0341056080b0305240c03103034100c00756000d0900c104014034201080b00303036003103040545000d081c4031054400409081c004100903102c101005c5200b0b1400112007005 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 330599289 1250 330598039 330598097
    0x1707050f030c03090706030204060f030f062606060406060804171209060601120b061b01020409020c0f1005060109050d1110090303111203180a061a010206160f 70
    0x1140c0d40c1c82c18074a014100d40094802c45581d21039a6404034503180248200c40582e41d4507140d089030800808001c07000f0b0326607604048507080c1c4403040050351364000c08100c81d11050b9805296603210500c8a114617056000b03205903c00c40c100401000f00581101d01e8581181d00b04410001034410710b00c07407a845105800e19100c50007580001c00c0100c0704040f80007070142c04240c2c1e41c880ca42a04000301d1050302e03160500b0320f82c030200401c0080c40e140500c0e42d8a4407000f010f04005403c29a0381c840c140100d80001c000c1c0751043e00701c0ca0310030060071401d008140440100850802482c2020310000305000d510740240c2d401804a80c0700f1005205210320b00700948240144405602043e802c00103000c02040d00c4110007056291420700d102d10030120399001d50300341a1822608580d2446461840e541040d0050b2040e800f0301000200880c259006914414070084c4105c0c2022813444002882c1030001400d030324814103030071412000c2580c45640c4074112101450f202203648468280c83d0085425040c00c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 330600539 1250 330599289 330599317
    0x40212030c070905010302090702060c03070315090e030403020a170c011116030524090307120519050415030903020a1101170f070f1805010f0c0807050105180c01170705 74
    0x80003d083d0003541043d03040c1c034400da0b40114161a4844141e03541d0000fa42c0390382201d40c2c10b0000404803031003035000381c500d0004005202c0403150f54407007800c01c039481102020050303000003a06005508052a80301c0003010290600303c0d040d41c8095100b5154842c40090504100714800050510305080002d91802500009030030190f43d520726006030b4a064100300d07a5076840400703042c15890b0031030180261003045004007071f42c0303041d4003550f601141d840440e00082c1409020b0141055060035901c401d411114a0b40381c5075521400c1080c04140c00e00010301c01c104040c1080740c401d000a901145d0110340c0da0707003c42c07130741c0340503101c800113032000c0780c003454900c8610550000300702c650814882441c3c0680c80b942c490050040c540c080488100ca8190780000d00e81550810810480d44581c04000c501400da05d007030000510305a0711b58407181c3c40b420007920284c0d1584180072004501103009002d8181040041c1205040000040e0070000c280300c81e160303100c001500050300d40380101d0885451a800a031 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 330601789 1250 330600539 330600553
    0x606040306050703141807210b0f0406061502030a0c02030f0a060504020a050a031a100b04081522080f090402070302031e03040309140f040e070e130b040212030c 71
    0x2030050052540f11004a034170603103c4081031850742105900c646030307190580603011079418165440c05488480490036900d501218500001ca031404c107a05000d60000f80c4151040d0404c0e081000545460703400c0315010684c118103465500d6000400c48040c00b000d420004900f8038140006030401c482414010490300940c0300300e40400a0613032010307208a2085850203d03503616103046c01600101404002d2801d502d8680c80113079000303103d003620b61000340012150040d688488184099412981c040744241d4400342c400040d071900718807081c0d4854100320000b103103441d45104144102c0b03141c001c007510012000804142d480e240d00103d03201c149001d041950b80e0f940500e80295241e00c1041300500450340c065410b00d00034200401c40780a0303a0107945400d032a40c108405140d03c111003c81e440d078414182080910941c031117005120b401c0907810068800e070f80c40e000c0d1b0804951002080041c9403103600080b080007600003001181c0080d019100040f2103401001c01d1031842c07003880401000c078411030f0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 330603039 1250 330601789 330601801
    0x18090615030703150b0903030403080d0221010513052701090f03050310090606141b100c0306060309080714030d06080607030e03032e050409140f030c03030c03060604030605 76
    0x10b040003c158212020401804c1c1c0e85d081d000301c46010744407040d9815041000b041001c62529005404403294501006181c507000e01581e50044107101815910400d141d001000075141148081d02c141d520008140400c0c07078091141c056074180d24141207104003000004041d09082507120949969002e003810294040c541009400ea400c00c80d40071520b24101c90000c00d043c0010301581c0c0484029444807103005034080b1035856141c01c08959450480405005031414680822071001d080c4450000040c500c0c01855000303054500680100e41414281100b0172700140d40c14045445217900f000e03004a400803213900d024154826902d004841d1410043c01141d18200404c0c0c041c050040f50700c04100c045c00315400c0f640c03640021606d001650040041540fa47d4410001100002c4100910030816913114800207007202c4004205403090103490044101e008000c00103103c106400b80001c50030540b215030116500c0c0300043c24003102002c0403005c10003036210181900d010f0340e481442801140307000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 330604289 1250 330603039 330603041
    0x1c0323040f0f05101715091501030b010c110d110603010305010f1803270b0a02010603050607020601050d060e120c03070c05090105060711281a18090615030703 70
    0xd40902c1c101d0300e000d00d0300010301d03180c4a160440b00780316a8441842c00350607819004940d42008040e500540f084e00c1d050390441d50380c804000d00c28100f4076031a2110308240d400040031104403a0f0100d061000000c00d90f400f10b28642000300d5070070821550100d0011107840e01c400000b02c0074521035002400840048104081900b01421010303e440d410003032280d01d0030105000384c240c84c50250215407060610108141c040d4035074581c1d0000d10712219800d40e80c0c0c8042052544c8421445c40042c0d5481e0380900c1004018480aa00040c1c42e20080c0125410613000a01d558607011001704115681d1002c5c0320300240030b000c5142c2039611031199030348422031001455220341c03018504482c2c40c0a280c401007142e00c0c02c01d030904e050f110090903207800c1c005540e075049404c200310240365a0144d400c0000306120121407250340101029259104079191603c2c5020b0b000400018901c0341a040070701005840075148110030182e4041210b42182c5604d480c00030031703000414600503082144000041007074807601 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 330605539 1250 330604289 330604319
    0x60e0f09010c090510050a0905100e0a0e010e0708040303060b070f11030604150e01060302090103061b031107030f0509030615012c040c170f0a0b1c032304 68
    0x81000030b1002c0e002c0c45404407140d0599000321030780040e20710350540090b4411030240240c0354250074680402c075165400615103100c3d000c48200024095001c00186080c0702507010006e00030744040d41c60b02c0d410031212b00ca41e0940144014104520480001c0602d481fa4101700c00a01c1080f0031280e94943c181040680701450940a543d810303410048049641800280d40b40708940203025544414811005c91000c0c00c440d6415100541d04c07640003001507600c200100b4025841100c3c0000c2c1c00c817408110381d40d040e052014501c02d0502c3d00810100b244281c2c0121000b0759414a04641c820361041c9060b6203c0c020760391820f0301807162f5000c0200442091004001b9400262158045043c0030039014824420141000c401c04e01003521580e22402c0c150080c804404590801d40864003c0c450102e8100708111000300311100084184200b0344240d03c075504140006403001c40a44008440c2100c0351106010000d0030020340d8288500c1c00c6040140c1035540c3d2700303941c2c01d460751656190320318203414203 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 330606789 1250 330605539 330605551
    0x5031905010e160f02070b0d110f120f040c0e0606040b0d050402040b0303130b03100320180f070e1504032301140703090218010e0a110301060c020d06060e0f 69
    0x2001c100303082d4544c05442641001075150f40240205d9040240c13000701a00b01d40c0300c2962140d03c400e0320220142528000d030000740410b8150540b140c070f426400308103550000d04000c840340851400e000c040740e11038440405a55140080504584803c00880c10601c165441000c4200c004118240c02d886540c10450082e4000c40b42401400c000342e00b0542c0301c0c850051200f84080030342c03608106400c1c01c98040e40d0701412a01c042d604880d41ea480b40307880c020b400607411611110552a100a40c948284030b801080d50b0400760002a140038856003283c254080d06540500c04034168018040e500e4041c050885603002000340c0d00c90380c1e00c0c64003011002440420381805804a90020072201c814442c280300d114400c1c01800307182d15000c0d019801002c0d8950140c0e08200441c454041c101c64002c1d02c0c60007408141e040a00c5032520030b580d1804c0701d42124203450882c070104010030540c0ea12030746a41e40241c0444080c0807840345868010300a02e541d62101c0304c0802d8003020042c0e500c17402d24013244143c03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 330608039 1250 330606789 330606811
    0x1205090a0902030f01052d1903031e0c030c03081003020a080c0312160209040812070f030b030c01020c130207050105040f050f0105060a061b051605030124030305031905010e 76
    0xc0d0301d80c801c102030b00c07030030102c2c401f0b088110074042d0708510340341181e44031090405414000c0c030000c1d41d02c80c200824500e400c1a004950741d6501d440c00315006140510401d002d13440c00386041c2034240ea00501c1e0142864000c1c1c1040101070202d1409980208400001e40d401800e40a40c42da44e81001515010001002c600c82c0c000c0980e40804420f07110200e5504110301c00381d00102c080941e00700501904060015180040144028003c00f0054841d1a0040c44079840f503424a00100000406441160710400c1c041e8121380c1c03602500b80d07000548252000e1080700e80180e80c002a44242c0700034018000040d18940c2404140800c0c8a180c88024120310b004109548800d8203940e0001d00342e480c10380701e007074020750300c01c0c81080510302c00ca00070326510001c1562200c107240c0c0c0da280c0d00d00e8064844100ba00d03012104008121600c0e0901c40c00804031080d460845144404d580070840700030881c0300140034000d000000582c0c1f26065040701511001d031250800031b55848010700e0200c0720045030000151 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 330609289 1250 330608039 330608041
    0x311012d110d050424090315290a09020d1815060e09060f040201031107030201050114010309050709090804050303070b010302010e060f18240d0510121205090a0902030f 74
    0x2c548907401311400d446009800d050030442200400700e80030055400c4604120300f600000c000251805a041c20650480390041082645010307100820741d404001c00200000304000f4102c95100c000300c00e03044444000c0300584503502d207010100a80b00380c10399400072444540d5a0f0081144008400c406101160000c01406450311020040c08409440d821015403100c400109170840701c402c0c0380e034450301c189000309906031a2032941007540c120010480c0945d4440c0c005215510304241130704141003003440c0503c020600d5407195501d0315641e0141c2d0b25519110350303e40d000d000c010003c9078001d0001404076aa0b800a50802180c2c0007000e0000b01e00088856590410504e4420300751009802c005000f00d240401c408402d01803058501c40280d0440c203808407003540400024509098140d00c1134005070741c1c2d0040d08075002110030040806403d00c40000050100800c0c1400401075180d0240788242c00c0340e0021001e40e1a03000b148107003a80040c01103000f10702c4200ba6009180282d800c14207036401c1b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 330610539 1250 330609289 330609313
    0x806070905011b020415090e1b06071b03020306040b0f01120308060f040e01020a050c010e0604030f051c0c2c010806011407060f090209070201060311012d11 69
    0x146000340c85014000b0b61000c0400002512403407407180d45030300c01800028030003140381688034100c0700b6074488461035540d5a99000711200a0080f28295518644403151401030640051054050844c01901c0c060f44107604040c3c412035900344902450300281150160310f003614141c603d05104443c000c0a40316003200026a0400d01c1c487c0740d04d0590b00d5201c98501d541c0741c6041c4503500c01d4184030154401e0303d6800c05968001c0a10087c500340c1410b84c1c4aa03a140300c001e0810b4250b400b060a03440380c0d036001c80d0820010940c410120005840249440f56461600d51103e48540d106044100c05075464801d101a0b96038200841501c1c8803003820100c10301c0c4446485444aa201d40308102e03000c109600d0009845600c01d503040010244189006030034140562101006c40301002e507900d00d91071b5924155425450800d0a49510450703610091101c241540e46101101d2100d49082d4103000116030301c41c800c0041c2441c2801c040000d81a0000400c80d142c000030940c00500c860b8500380c0c098440e180308 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 330611789 1250 330610539 330610547
    0xe030f06091501031a0606190f170103020607081b070602010507080c2a0a150207021906020d08040218100501080c0a050715020f120f0a05091506190305010204080607 73
    0x3c100d13608002010b01c0041444500c00c84036200800700d0781d004604006082c14540c600c030341e9003500c003000d60b5805e0603045002e401814018503244111000742c11040100016542e01040307614480c0c0c8030f00036903124221040d0800c951100030182c034480b4015043c010503d0341e070543c0414403840481d40c462500d9204c04122000d5032007510b0462001c44000081c0a40e40c4070228040119280b83c00120340b919140c903280d0340c003c0744144060704200c6400007248025440c00e00e0301c491008e2003110301c80c2c03042443e000000e942c8003038820000040c441820000b40665460495000f000e09030040d030440300d842d00ca40340c20070b00c40040c01040e0201c3c0103800031400e101018000d8071040085519403d10300344240d00c841d548420544841c52015030200a160001c5d40c038403014154a099400c0701c94002d0410b5035001803141d40c0100070b01e10091038007013000302c6034000003070387e01809061202481e020f48400b004180d038000c01c55400302207410111000000c00c00154014000c645e8803078140d51550702d54150442d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 330613039 1250 330611789 330611791
    0x4080129030a0204090c0807080f100c09031712041101181409102403060503160e15060301080c01090905060303071b09050c04050301050f011a0a0e030f060915 70
    0x141c065000b031544100600b0654002c003034403402560300f1000d0301e0b030303c1c2da031103103030005a03003004806070404255400d04100402018861882804091010280030b040041c0200f2417403201030403c0c0040901c505144c50058102c48070008070f01e108068914250510002c04d0030340c400450300241400d003407412048040c0c4810302c02e03211494981050040b0800c03c0102d610300180c40307580d00c2003030780c00b0000303148040c0c900c109410b80c0e4512070b949000d0000340c0080c00310707291a0702450198008138424403884c1100358040d0181c0354000f05c07001260b16401607503004000000b040d40d820040c00400800c01d85000240e4007907004090b6a99518251940c1088042c2e40055840035010f600078450800018108104141e124864902161155a5440c0c00d0416500255581134003144009002d115905080c01056400503146108140552404a032003d0029410540114130000807944590341c5d0300c100e2004644107001000c549104040b003048544640b82030340c540a5078071510a5022010070007043c3d107 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 330614289 1250 330613039 330613121
    0x1a060d050706050705160303082509051e040c020303061212091c060501260102090a090b01090e1014100806040507091508090c151602010c08040801 65
    0x28001d01c0b031801000741c0701500701c06011100e81c003d5403d8100107081103003241e0001d5001c1d0340c40850504181944030204038286500007039032100c0324020340a23140c2040d81d0308110f50040c0d03000f6030710140d0b1407440400d8084104c0840c0e805405c002d003040300c450f4000f02460140c501243d20744800d84014066595801e00c00c0c6590504850030310031004ca03031808403030f0f0980c0108081c4000700a114075940e03500450700300b40c01082e20300d28074516850b11107c0e014282c42200750880000c610b005219000154207204c10301c01c40c90b88541702e0320034003c1030f4443c14034180100b941c00924400c074103105e400041000401c0c02a015030152501c0010a2403410790010380c101c2d8101d032286100e41e11090213000240a00a0250091094440d80010b1148980035036801c0b48003180c0c0c5500050402c12590b600b4074181405107403140620984118000f40800c044503142000494014149120751006945d24105000f020300301c40f602040001d6000419081102e01c0706020340440d1030711a0310b074001c0c10102a84006 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 330615539 1250 330614289 330614293
    0xc1416020603040201050c06010b041505071a270708010f0203070f0302070519050606090a1a090915101d010b0d090c05041509050903070308041b121a060d05 69
    0x1502016040150003943c0040c01850714914040341090760514080c001c1c2c0c070403000d2030400142000038000c0311000b0f480062240c944545814030b580c9640501c0c401d4904003940058841010621422841140540c05803d10300c00341d0107681e40e562043e0300c50070688964000c41d400d01503800e0b001c091501c2100d00c1030b8401d4031050008070552604400075000100103e4080c0f141d0f0a81c01011100c10700c039940c0440c400d00062030980340c0241400788003c00a4000c0f0106400c1c0015445c1c4208450041030402c001500c290484c1e50321080c45034a040c6001000580d03892100040c480e02c0c4200c410840306494071115aaa91001c940001080344242481f84c4c01610038140002003520758250412000140962005d504081d1280c00140c103c450468a0501a542c41c203010400c0c94203a0051540c40403550015504151217174030058001d40d0000c0c80200324145000295420b1182454514050884030550300b14100440c6484417061000e9841084096078480001c3c2042ca01901420300460344200 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 330616789 1250 330615539 330615577
    0x1050405030a0c06150905040213060305120705032208210304060c030902030607050301080f0708061302180c212814090a060e0d0f1d060a030c14 64
    0x5003c03a40185584030031102d59858690365450243d907090584054484424005024100f61040051072386884103d01d01807401e00d10300f0404207001040b0034903214420401d66030b44020a241c01415845006420b2413640800e035811246200a82d42000030b590145003111010706a007000c0e40e41d0a0307000d075018443c040003000094000f0303200ea042888640828100032400b032809600183c1020070480760800001d40c04001005071100400c002078140c00101c6c0501802030030000741584480004100c8902c54074188410411501c0b0b000a09901e81045c00e810b00003401e06009042d03442c1d00512028520004150380c06c40c0300c00364000b45c44d00503c05c0081c88600c00c20315910f00c599020100e1421104556111040d13040c05400ca1000e6114100780c0010300000c952a02c1d10070120707204680d52009950202031000f100c1a004a44000b485d0b00508100400321041480d90480b040c128007440e410250100c0d50300b00c125010b03082401d507205d03107031140116202d62035240d1240e030299081c0d01c00c5107080d0302 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 330618039 1250 330616789 330616807
    0x302091e04030f030e1b0f011403010506070809061c0501060e030a0b09250503010f11031504090f03110601050616150204091503030e09010f05060c2b020601080105040503 75
    0x243c50260124014140800c0f0192a83d426a080030101800c0307140805041200500d2490244103404444c43c090a1501c2594084221252140014011907010301300c0001c5c114248418102900d0310600010031007035807000c10a02e040c034141d500e401102032950500300003090044c0150340d4801c140402500504da1044252914280d8200c0030f0035007003480c06980c1c18149030a8103800d103000b01d008640701001845103000281421920352101103064240340040c2c00410001d1b0f4012660405a5022034040642501b00017070010400000000d08400f40c80c4018010903030001000c104204511040d182d041e83d81c2d00c14000b0920448003e020b050981c80303801c40004200412143d01c40100c076500500f4151242c540d101165880004c0c4603094110300010020140d1200e010392218900f501d401240d035160028011200340ba0f801032030301c901c0b40420f511102600420aa03003c800d08280f030710000c5512100d03c2c215850b0030b240d00034010f009000021426001c14001c4a0007945c2c0324008614181c000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 330619289 1250 330618039 330618047
    0x40609020109050306150316350303070314180c060d1103010e190b060f030a09150507020d0206090706030c09030b0c0d05090f070b0906160b010302091e0403 69
    0x604100e06210403088046455201040b2842c440c599114a900d4015240c0c01003514200c81c41d5040c0e086c400c0410002d01810218841240d01004180010841010308c1c200d00c03860030500700400724140c4404020000f034103074940c1200904d041e00c043c0e0184075031034142200007000b035003407081ca03801d511202012981c3d090140041c1444150f401d40015440c482039207900303655100781e00c0207100d16205130074080d4040c1106140700b039030054801c0400490426038041581401410204070a081010000821b4a41a60000d03917245901001a2016030001401c4c0c4004040a641d070340d0041c401c06070007400e86c40c00001e502d800b0b00c1c02030700101140c034541402103018010301000c00042100b5145e002000940d482c84640c041c40c05030103400d403200c10256042c0300312080104903000b0355000c1c10b82581040300c01300380101903407031880c4029600c1c148000030502600c103001142c03100c05c0d26000f001050104840c001410380c0d200301d80092143c0c03510300511680300c1c0526900c00c6030403403400c08100000d0107 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 330620539 1250 330619289 330619301
    0xb0f09010b0c030918070f081618051f090f050f100302120a0516140304031d030f01020c0105011e14010c120e090a110d02031008250503060705030406 66
    0xc00203d80c03030305181c00c010607200380c20341c00120400c40b01701050040294101d01c05d6840320102e45041e0110b840c107900905038480c80440003030103200780c0319450410110a4510038016000c0902000c0360305a03526807038103001ea0501440800140d12741c00225605019264007030031210010481501009071008201800001c1c2d40c0c140e0a255081100151802c0e02002840c81079510341c1000074640382203040792105003495403d501c2004210140c84180114a03822f8a4005402d407412100100030718400e10054035038807070016072611403000b520040c92415002030148060301d800900c42c80c1d03690b804440620300c504962122080143c04103000c40200b078400320401100514050410f409940c4480203047c0e62290b110002800d0022034028600b4a80704440d08071145200400041140c030301d026803103010307200341c407414a500000859103544c4081030004c0541040c105031a04440100105002240134089032903001d00005c10003d024600840c8442c4a076110340c980500d15582c980e1036400900c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 330621789 1250 330620539 330620557
    0x2411030d0b0d1b08061e0a0e0a15021803010b10080703090b0117061f060f050408010f021c0b090609180d02100b041802150c030a0201060303030b0f09010b 68
    0x44035911880c040b904200f119114034503035204141ca001d04010000741800c1004141c0d0043e203e1001c8406901c10804860300c2c0d206560307170800a0315040d90000749041181544028210090f0402e0452080c2039070b90050070f8641c060121005141560010b240c20780d40e40c004003c2c0d000310407094036080c09000c0c101056002c3e0b254900015a8401c17135a0f10082200b007a0055400d54541520141840104112494002046d00f008008590a500800c0e0780500c15009140400c0306907030b2a801c12038040c40c243d9014080c120028425280c23008181c0e0000e401180d81c11207805105500b100800b50548103c11072240c000e008040035549080034400301e810f000d060101d55560308510365032246000d00c0754039011801907019040a10021101000381c403a80040306202c0d628043c984818060b11850300c42c10340f0707410364034048040c182d1140a40240100c0d0801d908a020016000103055410361007882924400c0c0ca04010042180c001d10000781c1030344664580009186005022380129040034114880c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 330623039 1250 330621789 330621799
    0x1051503180318100513090c050c12070b0708070903060c050f0703090602160f050d0203120a090503160b030714040f0f17030c06011e0504062411030d0b 67
    0xc80044240303807442c1e0180d01c6000f90030301c91544102c0c0601d84450707464066003051900178203020107604060705c014958414451010b99410713007018020f00880541c0d0104122905442d41911800c07440307c0d40794130489003104c94501060000b0216400380c5403050043c0d0483d42c88050160655556000920004134194240b040c1845040000ba40800040c075a0612996036182468075152010749004044428030142c131701c00b61020b024121000c42c8603001c0b22012200740c40001e80600209003458426a10340c84040b5000504030750054126906108842d0f00303500701c50780c1d503620071018660910240110800c0709420408a403020b0b00c54030103103204400c2c1c40443ea1409a0b0b4813038241074641243d01003400c00485d000204007034840000c0c8141c00807841c00c051441e20cc070134801c003504c80005004042c80306001230f0b002c2d502c1d424800300305070161034050710401c0b0060b10b85440681d80d284c416018010f14110b14503c1c0d507045d1240401ca294107801e60300031428454040003881c05001e540304459001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 330624289 1250 330623039 330623071
    0x80a030b10020a05010c030c0e010507290f060409200f0303130905060607050307170702041514010e100e04110a0c0507080f06010e0408070c03110f040501051503 71
    0x5a580c06007024540c8405400800140900b49442c03403d490340c1000c03030414146400c0450004a801000c01c00400e2400d184c41640c0e050709250111412603005c950500d41d0b407a820703986020302400300d000e6028418056074a0800e5494008001c1a2180e441e4000c0c07141c0c0700d030002c00d1444040c4900040c00080c0007003859410746401008281f45401c05403007031943d4041d6840c1040b50110034850140c111106403a01403038041542c42c0c091342c034490010010001000005480b54a4024006031190968010424401804800e06d0100b0540c42c9000d4100c1d8a1260b040403a40c039805201907003800303900503240c0000310308200000c0e145030140303030740303886d0095120303400004802100c1c001041c800e601e0351500100c0b261141003181c0b501165401c0800654030551007100024800510281103441c1c0030182c032042c0d07840e454801414010000002c00c00500000c0200810000302d504c070141c0d210036540114511030442c200003c0d541c0a2185030f0304400207140004007481c0d00c04c000c551142e800c0440c8018 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 330625539 1250 330624289 330624311
    0x3040f050f010b040b120d080c0d06090504030f0c02150a02030c070801091a0c0414210a170703120b03030909010303090618081c030b06160506070503040f080a03 71
    0x51079203a029072034041c0d42d514104880c0745072522610600450948400345504080c422203a620700d0030504003c1800102400110446031050484440d207560b01401c3c841c081d950901d010240a06840807400305002c8240008070314030032500d83c420180c00030252038440e1380c20080d45240d0b03400500900218041046451f924510400c031000c000d003850000094445840e0411802d410a8600300a1100b00c020043c0b0281e0005030054a05940000b41281d6041a001001416629183c0c84e0010791454a040300c82c3c280743d001c5003d100702d81c0030b1411801b46c0240e041c24100c0c503104803174000703011071140071962035141d2050340300c1c64111001404a031700e0b107c00480041c1900409910440001e00582424014070350b100101541e00100000d04c1030100d414407203000d0b215240284002c1391460040840c405051081e0815504124040d1185585650f000740100f0903210141040d01c0c1407056202191070144a0400c483c42290003210700a040d829503a1180a682e0000c0c08200426485a4600603 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 330626789 1250 330625539 330625543
    0x90c0c080a03050a27060b150301030b07090f030b09010b031c081003021c110406030c0e1906121b060f121407030507020c0907120222090b031002070809040203040f05 73
    0x11010b17aa8020080c0d201503e10340903050b41c03503084c5c54034020360130001104a82a1041c041c0c070705480c3c1c0284600c0309556900380c121000e00859100081d40300c10808000180100104600d000d113800000900c1181148028942e46c0c0102c2c1d1504611044071030104a10039224403a4950840e82e840c122210300395407a0001014105510a2080751546442c0c00d54204a0740c080c03a070100f1607041d01c0038800c3c6032868503007869000d428030a900d00d03881c801000510714001c0480d07150a084003c9400c211003031311180b5000e9800c182c04412500440d2200c407106401c19041410011903a45a440702251400c56404655114090320580d200548400102440c0791880c04d80c41d00c540d0311075500061038540310b100241740c012804400750041e00403006104500398840f0303a04001c007611002c0580e0782e1841c001000016000681c5c4000f162803400c201007840c3e5182d42040480380821000c48040102c281001380892080e204000c00d00502000b40010500f0503401440d07002d4003d1113056120103070f0391174440c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 330628039 1250 330626789 330626831
    0x10518071d01030902061b10050f040809041d0106150915050a0c200108130308070f1704080301030605090303010f06120b061201170d12090c0512010501090c0c080a03050a 75
    0x56070031400d803400c1f2840c40da010402038102c02888102800181825803000900383c0c00a4406499404001440e040741d0303c840c1c11545111000c150000d4004040c039a6445c000c06c014000c8040c01070340c05d5002c1598078071a250000640700c043c003c0344c0080304604400c2e651a03000300e4910090040c0242d507840860000c0c1c490341150401c090030b104079001610001081c0c8c4400400e0a08504503040460010a40c000c152580c840d27a0760a200e1030300c906590702a50095100c034880e801202d541402c000402201601440c100c134400c41003031249856054100c1d850380424012044108140101005a640b054842d00c1041910000025400c0d0380040407403015404481c00e00c0780854184010002c1c5a000140150752500c018007030103541c0c20306040100501c18010403661515204d0120304184000d040c0c40500a11005117840c0700078000b6034101e4003a00003441081191840c2c00d400590103806034640c2c40f400c6500040c014a4107241d108250000c00c0041c01800400d9a18800a5104001e1040314 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 330629289 1250 330628039 330628057
    0x1e1107060503060307090615030b061621020601081b13050108012405130506060f1603091401051603020106080607020a021c020d0212010b0315010518071d0103090206 73
    0x1640d580d19104050500d1720399260b0000b0842ca18142d0100080307504580d0038a90b8020320324001c50300d50307070243c0010854040d0304095848590007440d21410031040f01d05c16114050580300d20b4088200145040e0b8581600340318810740380d003100c01611503031020250240010703107004080041e645568280441210000d0b049546169942d8180d02c45241520300340c0842c0b4042c00310f59500043c00c120110f07801100d021403800702c442d01c030300c049400b07076586405460b02000311000041c1c44486075008200f845603141030940103e03940b0a404141c03540420496052002d049c4c54003803038041c0302c07240d01ca800c0c0b1105100b82c00715581c40201168400050103a6406801194010030141980340100820258914181503580b0800d40e440340040e2101012948030540441e20070341c00c0f07105901518054540c0701c24041d030500482c4c01030030b980309031494224182c55040e940b006400c04c1d51300d075180c2034034020342d0200c2c0070510420419100310b04401e84412080c00614001c0b0300a42c15a0100350b10350411461 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 330630539 1250 330629289 330629297
    0x80c0d0302030f1b0c041a0d170304080403020108010f0509010e0717040506011d090d180b0f180904020102120904060e0a0e0613030e0d06021b0c090a0209011e110706 73
    0x103100d800f01030401020101000449080040d1030b500c0c102c0c0d1000d80300c41d00300e0b1402307020442045028005002c0005041052840c0031755581c0c6001d107040035141e48180400c90100f00c0b0750001284c1ca81071005c0106c00c1c0c403006404c000c49a420b05903500750030308005110004100030030850100311a140c109640c09640716400414403541082c0050030301c044140071002c11035403510200040a00e0019140342c445c400c2c0d00301901010314074100740104640d150040c0c0d40c1c5200c000b070f980881c0403420008083c0ca0a07012503480e10804001c00f0010000415100640181d100020540c045d50194005140d0f2900062001842ca581d54100010f12001200c00d907015aa031007101e4059400d050102c25400744112440c8414280640d038090a40009185194002d5884501c401c0c1089003603411103110000e0500030110000d4502c166940e2012031140c49800340d00d8140115510300c0d0f0a000b5100c1c4120161074901e208003641c01e1400b1400f1101c8048c20800650340d40095685c10b0a104000141c001565 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 330631789 1250 330630539 330630577
    0x702030318030d050703320307080411061206091807080f1903140f09041a0109090c0e040221040807060c080606031512030c0d021501080c0d0302030f 66
    0x1010b0809040d0100c03d420700008014070340000358404c41615280307400b04100000a8025100250808400c07024a5082c04001050004082e0025041c40c825441502c0400f41071503408140b1a139400b501d03140c02c903001151004030381a8540110410343c040d18856120b5201385900c864146000d2075644012007940046c980c0381030300c00f400e2114031818440342248003111031003270b540100440c21424a80202e0440403402d460345400c40001c440c118240100107000940c548000f540b1245c008144460114000d1100010500164019860008080c0d207491020745114401d0101035441041d80e0780d81104c104800081141c0d0341000725004900446900362102ca03945001c004841d024070300030080c4090340c0c003084101e954080850781c1c0f040800004446018040011a42032202a0016800c03030001203003484041c4d00004209291440d10f40c211040f24240050f01a182c600c20701442c452500308400002d40c6041003140007403018031a204482c50540d032950019502c1d0230051007500c0241542c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 330633039 1250 330631789 330631837
    0x302090117060a0b030c0702210123070c030203070c0b03180105040f06090f141c0507080d0203130b010b0304020909010b0915010e041a0415060f05090607020303 71
    0x190054050190300700d69090981005400545015418403415449600000c0003910341404042034518850740034115a02180c000311030b402900408001d088080d41c03801904000c1d04405a8000441e4010b60606403915100e06004445039030f0b8402e0264154441001901c000070004400c1c400102820081d10b5224140205400070020784001000400d0781040140800b140a1440030b080d801c1d8010000074403c81203140224000440180140c078800c40804580c54000000c03521144030800c12120789500564a4019101b078011188060420707179080c08503c03a0b21925600031038214200c1c9500180f00f001595403619450f01c01d801030291801d000c0140011400d00195594221018400a00200e00ca8001003203221400800f040c9107420031040d0030303810f82d0060300d165071044005401804481440340a40c0c04440c05840e031980075034900b50b004101c55033013049030803d599041da01c1c149040b6250780112520b401c10040f070340d400041006074000507541003000708400140340418080140c00c403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 330634289 1250 330633039 330633047
    0x110f0c15010602101e020d05071b080706020705010b0907111b010c062703020601030b0106020307020a18021c090c09020f0a03050406020c060403020f060903040f0e06130c03020901 79
    0x1401910890408000040c420b4035008100740714036118013280060003610000c40381140c40100e010020000744001010140c60309542c0000e8807812032504d90401441e440404054541148400580004c505011100002e0280d030001d0034542e000310000f18400303080d007002a05500090301c1600214006014104100f00d040c80795900c0400c02004c2410080c40510028100005004d001028680d841c4c4014000002d80324003524905500c1c80464020181840c02940c4c4000070300080c0c880c4042e08000240c1c0f0391000084a00355540030b0840080945407940b101c03d0348800f00508034030150280300c0c090541c04140984003484210800100745426141060103083c3e4807600304c503400c940100b01d00c1180f400c11504554003030085250002c3c40b6600c90170031800a0084d940c0c2c031845802040140700500d540000d0012207044020141c81141c0c40e07404401d41c2c0d034401c030300c10003441c422110380030000b24184203a16a03101d400a0803810405d40103c5c030400450310030b9250000402c0d0702051201c401d581c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 330635539 1250 330634289 330634303
    0x509010e0109050a020f090d050a050102041d1b07080a11030f4620031c02120f070c0c03030f090b0c0606040b01120f060e0f040215090301110f0c 64
    0x4801021031500700810103101c51445021f41d90350060500f200320404008003000300c406615081802192240d031186c040000b42d030030300e902c24200a0510300203d0441c05201d42410201d4401a4001c0e1a1400075a5a403203503802c030081031010300525004440c101e0300180700501d0300c071201ca00500d60300e850000100c034010361107800c8450030a0114143c90124040c0c1c000944c500310b0580c0d14240da900c6242401c680c582c400e644011900c140070011441d2881c800000741200d001d6882c4441c0240a0b030f55601c1e0124025009051080e549420200d041c868090321165040b844500d410440700300b0320b40303c00c1280c44c41680100c00007200d214002c0685c81d44400074901403d1400d842c03514100c941004280d40300700262610740705658490070b00c10168060382e00e0582080382c1440620030240400e03070f00d0700144403a1240342980b0b60000c00040c185c4840c640da641c4901d0b4000d01c3ca400804201004081641020800300d406d59a01d10840c40d000710124090020341d08424400c0d81ea603007400c5052800c0800d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 330636789 1250 330635539 330635551
    0x406060806030c09270706080c03070519090305030703021c020a2604031707150627020d02040e010812040608010b030a0906060303021605090601020a060b0301060509010e010905 78
    0x140352000c0c40340d1503901040070218024103d400540c035842c0c01c41e0707551606095480788607106641840780c0c05042000300328070040700c8641c0c41d07040d119651440200518401100c010000890401c0550790304900c04681c00303002c600901e0701074050783e01c03a500c181c5190b110310400d8000d0380c80681c000d0200040483c40b18171480161001d4211810595504900d903801c903220001c02540582003042c04519401c2036034021900f180c1d0380306205065500000c01f42d801f1000c2514200390804000b003040704a80075070000c07101d91150101e42e0b21400403c49000944170820140c000c0c2d020010300c0a03046c0e150019001806000700c2140c41d95240c490000d00c5c1401031007644c030700036606000c1007103101e8210507154112443c0490291380c079500c104c1c0650051030481c1c0c00600084c6410008018941e0001d022140401007050001d62a03448500f0410107180c201e40c045d0044e0b100030b10400001e04247c001170004040600041402521034000440c6104243c01c5105500202801003000c5c0c00c6602615801003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 330638039 1250 330636789 330636797
    0xf120a0212010b04051309020f1005041406094b011215032a09060512070f090f0b030a0f021804020f01050a020f0d030605130e03040306090507090218040606 69
    0xb1704d0000400d00c03a56818507200039465a5010210940d120810064401d00c4000c203401807074060b5210152807074205c0d00070105e185e40145140941e50510504030342841c200103060031007411080c4000000803000d000c00b0840801e03034002c075800c4142c044a10807000c00d1003190201c800894070000524410700d2080307103011242001810008401285181c0c070550b03421620001619010500049000300c046010b0051414603280010b5100350b030f03521000944000320742c07003000c462207044070669440e228050381050980010080016030500c1d40001c00c1e25401c0080401c99807041300001c0c1c10b04061401c260764458240765080114a0150f078005c00701c41c80444079040b941801e401140400e50710768038850602c4000100042c1c614020091051404080c81c12920303090031501c00100508a04c3c071489000e10000c0701196014111801040c0c54400718400541c106882c0d41c0f200b002812040c0c500713859a025074003010030a62498001003601d13440095211b000c1100840c1408112103840c0d011100700 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 330639289 1250 330638039 330638047
    0x901150303110d140f0c030c03070506160e09011403010605031501081e15040f0807050a050c03210f07050a120e0a05010818030c0a0f1716080f120a0212010b 69
    0x218903558141e170004081e4410484d12018042e40c0c0741e14601c208139420b88503110101d241c1081010001300b01384a60b9803140b00d08031400c0c40340c01c19541042c2d00030090f41c3c8018103100500c8405000401084902c0c0c0003400414603554810100b802c1c1354800c400403450060382ca006212640c8104030542e0940780b03061803003121034205080700f80c5a94150781c0070030451403408040390600941e4031403615281d0700304815540d2400c040c0380c41c0ba55500e007620112681e01a11045004600c0c01280051045011444c1801e000701e00104d017003499445100c070b1a80e02a000e200d08004500b01700404040144200740542c2186400c0e80040d0400354510407e9106a043d00014030403640c0c0100f9581d0043c001022110580c0700c0010002d041d40a050460800c52003101c0c40d150074403841c101d01003a0f00b4050f465607080074903444101c0c08141b00c0d0400742444421504401d0000601d00c0c0001c2040b03e00501502d8100240107801103078410003035a0407081c89801041d01c05007c004a1510303401400700b40e00d01458 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 330640539 1250 330639289 330639317
    0x6060e010506040b07062309060f09100b1503010609080601080a1203050a1b0201090312140105010c050a05010c080108100501140609060d090308092104030b0901150303110d 76
    0x114403990013607048a5030049804c104002c040d8128141422a502c00b0212550511800b8940e044045030034001601c29280800c00c100050541c2030301680c0180090020341c0b501c5142000944128162103400c618118084980322043c10090f502808044c1d42d40c0f40c10303034034102c5041d1601c10103030000b100e503420015110740010398900240880d111117060104031540c6040a0100a00d000055a03503080c00c0d04143c0403c00d58194000300b1820304c6134031040000102d240b03421080318000490310300440a0080113201940c0940d14801c2c01c02c2c0b0800407690b001300150340e0345003554402c5041c82c0c0410f0b554801031007805402d000c2c42d1004143d00004000720b42c50244130704100051a6074890040800041e000081c0d15071710219441809824014413900e00e403860000c24100d012a40d90405015803800350103481001981039061149040f8200d040ca4250780b520201c3d07400c0605140d84541d42c4200c200700110303100025500550003a101c00301010011a0704031300345041107541d5420004010f0328000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 330641789 1250 330640539 330640549
    0x901090611061b0c010e010b10080103020303070f1b0f140607030e04050a020904180201080903070b01030b0601030b1903050d0e010815030a020a03060b0406120308040b04031404030f06060e0105 85
    0x1a0140c43c54140401000220340c60400510649520084550810581841842054004d1f81e40c070042610500301d407444140c4102e60005003070100944c950010840c107404500d0321201c421502c0c0c014082001d05c124000340c2401c001c0c690f580820318030140c0510402402c410b1014440b031181040c2d480a18001f12668014042561030f04014801d03680c400c04210f13481c40d50350551301951800f42081080301a09140701d0744440520004130f0010301841c00141c19a4070200a03a01c41952002e4142c88a03400d5940784040c84000600c0d10b410113071385041c0700c2266981e071507520203500d43d0088140740060460510360300b850003030007801c000d02c0700100c0c08001030b981c40450107500c04d98018403244245520030000381404407040d806944880c83c2000401400290391100c0c0100da0100d604100e000e907145400c8900b050302020140105d6402000207000c0f5800b4035400e0ba0141c030030b1a05880b100c008011070745507600700d41c1098a1510350b84c0019401c02109108140240003480b201d41159850180050307 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 330643039 1250 330641789 330641791
    0x30f0c0c03030e100f0b1f020304060c031412040203060f09070b1e041e061713020a0f0b0a090515031303090b03040f150614040c0e030a0305090109061106 68
    0x80c105030f0344520780c4500b01404d00010205043e944805e00175544c01c072001c940540301100056210310015003003003000741741580c40700102c6410354014605080c944041919806a41c400c01e90a0004040a0400d69403909004000c0e60410114600701420140141072424500a001100c202d20b51024081640c40025003c4200d41488401f950383e00031000340500e0201c401c220302c1448520200c0c2c0401c03110702c000301c0c81002e00a90030900c0086c968564084a1001003605070f03c0640000c400400c440e601070f01e6100710490300181203c00c400b81d941c038a0007820141036100440007840031803002d14070390b401007100707004000c01c81e8650700340d180401c9031a803148009850300c54206402040c2404041c001c40b0484014080b5119a986a20740350501400400508d40100d07007105c1c10604412030944d5502c2040161000304002c0340030b030300410303007800000d0038498031440a1050610024030282d030708019443c0428807a80d2001d40b40c00b4032600260140540d500144184083c03502c02c0300c3ea00c07074002461 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 330644289 1250 330643039 330643043
    0x30c03050a09110d0809100c0b0a0c1202090321030604110c060c07021f020c0a23130e0102072907020a0803060f1801030b130c0e041109090c01030f0c0c 67
    0x51070416042c85d211500f0b210b0a01c840ba008060f21003040101d6401840d94003100740915160340042d80c2d2544518121001c95184101141d443c3e260f80035400055030191010782005000c036503444641460314110503011180100e012000042000850700f031074012400340c4c100603c3d095081c40d03004103035140ca0325401407480c00c03958408104002503565003400e401c000c030036200c180405038002c944025100e04191500d03600450784400b00148090b81185507940040340c1004c21060700c4c2c9079004110503820744100044405844443c04071a4640a00c01004010322070094011075040f92410310401815091078600055404410414030b41c0c0c000c0351004481e80d008100d1540d983e508000103503002081c844035a0098001c001c0012404604a030703050589009802680d120b0782c0300c0141c96201d22650340014a0301c0c43c1c1c2c80c000c00000000d2070140c2d8006200c3c0c02c0c0c0703905241d04000401c1604e1070803115078143e40e1000740070104550f0948501120085144424001c1003240b2601401100000d200 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 330645539 1250 330644289 330644299
    0x706240303021221010806060f10021b01030609181106070305030408093606040501060e010804060f09200103050c070213090503030a0c0e0303090102070b030a090f03030c03050a0911 80
    0xc0c8081d010b013000001591052a600e0301e6125507141c065059440c071085901c240540302c944640b10f840d1500440d6540c0000c21540108006030403024040b05011001001605040d155803000c074145030103000d00d054801c44c881409280e0031480c1482c21030380c000312450314001c1800f006543c000c00d074400c04032a8050b800204656903070b406007001c2a1081014040d540399154441c013454140e00910886504003518140c11071465112201000300700c500030700c40d0002107001d200b203400d000e50182d814541c1c450700502c0c2c0024602d1a9445003404d98011110480f4010b200b40c5080511220003108008000c03420f1074204000c0c900035030341080f148142407000e17110700311040164508035607940044540652010582740c60781024003208000c1d02281c280100400d004126252141c1800010395140800527401014140c2c03600180c1c1809070300241071540c0702521081031101040c0c44034449500148079640c00600f10300030550003422510090701102c2c4003801c01c0e44003c08502c5400c811110100200c4da = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 330646789 1250 330645539 330645547
    0xa14010c17070f03081005090a0c03060f06020609060901050f01050d020d0501110d0c0305090618120f1209030901020c011805040f0c0801050102151f03020607062403030212 76
    0x10098507250341a084150710303640001e4200100032460341e500946510a485003900c507141c0c2c10002c6c0c0e9a5080d030040f560810070741ea002a48840b0103030048641c99000c0d050001d01c880c1c8a42c1c03500d11448040c0c00100c00b40e0f00080c00d000420000704103107a440a0001c0080103a42480385221000890610845100380c2a0300000002c6d507981d241170110403035010000b00110804803001c4501c50f004600c2091116250490803401c150090080b1841000c0d220080c9c0065075940b440c20310440c0b03040b030041d0018807442a50305030703140508000740034150701d01211940310705044403a1403000344010127150440d00144600d81043c0d80020710010500ced024201000441c40350100401e916034143d200d42d90250820100901c119000e9115080441d916039424000380c0e200e2006a941d803003034486860307180c8040d8000070b0904001c094010b078800503500b503084880b9900d40018034540c01011094070703a00d079582c450004004881c1c44140e09000d100c80914015031850b00c01035160780e0f00b0f005103103c003c400a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 330648039 1250 330646789 330646793
    0xc031932040e09060a060b1e0304080c030406030e0601060309020d02150c070306090b0619030b0415020d050702012703080c0c150703061e15021c1d0a14010c 69
    0x100c107a401619a4040c8a1a1807401040d83c569a00c8192007080065103000e00102d40c0340d641c81d00711101480c88130f10180320708280c5440400190f10051060301c604d8003c6c408031814000c288010030042c45590386c0400c0074055003806504281d0180d1041c8141840e20141400584405943c404150340444d04c11440707452980c51740c0c600f4480c1805030701032405103800c040300300255a4400070440e0701900c9204000e40d2040f05100958003d0b2920301c0c00b40003608002c0002545000300154001e1180078660302002d040c0e0809400c0e60010899107030700c0742d2900200000c03298240b2843c2c200b14880740704804140e2244d080c02003e00341000e40a02003294900009080900c0c03038003240d00e48a810b03400c85411554907a561030405000341d40d00e6000904120700040d80b5020500803040000b2544440741019150503240380c004640040400c056018070154000a60320000380b42603210161341b0345101d10750f00a461409980e2400c44d00500c9048003001c1131220910345058103220b0a428280001102114 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 330649289 1250 330648039 330648137
    0x1c0f0b1804030c0c12170909061c0f03210c14090f0909160602030910030b270703060b1908070c0b070905012a0204020a050d020c0319 59
    0x103403c0681a091034000000d228030b250180c0030308a074000c0404107441072012084d9180381c420b4000d0b1550069503c0046801c40c81c05070040c00c0d9500d8a4442180103075581e41d0784011050314034005402040f200202c5600322114100c9002280c400380004102c5184110b402600c074150307070019801c0900020480718529121004103140025006140788200d14284410503500c074201e075141982c21980b4040050098000000c1d10400d6100800c0b00301c0c10718045008900600c0e92981890303203d080c00c030058400b04c05400d1814184640d040700b0f154949807031080601039580503402900e4105080092010f040861144480ea5900624003000c80c0d44611501315444180710300f000d0203c5110109105c200340c0c00010101c1219020b80340c0070b09845400d170500300f540c20384c44000108102c860b02c1d48001440e1540c0100040049400c0007070900090358900c03000ca8014030810022079000040c1d03212030500410003010303c01220720b041c030403084001c03c195448044c40400754501445200c0c01d00610703000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 330650539 1250 330649289 330649307
    0x1e0c0705131a010c030c031812030c020108010812040e09031905030709170604110301020c030a0203041802031e040204020904020a021c08010602030a081003081c0f0b180403 76
    0x501100215000c601c0c188002c0603580010300c0d400c45a0381c907500183d4001c8903140180340d055294540201c815480c16101084200e884a000b448411404100180c20450211219009903a0003c14101920000d041e401060304400250b82c0003d01540511154108481c06d64215505420103615900c00c15803543c01400d28180526584501c041d050503446006540b1520341c0f582c441c650300e6510403148928060146030340c0746680101c0002070206580c0e0a60340040c803001750005140c000490f038003a0031600542c04020060f0400901004450010401c0c5001d07400080003c500d1350801031803d056010300d68202d03500c0340c0c000701d0004082d966254151051410081c00941d50b0790035070000203458241003581c2d03c3d642810b00b00510308091003200642d0590b420391b0021440c00e0031042080e04c164100404103403c0700380982c00400024518400f41c000c0300d0701900b03110284850416050140d520280e01c1c810041d26000380700d44031b42d4400c03050307101000c94007201c01c106031504d00b421615a40 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 330651789 1250 330650539 330650549
    0x6161b0813081906060506030c0f09011707120e0c0d0b07032403050114090309150409090c15050c0703200d200402070f0b07120c0203090f01051e0c07 66
    0x540d0100b070300403400706400000884d11820b0100075064413182000018081601c0a00301218144140388040f40901d00400d0110030504003204048102a841e19110740121040700c0050340c20490f440600744240180404002e0800280c01a10780b0f04011440c10300c0000005000381c08010f001c0307441540207a001c4030070034804440203000750b0360b05140d00b41411254401222558a401007007400e0103002031a440c02078548001561074040154200440c1ca0a20110000422402c01c000910260648505a2014811044003102c14642070100d001040401210001e1250030080c6c480c64881c0412544d040c1d941c044885490310840d1403e0200c00300032066499041441e6404c240c0500c44280013104410b0400455010380c102c8070800d00c0164000c48000821104400c0b10310310019400d504e409038000b14610300316801c1c003520b85008040d24102c0748420096000000e4100b010b01300718003882407008003800e11520307200f1050024004e0003016803000e01058008110103e0032402400b02c08000c00c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 330653039 1250 330651789 330651793
    0x4140f0c0f01230d091703060a053a0c050a1d070e1027120f031106130c06080c0a030e030f21010801050c03040609080403120206161b081308 62
    0x1d40c041c44c01000901180000b0b0380d500005580b82c060109010084078883c48002c4d05007807800786004103214400644c9968100303c0c5a403c198014296030307203050340d038a52260525004000009092001240540d074000c240583e00301c06040c0410021445542d0b0041c00800c0006460f68640d481200c01035151040342c0d40c408100501030000592001c080306604040e02e15042910280c1000005886401e1094030030044051030380d403000c269041004c6c1c8000e4042d00b05401c0e0821010324041c1048d4089555a614202d01c40c402c409000759610244d0242545080c642c2c070b070b414070450300d10b0f907401400b07106c0c130826484007134074030f15500e05005a03071003515071481d280d80310414200c1e00d801010005041c1c1c10501802d9000003840388050190340d008810701050a440c5441c0d80d140c01e170180c00c0301c0740c05030f450f00c03001c01c80040010b84c0d50b50000b618030175990180c6082c1c10049401c105c480500d440c000100000e0780800300c000d00088041030501c1d81d1281250b5030714035400c0c485d4090507485500800f6a4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 330654289 1250 330653039 330653047
    0xb06070311010b0307080d03272009070c060e1e070501031808030412031107060b010f020705010807051e2206050403031704060b0904140f0c0f0123 65
    0x541020040c0751034007601d0028010868010103059803a07550b4460301c4031030350011641c504410f010342d1020f861295504419810034540c4040141035042107081141d80c503400c8034801c02c0c104010801c2181c50725086844250900b40048020068000b8800140c001990703141d941c40c650740c042094a85419400030002901c800040d141c5d52161414405c07180800d040442603806840440f0406001e55440803000e0304584a5031920300c80c444960b8541014559070f40d50203a001c1c840640a00710072840f4400100340e075480c400004180c1401032441105560202d101800640c1e00303c050190301c03000c1da243c000e450391102980480159803104100d000e8550000b1071488e020340070341c400f00c1386415901500c00305690f601c00441307203172242e0b05c005070024841d1070314000c3c803040003c0c0483d006406120041182040040011810a0151021528052010106e00a03031a050100d00018256607010780010a01580480c06031400106510b04010041100360495010740503921013a8401610083d22 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 330655539 1250 330654289 330654293
    0x3120b180405011a010c0f030e0a0f0308071101051204140c090a0501051014040905061201021201030c21020f030708160501141611010e030d08061903030f050a030b0607 74
    0x70010303600102d132603000d903130401c400c10b50041d003001040c00d41c4003144041c2a202914112000c41c048900b00e5030000b10008005281040010600302a42c007500125076505480e02d0802d071841c5080d060141480414041143c01185100000d50700c11b410005c0021402d00315a0711f039040c0b840240e011507000b840b100074888845c00503405541600d034180d80e403015881d8030740416108120b1000b00e122140342c0801c0140051000e6803c00b41e0415409001c82c40e212040c60011401c0e60000c22005900e12142c4004105001071007090303000030125600040b0190420808120b41c03c0d03400840030b0b008202482c140d010544042182c81c0062208205031050b20b07141130380015000f2043e11807030b4009040300902d01d10070035880007254296000c0c0c01c02c4803d0640c20b699072100c400000301e0f0b142c0c1404540012112247c50030701c09540d98600c0c1e65280005458200108a251225500c0c403a5908035000014800a07401030844488c801d52400e00300d4440c00340309401c41c060840c40541030381001d800321750302c41 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 330656789 1250 330655539 330655541
    0x30501120f0507091505150702090103030e150304030206070305100609030b1b122409010e041a07050d1401082e021c0c03110405010c06060506030702032503120b18040501 75
    0x81902c001f00c4841c1e00b4288031030580350045c0500080650312900c20001000041d010300c11158030010b018040c440040905000c2031019001110f0580c0035810600c00c0000b03290741882034070f030f1140c0f4404440b00b0041c02c01d20300500703030700c268000100b81503040800306a0001e520341148603030801400c0c01030390304c2a445612148074081540c0d030400c442403c4504444c00c441440d4540d50105000c0c0690140340c2c603140d620100004050030690b101d000c441d0300843d1a03100c181e40f9034403848003034407500d55886210464504071400300c0d0034050608030303140041c0a031000118083c8100b0f00300c207a60070021460f4000c1200d41076130000c102c110f068400158600320444c01c01050b80b0401c100f0000700560b0381520001e500b603425220081c40e24030010013007072015600409070501c04500030703140014070b1034951000c600ca80d131058401001680c4023081c20101002a0516185854100030310440c1c4039645c2e41e0050842c503146107260000c95106c140100d925240c0d08140c9115884001203080103042c1030a24034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 330658039 1250 330656789 330656831
    0x260706060801143102040e0f010608070503060f0a0b120d0f08180607030f09061a031204151214070c020307080c0108131704030b011401030501120f050709 68
    0x103150112500082003058080056000c001000c290351048130714542100313003541d021800c200d074055910920f241031403404000102070741d10010000a44a4103118203545003903120790025200340c0c0319404010f00c008000c0c07519904081304650105442d01050001850407141d6940380c5090300c0b03440401f04c0300552005401d0001c42c4140c40318107964413070a1002607240185a24042d880e44044007146810340f0070343c0700740059641c1035000a444083c9a40d4001a21002a00c01c1103880082c1d0021140c2d14080c00750070b9805609404040ca400d1a000d289040c0300200d48200080c0945105401e500c659241c120a20309004400406100c3c500481c001c0c1c011107042030140d02900ca0703108003040f540c8002506880c3c031541611094042d903501184000059240036007100d1003091600c03c100348940140140000c0c1d440380000b541107604000140d058040c0301d1180c00e04041c2408010014240a01c414084603a000384003800718202070300300f1628006c510392041d040b880c80d1100200084040780e441c8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 330659289 1250 330658039 330658061
    0xc060c031b0408060f0a0204080a0807020f0909150702011d030d060501110307170c030301080a050c042003042a09060906061e170a0621260706060801 66
    0x312408001c410421160059000c0d160315a4000e101150440c03a40c0581e16a1102d0342d10409450140c80703018203414410741507c01c6545602c08502c4108600e4400a41400501c060b54408111719044041d6a940c920000d017070f02e03441106e00c0205062034401e410490010240703420000010b800384141ca503030b9500184030b9092092424201140640c0b08440940b401000000114185901601c0b00c0444105244c1030001a000400035005602000c0c00903600034039507000648401407407401c0c620304003181541d105100714540b1001004100720f43c10880744162441ca8059202c0d6100d140c000d8a00c01c0100d00d805a04008040201300e038441e0f0050360003543c201c060148103041c1d80701080300c01c2c1c4074140968000b0583c0810808100400f02c402a002c0c2c0819141c50040a1004840c480e04c0c520142c982c01c1090ba242d031010b01096076900d20400150b5a5080050340c0360740503460382551088900c040504c081a000208041c01e0410001d40700303501d030000c10803c81c2a940700100c5009260b44014 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 330660539 1250 330659289 330659311
    0x201151d0f01080c01050c030705070e010e0a0204080d0809010e15060a0807211703040804050406060503090c190302090c1308030a050a030f090f0b0403201b060c060c03 74
    0x140d2403001e41e60215048030008001041e64400e102c00540300c81e08025660501031000344805804207108020540c000c0039000c800e0001035040440c00c001e102001095070582500401c81002002c8000840d00300c0c030007640c41e0030132464a6180505000d44100414516a8401d0b040240119841081a14081c103012541a01013aaa0310001c9440c2e43c0c1d40d21401c0e0300c03150001b41203d4082c3c0007107204481140b05a0102c0004440c13083c3c060b00a4206840a95050001003000c0c48a410701e842030001600c1e05060590640c9002c1506d103940d500501501030007400703200c01c0781c441203529164510196038000d169144a150940d501c606641005102401c0074544140000b5284000310444d031000740c10f81d84117454896a54810381c003510049002e0820b40d5640d90700c010103c1e0291281c049220320a102c503104605003414001e01545110950000c03a00310300e590b00c3c0b420300c00001c1c000c100d20385c184000c84440088800040c5140140c10401d2054010401003100340701c00140154402d401401e1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 330661789 1250 330660539 330660541
    0x90405040c082503020d0204090804080106030201030f050103081b01020c03040914060d030906080915010611010507021f05040606030b160f020312070318150c0e041401060804030201151d 82
    0x501c01d21682d0340c3c500c80510006540500c09402e01145460f5603d0020700b0104504500b65500c2c05150701030b51041800e6551120244210742c1d00d17004101c24101006030520055040d601c03000d60300d2081c1a40d06107800c1d1880c03041d40800301c080d0141c6081d0b5200400340c84c0c1311640c80c401c000c050284055034592820580703000842c5450080c5001d81e10315099a10030070858207081040c1e030b9010707010f44001c00a1041c00c10340d801648000194601812450b03680103981c212800426080d00e0024000e681590042200c10310f20913244107038564802050607010405844604162005044640005e0140103c01081007004103c1b0300c7d1000000e012542e4401d801d0030140300c00c0381c032401240c06c290818100300c00418901c61184d005103400c2c200c48811003240e40f010741d860308040e818040f0f1000106440701c0c03c0d200410f03007002c6645130101094809001006019034180030044e0140070f1030050000c628041030034903200758030252000180c120604562500d4041c181403566081160040b0109154 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 330663039 1250 330661789 330661813
    0x1c0617011e02040b04030213061a04030302060a0e03090112060806040305030f07110a02060703021e0709060503011e110f03010e040b0a022a121c111303030c0206090405040c08 77
    0xc400c40d02203a0b113195800d410941190708000c840d20445401a103c40c1d264400450f00c000c0c0040800d044d0700701c100d81140e48501d18034000e418a50300500311103082d498041c03051000400071045034140b2009280c004900030000000c2070040415402010b41c0d0b12508040200705508000154014515048a04440d070f036110000c0766070032800e100e0f000d05600052099801403c0000242034164480e005442c102c8c0f804400641080e890121004503590120a040000310598481c48020b4141a4024085002a0100d03084a54480401d0700072030b82c0d442e0343d0214940c12420913600000440b181195495a40340808903030900706803401e0b12040049808a00b802c11203208a03019648110580e0001c070319000720f151680801ca5481050700d0040ca9001c0c1712903ca032070010180b000e0088402852103c1102421045a03203411000c007a01e02d003000311442041d9809201001c42e581458400380414652011840030302401051640241c1041c080c0300800144039485019524110f04960b00e500c044 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 330664289 1250 330663039 330663041
    0x603020f0a0b09130207050d080a0c031a09100b040303020d12050127060504020f0c0708030c03121306020703020105040215130614090909060403080c03010b1c0617011e 74
    0x82c0704850700799108101040320740c10460142c0e007007a8008000182091000d442e00c1c1e046c0b8007400c40150026214500700040c140306441641c90b4102d0524007001042c80d20000c103100b10b540c1c1c0c85011b00c00e00700c00c00021424a031a040310400b904030030031026240e075603914000c1d5459401700c0f44040459051102030780b05400c18424141250340b41d030314070701d003000c1c5602c100d0000c2080221029081512071001195a0b04d440c0000d004c9810000c0c14540d80b00d005c090392604200590b045600140c20070890380c08141d0001083d0741000c0401c640700c002a48a40a511500c600c00481c02443c81c1e0001c59444c05254042d4403480c0300360300a85415202c003802d101d59140a00c01c084041401450000040c4107417841113039080c1e10b1799400b011562600ba9480001000d8a204a64544075648114104020150301605590300b0a154100a45c155414a004c0c64241d0080d0f05102e0034504124000c0c44108042d9000720f8000c0403203079140c0080201811103180130b0180d001e40c2c40071118080340944c5070003a207 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 330665539 1250 330664289 330664309
    0x315040501050f07120b041419110403030e0108070c17031e06011409030c04020d091e0b010905040813230102070b0a0309081b07030b0601110a030f170a0603020f 71
    0x40c42d0b90705c100401c60324901200500842c4825a04150b0b40e188100320200000c2c2958082c049800407241060401811041a1518428020003183c000c0c0820400642c00c420075600134030302400d00313006a98891700201c9608040c6c074030240800420400c80300030f02080400031350041816080070b41c24000e00056620405c4010740c0d8490000c0c41200184490301c0c2c2900181c0040700008040e140c1c0015240001400d98000303020440c03c040c4c3d1924031a0030042001000c0300e07007020406400c802c80504e80c6036081001da05201d1f100110740c894000900b00520070341120019203210050b0041e882c0c8a1040340300381c22119003800b480c041401011000c030341c00000d61108440701200542e25000403034108501a02502504892450003448482483c060f0301e0903011003c40105c0050075064518108050807850240001c1d05002885100a500384800301d00d40e0406901420b109400c03155400048404902c17080cac0b44000c10300c10b0018000c07091219008901124021501c004070141404200088602 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 330666789 1250 330665539 330665551
    0x3160c02010f11010e060915060904080327160f0503030909150111030f09040501050418060506060c010207030309023a1109090109030809061e0a09020315040501050f 73
    0x940b903201c4a50080c440c0d580700301c3e200780c160b0000c80e040f1040310380545090000d0b104011141c110301300d00c15060080701c40b219845003040314820721a0410b0b8032450503d01c0064502080c491038064410071082c6c240c1c488030481881035040350110618921112002e05040c0a58040c0b20090f03640040c0710b20b0000107071107440c40002d01c41ea0b03498650035515200c1c0c650103028281030004c440c0c1c2e0404007103414005003201c0003455402c55600c0483ea07040200b04c8005800943c412482c200f842d940c4900740070341c4480e500350300c941c3c00650b0352181383c0040c40a001d0b6100d10055503000141020400d40e03d6041128018800da030075414414817500d2008144118031800c0006583e41d40405071138058641c0904107035030080d41c4807800300c0c06020100b88410001c131120303d09a0346491140c410554032a041035404076041c000b40056003081d000302503101100032502202910100e0104403424826032100c0484c65004040343c085035455190303004c07c408100e40c1030381e582d4070304000210300c040c816682030b00c550 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 330668039 1250 330666789 330666797
    0x2d020714070621110a080403080601030513031101060f0f051e060910050c101d0d020303060f0a05090a0912020703050c090403050c010c0816050c03030109180503070803160c0201 78
    0x90b420000e100505080c2c000c0c003ca60791241c424004c0000480c00402010b8040d5075a64081c0c44d0038240603041c4040a842c05040514003002c00c85620b04510104d64420380c180b0340341c00e50b6100d00d0364450160032150090800f400c00c400001070444041080c201c11200305590301c0792528400442000c2100100301d10756080742e802c000c0b1403c10300d00900b21000d844441d0401c28207000c4010422894003100c590750240540c0e40b21304c2c1280c0342ca945a000325a0342010b02c002c240941c040300703009450340000b40109000302000d4071007000135034900c80368101408025000c121b0518003003c440002c0c00e07145006031a4140b4507691a050584049007140c20b030307070700306000f4034984405d18240408048014400ea0800c0401e0006203520182801a010700542964480c1c00c1410150151201c1c0d220307507500c107000e02104004124143c0008015a411291000e4000545000c0320416a0800802550040c000c1c0400a09042080403034009503008a00a4502000c6501c162006072041410307004040d01003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 330669289 1250 330668039 330668057
    0x9031605030d0e180c12150a0b0306130c02070803131a03090705310c0210090308060d170c01141b0306100e0d0c030212120d2d0207140706 61
    0x400c034520315072030300041324050086c0360000c41145a81ca014040e10b000781e0f41c08408010081c0c0b032900648060140a248040c070340745050030360014030950842d20910780007548504100c08400d00074842500181520803d981d600c02500450005655146c06a071152000c0240314000c4010040280c901c03a00f800c00041002d01d0402003040000042601d450401c0c00c9040341c410907040110045924940580c0b00c0072425030210f400c00b03410f103101e1700b42d01c050701d0385404000e2001c40d41c400642c075084002a45d01d00c84e00009414141e415041100c402c0c0390b05100011805240441548904038901504900d0a02511403100c010030741c03124001c801e00011010306c00b1600a282480c0b05540c686100e0401540030101100441c2c40e8010101044d94244a298010400c0d820890b4800c070b040350001d40546260342d0541040101400354000c1e201003a950742e031031001c01d50795586000c080c03a00400c1d0044240c13505119944041d60120600321a140039040701e18004e410006003540c1520041e0f100c0181c6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 330670539 1250 330669289 330669319
    0x90e030a02190816200418030804023f0309011413180917090a031401060b12090f010e0d0e040f05040303020c0d020f0303071409031605030d0e 63
    0x30700401402910140c01c20400e4121480ca07281509580901c5001d4070110980108805c289080e000c0704024090f506054410307100c91411885481220b905041810151f00c0d640080b9a5400106018034030300e1000c09207410024004540381c84625160f1180a003d8400d00a0400d80700d018440505000c50360701c0c030b24001c903c0070120107440001c12044000c01c8169071603007000d440610b0501c84106e03280d0b9821092003840f07517201241e0b40611540082620b050901000300d00004443d00c4003030409854052281d140910a401c80002401038104042e20781103048003000b443d075130a44200e043d611408000428041c410300640b20381c00100005050b201c5175602050740d14075840303c2d8a5034031587d924064030305900b42c1d2160314001d80c02558010307100c8029100c0e440c942f030403056014040d9401104100031050b0000116a840403003031410702498250400251403a0140d000f40b607906003e40c01c05101d1814804440c40e00300c4400320103c800c1c1001c880c1c01a1580d0b000c1454407a00160103400d4200d07 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 330671789 1250 330670539 330670573
    0x8030106080c07020d11130209060711031c080114040e0d050307050c070f0905010b071e0f02040e0c041a0307030206130312030e0c04020a1d01030e03040e01090e030a02 74
    0x2c0c1c045681c00700c0c10f10707062042d8000b410340581500d0441c0c0a55640400040c9030401644078030302032503442c0d011440c01c144080041e040340a0fa1400030f0400042781c1d640b400c2a00c003482100030703450046800707480344580b0040c00761500300e00340100440600395980750079440c40d080c0602000b0348900006020300ca4904041164a40d00080c400c0c01071210030002d503c07100c0020000c4c42c0080c0180005203019a040c44005025100180c2c881600304034140100004030780208004403540106020441c1c1c00856443c04500c120381d00000030303600c0740c84c080743e01740b03c0078011607910012002110200094510591401c403500038a2030010342551040c18107000600304000100030b030482c0901820003040d40c940e900f42c1d09400805608000945405030440b40860802c42c076652034408131410350070000e1010b070042030b800c0f04e10256004104864005002c5074001d502c130700002c0d210314080c0da64031900c81d60303034002010007032250005040c034003038584070981004005da4214400c00e130701502540092008041b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 330673039 1250 330671789 330671791
    0x1a12030d11190c380a1b03021303061d010c050a020c12160605070c12030f0318140102070309050d020904030f090803041706060d1e0f061a120a0803010608 68
    0x48001c500d56090460281c403100100600c02d04800f20b21071a0104d0259001a001024100139441400d2407910b10602044004c212600d80662800507140e0700400f660103860001d660015020614100400301e040084290103101d2440b000006e0001c1030800c601181e0901c1150701d5038005030040c1c0401030043c038101c91080c6010207400c2c116111a0100d459a500756041c0f5032002c0c000c5200001c0c0c403001c04c95100d5170440205414082c045800025480141491b001e440d026420035aa030402e48000e00e405580e0308034111303000300c40e015480c0501d2305098000e50007140e05401007a812100021186007180342c040c0348a0b030284c9404201e840e140e03400d442000d0010740800511a007208041100c82d81080540014640c00060301f030043c030340031b0b406800c03c8405860b0314000e540001d1010701250300c4004000c3c0184c807950410343c5070b170304900300303441080c880000080070b5500b00a45401101e90020f842041a6030071552180c00a1401d0b08840e42c0c0c07801d10350001d203600000c0c001002030a020741d00007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 330674289 1250 330673039 330673043
    0xc090e0a020f19080105010215070801091d0a03051804060b1615050906010314150408090d02130204091d06040b0a0905160e070509060d1a12030d11190c 67
    0x34509060000305039803503c1484800d95030000e455200100013940e410402d0064a004a03540740382581445100145000014090a48041d40700c6c1c11480d041500c0039615000e01c182881650341c03288882c6001406a032150041c20385c4000303110031542c0710b4540707881070b00101c0792511860381c80c4c100fa0b405400000075800b002581c0514a40320980d0100850780941c85c071424035640541501d40c11854403814422405645108503030201c0b4040792000c0b01140540c0e0043d030040303800c40d02e502090340024421410074400035000324842c03c540340e20445680182094908000c1c0607c402000c09142004070b25520880341050741c41200820003003580d0400030354010401d1074001c0340c5044c90352103135403034106640303500d04414541c0103042001540030010705400c111289411403403c4054400103a207070207080c2e145890156500b01140c01075850f0050300b50607010242c070848440014903001a00c1c0d42010040c410300301e042102000c2c0d0b00f0302d420106e80c41917180b190289495100c040e4204c0d81c40040f5207003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 330675539 1250 330674289 330674317
    0x4090c0908060108010b010807030c08060f04020d020a030614011b06050a110c0616080601020705210d050d050a0b010507060f06081608071e03200a09050601030c090e0a02 75
    0x1041c0c0400c14003549000e04045000491800d9252000610696000b420603007014a809000e030030307035035125141c0e0f40c2081c0102d4031440040d101c0b20002e002449070042c090485440010807905454040d0005021104403607020385000340728078015100c181400082c2042d02002c0c10252002441a070700c240c0d00030b80c108000044d003601c0d0201040065021040c6071030a40d210404100941500e40d1a154109004d4035244501f420800d0001c1c2d076a043c10300481c1d201d0601d81d0383d44484000c0761004070300041c06040880c0e44a80c040d1802610b02c0d4444850b0001050030180096144001d50060114288060351245e2a1501c0c80e22048000c0111a550541941d129900003c0c011000c100242d9510758551107504d001e440d10062500e44803813503000042010042c5030100555285d40ca100b41103a401042c9280c00709820800030921018001d50a41d000007100c102140a04a550100d03100e860b017a00c081001c1d00300088260ba42c0e041501c0341c80214008900047c4043c60280c000d040c43c0034200308 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 330676789 1250 330675539 330675557
    0x506071d090705040e0912040612090c030c03021201020909040f0501090b040804180b060703030b19060c231b06070c08031e030708010501080601050403060e0c0f100504090c 76
    0x800034081c0841a901d00000a4010030144458040c0707070720207900500381400130300440310f40c450080d086004611503e0300744550b04004040d003002d03a410406010307501001042005881e454413000d40c00c5203003c10381c06561821803040b94060305108444c10709100400106d0b0b00d070703515640c00001d921525030484a03952201d40d80000110700d03c120740c1c003407486100401c2e00c4604100451501d1640014024801824004c0025841e140d001c210707040301e50940340102d061403281c8085540000c540d21b88100c260418400029003561081000d50b900d4810810360031042c584d44010010f0400e10381600220750042c1d00d40240607901800b1080d1281c0000e0724003400c00300c840d1680310301407410b6402148103810001e11050103a100da0100e60f041c1c80000d0718607085041085000300b40640c140215810b01900c01e0224030341c8ea0066041e0b1f00119848401404074045094645840c5d800303414000f4025490640d1402c4c040c60900141034205506513074150034580b4113480040130304942103001d81803112140e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 330678039 1250 330676789 330676847
    0xf07050a0912170a08090c0d0b190b1f020d0305060105030720030c07050a0e0705030a05190f1a010905061c091a041704050604090c0e060a0c021903050607 68
    0x40103004d0041180c1c55282035840c1c00490241003206040803203100303003801d00341d500008800440c4581c01549a050000382c0180358161100100f40081150754080a1080012000e0601165941e2000401e07401e454000e040c22806a056030743c10f580150200384248001221688600c0e01c5400322680c04010840d0201c01e06080ca0860b444050b42c203441c6d0308401014422400d042e00100001c28007020300070400e103400d0030018030500000d03012025282d100e801151a042c40107803148031383c0190720800c00c51164600c514100520344044c0e8200860303a4428098800c1d8001c2c03030136200300e072406482189042c480601e4082c00d801c0800340144402d42d507050390030214540c0a0007284d5500155180f42150510b4240400780065101a00061160410080c417403501d030601075408880040b0400300f01c4c4002208103454003443c805006400c40c0012030719000c283e500074020001113000f501c0b6103901d11925058100300c403050f4000030740580e00407804280301c1d520480c0a004540d41c074448105800c2144 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 330679289 1250 330678039 330678083
    0x1060e0316080a140d020d0c140111040302030d030b03100b03190302060906010909020a14030307061401150c0b041e06090c090605061207140903150f07050a0912 71
    0x1d500034900b1035100e100b94000b0409441071000307200b030f2004014000b40e210380000039507401c5443c030160104040c82010300200240e2058400d00e01d90700000900030030911006800b03a58100d031000382d11a01c1040c04400703945010f4450b46030094000f0303000c0d000f180c0c1101c8280300944106c14601d6054070404c02000c0743c0005004110b014a44039501518207810302070540d034038080c03040c0c10400d121481c142d144001039483340c4484080b40c0c01d00070f0081c4650b000c140081d00b1070080f800094001030501810101250701000c40c0b6058508128010305544e92141c012200311200c0c01c802481c0b8003224002c80c003c189004661442c1900180142124000581e0340c8425510481c90468003185485028054002503000384005040103948550805031020041030b1940006455601030084011802d100a1210710848a0042010302110460008080042c0800e2001c8a01007002c505101c04517003100d00c900229961142c0c5039039002205420040d0a90b483c81451741c0403201452036019680100c040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 330680539 1250 330679289 330679333
    0x10203040602030610020610050d031106070314070302040e04151b0207140d15050a0b04060b04141203040e0a0b09010905040c0b0a020d03270c031103011401060e03 72
    0x30440025849082404c00d04c002d80311192840da00f503401400802654101d494489811150b04860042400059040a503418444e5489040b564010380d010408042c0d0075801080100074440c0b42c00780281d4407450100c04900441c0207003100182000c0102d0007050144002c0d5a2900301c4a800054012a4100021030656501803920268100d9841041050784e00070a205013000c0c241c403012004843c40d59584101c46102007103014455940c1d0210310642080c0c0d00a1101e10f5016204100180e1254000c01054000e03100715904284055a20001800d005c1003004071100c0290003182403a0824090407240c52008001c0c281c0540e88241188295a80b445058020b200b043c10000312404c040c14645550501c542107550001420000c078810391b580000d00110380011071078001845100c3d114140361503160000386005501070481c420302488080407024007120300c507041c04c1c0250241c0100341801d8030201e85c482d20000e00b21900420075a4040c5003501c890247c0101502e1801071a00398002001c40c0e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 330681789 1250 330680539 330680543
    0x90d030809070605070206090108070306030b01120c1e030b130b130302010f0e0601090c1107170601060306030201140f070b0c030621070614130605070309060e030a0212030c01020304 80
    0x1062005100400c58144030305000381480b844c1c21131030300055401080780b034450b1644180c1040301403800250080d1103940194042e683c0f0a10b1a131444d41d59201c196500c0042d6501640d14002c044000501c00c01c154680401e055a01c0300c90300740c800e2440d25040310b220002030030f040050740c1100c2c14000154a001e04540310380c00d0031040d4440d6a0b0f00e4100282100c000d8041002154949000a0541d840003e24a811580b40b038502003802100036074125981c450340d04c540d80e403038030490340c0c0414054a0f4040e08800c51104000712a00e0360303680c0700d0840c02d698080c40080d010500c0f0101071451854a04028904042c83c0714020745090810341e51000081c070211400c01d05624084140f00180c41c2040d50500d41220041c80700c81070741c5007d80c4460326134005118240c2030119240595000a50030810765040c4802d00c66082ca00c555690380c0505140d100707480490024610280125401d4090700038000c0d112400740052554006e00d90a00803184041450011244000e00180018400c24001148a64 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 330683039 1250 330681789 330681797
    0x6020102070606080d270306020c010605240708092803020907090806181f0b01020607030c020d0806011e0504030b09010903080417040f06210203060609040e03090d03 73
    0x325061090490fa8075410006071608902441010f883d400100c20903000c1045400c1079110001c1c810310380c3c09054550000346042c0c000309080003641c406620010807100c0c2915400e58030b1446400011148074040306a071115034041c004003010411490190482c400054040368040c0d482c91aa1110001d0400c20090b60303c0b242c590520441c206540f000380c000c501403e14019850500701c0e0b441e00d8410062500c10159481e0740c041001c02c1d0100b144500b074070850600320903240110711100f03001d0090881c24074003612490021540c468428841c602d8031507840d6002d03081c040882d61007107419000240c030907810420300001010629409481109a030381e0103854950b1745510b5440c041d110a80c2c003d0a130103099141a8002001c01e41016640e54040d40c080c208454400036511405507500503a0842c442540c1c003040c0208c2d145400400f034000c03540180207240c6400c00300c0e08100040c0e210440d8030603044801804802c0040c2811b0300710415142c0c8010644c2c0c1041410004144c0c0080500c00640c001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 330684289 1250 330683039 330683047
    0x1180c0207031703070e0102070f050904020303070212030403050c01020606060304030e01020a080427180b0703061509140405270307082d0307020c0d1b03120f020703050601170f060106020102 84
    0x11500151b96190940782030001c0d02c525860013060441c10301151003480e0054203d5800913046540a20031036043d503a00a120482002c50484096940d03049030000f2203061003990390300641d641c000911980304030740c0286500e14541c0d95a808407400e501c010312042c103500c00d40011800040501c0054400340505800e51212403107980307441c14040f01e0044c1e00355800c0d4948140c8050240300d0b0305c080c1040302e4002c120314400d42c50b4650304600401103940a4040c0750340c0b4026016400c0d0b0300c8042e2100b00c82e030b0107032101109607a08007000120b600c00d482c10b1180e40001d0810351070300451008500f5951480c4803d0320304105403a01d03409003a500651109141106503d402c10303400d06601e01c880d07401c0c50352540d811f0030361401d0340000c1d5071100c1c20f002c142d204140e0b002c0d010003088071700101c05102244485204020310354900e003146225000c0e071120004511040f080d40d1103580b001401c502101d4021303009000907481d1054440c1001d0000c0001c000b00e0050481e8041e4407102004500d0080806900042c0c4c0c2d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 330685539 1250 330684289 330684301
    0x2060d050a020903120708030a0507020703150606080703020c0607201005060316060e060d0609090f02010e0d080301090518190302060c1204020f0102010e1005010e070801180c0207031703 82
    0x740315416a40d590142c2e000d00c03585000c00c1c0d01c7e130107880d44001082d400141644503544164134060341036000400c0c062645600400c0c1c00c046404c040211084d613100d001c0c6a4440b140c3c240c0a030301407d40d020126070702c01d1f0000b92090b840b032071020801d20303680d03078a441034060a020b4060902e6865070343c0240b099112024070440d403c08200000100310f01203640900c19051400c0206060022500d15124842c04501001c11202c5c8c1e41c4140700400014600700010500c505d41180c0c2180140001e902040c0000d032108580c0c00d01ca406181c01c0e41e4405441882e50f0b00b42030401004010203090754441514180d080f00383e800082083c400202c0800d0b0342d035003080c5c085141c000e1401100403c59020800144150000100f074001e565810a60440d00000030410f8940102d00425002a5520161103403030a0044240c1c0340d03500072410380710008070348043d076900c241003a5808002885103501d0280074840351037000c040c9034000002140e1620685280030354a480310f652405248180c035030012380020038088 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 330686789 1250 330685539 330685543
    0xc200606030d050913090302161403010f060f05060d11120a050a02160b13051e011505060403080f0f030103080a020c030106030b0106031d031303020109060c020a1202060d050a020903 80
    0x100c01c1c0708901e0224900641c00c80411140880380006117681340c4c81d22003e404060090095528600080240c101c0241c1d0ba906c00100ba0740c0110000c901139443c0c00851003203811079014450030340f90f90042038002685000d06121107a401034410044055903070a480c050400043e0042078941c3c00d61000c02041e06262400c04100c90000d0807072a08035204000c0e01a02d948001100072010340c0001881001d0741d1760303484072030f00309051071001403850154012100741c004460014440e40003c06008000104040c0b5000350110b006000e8035030300c50000e120800009001800404219240c42c008608118112030f46035a01e03042a0402c48007000c0201d03051045c02d43c1004070614645040b0024411540365454685ca040c03010f00400003010380b112000380046032900745a40142d0b404034112641c7d8003410301c6080c0c6942c51400304074001145401e0010354644240c0070404081d170010680e5000d640b81000c01021161070090498000ca014001e81261079454071070036119001107a0050390741d00b29182014 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 330688039 1250 330686789 330686803
    0x7080f0c0a0909050d030902181f0801111e04030501020a030f0b030a020a0506090d0f11040c02030f0f0d0902190e0c1206100c151a01110a060c20060603 67
    0x41d01c00c0c0d02d00043c0d840800d41c00606100810018100003808590500108551480d071526a407e80c01c1d0344030500809640d20381520991140744083c0352055500c0300682800e8503c0b1608074401c0306400d01c803c502c14000e03080d140400d10522a422440e140c1c0c3c03685c83c43c4c00d98201c20691004030350390380406080440c0d6805441600e40b0220b000d0034503440c3c0c0c0c0d40001e1001a6078060030780035003004144600725840e01d0101350341c940d0b00005903000c0d03481ca51500d50148158041221302071070411202c0c940c0c0900010a1b90629201801030741e007800050300010000d600024182c61075141c81b40c034401d000d41c445402ca031603454100418001c280382840e60100c080c1201034150b8070400c1c070400a4241440c00012425041141203484413858410044101c610b6a0070400190402c0503441e44007401100b254010300e080804c15944d960405110001911003620a005851441d04102900b1001658542c04084440d9407030402c0c0c4c180d4940c0d0750750380704014120700600000307500041c144029868204851 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 330689289 1250 330688039 330688049
    0x9040e070e1519081b120f0102071101030603030c0f0c03150209011404080304140409050616030f060e0a050711060c21220816030c11090906070f0207080f0c0a 70
    0x1040390904d030802c400e5540c02840c1c140c071800500140070801d0b0b0782e180101d120b00c21000c5000c8a0215080c40e81d40c5000758001c0d0ba084808103610180081d1550081c06601c0469826442e4080b428049868203034044050302d60442d044c5845d41e00100014000400452040442190041e11515141c001500500c0b12070a100c10340c400502080003032810000889054071440b0f100d105580010601080141c582e102d0024100e000b030804009803c140c0c05200c038002d00c403558040c48422100724800044400e5801440c0d008040e4400143c08030009800541c0c10208a240c0810300705518080700d8180386041e590410b4038400021005c1c00d1b03c40c107105c3c01c03c021036200d65040050034604c041c000504000b458200300710340000710b00401c0c070000c0c00a441c00c410138080451401c4000c1e02c0c000385151030b90030080310b200b0500c0928200301c2c204003560b2407280c00d191004044944071010282c5039240400700b540300f18401c0140110300c8113400e2140000c2c6940d00402062141c02d08002c0200307103002a001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 330690539 1250 330689289 330689329
    0x302120105010308090d140111031e01030f0b04030c0507270605130e0a05190b01080102030403120e0c0a080109030206070c11010c0618050601060f020a050309040e070e15 75
    0x50020030108005c131414660101d4000407100e610b440c050f405c800c460401282076500e00130700c60b0508030914004520645501c107103081c4000c020803100c803206101303000280c107000a245d84a000039500c0304401c3c1e0031900030704005141d51003950380d02d0300d040090b4000f801040007011000c41c1310484510405229a03d8034003d0181c01d0a00000c1005540640103520040e502c80012030901007043c4030b012043e98002c2d064502c0c82100c12a0b008070204190011500e286d042e1000240042c3d046c0300796801a0707816a19104483d29040050010741020002048103000384207a50005644201c00340000300900d000101c4d07070491030300300a410104000c24400500c21055190000a200c0c124040344c103080c2424444440714075800d1030401000040f81219064800c200e111040c00f60006489048074445c1d03468207034030714000b034040740c486008020041459006000c82030b40381c50319411040d201814034003290740513952422181622071302038550001d20340150380ea003805818001016a00301040d012 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 330691789 1250 330690539 330690541
    0x270604060305060435031b030402061c020d0609051603090309120303061511010b1c02040b03031207110106050901060f03020307030902030f07090501140d02060c250302120105 77
    0x1c0702c54942200610042040c503096083c0d80007402c45d40341a0320589990000c50742da03a20030440704102a0300903113691000c8243c81e1050050703c9001c0e000c8074071480e4054030203400c00d1501414189040342e400c40c2c0c090303095024084491403c02da40310f9440188015100400e10381808071304123010300104030503a820142040c0d80c20011039080b591810032510303011000303078243e815424110000c0466070441c04100803601c40200b02c0a60014411340842e5420008001c1c1442031820419058006801c01c01d0020004064001501d8103a1100e0b860701c0c0040c0c1580d00d000110006040045001c807446000f081942851014070300c024400d102c0582002d407040c540550600700041c1c054a440000354007090340010000d56000e110b9002003a040364090304031560503100400c00e6031138100078064410703298981f50000802c01e80000608120b000081c00b09801502c0c135409100c2076a00c070302904010b80c4911054003058901c042923140741444006503a2000c20300b148100720310a10080300303000190781008 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 330693039 1250 330691789 330691793
    0x10121505010509090c070b0f0106080f0f010902070f020402030c2206050706090f050a120f08150d1a0109020a08090a0c05040b0d05100c090602120d0f0b2706040603 72
    0x180884203032400445243e803542c5d41c0c800000640d88900742000b001004c41405001000305a044428180d9480b82c858064544d25142d41420100701202d010200c081700e9801000100c550754000d01485004001d080000b609580200d03060ba401038520500401d00026a81d030980319007944441540100b03089000c00c070f407030410001d049018403680504244c1d51103c80b141001000f200080c070860b0f0200039a081e2101c2410643d80c088011284000801d408040c07003804ca41c4a99030b103038402d00c0c00c1031003400c1e940b0048062100c040750b440c2c000c45070300d61400c09a24880050354043c40c02070103091409640c1728050040200380140150190865502600e851000595884605419540150380c005903e12020000070005851300201910502804080c014030549a40011008507080e4a58030714642d941d001c100c1e55000c1703200320403810410a01c03410440c00859000303110444031905c40810380d416070300001400144d080304c40803000708280b00b422241800081030154024012501042054a96 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 330694289 1250 330693039 330693047
    0x20708041e080a0c140a0305010c1701050109061205151f0e0d020d060f0209100c05011424011e05070308010b031303080c1204142a010e03010b1012150501 68
    0x4d8007580c8070f0300308011501045a01c4840d03101006540083c028044e4500601c4054082c40507909403105d4010940700105195005480100407903141d035803106240f60186110740c00801c4017030b10340000c0011113070050350715a942c030124014a00081c140031001041c45a03001d0140300c1480d880328080c0031020003000140e41d41c45002d02c2da05030081c40208070b614800300400c0c024441c0c50680c95100d1015808022801d03402586a0241d510480013080340c0409031864112a000c120345000d02c80d0072601d05030315405902c40c03041c02030203030605160000c2c41d043c5140180390100c003c3d00a0000c2d502060840501d0b5000b41080d0050031210109072540c00d144040404094035043c0103024402194040b804040045045480d215041120440c060509260200b101c010400c0150b480d4812110000520f244005d511541c0e01e82804034803402c0c044403c015584000d004c2c0c1c5443d8155a5030058402030313125103607c1d4000b403000b5941e503d40d16111b241000100d075403140f20b14990140c290014485030740c02c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 330695539 1250 330694289 330694313
    0x16150212040506181c0b10050d14070803030c250c06050a0203120c1b0c060d0b0f091f06030b03100b0a08070b0702100203031e0a020708041e080a 64
    0x100343c07600c613554880d41000268903200041a20f4100e0070340a0382c040c001c2903d00e0310350320300351140d104500c40d03444400a41c500445540035584d807007018a40090001034981081900c011400d070143ca000541d1400c01c682941c004481650700e0081c0010103c0d00c801642009a00e4402200b0308440003c40b1900c4021488405004131418880d0000b0b49140761802002601c1c03c1c1e8070140d00260303081c80d12162005c69500724641c0708190f0000112868a446030106d9565822000074003454140110141a00040c1504007661504407a49140c10425900c44100035841215030441070320700d01207004240010b0381c1c0954018020140703004480d10b11554040f4441903023000070f000215903003003d40e0010b120669646c0c0560154803881c0400030300b8480d13120140610900032a580308000400ba40c0c1640c8030312013100c000300340000c0764034940120709800f807007035030030104d0700c0700060805c1d40300e55540c00c09074080c0c0c0144400c01203081e60b1002c3d220903988480b0140440d9000307424011480c0c0d95074041e0000c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 330696789 1250 330695539 330695549
    0x70309140a05060417041e080111280507210e0a060203031f1203030905060f01050916031d150702122d0d020a0306080102040f03020910081615021204 66
    0x50101c5e511222084e1400660b4042c003c0c8444012400080c02c404202a10151290090a50a005241d00b040710315500351550259038000e13200800b261600c203180010a003801d01c030180201403200c1d6010600315000205d101003410a4403100300000000a411041c3c4040303c0b602c06c90741a4001d209a59020060721b0300007088003034a00b1140d428203143e00e403014080c2c0000001c107052541c50310515030b06412122845001d40c06450503034651803005a8565024011660002c00031800301c3c1c3d0120303c03001400c000b02c506203400a6240048030034640034142d00004101b4540c060255040c2c2a0081c07805140c021000d800140318034500148d411080b8005c01700e00d480800780003010b0812045020700000411104404500d0342d407150840c0c440d000350028108140000c0c40d041000c01c12040c14400c80b42554514100109a545968200004d101c002043d004210009050000700c10f001040a03084420040000c40200341c1003521a461a9010510200855101e15500c0028020f0181202c003510 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 330698039 1250 330696789 330696803
    0xf15030207050c0909060406061406042315120603240c1909090507020a0b0c1b0105040c06080a0c090b0a0c0c0605030a060f18020c0f0105070309140a050604 69
    0x400c1600b082d42c00d100d40d05845a4002628904000c0070300d00128071248164031490082101c0d60b1a06140f0b40700440c0700303002e145c02240410040c003c6825503403a0f460745501c6d50303007030346c01d070141d00d002207186c00402e4850f8107542240841ea00207224000110641e2098080c1c00074810b948041c45005070030354501c18201d045001500104e10001ca0040840700131498142048141c3d100d002030007007000e00d040c8154000c00385040302088e9658401b0911140c61034001d5070321013081d103644d100391207154031400c0b030041480d221100d64922001e081c045c0f2803045008881d00540c1900d8050f02a14154000f4000f4400c145008201c42c0b0694001a901c0182c03000c2c42e820310b440792055001038402000d080c2010700208141940018050b90200007184075482e400018410380f641d840c0d038128986190b0240103224943d040b141080c004083d400b4043c5d80c100c18044541002019582900b1a4800e0b40c207040041d032665940b100b4800040e49102002050000a09001c0c6a50320354940301c2c240070384010701074 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 330699289 1250 330698039 330698047
    0x1201090b0a0510080303040813060507120807050403020d050601031a190b010c02041a1c08091003090b0910050c12150f04140108010f0e12090301060b040308130f150302 74
    0x50403480707002c0c20142c40d1130012299241400e0410011940120450b80010035100101040081c03207030b4240c504003030f403258181e401008000805d549442004002030b0400905110000259079004400420f007800f03440640941d505609084400c4002c103a04800d03584004030911090245621814000717204200d00082e00310854801211003401c402c0019601030700340241414065040410401d110004454400494240c1d00414030720fa010322401800c800000d00401d142418484103546213100b07d0701d17001401c80d08545d07a40c60468415038403400194007005000340d004600b485200c0c2c001c4810f48085082100211031034620400050500c80c1d030120402e203100d09600da0740ca4840c0d030340314000c0090101c030034220000c0010000901c151041c960078104500e40415040c411105001001c13406419100c2103075400f41c900b903000690442d003542da1001c00081d40520702001e00003540c45850000d69446070120100b400180c91f402070300c0d50000e40c0d0010000c107600380501d200c030011203050150310707 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 330700539 1250 330699289 330699301
    0xc09090809090a230c0a110a020613080d0302131503060308032e060c0318031e050d181a070c0308030f090105060a050909101a1201090b0a05 62
    0x4603025a800c1d060300941d6034001c1c010402c03501e0300b0005070b6160021080c0307465a50000380c0d0b114010103840b03c0f81162400c10601d03517840d101c0e4010314041c00380501150704001e41c0f68045101039000c91000c4c1c0d8541c801900a1007100300611071803010444c21700e015810904040200c02900c2550b1142084000341e8403845a542406500580003e607003200150392a4500402003282303418130310910304803030f0130381d2a11480da107054152440260b071314a03a20914a28000d80e02545e904440c540458601c010103c80000050f003600c5048840d40d010021906041c0380c1c5250a910b4629811054000d000c0c082d0900c50a01447c04114000c507a48603403100c00510f1007103800400e5100d04080580801c036401c0010040c40a104001c50281903055400445542c8004551742214020303204c4c16489290008100218640780710880d03084815081a9940b4035022100201140d5000030b03501d605084507044143e8500d841c1501b030031807451900003802900503030758910200c00801071a40094598600100340c03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 330701789 1250 330700539 330700553
    0xb100302150c1606020c0a09020c03040b031e04050a0c12051203060d0605130b1303020d0c03031b02060a110a082208040b180609210c190806010509040c0909 69
    0x1c4500003c1d4030b8140d50340c49510003901c03007007013a8401d40664011080000c20b2a498402c61f50f42c1500f980140d41410b041080302e01e010b40c0060010b4090300801014140356804980c03c1c20700981c800c0000786212a01480c001a10b0b42850340f0584407115211103c80c0402c030b010a00c0ca4105804807a8180d8079952007000a0400c3d200c0040544100d1400041055140480f0400000306009400465032540c0d1070340036605441904100400580140c450042e2203401804250b54092180c1008604550140302c0501c401158411600051340f024041c0b000001c907510560038080d409d507440c0c920f4041e1072040600030503805800b1107100e120101c400003841c86161080106980e2155105550f00e40d00c082c8040140c124154004010013100712080300d52801100b21091140050071307280d000c400d00d56401080c5410752220b00d034103000f0f42c1c0c42c0036000d41e60f540c41044070701c084031f60840c10b003401c02612a240c4441600603074068103824080c03101241c04026104202c80c2c1f066404185515245000720b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 330703039 1250 330701789 330701803
    0x1110708012c01020c1b0d0b040f1502030105100503090a1703011d04030c0222020f0a080105030d1b06140c07050d09030818060c0d0203070b100302150c 67
    0x581070752a00c0d014629103055000460711180068068070707203071095400024202d10034104245c810750300c04030600c04078074181055149030850051506035003d40f90f89548010180483e800c076089800a001d500421912042c6c404034402c00382011811981010b0108040e04101c1e1400300a00101000103038441d401084074084160b401803000002c00d0003030410110340c2d0428081d60144251000580f1480e01d9080e0006105503059503c003100c070402d6409100514815860b640e412440142d00644112418001004903051419006548840078480240012011b80190303102e90000003103407040d01e5000301c4168042411003400590010036281c044010490810700d06030340f4002c241003285000322200030303082460240e0709032501c100000b401240d4030f030213501000704030003000e11002c500b0b0b0036400042c0103014000f4240d0b07840c20301600042864086211200c5005a00000d0482e0402502d0004c194000417942501403046082d130340000e40702410003409421121012440d411184010001c03d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 330704289 1250 330703039 330703049
    0x9040207060e0a0f0b0702011e05070507140c18040203060a270b04060507032a02191407050d03020a02060d06050d0507031b1a0a030b0a17010c05030601020606011107 73
    0x110340c065520b10346040720030030b40030043d1106004179000030180703401800b4822003103419a600081e0b4840d00c040701c10042c0740c050114010480c090100ca000540205048000030703261000802140b200001000b00400b00c0d40314807020140602e0901c4016200018816004030201901060100e1105084100380c101c001c443d049101caa622031000f8040440f00d0303140224001c00c0d06005030390f200c213416007d5a02074241004840600100d8504800b8000070a00c3d4800342c070300c15107040802e680c0228041104400c01a039074140c080281c803030f1044080040750300801d000e80383d050901929480280d110665010041c2c0616000140c0801400c5075510620142000402400001d5054142540d0301c8026000c11502c0765410300300158200b00c0f4007095022503403218104540907480040818132030300501007070428076403074021040e9180e03034000d031020242c1248c03580400905000c0460509458910340b41506109082061002590780410080e60004c000e084caa1410144902071134039020266100c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 330705539 1250 330704289 330704293
    0xa0b060a05070302060c03220201020f07140a0f05090a02030406090b0f0f24012307080a0f0804021e03120f090108010f061e0c060606090501030513020609040207060e 73
    0xa180300381c1d0407102411009019134221170141d5220480c0030801d102c10f56001e03510f440320b00c4407003299105d40403800004d140b06106840480c441c0c18019403400c40786407c82d6001502e604414155418120f1070040241030502501c40d5071440c2c08042004017401a10480e10542c0010024003031014a4100e2110254480b040c601c0528003d90200e42c600000d0350f6108081c103130000814041d03485d040c920421102c1e10144030030903410a50054640c1600080100c445000000c810048005d0300300182100c40d000300b480c00d95034410b420006000f080140240000c0c403a4907000c1c8005a15941d21440ea0030200e440a03039185502030303000a1401c44941510b02c02c041000440c01136055501c0f001c0c100d072070740030307259503040da62a001da207801003031240140ea0005051b0640c0d01074400300046080c130f0740301e500e0910802000b0181c56120640da0b550b00800042000d0690030405542d1600c9450b41c41b1040703040d1064886081e5001500c184986500d0610480c0c010407a00c09004031a80032071200000c80c41 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 330706789 1250 330705539 330705547
    0x821042309040308011806080318040603060c05070b0a06080327030109110a0b070b07080709080312070e04090512030907090f0b1f050702150409050f01181e050a0b06 73
    0x50004d242d0f0009000c1e040410104503c101d009400f14082c48081d1803440700910b09122070300e6410600c2d002100e0030190302a40b82d20000000c14564410b1070200440d607070f1800d03683d80450034141210b660141402d002180750040402c40c2450100544940100384901c64215086940040300c4c1042500308099040d440d000600040007016200443d0709082035401c050712907501c03d8060401d0094034000342030603a014001468451140c84169404512801c0204003a6184c501c040d14541101c1c020511521000c401d1003c481d0b000805101c1100080390240328032562aa19a500c984900b40003481403413001c00400c456140601c4542c015021600d0104035852901c0c0d045000b41c13901402581c064942c00702080b0152103a500c0701c0080840c1905c0c1e651410a5503424084c9540501030100420750b028007004c5039801c0a405010300a841e5540144101e5041c1070011251706054088490007524151800b070010707140ea0700744104405007040001e0907940d8002c1c00005801406840c0c0d5209030009 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 330708039 1250 330706789 330706793
    0x8070302271503100902090f09071205061909030c030807021c0302210705040b03060406120b060906060a020a03140c0717250302040b010c1209082104230904 69
    0x2008069068200310100d070204d00150300c0c2c0c08201c0c2d6417102d020f50407482010014040380041036030560454030031412118201c0d5108604004010301c82c404841c3e5411020034091695a6070000b0300750b441600604012420a070f64001d010000c00e044000c5c18008818000b5603554000c0c041d4007083c012610408203110304480e0010000d51028007018120312102c4241d0f141601d003e44428400c4508e030726154501810300c030103e222504020889a4825203030340011684414048582108920038800c40010341003640c10012480c0006105a00500c4203000446560358005081004290942451503801c901d03071091429510030780c82454054450300c00700040c43e040c13440351300400c001110181d5100380c0c0310180030703941001286001c004041c050302041c409442d00e544210b101c7d11050500041c402200c3c1d440da9a40e000e80c1143e00c0210300d06010030401c0c000244207400d038403030320203160a0140d0f0600f620031405020782e000b04641c00c1281002002c2907502e110726401f00310b45c02800b0300c00c0d41c5024 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 330709289 1250 330708039 330708061
    0x18010605041b0216080613050703020d03030e0d080f06010e010921030906020c101101140901060501030e160e0405030705060a0b0f040b0d151d060912040807030227 72
    0x5850101e0040c0701c2d25488128010000d0302600c1034405505c040c01d92525140d03140e0780c0d03000e0303201e1055843d4000c0e400c00000503914100f104003054465100400e58508240c0d005042010b20480201400752940400005840c00c2c03840e258082e41c2401c1507030700303201e1f42030040340d5a690700c1e0071a52560f0b11603d061117100b0320f16100100f01314444d07035500740d0b0503403500350032611032900315040758011500024001c452805180c42440028020700001241020343e100081c3c145402c0e600886030b42d543e60000c0c011542d1602a903e102d0756100000c110f088c500103d142c0c42c10603e84101c0c015009080c002c901000028000c545580f5004000ca8816042c03100d8900020540182c24603c2440b410f001c0c405203081c540901c2f0000030000304008404141521154260301a1030100c10015545451902020380c19003142c252200d075040c000d00da6450322801c1c891518581c0e81c5468540c0c10103010410000703900240c41c0301581d41c1a68210a91a1200d90000d41401c00410706138094020b0020880100c0c05 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 330710539 1250 330709289 330709331
    0x30c07053007060b0d061409070302150702180c0d05011208030a0b0f030106030c0f17030307050703050f1204020901091b031a15040e0c0a081801060504 67
    0x44003034952000c21516094020080e040d582031104048081c9a00e000e003498025058560003600041840d54a800c000740a5032089a0100d88484c1c5c3c031452101c2080d00c5039101c5920142c648001c00d5607a040d03800040359012903100540150600080b000300315200c6e011008540c40581c0d100040d00e041003408104690800072000040a242070000600328101c04243d42109406c28041031950702c90980a101425030010307043e41002080030321034120f890910940005500030500030705103d0400800303561401d00c80d440392281c0001840c480000c85000b008490300009981006070f0b0740c030310616040d1070501a0642c500c003039000c0450107a01e200c2107070342c801e8480c3d8421525081d00d07070307201c00c0500b045407080000b41080e40010780b2101d030400e00a42c07094040096000c40c0603642c1b0001c0300010407880d22240319280400020500300030001c00c1802c01900f1003040c0c20800e06007071805400400c1d505c40145002d0b801201c11442c1a2046402e60000f80900001303081404180100b01844496140e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 330711789 1250 330710539 330710543
    0x17070b090c0a1203120e030309031224090907030f060e2e18020415150207050306040f020d02090703020c0c0a05090c0a020f010515010e0111060a050901090602030c07 73
    0x41c4024107009803034072a010100fa01e01c102207403110f100c0d40b40c8040301e52000102c07120001944e585000700040e10304101451040300c00b0f20007181d680b181a0307100c42d56000f0182600062200720801c4a048244019a245001c04291089900c1d90b1740c4060451801e5682d52000d404001c01c001c000e0140700c400c0d000313145549400d400300c3d92608800c20380da07501c07003059001d4800b918004520480010000d0740041688064200d0315004903070560b00043c0860700440d201040d810380a5a0411146840700700b81c0e82e101140b40040d0540e14541000700c2c0d200c090043c8000d00840e10481c00004640e18507900c0d400700390700900341c41046e1608050280095211803052211031082c0b00b22095203203000b03003100c0c0c01c0d205d02401414039030702d03a581490082e03006580034000b50300030b50100c448034090034417500e841031000c032100da4001e1100f03100140c44107402c0380d8a14100444d003040e20059480014403e5000000e003100001d942e0396102d60140140034004004182d00d000005120941c1c1c004005003070118 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 330713039 1250 330711789 330711793
    0x60607150f0b041802090105151210031b081f020f16030305060a03020310110f03040606050109060801080d080702012702040605060c0d050306060403120f02102717070b09 75
    0x40c3c004c0b140b15100000c83c0c07200031b5001c0c01c04c000520050070100d0f4181414a4050216401d00c0030842d0324081040c0c0c00ca540d441404001c031010024003000e031001c8800241e10500c0c2c1c4111504100210b40c560921800a20141d0818003201800701010350403240400303030030200d043c3c0b5204881c00c09001d4080070328054000a0404005c40c00783c0ca4419444822603034020002c0c60003041401c1ca080240110061040f0880000d00c5070a030604007040045200710722400d800595130f42000300141c1030b00055081702e020030032500f0040c0185030300000c520380c01500900b00442c3c16a940711040b80500900c1300300c800c0b848550860460700c50610b250000480d8401c071814000c0ca40c4071024041c06002c0c0400c00e44480d40f2020394080c156014000035a04410040c2020345407680304d465600da218980c03c25980010555001c0800540e8180421032410100c508240100c8114100c0c1001512000310302c1b030031441c1c2c440c04803000c00581c00c0c00c07800c0e03480394545c1c80ca80f00c4240d41030886c5803c01c1240d81c0c0050b8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 330714289 1250 330713039 330713051
    0xc15020d0201050105030a020d02060f040b1213030c201e041802220e1b120a051b1f09030c0905010e240405090f1b0306060607150f0b04 60
    0x440c1c018000c040c162107002e802001d0840c030315001c00c0b01d903180d0f020050b0b0f0007103420000381002c60301d441c0c0203001130155401c0c0d040d51100c40c0500c02059903001400f1120101c685c200c08400643e11030302c40302510740c000f141c01031210a900303042d8400900404040340e0104c19445c1b2550219101c000c07039024201d00310f40030811154201520300c0000d406210003540701f124402545c0307501c0e90303228000300840450200000d95188010400c2c1c5040d0b50412100c0c8800380382c44d60800c00d840c2010161302c1024010001d0202d105c6c4503511a03030341d04e01c03410380b0b04a040c03801c00c0c03c02400e80318810406140e1044501d66280e600305640080c0042d00c8900003034968048180b4042080304042c000c00c0c0c1217505400c2494201c0d070743c916012407c00e0300002d0100e0b10501d08502c4404982e56405454000e690040c06800312582c4444520b01d4100c0c14007c4018108040c1080d034030700e541c0031950179480b0200341c6080365582c0c0c051501c071406400202c00038a14918205500d207034110ba0381c0c8040c10800d0156010060 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 330715539 1250 330714289 330714313
    0x309050307050306191d2b0c0b0a0209040b0405011706130b0106050d0603080c060105040b150f0a020703050a030c0308070e090a09390914040602090109030c1502 71
    0x244c00c030032128002c040343c00074910070650f54170303601c0103414040c5180e807071011242403024079041c1a144402c800314041d26941c80e00440c00c0c05500b89840044a0902808010702c565400f0050385005000c0c5003029400b280d00c29180d11603030403210180074001c208202a684494405d409004040702c2c0f83d050384542800140342e10180c10b0004146600a003840b6503a81c6001800c948681c001030790080c0c41a00c801d400400a105000604a1460164080d0480c1c0d030400050000303c50003072100520800d03054014a82ca62800412100800c0200000c0360f6641d4000e5003e0740b80086503400100302d03101d035003018001e01d6403080020003454880d694484032604c0c0e1400480300d00d10410141944005a02c002c20981007446e8405042140b02d92040a515013581403c01400c881d04001b8403c82c0c0140f2840260141c80c4100d500041c240114040094180500001240c4071006000810440e40041c0c0d0341706a81c007c00c4a14000d65010040d00207403621508070b096501c00d010050400b40c8030f43c0f422850 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 330716789 1250 330715539 330715543
    0x30102090d141204030809040b0301060b0403020d08120106080103060e010501150c050f1f14011a0f04090f0905060f01050102460201020d030c350403090503070503 72
    0x200d92000100000100c200320344440b014100c14050148161244859002d066191040a4001103003c0d074007060703d51040c0d07420302090780c04841c0203d1091b458a1400e210005490086c1d0781904c0e010381e07a007c04c00040f49041d8a00744102ca01120000744a070000040155100000a0607a8071400e82481451301c1c00d0300c014240c2c1c1e001c3c003941300020041d4118070b0085106daa4040141c9002e9011142c02080c64480c0e10704140001c01103442c0000000300003642d002407401240030083d0410707019081c540c50003c03281000d651800c1140e1305074500040c1003d242c04103000b580c000d8030040710100b080c0360155600200030014544200c8a6000e20000074150b4030841119904894040e0007409080c3e0742d08900941c0c0c0c10300319243c1c540359262604001c640041c1d070032a019860403800303082c0b170745009240006460158000040001c050a0402ca00813080d80100c55842034400f807a1004200c030047c65114094900d1507011442d10300f44032040106041d801103408007255410b805580f051074486050603 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 330718039 1250 330716789 330716797
    0x100b0f06071b0605070b15010507060e0f07080f03030612100c0306090b09090a030e04021e121b0a050a030b03030315120309010e0d0f0b0a020307020c2b0620030405060105030102 78
    0x1c4d24051b031080c0083d0412200f0f00b180356280b030301498817a1501c5481c1d6180c8040f103015804442869206007109203980c1e6040202d00080c2110800601803807036a8903100782e50388401007406000d009100114101381d0f1003081001809281d0355010300028200183c020002c10b00b500c620340c0468180922283e060800030b00c41805052200083d2a20203400d407403d4031400340c0301c45500e4025900704200e640301c80d41c90000005428000042c550389107003940343d640c5129009802d00003001c070141410340d030100e140000c131079503148541451030b02d1f030501e0079098000b0030082000d2605400004208a003204080421503901c9034220350304c0d00f440c40382050a070744d28000c01c900640843c04010311486a0700c2c0c81e503818030340d443c0f18818802c1781010b0790b52040324a0300150760220215801100f400001a01405550500c074825107a9000c2508030894020364400d01540b11031002128600341024448039030800203620040c1140341000300100c1c4000b02d4650320885007511b66005400c00800e40c1d10b010b000b15 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 330719289 1250 330718039 330718043
    0x21638091b060a032007080417061e0603100c050901020706050a02070509131a090106050d030c0609031103040b0409140708040206181003020d1a03100b0f06071b060507 74
    0x1907042003902c041c1540181000203117601e0161500d8203461000d08500020005548240d10382500e0714502400900c110600340c4418901e504071100700091107480c00720303c201d4080e241000d80c44903116140801c1c10200e00b148010000ba04011500c40100d401030005c0c2000202a0300710707003400d50b4814040304e15003e661440380c0141c00501081003149040302c8080d4001942e5251a9441e0f4191364404086042c055884852840c801c0f0030481e6282d800c1c8191700040c102507852400c44486030740c0042100c1041d510042080756550302c5034040c1485801040c1424910000320b0340e507991564041c40e40c0760080d00c15051041d0414513080035200002101c18013808440e04c601d034240d2165400c00402c0d400c1440d903000741801c2e40c0700082440c0c1d20202c1c2d0708000700050f00e005a4030201c8072141c0c0140e8140c442002c181d240007131400321840e200028a50183c40307411600081c64040800002c04c15000000750790f5004402058140034010100c004042503020b003050a80b40301c0d80d030502511140924000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 330720539 1250 330719289 330719299
    0x20307031e06031e1104090c061e0c0f110d081b010b0a050f03030c01020d05100504090209070f031103090303012909090a0f0f0f06050301021638091b 66
    0x1501348400812801928610640421004128204c0403c044070340060041c1c82c806009142084043d4011707401203080031038050003031400107503400c0140581095040007403040c10b501c2e01c04810310180e8540d040325080c008101200840407818080001e400c1401c40030f1202c02ca000a00c4041101403182801545000c0d290b00703540c503d072070204865003803803410494050104000380300042000b80300805071100c0366900050241001e407510594075146401640c000d900e003452000c003507a900102d40380e22105078074182d001c003e044d000440141a041c0d0460b00540c2c8040f0034424100d0000c005107050f603580311805c40310002208812250029410342d0400002d80c101b18844841c1411480d03154014840e4002140c007000c0b000d011002c9400c0a002d034103540f5550394078001e010302d1134080c040090808400950a00754000c5182e1410140c0c404000e00e925100d0001c1459400001003110240f104030705540f0b207810345c2e001c1d003141d0510200c6101850307020b5003a0f035040010f034054220010240c0a04 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 330721789 1250 330720539 330720563
    0x306060f0a1508010303020d030c020606090a060801060311030d08010506030106080901020f0c0a12181e0504091a090d08040b06010e040f1505060403080306130906020307031e0603 79
    0x180410040c401002a400040c2690003007000c0140020000c24030b0350542d00c04040758910b0800070704150b10554070300c00f01410603c100d49610340c0000d03241e8200c042200c0c01e1400c3c1e11a0000107008060070341c0502c94550030701038004280507040481c44c040b40000e07400d0701c41074585844200e4441c01d0074081c0540c001c00600c0103200c0f80d840385090701d600000c40000141740c014a00c1c41c030206508919004074480c1d020001c07400800541c14101c0c6820300341410481001040c12004004082403030040940c0f60100b0341e00c1d0882a8005208100107120103001001203130714604108503200d0501d0001030446002c0000b00d032080b4000a000d01d18900c60746c0d21081541c54981e210009208040c0c8050304202c0c4800610202d82d03558446c568211009500015094008a807000e4901d40c269215600c64070040c4820000300fa00301c01107a505c0002250514604c9081c6103401008101c01000540840c4c404410880721641562025230b0382c612603640c1c619811191000d070820740b50140001000d04113450 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 330723039 1250 330721789 330721801
    0x5120a080f060a03082101030c051305190218100302092e030509010e0d020d030b120a080306031906140916050913021306060801064b0e040f02090306 66
    0x103014040b01540e03100c0500c120b411907080700711500402e0300706442c482788074541000701d458007801100c060a200b04d001e001c1e615100c0035038103c60400c00c0380c10380c500d0703000941c040310066044036a8105000041000140c48c2c59004000e0003501301e809014080c2076034968805864030200000000c002c1030ba804180d500310300d03c2c000c401500f006040402d01d5903c0301003a0324100c1c014000030040c0710165000b44488458040c1c01403c0e00c0000003030354010034288000c41406500840d04401450700488400c8d60b030340310140031900c1c0400c805c240561170040c85204108104054105103143d0444481c100c90130740f54800220348440b01c0c44189120002d076a8030400c594101440b100c0d50008000c41014070481c1c82d80c0121742d01d945642c200d08a0199601d600740000c6421490305400b41046141440c1402811141052140d0020b0780444e02803401c004452240100c0302d001c80ea00009606200300c651a1f10741e00030300400e80c0072088902c1a4100380719007054691520a44003205001401007109441368 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 330724289 1250 330723039 330723053
    0x609060c13031203090203010c09080717031b03040501021b091308090402071110090305061b07020406060c2307090506030a02060304211806180305120a080f060a03 72
    0xc4562840401c10a00e4000b0219031845140b2582d1070702c0b901c02062840fa42d104160071101180604000c2c400210401d020032600000d1540a543c504540b180b10f43c194085a00d282d0701655402e20458401c28000c4465080003102034030854400381c00f01d407a031301301c035055951496400c801010782141070f42000030a18800c002c040682c1c64040c646842c5460042004a1b00341d0740a10700c00c1d03c0704c24003c42d40c00034901305070b55400000b403103034600654045d04641c0c030706480c1e140103030070340d007484e0310300f0180485540e040d07412141020380c020020007480e03907504405446100d49040035034520380d000141c9070340b40d50811600301d00f04a8400141180d1070800c502c00c0001c04025280a4161203196007000041e200c000c021030285009001411206900e400c0506002204079100000c0001052101350b031440c455064030256425800d2080252982003103052815086602c041c20074882d9040b1080c0761142480205007c01099030b4441076582d803a9041c0e00e08000a684040d08042c803030b041000130a00e0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 330725539 1250 330724289 330724297
    0x6010309030e0a090e0609010c050913110310030b0604060602120a03021c090b150901032907030510050a030f03180e0405010b18070806090601110312040303060501020609060c 77
    0x11a00b4401c04020140020860380440ca4100c102500d660340c0d411050041c2c1001056072140c2400000d00c81d003d079980000b07100e03010700320a03903014001d10030030700d603102003e5080200c0800c035910302d05480b4506050b0b2040d11001c0d51209860041c0c12401181172401c0501607501550300315001400d00d80c48406510140380d0005a0b15000c056080c4100c409542d0066541c0c144000701800100f514603450074600d080304000b50007001c50466076241050310351100e4200604686d00b101d1024901d1140003404541001c1481c034000310040c07900100000b498040d40140c0c090720150041d09581521130040c00040001404040d065113900c020f407000191003040400d0082c01440d41043c0d07519903664001104407002c0e03608a5440e51981018042c0e410303c1002e1000100c8100010600741c20725110280440e54080d0642c1c0c066081e05000a9490f4040c503a1040c107690598110f90781c60b030114514101e01c820594080f0001703402c003c2c0003e080d600c00a5110300412248024000706e4854256213030151348 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 330726789 1250 330725539 330725543
    0x10312090504050c07050607050a090b0901050f0712020d020c0102061506041d0615091c140304091d060f010b071106210f0106211d0304090c02120306010309 69
    0x15090388003142540701d41c003070742d03000f56080080142c407540d15140030b50074244024503140400505000c88004c26500003882ca0440d500a60211354030f10841004985034469030882c0300c40c00000103100002c10003021145203001e91150b080d0b07103225046035022a140c20002d00e0140c0143c0c80344001c280e07031041c60403280740031031401006549895610200311101665180e40b1001358404041042054104019030b4a241c45041006903e4030810b6000541c80700c0e42c010b858040301d50007241010420500c4020b100c4090740080840c1d494030f588541c4c8a0141c008a221003185d4010301c4543d605241000551a0044440503003140190f801c0079419021f41c1c20401e01a928400c07070698848080e25000d0042c0301d69030700003140803e10102c0c0b801d59070f40e21a010b80140c032900403203801088800c0d0320101c41c07201000c04106100507404410002e2016281e00d240c08109111400f20301c101134180080240115007540109000609200c0c5050f80c0f90540c0140814800703a041000600782e40c840d82c000c8034003134 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 330728039 1250 330726789 330726797
    0xc060c1e0c070510020a0302060109090f120903060509010903120903080609040f0c141f0f030c2d0807081501050a02010e010f0608010b0901050d0f0f24140609010312 73
    0x1d43d070b58000351454195074009000740c2c000e1000401030682c1480b29a0140030101e10620000311141d65040c121198010080c004102c4012a211024031800300c0703070700a6801200c14442c07801d2541c40c3c64004e000c0c1c00ca040f0040b07418280007105a00c524010400f681d60103031950a03c0d543c030002401400c5d00003c2c41140e00a4061080200003021804039030040d114181582545c6001e0394140b04a01490b1142c440300e81104200082903141d001d0011078243c4900d250100e03618040c00e409407507180f266a100c0075948851652010040b40c6030701030b91500d5460382e032004106d0b01d0b10b900564440308181d903018900d000c401c0742c1c0100395010780c0084c0704c04111380c400040c0040ca10700c501800c4800496000c1c1c1030584801d01004001c03400d002c1d0710f803c0c003c11640395106514000000340d032a00281da008000d03601c210123840c180b0180c0f654103510036400071004140482e44c03880803207840041113060030b002c5140c8016452850710902c12240320ba0303800b81001c0c0481e402c40d2554030540320307490101800c01c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 330729289 1250 330728039 330728053
    0xb0f0405040c120b06040c02150a020a091206020307230306041a04020c01060509180c041503050d02010b01170c03151c1109160207090908090d080c060c1e0c 69
    0x2103400e40c1c0f42d052140907150200039414107100301b0080d650000742c6002107502220810307183d950006411504000750075001a0ba4040070700c419150742600e03502044040c050a00e003d4144991038004510035810303551012505800814406107100890301c0c1403601c4501840000e070641850b90140c0d00024410707100e400c090440720009010390380581c1e402c038040c0e519040100854200207030344c2500281c829000c04503030b90240c404160f40b070508003a454031803a250996940400e00e030103d02809150840c099990180d040080030b4040d00f00c5020584c0080c03000419035441442c5842d015015404c0c8001051654640b80070755130700c20707000058041c0e020800b0b41c03507550b44a149a291410b120f202da15001104580e0100b00064924000d03c2120403103240c41284056039404036052041e1152210f000800d41400c2c02c10913047c6c02030101e816088448a8032440502c202c13000905505080c0000301d42e01a594003010101900900134505803810f9074442d07072400f140c0b0001c050074880300b065045440c1c03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 330730539 1250 330729289 330729299
    0xc02030a14030d061418040809121c0f0f050310050a140f040b030601060c0302030c03030a09020f030a020a061d030105040308061e0904020108070e0a03060e07090b0f0405040c 77
    0x160741001d50340c0a501da100107011241d010302030246500030b20b07802012440860303605010a014076064815a0000740d40d510000c1c041100300b10035582e0844018120142020030544069901d080c2e80c1c907030101031a0030682000701244203d490700d01031500c03a910322240d00c18103002547c0680000e84540c504a14194002c501d9894014400f40140000035800341d41d0180c00085c401c4050034881294003e40c00d050030006951400201141121b0481c984100001c5031814101e055004585113040c86002c000107102e0300d070420ba040800d0160003164901c2c0f41c03443c0b810405a4548441d400203402c010611070400c03126000301000b07550f442044a1038a40ca841e4440024210b074401c5600300d01286060741404201e00b481d000e2404d51400c00c0030715050394000c5000241d10030400078002810802e910b80090201d45c4583d25102100300e01500c2220090f80781e1920202412007400d80321101d210724000080d44030a980501d041c203a0300503201d0422040000c060002070b1000410640c0d2450502c1b500040c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 330731789 1250 330730539 330730553
    0x14160f060210020322080301092403140f0303270a050705060307030902030f4218010c0207060305090705060316140301030f110a080607030f061802030a0b01050403050d0c02030a 78
    0x4049200c0c08510703030780798107200e4101c0031141814a40c025925104100354001c10ac0e126001c82500d800441e481d00070591003d0191400b070300b070305200600b07020200910007080341c5001750080542c0d03064034400c2401c007508950395032825548805840c03503200800c1001541007090007180c002e44c25140100b50b10010790082890444031520b001c085902600001040c074044840c011250040d4000c0300320420281044c04003041400500c0489640c0381e00003042c0700c40ba00300c40c1020001440c0000b4000040d6109019480c0c038058402c52000c20f050200165460601041c0b2400380c0d800102018115101c00c01150f40566005081c0c0d403c0c41801030120150407540070180d40203501c03548010b10072804034504503258004451656004880401050010382c0b0041203d41c2d1040183c6400a60f40120b010381102520066110f8007440c2405080300d400d000e8160003c61007051240f006229506000004640520a52002810f190030000310076039680e00c035908041d52036000030b08541c2d0507041611f50f04 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 330733039 1250 330731789 330731851
    0x10b0702030d08090c040606050c12040e01140406210308093705011119090b0406230412140a0c0612060b04060509120106050a0b0c010914160f0602100203 68
    0x30208070046440265840c040204480c2000400942c0e4102850090340e0280294180141e4961080c603a0b0747c2051500c5550151009048031502420160f0f00d4504100c41100000024f070005040d6200062042e0b400207440b0140741600503a00d80481c4070301140340074581c003554880d10300b1403400030b03a000810401d000300311454603844045580c400380850b44407041c9201030018414809040d1040010324132510550301141c00700e01304911501e001d07003000c020003141980451030217240131030040381040550790b03203200036032080c0842d021410b1054180b13503075691041001031045010601c00c0c044144501404182942c05076030108926031281360350039440c0c01641281001442c00b1030340301400e21703001203819044800800200821170800340452140f000900441d28004000102220940307000d50091840720b410100c04824584d020110a4440c6003450701c22404940f07994020070301603022100d4038121500c0b82c00414828210000480281d00b00600c8a43d0328401139103406080c400c1c1501d44 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 330734289 1250 330733039 330733049
    0x301020c06012105060105040903030b09040809040e03030c0f070507091806060b030f0a0e03040b070b0a0605090f04031b1217070504050a35010501030b010b0702030d08090c0406 78
    0x24104542c109140c04120103c04520422001d000044490114101040c0e560548106407008103600c03500d410140c2c080c00c1d1007070543e17070001562000c000c00d104050010301900f220031a401d00000c1113505c1096500d000030746200d110710108002e1080b241d1500ca0007010418410b41c07e03034820310350f1001c03144119200e00c0d01200c7c2c3c4d003542a43d21001c000840c4a01d40c054035821210504600b043e42e5407181d0848010103668416a8031000c40407402c000300191340052030020402940c464041c40c00c205801c02c2900c5031202c81c0c2c24110b01040501d03043c52503910924241c0c1c1500400d981d0754804a6041c40c0400310712441404c4000780b0008a0844080a010464640c5a00c80030b98050089610208c0d0014588420000288810b10481d40c03203080d000203c56030101880c0e0201440926a00e180a04030344004004082e03040200c0180b0041d00540e04882c06442c01c0c20030f036a80c03104510114030404134025895001b40019425940c041c4d03031002d410044240031103505002c0031012500b211556001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 330735539 1250 330734289 330734293
    0x207060f050909040606080d0302030f0610021c1e23030105090c07020d060e0610050f010c06090809090702071a090f090a0e031305031c0807050309010e07030b012102060f180301020c 80
    0x402080b1760001841d5034100f5023b5504904030703080003000a4580d00d100800580c401c12056002024510509240030300500b40c0600503180c0031140006080b60b45059150707894151006400c2824003000c1341920f0403a1405401b50840d41d0307030192048445e5000480407039002d01e686809902045052040c0042541210001c04071800c01a4040421a0450b8030a5104a650b41c164181503643700d4000913456a00c0030021465160302d142030b03d41d0b070040010480c0c202c0d0881c8100004036034000b9541d02102c0350242e00305140301282d001322600c1e100b419049a04031000d10051025400d1044881c1d60100311000d001503d410207070000c3d811503000c000c1d0508821103203070742809075160500c5085c00307014403c010400c0705241c882c009854642c000b00b0240078400c0210010b20450402c2d000604c20380b09401c15030310525280d02d4441c003000d0085c0501416021107049094a8400011003452426002801b031810104c0c0e044410341981e106078007d00369441060301a200f26142400640304403090000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 330736789 1250 330735539 330735541
    0x311030a05090f030a11060c0c1e0a0b0406050a0e030a060603060b0f0d0f0206070515010e0103150506150f04050405010b0d180f0b100b0a08070207060f050909040606080d030203 78
    0x300300f00c140c03062200300c5803003500070b0300803500060342c149200303200c8280644409031161103001d6100e00b00030191082d580c002c04004820006600c240340200741003034003100c034459500d0f1a100016524040d0307015a03004207000f0090f00520f240180301d40081800c004048400c0c85665175214002d60742c02d507104403816601d4503047c60481c505a0f4142c076445100b522900c01000c226220000e00858241d006400f5100002e040802e00509018050340314a4110a8000710750713580340041c072104024801500e001402d1042101c41c41307001e020f402e0142c54000c1444541000703040d40383c840c6612000c1c0e01ca807500020003000800e610b80f400f4150080021880302c43d2643c7c0307582114001d40301c404181140e1b06280390880340010341c601001c0d0420a4100e8100ea0b16030399190001d0108049580104800b84001b04101448541c442d003000c0c41140c060782942d0103240c2d99a420758880780000c05040100d5000d1050b0001400c1001c0c0c00c0d40c0c0a4010701c004503041b41c0d6900440d080030040c2a403800000e40001c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 330738039 1250 330736789 330736807
    0x1b1d04020a1514180a0825060c1202010e010f0e01060e060a150e0d050a0c140303071401060f030b0907120c090b0409060f0b280e040311030a05 63
    0x11075014014000d280c1e00c85010106801d00508002250b454540700900c0880c05154001c14a00008442072000c0c0000b10003944810745160354020032106009212044105884484804c1444600b110601d403100d168a00195549000b11a140340ea12005c41d0b41c0c503d60b807841000c0034012921984404200003400040b40c0c104682900c41c9900105e800c010301206100194441d896444212960b0349000c01000400d003400b01c600d06159041654441c0e409100c82007440b00100341c40c642c043c82103541ca910f4650f948184260a00b8102030340354903402c180a6203010420040714104404802400002d00c0c0341c0320903518102500300d400c140c43d507072404d50401101060030080070000d03102039440d40c42088015a01c209401e5200c1c0501014140c0f503020421141e1115003044800590080c2c040c0200013070750341010000c014a805040c843c06142107049986241000d080181c08a104e040609450030440d0040c2d080102030000c40030052098409008004280003400c0303001d409a407030564408081c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 330739289 1250 330738039 330738049
    0x14011502160e040f060b030706030f0c0903020906010f0215070807021b06091c02040e010b031209030c04050717090309040b0111100507030e010204030506010911040e041b1d0402 78
    0x80e10360711644041d0140a001e020080c1c944981e01c180e0005009019106511700280906140d4003400e0b050311079008041040e54160700a0403161403000301c2000084403001c8200c0700c80480e440003a400c0030302d010108125520030500c03200b0070010350044490040e501303e895140b03d44110f0726000091040b80911030503680c184a221030660014404545862140c0c000031000e21894441d28452080f40250310501c1c0b0003107079400388150700104200020b401d444a060301030400d4083c0d40c0d209009924402040b9480d9400351104880d0103401443d1444e400c5041c88000c000242508080c80b0050b090240c01c181d00300d141901c2005204061511000040300380002e0340c81c056182d50511807070751440c402c1c13040d001035802d00c881100000032881c0e89400e04207900900f44003074460540d500002c1c001c428040c000819030304031281840204519005409140328500690141da000c1200c0100440c0110ba4480d0a00e801c0c2c00200c10010011540c0e000c003607070701900c00220326801d94403140400003035241c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 330740539 1250 330739289 330739303
    0x30906020a050c090415020a020106090b03150c030403020307080307030204050a0e13060b0406090c020f24040b0403052512030219050706020d05090a0b1005010e0f0414011502 77
    0x168001800358000c95503946480700c40e015001ea0160381e541c0009006e0090485a440b490181a10115620400080024040c0040d03006014869081001c00080c90030005060880b8062040d003038011030325100c440205070f070b0000d84254110b2100f80714070300203d22484001e40c007c2c28980c80040c1c1d51850714081c400d0b44c980d030b5800018890300600c200981c0103c4955699076a9610400000d00c00880344000340c02030881d608070f05103c42c50301700c41842e495000256034900e210708070203c904240c5110740b15122038800014288030140490f021400203000c071501c50350824424103240782410458104078248181c1540b140604150b960421030038002c0a14441c2c0100c0058074066207442d83e040102000710880304000c5e070802c070700002d9610a00038941d0554031280c010300802c8c0250309080c00f40580e10301e107000d01070383d9290380e09010070065120607081e54111003068542ea11100f81c503004100a0380c40c550900c9400685032490700c080b0034090a0010b0181450300303206089152215402880c05071 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 330741789 1250 330740539 330740549
    0x1703071706131e02120f0a0b0907030207020307082a06071e080702191502010b0913020105040b03041b0603140703091b0602030c010c0302250203071806060e010816030209041806090309 81
    0x1260108d0b03017000e515440805644010350742405650784181d4800b003441c00146a010820a0240d20113004410403140d0385001c40c03103c0079003410081201d8108204061258120040c0203250006030780700703d418200381461486024514140c1405030340e8012402075039110030710a0481c0c68001c81400034844465541d008003506100801604845101148002c01c000d030402c044940100c00260031a1310550484024220507600c46403203040c2403422010015100c50440303100c608100011807424481d00c103070741c0e64a001030905200e9440341007040d0010301d1003a0066407448039404890020301a40d0101400030300d261b500456540c807021400034212610711603000b041600400000b03112002103100100403078401100313801c0c0a507417407002074030703207005544000a210009800060107421903400001141c8041c0c40340e4146c0340c040401184c40441c00c8483d40c03000d40a45001051203403003940948280360000c1d06c0010300030000c0080358100851508200c600315141c40400c01015880411107000348 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 330743039 1250 330741789 330741791
    0x25020a0309080a03090e1902070803160f170601090503010c0207050a140303040e09030c060103051f060305031b2e06290a09031703071706131e02120f0a 67
    0x58602c0c2da006090500070300c250414846002c0100d08100003c105002147c0b0500c1e07000c40d62030391103241040781034004450580e244035081c1e9591048078010000291000340c25580e201903c6440b101300001c0040c080d162504011241d80e022441d40c409200f0b140d040c01d02c940007400d005142004210107904075030000c8082c03103d280b0705500144c5000059405940b0050022100c03039032017406481c914042e0380b41d1031000348500c1000100707000c4e0124210070302145d50b42e802550095910741c070342d082c0c641a22004020364020042d000002e14a001c1c244a0740340c00d03205590040311507088985000340f40c80305000d600c00440d549040369000e58440c07030300240003225889050075100b000545508003481c4140340a80300004028103044e10030074507580034507401100310128402e80c0d4090141c1390400c45094001c50f00b0195030010040240100c18480c00f4010400da50260064000c0c4000d040c601540e150162101c0c0f1211030032031558006032010071030030202403000f4503188030342412498010300070306082 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 330744289 1250 330743039 330743053
    0xa12020c15030915010b0d0605030a0804050108040318090608161a2d0301030b09060f0c0919091e0c020309120309092805010807090525020a030908 65
    0x39403221000030030114420704126441c0ea946000141c00c18034101314040c41301c01120008174148541c003003d098200c1032800308104554590080c90ba491071800b90240c4040028031040045603c41c5120070f034824840d14010758583d18240445e051240503030821031105854000904c0f01d40d90401070754110211850340c0702011861b02c5030a4124240414000b2044100042c0c0e42028208030021458000c0740e050316018499006d0b40e1400b0030b0b4200b800200d512a09450200703a9209000401c607002d0b40303c030102c201c01a102c2420001d401d620941445401180400a80242c0b11000741d40c80e000345415800480c04101110000450102c1d0500044d0300a243c01010005194008203450003201b058a0944c00314010440c03042c0381d801160341a60b44000803108110303428115030a00f0000440d9030706490390140c01c0444840a80384240a40c180c150311002c81005442c405820903a001582031f91200e1103600f120001c0080b170303d00d0f031a214000d40c0c40044120101607210a54800420104001d0140 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 330745539 1250 330744289 330744313
    0xe010206061302032502060103020117090c10020c04090c21030509130204030b070f2606090c04051e1302091309020312131e060f0318140a1202 63
    0x1c1c42400303414509081c3d030200021717240e2001d005603203103c41c2460705182c038160322155009507500424001207000803224811090a941c02044403400f900f1140c0182a0108848050007503c44102500004501c01d2082420542d2928482e45d40f0007030080100203001820950110381c02e0704400d80d45442e03102c0400c0200042a400815200507482c203c0e8480c04e070000c4404044080c1c01240c20103454004000b003400310098000705c030050fa5160715190451400300140014219640100a05020814103000987c4034501603500aa11010502085080640310b034049041d07a90341003800c1204102c070020881103480c0c82900280c11004141c42585401d10600c00708000e842d544012947c9641c40c1c044a00c01c540c2c0a0007024103400e20501001c0c0c13a02c0d250040b0714213141311481010070380f100c08000e0381e5602402c145040242d0300c042c2c803a800b0f0409503048c1100103040c40d241c400c80340c090142158001070b50701036002584240c06801001c402d0342e80d080a031030019043ca10791055601c01d00c40466 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 330746789 1250 330745539 330745549
    0x1080d020d05030106030926030a05060f0a090b0406030614090c0306010303091203031d034801020f0426070608012603041205060a09031407080c010509010c0e01020606 74
    0x41520017a260200b001145442e20b500e00700441400d0391800c5c0302000e04003c4210703000c409140309010815003404184c8400040c02020711644603011780080c0741900a006160098102c00c04041000d030000a14079600d03110101151a210804582c1000780380501138400402c0149407004602140940115455580d0103003543d49244658803161640c00c020900781402071303000c4001005600d24068219034401d500399103d5103d5039040c1d02d04161240003003854540190007101540c0c0d40c41401031001c00803062299407061008140140359020020742c40b102c03802c50007800092a07048983c0540d0904c040c00b4280600342d42805156943c0038020401038541e0004216044450074009500d050181c0c4901a40750540e030343c52042ca91000040c0000c7c5810200c03140007400d80101e0684141e40c42d40f90035002660600000500000c44644460074084500b1000b0300d140d5108036441c034a000c80b80200c5030300391503080b2180380700c43c0d55031b401704201140c00100820029400f440500a58a09000010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 330748039 1250 330746789 330746791
    0xb030a090303090b071e0c1104020c10020a050304020109090903020c0f030f06130501050c0c070510051227031c0216020d0606083304030203130801020301080d020d0503 74
    0x18010544a20440041c103010340d010403906604000c000850345403011000d06100c200301e014000c0120f1800d120143c05215071002084240d02c08a50b4022426100070040a0b400680e100c4029020b00060802903c1c124030040000904540710240c492625000140c000304150384052503882c1007486150010f503022640340042541180c46410022204010074501442c01c800888c90b8812a018031550b8420100d882c0c01c994030500c000c0c401a5140d10300c003080b40c09089001c0748242e000c444284018071704598050791680c1c20749052814501d0094031801810000e5600302443c201480c1c00c6070010702d0300503084007900c000800447c0b0702032840b0030f0500d2041112071055269680400c1b0046004406c100c02c4188a0300102001514032082c10004020b00785071103a00e50521035611881200e42040003a00315019140000c20000c0301c015444442c40900100203c0450008005540022007034a074400b018100a5000503143d40c107181d40e1038603240362803948606540c088480c040c15664444122 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 330749289 1250 330748039 330748051
    0x60b0306130f20060d0915060602061b210a0c02070501120e070803030c190806060a2303091b0402090a12050c1003050609060f06030a0213120f0201020d0305010b03 72
    0x80715a1241c1143e0710070900703166001140d01c84400143d40816055982006e0403480c081c0b10490206844e20b403101d4112180703803203100c025800c29800070302d0b46140b503a2848500340070101035920f041900400d01e00010381840040c04510904d50500420600c41c0c40381e6003181d03159000402a03c1d040c0304c00030703001d102041582e13132015403141c0d9403031480d20381070205074010040c0e007080b2512403c040000000e960010307108014144148a0089280352061003804d005140150005240c110320100441c2c55080e03003030030400c0031100844a500360404e038500070361203a43c071407000c2c02c2c861000100403000782040061103481a801070044000781e030766200301c0704100d50700f00f442c480741414a0f291242c1480707030406069900078025a0459001c54043e0440e0344030391000c5480131801d0fa80c0008204e019a017060030250081814000102608070545c020310001030203066051150f5134030100c141d9070041d1410201c81e0b44840340441c1045580401c0414044a800c1c02c0c20b00a56050044031425800002c0c44 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 330750539 1250 330749289 330749303
    0xd061a0a060212071401092604030c030b04260901030c0203040e010603020a0908010f05010e0703360c171501240e1306050a0803091c020f03060103060b0306130f 71
    0x1300041141040120005500d4840240711100103400d241d42c21600c00140d0301d030072050540410358001480750488040c1c4e580702120103c064210389a40000300340090007186c0c0208520002d03100740c0030206000c59524044e000950f50340c01640001002d030b407001ea05030030940d0300c03e00c0306000b50300d0341c0c2c00c421781996124a40140c5038000d04000302c908415a901400301546045a0358012100c3da8005034103072145d01008543c1c03a202c854045080340c6c208900d00441e05880001c44642104911070400506404d80c0b81e81d000301c0071502c03141c840d03403c1c6e5800903103410300d40181503214540c18000e0403030a49043c4aa01e10543c504038000c041c031703151100c5040c40f14000c0300c03401810a00501c24604104409051031514170140c072514002440d580c011188140d0043c680010498000821102c1020010f02200c081032442c0e41c0354040000507001c100da12940c400c074004442e8404214140c02140208008100402040700745418404060000540e0310507070140703040444e80e40c10f160316903079610a003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 330751789 1250 330750539 330750547
    0x1003121b0f030201150602010204060315230a0b0a030b0301050a0e030a11030f030a090615050a030f02030c031504030f0804031d031213030213021303200d061a0a060212 74
    0x1800300e006103040581080311105c5401d0120710182e05501078801d444244c1c40c02c000800c0024044c0000384001c0c1318032071410005044041510090030854088480060007906603251540c0c500032075a04100003800009036128054a03003884c00340074440c0c0056650004011441803041403540320300c9500c80d09410310203105e81207400c1c1982081140c45e50142d070300c801512820008820b0f000341403446c030305580040c2002e2220301107582041c00301c41142ca00802944a00d07203540d03611100f010300030030103030780c1400ba032207070221540c800340301e441c0410390750640d92400b0f864145000742481d5000001c10040000840802c00040e030400d41112158008040d522621107074000000e00d041a9128451800e0070080303440c400e00c4130441c1000701aa4801c8808414040c0c10313214180480c000c21501d00051300b0501030820114562030170340c15807000115031403d00707141740801180e1242d2140604642080d42c031071402008800402e0b0004d05402d080764200350262074110b00070b5a8004065090990b440005 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 330753039 1250 330751789 330751793
    0x40f020a14130306090305030a290d030504030b070c021c03020c0d05160f080d02010504050c12120c03070210030e0606040e03040302220501050d120305040f0206031003121b0f 77
    0x181c2c9002982e1101052000c110f0a00e030090040d001514002c0f40356040090998400382c4a001d0019071082d803400c4105111121010452084000401642440700821020000c103121401d03841c1301d21415102c0e60305000380c80c8180308142c202825081c0408294082160020394041100661043c00316080300304640d0505010b824403c100d00007a94401c0580340c0040d130318090340d004a007162240c0080d140d015004207007d0342a12012a00103115401515a141503842d1a41c03115000c050041d045455840c0e8803450308030940d110704142c49080c1c4c000301e01030b0110701c0c10034400168290303140f8007031080c240c007009010f41d940e1001e000e9610441d210803240b009440c08000f03035001950000c16450b031a04031040720388001c2400003400113406003403400101d06424600c4003a029550301081d280002151007904400a08001d00101c1d6148251140a405030747c0d0781c0040c50040c603901400300140c51840c075010807003030f5502c2c481d130041c090900484903441d00c0700d000c034060443c0c0000d07009694042d24 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 330754289 1250 330753039 330753067
    0x30a0f02040503010c031d0703030c0f1b0b0c010c050403020618030c150c01050105030a03020304090c090f3f02090c0c0115030b012319080f0c040f020a14 68
    0x1d900010340542ca000d188034101035168100c440a614511000704000c2600c0d0011515140140006004100c190700c5050008000c0c41741d082a0300d00900000b841e607404100710400600f417550020a81200102c0c402050040170710500c074a80c0d1490138100c1c50245140d000c0391090190444804200804262031031254409104c203082d1284002c0c207543e41c0049090600b00c0c1c5400020110035590302e0540081040d090008201e00b9054041c0c004608003490006510080d0041c1e81a000401140b46c10015a1118103100ca40240401c890071a00d00c601100f84000303034494044100f22581307200003501e101011044003098919406982d0900c1c240d4070b14035440c0192044002407025903103004100c1115280105030807050768480c640050080e666450240e070030ba4000e02d01d560341c0040844642600d0b14080c01054001800c00d07a07509041541e44507254280b10820816843c80c0e08240d250b001d2600c0c0c140700704480a90408400c500b0310f4039180c0c00810340b640405a640400c4070018100000c0303009 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 330755395 1106 330754289 330754297
    0xe0601032f090a06080f011b0507020103091a011a0a0504090c2d0212040b0703050a11010504120f0503040b0402132004050114030c030a0f02 62
    0x41c40303107110500c0300e0881140c4199161142500c4040c0c89042d14503114003501200018100e20300710702c0604009403809074202903494504d0300d0440410401440400004607c0c2281d1210051302c0182e000341380403240540071149030030722107684040b81401141a1175000e5500441042d05d004400d20384c0c000c0d14120000305100f0b00080c8008040c42c0c0c402c00c0120308d1440e021003029988080440c64a800d02e07081442e241e0040e00301c3c18610f404025001510100341806442c6c40e20b40004c084071401841001001c000e80041e08100d824412000c607043d041240380200034904052822424540501c203c050105407400c4035040781901503410b4030b2040750400c0c402c1e03000d03a960b5401c00c0941e05a00304110749581d5a025241c00c00c440150325104050903840307415546508160000d001094101c5004040400410821034803012100940703800c0440b500d000310f6400360803078058010380a = true := by decide +kernel

theorem cover : BRFrame.Cov 330575539 330755395 := by
  have h0 := BRFrame.cov_init 330575539
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330575539 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 330575539 ≤ n) (h2 : n < 330755395) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
