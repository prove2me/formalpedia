-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1476
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:09:59.607985+00:00
-- url     : https://prove2.me/submissions/2e98efcf-c40a-4e17-9944-1409281cc4a4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 265287769 ≤ n < 265467625 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 265289019 1250 265287769 265287779
    0xe070b160c0b0a0f020607080708040f0b07030e070807121704080d050702090a02040b18010e030f0a11120709051f1701050705090a0902070510060608040302072903060d06060807 78
    0x140318a45010304007190700c0842040111948002e241e900484146000cac0482d40359424050300c440c901c10300241841000348144044070741c040c3d10000c181e40c01c81090b500d1150755900000c1e19180940710307480c04200c900b420342c030000c0c0070350080c0a102070003010020304054a81c510b86241251110030030380071500000b00300056190075444240e10030031000f000d40c034142c01c2900741c003803030f021300c0480840d506141c1101c400d1603030041c0840782c2020405822210742c068000ca1a80d40c40d640c007202580d9103840c12043d00c0b101c0c14044082d1496031404401071213254a410540380007460014006e24980c122a1210085580d101d54440010200503d10680355240540110b085640c00f42c000414403404102c0180f42d40c6480c1001811900481c5006884984030b003081800c0041c0340c5201c0d580c092806d4004142950800c0c40140510300950848603070b161181c0d04e002007804c2020031200001c0c41d1005004c1400d44002c01103030f11507000b804c1d084d41312080e035466005540d116004508940c01840342400303 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 265290269 1250 265289019 265289027
    0xf060b120f0601090b0c0c06030a02120f0702061f08060a0e01051003020109121b030c080f01020304030e04110714030307020d0509060a0806120312040212010e070b160c0b0a 76
    0x5001100640d9240700303400c0010002e031001c420703486400680400804c51002c4440c00388001ca1043c0b0000c1d2645550f440c1040000c40250721800030009844544004034854920030b8030b22902c41c2c0750710b80017095181c03190840442d5880065484c0300490849020214043c041404481d0041202d9100820b044d101c80c00c10780d00307480c40103022005507a0031301070800160307030311400e140f04031180003401148c500c2403803c25072104d20b091031042d8142c0050720740010801010310005001c440b401c400750742d000882d61036451700742e10007a10050002002c020f222070191410f68026195840b888115034604003055450050f200702c0c481206481c0d81021042050554061010141e024010b1a0051a1865400000d40e0300d0080304000d004001c000300002d125a2604518040c0349143e2108a90304ea2450b11740b0180031000c200c8040740508000c01100640e130b0300c14052a02c0e00c0360054050f00580d0f08110380b00b009034100e03507d800c104214091202c00410b50181c0100043c00158001c82d56a543c2c6001c00b0f0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 265291519 1250 265290269 265290271
    0x406080a06081c03050702011d0d0320030402040506060c0109200102160b030601050c0a060203040203010f020903060a0f11071a06310615050a09050a14060304060f060b12 75
    0x100c1c46400c01c0100c0500407003c003240c1043e00c80c0a041c001010786a14800300d00401b51b4030003035035088960340c0d81d0700320f40e41000505070a0700c1556542480f03491051400d0f07402e030031040320301e80c1038070042170010600600c1c142d04040c0d40450041c0101c0d007440d2201000381d0079208110401d5800700b10900100000c0d01c031002e08001048000e000400400c1286212001d501d081445030305103088010020403041ea100b035080b54820302880003100c121041d50b061410096200345c40492203503190448808058002d030090700c9403040f009029041030f64071041100e02500b00e80081142842da1000e02c04095641c84000d0b00d01c1034000c00c15880300c01d125808048803040081d24031817203021001880d00384500351170f0b03400c90954418980d000c0810004030010026007480d0704421604098050040503c1b40c1c0308004e88200125640c0302045d440c0c0d506e0a201840001c0c0c050810282000211000941810002103400030311a070030008141e03111045000c00c5032500d8100d040c444100046401500008000003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 265292769 1250 265291519 265291529
    0xa050103020a050d0b0301060b0c16050109030c2106051e0c030f0403180509070f1d03060a0c050408070e010503150906041403120a2c03040b070c08030406080a06 71
    0x85182c01001d0718081d01501480012018603521420040314648007900310400a040784600c40b61241030a10119440e02d0345411550241001e10900040c20340c0710340c0c0d5080440c2c0d00104861203950502100905540e4901e101c4400f030301d0080304240c0001c1d2540310303180c4100a11841100081c040711041c49907040082c10010340d90b407045c0144601020301d228025001641402d04803407822084041c1403031075800368400e078ce00003040420442115007104646042d0120ba544002961403440d0101e1801d003c412441a05a8000c1001940f18940356020003c1c44180f814054105039407001e40320314040480d04150090301c0d40350010066030501300401d5114034290201200e40b0300d41a011a9504c80d4010302c05803140020302c0b11a030a03000144200c4000d004e5444800c1c0309890310b40182400b800480600030b0304484504045a104004480498007100c441c1010707515140c5482401c55168002442c01d64906059903000250010208002c00c024034032070b155000c1c10f240040d8010700b00d038119400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 265294019 1250 265292769 265292771
    0x1505010903020604090902010c060f0b0405010b0a0c080f1e04053303040f060207050d0219170a090803040806040213090515040c15080610050909040807030c150504020a050103 77
    0x10710040e620a0281c80960b000000c0004200501d40012580360000200140803145014425000744100342c2145262701070a68045c00b560340d80d1410580548070b201c94002c0003603000d401c00c000050b002c07401091518510b004007401d00141c1040454030b040c0e8012100000d030310029007005981400090603904103c42d000d001012040503024050a845400c941d14448500100003820805400b01a07098140c0040c000c41d102d801234a092551000c101d1042070151280e0500410204100c0201c545002d9001c0c0e0303487c101800000c450049500409001c005101001c01d020402807020005000141003580041c000c0b805d20b070050205440d04030303a01d180d20504081c00b5001007100019a448240914404200300365500d050104104615421041242050300c0c5141c101d20380c0030510311300800b4120707058003105103854415070700d51286d81e5010b9000850307040024003050b000d90103411201e0080c00c0c00a185001c0780e4034004000761400c16011407968610030b11044d4101011100050602824 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 265295269 1250 265294019 265294037
    0x40201050706020a2f010b03030c100513060203040c09060b040f060806010e04020f0c0105060909070308030915071e0309051216150b10030603030c080c030c10150501 73
    0x3001032040c0e660151450740c0000c1c01000c460303c601200840f8690514a942e101e85042c80c003054070800c0000305562039070070400a070a543c900841283c0c0c13000043c0e030082610100e00a10540503142c01011081c1c000420581c10012400c030303000542c03040348501c02d041101d90500d00c0c3d91048802c0303500003001c1003030207010600c040103600000346c0980d0382c1c074200451141c1d640c0d80104d440c030482400f030a400900104040b81800c06034005401d1481802000f84003554588051150150382150301740c6003035200040c10000b048a600040d074022034150b060f6254101d1300c0136284440030040d5025030004250b052240c45865540010b01848034440c9400d1001414503250140d40303042c5c0f496070070b0310704400144100c3d00074880c41c2c105440e554060100d68a680c20756008000030850300081d14001c1c00026101c180b203510a1055400352039068482d941d46544a03256400a40c0051b01036000c40c1c48204060710540d201040308140050f02603202141202c1c44007218180c1008981c4a6814000e14234 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 265296519 1250 265295269 265295273
    0xc060c0712030e0f0109050709060b03060306040201051b06091509030c0d110a1b05040b09010b0313021c050f070602011401140a03020a0314010501210219051804050f030304 76
    0x14501005010700d0082040282d10f9192414a46030900b2007501d58a4029910304019000c1041c070202e41c00d04d4802c03c281640e0b0600412a4031013103401a9054002c2000600150b0069001d4841c6400340080e0b500daa451824402e86007a2094803101e18030791003c844420000d81c0c8184c20755000304041d005e10305158200d40c02c81d680742c6014007000244550108060760001301001603081043d0418000d120341541303131541d0100060307075004072801a402c060440f01541402800c0504035481c11f00902e1440e034400d09240300080e40030100700d070320500769031a003401c80c3c0ca401e00e160505030054000c1d05403080411a103070b00c0d00110781d11000035641010380019440211111083c112640102407000e0149504009001035600d904000d52010500b0808024003e10b00c20f03a29021741003800811980e40ca41c03c1d404100050010404000000100b1010043c100ba081d01da01c0c91030849809003085888400090351100a09404085a20240304020074008200016400a8042c5014619504090b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 265297769 1250 265296519 265296533
    0x519050a051c0519050c0d08010509090a020108010603050408040b030a23070f110109060509030c0709020405060a0c060b03011e06051c0f11040609020403110406050901180e030309030c060c07 84
    0x140480c991131140328066824424020000c8454021404064540c844a40c00000d0014a803c0c040da500801d00c000c00140054030004003181c040ba0140c43c5e20000340c0c0f038040200c0c00341078010011100c4417014400010540c000101a501a6000010204208440b0f0009480ea1074084010700a20003014091000c619040300b811100000c0e5072510920b0a060030b1132560140c420a003004200d035240100b0003a0700750740400908800f80c00318050394400d03a9550942d106a01960283c154807040402a44140c180501e00b240001ca106040100d03480c3d0700f9000090031507075060300c01100c00c0004c00220000303040920502c0060101140d40b8100301c904407001c501550034640008001c0035400301d20100f808415020354000e004014024407040e80c6030003172076019400c0341c84101d0314010708101010403858107004a4094880180c030180e050fa10b1704000648100d080140086000d503030383c03a12012050300f800198450508003000b51342c5c074a240c2a000d803800c03800908404116005100700400a041 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 265299019 1250 265297769 265297777
    0x50f0402060307051e0301030336180b030a080d11120112080c01090c0303031109090a02130504020414030d0906020a11180f04031404050a030f0519050a051c05 70
    0x8a440c10517110210041d85044480307000341d0100e45c018020000004050348410070141405004103000c8082030b110300003001c1c40c41003803c000510040740ca400e014040c140c5c684002c50403120240032500003084800700741406906c0301d041c0c03900f20000840e428000694001c0ba00c81403040030800d850810403e252020600c0c060003410a40100740440308240504003040c3c81c1c016010000030004040fa91410004441251008801203030030400000d040b913120109442c401c16004d00781406a40d034080c10340300294404162696010400140402c1a44503440034101400040c1c600305807250b44c0c04105450510820710100c01c100715540c00344640c0d83c0c0807030341c000318a40c8501c1300000d042d90340380003840c5071075480c00920121041d4020000c000d801c400c801c0d0700450198139a034171001c441002070300c0f4a00c12802081d2304040d031640100001040e5220b0040b10034061001c0e0f0301c1013220662101991017120780c2c240c4407070f84245100002e00005200c1700da800d1403805040342010f960000c016041d805 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 265300269 1250 265299019 265299031
    0xf06050a030b060d08090316140108040506060904020109081510090603080703050c0307140102031906080a03110106050d030504090f05041109091e07030501110a0512100506040612050f04020603 85
    0x72584c1c0210410030389400b59285098002c040d0b6620b69004591001703148914882e68800c0301442c81040825400384458501803a00134000d482140c0d0b6882c28405513400141040381006910302c8000b52403c0140704ca4401d440b1485011000ca043c02082c075507400460b0741015495038038003582000001c80140c101d07901141d240c10580d031961039a00105045004112000d004407004003c504215001035004521504031800b000a01d885c1840720b2070203c46079402003406e281d004401700710210f40501100c55010121100101c0c01c1d503220000b03c0c03580c001004c400c40100720041401c2c405004240612821081158030808c01131400361100303100f1034280d21800c0d004040110200360541e1040c00620780905a1590700985d01280d03a86060ba174280700d1000342c1d585e52138618400c4485100303502700c0f00e200c1181e9490394100300302e142c600000440060800c03a0310340c40b40741c030018064503164040c0c0000d1070103444160300401025101000e03a1402402c10f4040e80c01e40741004010781d148002d0301e802c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 265301519 1250 265300269 265300279
    0x31629120106080c090d080403151406011b0c15080106111b1f08060a0b04050906190e07091a031b160b0901150608040f060b0d060f0f06050a030b06 65
    0xa1603c404d0144188600d00d032213504910410401e8091000f0003006200322840b4014128040700044000380860f40345450510007144a100810b6503076100b0340d80c00f111400c0c06030110090502540d1890030201c0036038401040b0b44482003514082d1a003119030140100720340d04080302035890315140301c0d442d8550302c04410040c00ea04d0000c000180c952818cc2318040e910304801001c3c109a40c1d401902c9200201c3e0503910a800d10080810b00a011500b5901182da01400e14141a121703c010095076511210103004403801d0352200160803040341d88914007a040a89a0710390f8203050050402a102d5400e030207403019a810001d100300092072806004034114010354140c3c40d000900c40841c0c0503110303910054002008201442014001940155426400341000c3c0c5070003565640b0079a0030b902d00301c0c1c0c0604014030403d000e0000c6040d80e0000c8100e0300300208500f81c8002035540d03841c200e500407031451449581c1d40e85480040e504a2080102812040326210207640c619910903002c1c1e00300500e414020 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 265302769 1250 265301519 265301521
    0x40504020d09020351090c0301180803011701020f0f0703020705010f170c0408030c030415091802030405150a0b030127031404030606080d08060613060302070203162912010608 77
    0x4402e003500b2841610345405041740182040c4049030369500c090041d45202c2d52902d15200808001080001056130303024804a045070318000307020540741080400451195020840003c041015070003c1846800440180b9110406402c2c001d1600455070042410b0003080c0c40110055034200350323420800500d100405420b40e9425011259034090b80e803003221184030108501d450b0f10008130140003510205841f01118404008080b01c481640d441211481e5180b8411090000c10315002103a00502640486000d41c0d40b0750789006a0f010100c1c0c42000030b0f540c408001c8150b107000e0081c1241025900550207500710b03910048410150000c00090904c2103004016071031000d10000c0d60020350304030104210840c0d451040c29240c0105006200c0080c03a40000a03506250020903140a050f100300d80881050901c00241c0003540030300400d0ba031510070451044c0e0503c440b01d500c00044d001d0b1f00c4112009200742c07400480d030900d20000d80742d4100001c0c0708500c4c800500385203540c11103c039071600d4841 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 265304019 1250 265302769 265302883
    0xf0b09040914010c021e062503020403020603040b04050c01020d02030f072402040314010603110f06090a15020c0102030304150903140c150105010c020306070e0105040504020d090203 80
    0x202c0c040c00500b1144550070811640307030355a004140489082e00480403c502007818141460720350f14122121034000c40301c034480c0c04011102d80c080c04040c8441c2d003001490140c880d00001d02580003150101da05211050410040000a00140000750800c1c00142030380080c030500607449005a02c036205209101055502c280120300401c28001071442c54100d021031046000320010b03611a00065030642d8441d8840c194100c0148a91011030342c12080791041c94140604101c880811001e049510400620072003d150392000510002000c428034400107503150410040e0400828007200f0341950010300030000030132541c0040301074940007040002950034141c0340c140c0d60907182540705506828080b581100c0709000161b540c540c040c0c968142d074020380c3d81c1d00044855162160009401d40c00c4280400c070b10900800180102e888141001401c042d200e2000c41d08903000700c1c2021545a85440d403c4c000c2d410300b4001100000c1181d0f4811000420b00b020302410368041a4014509500008441c11 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 265305269 1250 265304019 265304033
    0xe0606010e03101a09090703080f0d0b040c02010903080709030809100302070f11030714100e03030d020a05070c06030203040206030114030a02180f01092007050f060708100f0b090409 80
    0x81420011010080c1c1240550148801c00d0444c09107400f80c02d2820126640f82d800245400890b42d00620462425200d48401c0c40700350420100a030905407030b00385014859680d80074000c5490314550000401980d2400c008007481c0b0080e2070b01040c001e41d02e1003880851140c00407a0010103050710420020209454100c3c001c1c03198000c00b8017149205148481046507401e03a002c002c50084048548190b1603a0261420321090b40303400303a1021603604908000b90040740d4440818200030240c138144481034444a0a0b6480043c001002640003c0c01034204001852010041e0400d4a021400c624091b070209801d48811300503240c2107100b1000000250382c04202040d00740d0f90107064444102a401d405058405054074440100e491540c000304203041c0500c268501000404107245594a1207080800d07242d000241c140d03940c3c00350400d44134204504000321409900f45684046d0645403248090000f900c03660004c00c0303048081c1c002001032401c000d05075590703a40112000200d101e09464513030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 265306519 1250 265305269 265305283
    0x50a030f021819110a0c0f03020a0c0816080a021c1e081810120b060409020c07210507140609090906060f030a0209010b0a090b1201180e0606010e03 65
    0x42080740004040120303c4030070551030150210380350024089075021200854050046981c01c0001030a200c0b03a60000c24924100241b600c0c3c004e0064500402242d00e8480d8030175460340008030305034444c40c04024042c010b01c600c000105800c60161400c40c0c1240c0c00941550303a0380d001015010710350b82c0614103000d003050380540380c240c03500480c540c0401c0740c0c507114070150044850235000040c1c10494031804e0901094984214603941d4564017004410462800100142c0c0001500310740280000b044201032480207200210342c0b40c00810305d00b071500b54600e0a80d01000d856603951031110802030b000520000c2c03c0820b5039120401204031700705400c00302d626400344524040d4810303042c005121581c1c50105800e0702600c41507421654124407441416034541c04413000a40121108004100c40500c41c005440c003c10742d4500240750659070b030f540705240d8001080c8131042020800042040380040c3c460302d07203210b800000620503218040580c6032101e000411072030601c68802444060340e80c00744202 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 265307769 1250 265306519 265306549
    0xf0905061b070b0c0d03050a05072f0604050105060f030304081002030a3c0e0c0d0501090515010e060907051603030e070f17070f031b0312020a0510020301050a030f02 73
    0xc141c81c1c1c44800380c41303070781da801140401010074640302c046110000c09008103445206641c4a0701074a05102c44c032582c544181d80110364140700609001110b55005005080c00f4600843c004205414404208004241c038010980d03c01d9108100400521001007001001078101c942d00507265a1a0130b4180042c2501c2d4090010011003899581c61806500c181c2c1d0304400003014001c982030001040c1d11080321540a80c0b411207030301482d4124010301c0c001c18407181c024801d000201d0001d80c90780d95945440c80c4089403024228011006020303240071900450340c8140f04447c603080f40d040416002d05548140040301c400c0f03910080b00d00e002c0c54040c0d00083c41c015143c400f160005a07a46503000c400c005103010720310300b400f141000e09940d0070000450400b07440110020317924141c038541c3c41c6403d061240c0a482103041714860300101213515803155103501449030300a009800c45520307059050501d40594410f85510500050020341c40c4c0014602c00d0b07990049985032003002c0c074000110012114481c0e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 265309019 1250 265307769 265307789
    0xc0a03030203070302070905070e152203030f0305060105030a090203070b04150305090f150a2306090a06080c060d0204030b18070902071212090c0608070f0905061b07 73
    0x4008109940007005180c0940650301340c524180d00c8100c16010f503001a61a00d0004004e406400c6442c9007910405401100c0284051300c0d000c00c0d0b29030780c20030305607507005031841d840c864400b0030600d50440f02c2c2c440020311620f010806807030908000307800c27070002801100d2502d070745104840854034100501c01c05045014201500c40e03903500c80307103001c001d49030000d140003e0030080810461440001c0d019140003004010389805c2c001c40b80c2d4490708860041c42c502d800c03070301d400b51418070145800c081e05818121602c02005440c001c000d1005186c000f501c0d034414203203051020007207203d02044a40403103034100c850958600041c40752802034011a000a00210240c00a000301e9580c42c2e10102185e01200d4140c508070750b5904c00701c6040703015015000d8080842e041200c0c0d8014880c9038007406080c43d4032000607140701c0c50f40321582c0012041d0080c50101d40e40c142809801c0703821445000f101c00c1640386c0288224144008a0040d00811041c00c8081d8882e04203084c9903201408a00080e10034424 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 265310269 1250 265309019 265309039
    0x9090a09080c100c03060e010510050306010203160c050f060c150601020c06180a050904030207120611070605060f1c02041a100e1914122802040608030703080c0c0c 72
    0x7500f60b004100c03004288001c01c2c51703e5030000d4400c601e0b17140c01c0d040f603400412519106142241c2651a40d1000b449a8114003007000358407408680c2580740e1442c2409801d402d40043c1c107082c14000f040007150085441001c00f401a000f0080c0c00181c5100401401e014210a5485100050b40340150103030310542c0c020b50101e03107400129200401004013800c1110502c2c101c0c0c1e503a00c10301c4108402524003400580104806000c0030441210031102c00340700300800a08610034812102e484c0c0c108041c100e482c0340d241c2c000d1002900d0105580881d42c05c0890f03690f0f115000079100c840740900708080003401562120a19041210303046a4150303100e80243c050b020796558040000c06482024104a115246c0d800d002655112822800000d950b203c154071140b4000040c1000054008c0c90251400d0388512410007583c0065015001c0e6406e81020764210091014410002540d219070402d0007158010700001000c21380c010561500300c9100101c4035580c1140083c0c2c54100102c01c9074041c0c001080c00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 265311519 1250 265310269 265310293
    0x7050711091501211a0a15020a0b13300905130908090406080f010e0304051503091006180e030a1b1106030f0402010813030509041d19030f0509090a09080c 68
    0x14205c0b02c03130500e04031052000706403a00c5200600241c0150010300581c0103461407030009000c02c0c0f030640c00105195840000550540d039441079501e4500c502c050440b1700d8031084c10501d032452003180240045007000350710f8606007400300709500c40300e440341302d500b079200c10441c0d0604c000603040f541c50001c00741c4144440340d2a566040e82c0c0c0c20a440380080f69607e84102b503400000080152001e56030000d08000a0703001c43e07803000c0842e800250060480d0b004a400300c44144100344601402002800701e6800061100071010003190f81c04444180240c1042013050700d02e9074404045e03a4003414503c0c00b20b201c0d445604184040103807440d101508171400005106105890280c1148114401d0346d44400681c2d4500400201c0d880c00b24004021a400340075240e15494160440e80c2a0041d41307030446c003000c06031314210f494141d00218400301e0710000a01c80e0242b551006540d101c0351542e042c1f1600d400b5000000c85c3c5102c4d4000c092125041e9104400c10802a901048400441419044440c1240742d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 265312769 1250 265311519 265311551
    0xd032a08040f1a0304020a0b0702030c1e0f030601030507060c0807060903050711060703020607350108060108030c0714040e010c110d020106050306040602160b0705071109150121 78
    0x15019919080c3d01d851840c2c401c40746104112403050303902800c401c240e98500396190030203410121080b42d25004018a4017802d4490b804500c4854440c19502030021040c01c0a00c80100140300c0003d000741c00250041c0046200094004225142854030940f03200440c1444d142c14003400d20001c04280c00c10080074107145d40b20000d891f03414054000060500e0410382040103910a203000100541c01900c001180c490003011645c100341100124030075100302e18482c44208600701d0100340a4290310340010300410408012180c05420408000c41c078114903452480d07501c40306481450010822441e00101c1a15246c000c0603003070030070b1340080c00b000410681c00b80200201690000c110301c80c4440f8012070074414054541158400340280c0b02d0740d107803904d03000003035404007564032851b2045405034000100a0501c0f1841003415685281c0c07959540c1c90700e280c100003402642c80c45607201e50b05008182481841d0300c1c1146009007041c60380c1c2851869003401e402004550540c8039071a0060200c00f01e280 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 265314019 1250 265312769 265312799
    0xf02091e0703060e07030c110102071415010807181b1227081b0d181401090e07090b040b041a04031e03120504060e0c0d032a0804 57
    0x160544540c816598803100714116442da11a144100300203001140c0614000c0d888001420305524211000c2d1201081417826680600f00407501c22a02104c2410640c1c0248040720950004116082241d49820b40041c1d50b61320b103008603030702c0d06040c00c1d4510400e16941d00840640840c4100c0005103a060003020f001a40070800c8002000c0c1014103540301c07401040b0040100410410714442e0860241d141d8400c11b8200420030010305048030b00240d4004010040e295010019588800034240717030b904400300742425a030046150b2054a02c401c400750703030002d05407070035156809200c0110703603070b01c5601701c03540c2507031390f00001c0e101d0000079020840d84c40b082c0041080d07603951b00c003100a10f460100303615228443c620000d4408048009620f4000c400a032000c04500d01074075062490140c0d003c02101107400544089810540d651544000710105210140c820325080f18512600c50b040d85024000c80f00f0343e00c26002180400761001031182420201a07005500040b0007911162180b545040f52a6 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 265315269 1250 265314019 265314061
    0xb0906041401060c030302070209090d170403140a03181203060b04140409170f04030c1202031002030a06080f060f010e070203070204050c0708070506060906101b0f0209 74
    0x1000014019003001d01811035107003414a4a10240e82c40c11000310b490400ca00701c1101011307001c010f024051780e150310055003e086d82a000d05160400305902516460800040d5140000d076242000042508929a090100442c5030440d5130341e881c0301703c210003c0800746850f80c100d140300030005003400b00700c0d850192102c8054074200078042e102d40500005001f54481c804504080d03e2500c40745050541004518a110b440b204003c0c0341013001c4d10001b90850080c850101e40007103002c000b400303042c0141000400c003194032060003082d690003090b01c51282c1d40440700b155130000041030780409150b00940003406260262070340303000d10700e49194944a013540c20040c00b100203400410808401420305000f020942c0007036291003165070a110240c50300800c84860360a060000002155458008280c1248100007408007403401c0810040038400c00341c000c42c000e80b00d034000c614010750090034246100c0e802c0a4a002e0490756407610025004d01d0000c0250004c0000c030522440000100c003070101c1e15 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 265316519 1250 265315269 265315279
    0x503030d0905010e0a050714220b181519080d030905060612101a130c020d02010b060913110a02070303030606020d0503011428050f1f1b0b0403030b 65
    0x140d081001da602c10302c1d504041e00d55040047d0422880101c4103402d205900054061210080700c0e00c007030040c5002c1c02004944450311380b48084807902e2710310f55482c1d00440b0040803040909000160001d064085020f03180210002c80c481c00390300b01915160801814401c08403468403040600c002c015001c000b03000c40d03051003040e0104480385800040c0d100c191202d403008040e07031084040100050503043c0044c90f500a14071800603d10b40f18500d60f04101d0524500c042003154081034001d2420202d01c0c00c09046900d41401a80c0560f6000b04030f8018079011502100c102d048220001e000f00555091000d0500c1c0015000140ca40c000c201c500440780603413801c0204503944d5205036200c408160300c000006104000500695544415003840928080e0080311203c0f45c4401a416401801c0020481c07902051010000d0b460b00701d010307000c80721064070f0204003e0068000350b98508031070155038060195001c030b80c2c0080700b4410800e0503655089451221682400e040c050003c10503080b049000e0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 265317769 1250 265316519 265316531
    0x80f0a0c060e011a060306010203091e040c090608090c0a15030f051302130203010510030c0c140f0c030f100b030a1e03090b070f020411090d060506010809160902130503030d090501 79
    0x40c5c83d164090ba8420307441178016600c2e201e4813108015131070a0101d098400d8058400303070440242c80310b1080e10103030040c9880d02c00e40182050703030250130701d58001c00091240d0321420b1a85c0c51a194009141c003103c0248410b00c0b1811905c1e10260007800322100000c12040c64081006900701400031016109802500e440070603460102505003a44001d02a030f03900255049032004940380702e41d2001c40041898540601c850300c1030b6480d5101d401407590808015801102a405c202c54113200503918100e08900615003c020900708546038804585034402c0c603541e8503103a00c129101400380c146550ba01000d603248642d4400282c444442510300c042d400030b1290a008100a58440200c1e68860382001200307541c00025401c21020300011600901c51a01c14480e496007522006441190380c0c1c41707240007140302e181c004001000020001e10001c2d440e0721011102c1e92000c40d600480d02520b14028025a450080703c0907007100607540c3d440075405100018040017034000c0355005e40780040c401c500900807 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 265319019 1250 265317769 265317821
    0x61b0a140d020705131b121a0a030605041106030c1905040b0318010e2a010c02060403150b0a0312090509090709020d0e0604030906020c0607080f0a0c060e01 69
    0x500d003480c4011201682c020881800540385c803001c4200d80c124a8440450400440e00c4000208000c0020034000326000705141c0d024140e0328041c4403090507540c00d074004008000b80c0001c8103030505100141c000e40d07441000c107041c00302010301007a1140d000740c961a80c905000c0c2031024107612a4400c1d030358608021072441640d070b1080d8126000c80701d104001ca410354490702c00d2070515011506140c1d2440d0750f100d401d8141e8010910550b0390380e01c40c000d0707404c2c3c150024003800610261200f184038104046a954803005a0b180c4050700c0c103482d0010f10014041c10107501c0350b0024041d6500d07140e480300c500400082002010800142049136a03910342444590321000d00060050907100007940e5040340c8001c1c00103071490742c0a042c40016114020554010782041141450b0341a00d050b000202d5a100c14000681c040088103950301d400ea805501d41646511110268090140501111900010b0b5194568880c01140d0071550700700302c0801c2a881c1c00360301c003802031a00101029840d4820740070342034 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 265320269 1250 265319019 265319023
    0x1030b1501050d0e0c09010902041e03210c0209010e01031a0105010e15040b04030b06150c0a0f080910050903010f0b0a3605010e06060c0d0e061b0a14 66
    0x21948182c58441c202202c01003c03001400b4800d00d07075a401c0c400e1710b000d070502d90b0b526040c00703000344002c000041c0da440c10040443c4010014181240403000040ca0070400680034522120b084514031882c0d034005c0138800c5044510068030740020350300134015070010419182c0e0958242c102da20030300600010b034042d81c0842119400905c2034501003008014070034800d007400f8405e1001414040d841d03600e05600d40740c00024641143c1c00544000003060b040002c2400c1c0041e0f145600c0312072100c1c050030404880009981c0791441e10b4001c000280c0b0301030040400034207006032a10300100170200100684000d02c02003554000d80c0003280b19608240140100503200d2080e81010200a801c1140c00790070581e0084000345008501302148d54000c60000302ea5141c88075072050036600c000c010860303500d00139440c000c1134006409144961800c0200d0501c00c0030025801041649506102d5104144040042c2290103810508070841400d0401418101401318840f0300c1123204140b5030b0115030301e00c62015 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 265321519 1250 265320269 265320301
    0x3050d06060206151302090a0f06090608040f02100908030d1a0a0e310506090d03052401141605060c03010b0d0e03160f02120d120b030a061401030b 65
    0x2652660184d003219000f400c009400c0301e200110030001602e014901d80224444001c29403282c500340341410000d100256000c0d800800500307181ca402714041c100f9881d10320032482d0080b03000384684000302c41203a40134068080c0c600144010300541b81c8644001c50010042c01000d01d1440955410f55208802403502e401400c00342c41c25903140d0380c925959500d00c0200420849035950f80344191030342c4c0100300c809404403502800d10682c05411309041408125250804902440091505090070401c4d101c41c5800c140314035984402d00803060240c0e210060365000d040c00703d85503030b1290000701061002a0700072040c22044c401c07800c0b0b0f4140d9030f60305400720301d5000030b0043d09204002048116021202600704400742004a02030781c4c9440c596412520280211a00850700c080f03000501400b5480e280141000d0185088064610b182c40b80b00024501d07400075a98482d065511005030b91b903918104481f07039125510900c01c010004441d2800d0003444001d02c001c0702e0f400c030807900150401042070945 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 265322769 1250 265321519 265321531
    0x20406020c040203060a03051903021005240d08030c070515060a03020d030509030d09050111010c020d05130509010b27031c11060c040504060e0f070309050f010903050d06060206 78
    0x603140107000c0c031082001952004e0038043d442000c0b184007002080c0c3c24002d4060305030500081c241e0b08246403174064100740d10805403111441ca0542006201082c1c103044013030100c80c501603410b8800240f07001034160361a05030090800d4101000b08080d000d4120b00408010340182c040b903503010b6002050303ca040d0800c0300c8450304200098810001420a0103040b070001c1d100e400c05504054000000c81e01c1c02100e503c850b000182c2812040000d035821000144c1180d440600a128500c80024040e5450006440c4541004000258a001d40e00c60f04400d2000d048002c01d10799203542e650005070000c0c3c00682c101419201c1e8054000e000c1d01c6000541401000040e0142a00244240f10602e000f40c801e41e89000344070010145070f40480c418480c1900c0b850038641e2007611582014148801c848140c0c02501000d4683c10078400c51039001503015900c13a130300e0314000c1064083c902c0e1613410080c00d41180c2105e503080442440405412030090200071001d2a010802550354941c08c86c1c1e245001d441d1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 265324019 1250 265322769 265322773
    0x702060706110c10022116050c03042301020d09290708070302010e0705220c1413090506090705030403030b0105091203070b1005011b0623090c030102040602 69
    0x2900029034030b6040090344600e05080941440030b050081802d18828124003d1032513400181400700c0b02100926000d10783da200d0802d107252a196909141d4841181c4c0c0f90390a1000204000208039410070454019281c4400c41000001890940040004481c030886001d401a0300341c00825520400241c1c0440e20803100851242403420b81e481e44042c0a0002c036403000c4001c12041c00410420001005031a119038000600347c0c041092440c1030881581101b03104001c1c106082e02c010305001054100c0302e03240c2c4400120f481d0800da041e941c4d04c0c0d20803040780c1c81e5a000b207075a43d0048218104407040b200c0e1181d090240e03030365000c01c10210220480e101c1d008a0703000d0000c100403a20039408030446090604050346000181000a80641040c051f101c3c011340c4002001e43c1006001030115811004580c240f80f5414244000600b074141402c0440e603081160306449002d1080741d8015400500c0aa2014445040da810b500305554504503000242403160a00c074070700360306051084a044488981c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 265325269 1250 265324019 265324027
    0x213060e18070e0402042301030c0e09100305070806070f0c0c061209060501290301031a0408040e0c0a020f0c03330106020a0b0115050403030f17010602100b06070206 73
    0x1507500c0e10341014242004000e09454009407545461000340050003008020201c924965801c400c0e180d000e41c3d0b50303641013500308095400b0054010f0320200321418200d80d200e0407551a041d00b0f074807155981d40702421030300c207a23100040e00362004500b150054685a980d0300032241601d10640f4460081c480061007402c8034042007100a110300d0a801c1c65014103c0081000764903529400281c0d034003a041100c2e8000541c00d1540c0e0001c040d1002c00c0c40300351041410781591324580320b6080d4202c0041c034600c624407009000504211245046401402e2250f400283c070f401c00782c3c2c407000d1582003d0020700243c03180c0d031480c401c80c0c2c0002403051594100100280302c6011804840300d040c0300030a513100c54070100d611201d00b048401403105070203044107500800c0300060781d00340740f40c81c460180c1c0941d40b01100d01c4040f4aa50ba4490111000d072030b00b60508943d02d14002c2c02c11603c4940210891101010f84800440d00700c0e40491203c04282c9c0c01003003401007106241c10003003184501b644c000d41c4900100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 265326519 1250 265325269 265325299
    0x3030d050c0d0c1101180c030b0702030c07150e010c120e0607080d0b0901120503070818030a05071a0c07050d0c1a120c0309100914030c010213060e 65
    0x50442940400920080c03410802c02d00b41d240d00b55220152458041080f0000c02d1050420911980401308800c0412441c3c43c0c080340c47e6261582001c2c00068805000c4100003042d0038000c000f1600c503d00241c04a03007034550380700304610489840d4140100000d9610148400541c030522510b0800ca400040c070113048901540203640c03400d204040c281d08040c00380070750b2010400c2d080184c00d5400341c4800205011100600b08000220140c004106803009242c103600440c000105960130a5400200c00350349ea4413500a0030030005e81802a07031340c544107510009080050208041c0d00700c030510199041d49603601c1005c1484c034081c040c541d0840d0350041d83c042141d4a4004440120940500d181030b11058071203000840101c4c0d41031441b2400d01c000103940360310300c1c0c40300c2003140c5c800d400720b5081b819400c01d1807070141c461321401583c0010a0b12808001700303106562400c4851510540d04503555032981117010f50207034100a400401048a9210008403540504a40101e10300f00608001c4819280 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 265327769 1250 265326519 265326521
    0xa05010f05031f1502060117010c02030a0c031b0819050901020a1712240a030f080702030f190b010e010302010f08180d1124060f010c020418021009030203030d 70
    0x28800d003841c0948580000382071219100250344c0f80c43c10740d02070002581802c40080381c8015641d07607e02280c0c54110030402d015804015180c15a10714a000c0c40c0008150804a6450040c02c1c95114642d400c0c103217013400c00003048000c0c2030001c8003400100e0201d105039010740d62800303607a840c50f0140e080962101c000418070300d05038000c0d079500d500071130404200e610035440d03070314084442500103e640760110b0b04040401c00201008007044450480315404d503901e0355002da80501d0010162440410744608555042c429400c0f1030b012441141c10700031075080c903240254980007040e9504a070010000ca54140040c01c0c09060300c1c5c060b15030202c00110000c0884030080f00408640302d041c606800c00341c40c2502444440d04070b41241d41c850a448102006060a114440c00c2030080b816041442604030050703c0182ca6018000311240c90b070000301b000060320380501400300258000c0c44e10b058024000003a10383c030000140251030747c18040220f9401036503000801d00000c1e61546c01481411703502d440c2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 265329019 1250 265327769 265327801
    0x303030c0702010c1a040212210a02030c06070504050a0920071a010f03120305060a03030e03030702300a031b0f0203030a0f020c0d020d06020901030603020a08010b0a05010f0503 78
    0x1041c90030051200c407030b0311104c81640c442000f08400c0040740043c41b040d8503041e030b0445000c03504840500111a09400050040c01080ca510958404041204d001d064000e01c141ca641c20805001e0720b0103071030a000300a00541c0030f03000d094481c480c14a008250100c003803007104062808100c03060340030301900344a108590003090084410482244010b005454003425490090003c2180d01e9070041c00c518004490b200c200206004140c03a00c0c007001002d45d210801b072002c813905030500300801640c09010a045208241006c0e40188072805000261040e80c0d0458204140c908106810030501846090f142c0110f880080c000503c0301e92404503c2044481c1c00c41e125206d50030500c0b85400300c0d80800d0441e00a80040004110101040c4802d150144880e00a010044455030001036071980010032151248801401c0c180d404982c407642640280d01070409585c0040c01d4101c400d5451001c1400f91450b40700d010301418100c42c0000c3c07654080c0740c0d258000200b036202c00381941c1d105200342c0c0240308 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 265330269 1250 265329019 265329023
    0x923150103111c0b0601021b01020d0c0203032109010b010212070305090307030b041b05090601021e010b04050103050709060902030c03060603070909020d020a1704080712022119030603020303030c07 87
    0x1101000c0b0600d072030031040600403d91142540116500d400000642850f089100c040120b14155049440b070381c1c0e0104005a010b142030070001e0144040780080b91450085030801114a15440745860b0f02041d000b620622405003075009018800215004a80341d2811f003a2002c20080305004560010740203038090051614042d0855054503526150060424000c3d28244c6102c030020f2204510050000315070009040161040c480c43c0c180f000000390741d00c482d4014140072460742c05203009409002c0d08035040c0c110005100f407042c0d58407800c0168880440d0700c01c10b01c43da4605000013804088034001d80e88074507603400005040d030381d07183c040c021b01c0c0d800280107804100c06280003090b0030051f4400340503e00ea65500041c1c0b540c0c0023140151520710010400d04111480d20108000500103000707c84040c0c0c0e06c9254000d44c1070b000f850070707854108445110740404960090206202e1003d1024121766018030040c0c3c480c5048405058046900c6030001031b4044c0c0040000602c1c10305501d00400c1424 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 265331519 1250 265330269 265330279
    0x20918280501050109020711120706032a0801051f0203070201050a0309060501062604080d0b15030109090c14010207060503090a02040e010b09061507110112092315010311 75
    0x3120799079190840707000b60050f0444980c081240014002c100c01c0045440c042035038540002c04814411342c0c1c0c1c541103441540201502c0d03d40c000c445000d080002c00301c42000f0151220000310750480680722010901510b0b00038044550800070b0b48004801e01200d088498015520b40142c50300111382660010300034030300345510307041076000158061103010b008100075982c90550a40c070304039450500e650064080c04140400d001c3c003010a521008076912481d259400040c42c2d01481d003c94004105803000b041e5000000c4000580c881881d00b01c5080903109490200549841d19602c0300b10000d0031070042e006a00c204000d0200750f00400c001e540040218080b25000c0c5240e070700190958254500040060b5160404c019031401c0c034a820b0342e08050100c845680301100c9650030b100500038a88023400f1051281c041d10070b143d024494840c1140c03a000014804e000c91400c0078407903003003909024144501c030840148294400801c08e003940e00645503075080940d2860300d51244880c12451013640c04 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 265332769 1250 265331519 265331593
    0xf120f0d0503040c0605032d040201020c010207050102030d0f0e0a0303021309050c0d0504050322031104060e04060c0504050d050105061005130b09031c020609010b0103090f0f05120d09020918 84
    0x101da5180a030234000781c1035221503134072460300d44002800c000340d081e8420b06550000c0024400342e03030040180e42d01c20b0001c0c40c001841521413003d00000c6c010500c0282c9090080d10300020626038035400070010240ca0aa1441c6400d90382d4195001b00d4004841481c0860710034450b0488c803c26580116400074020700440781041045035a002c540480d1082e50240c400b0341c40000c004201011032140c1c48088119810003201e86401624001c1e45d500030001000d0703075903912955443e1401a408d0b5000f502018166922000491515500070310003910b8240c40307801c200790034900591164040f01d400c1c088964290040c94034085405049400884106034140a0112901040600c80348404414070042c1e00405c5a03050048a541c01c5800b010b0715141090b042c00c5544020031600a08100e04681c808280e0072003a1003414601d080003201c4403c5034403004001910a10b000f45508100783c000d008030b03120030040d02c41c000d091019802500d9000a0f940040342004c40c804501e8024070f81002100e0041055 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 265334019 1250 265332769 265332811
    0x10303080a062409090513140a06050403030f0b030105011a0d0b120706080c09030a03122a1106091504030215010308040f0b0c070e060f120f0d0503040c060503 70
    0x100405a018000c4000f258040c80e00b150384480920010900d15100700441d0421040707800400d004c203032024100e007138401691a001c4104120101e85690043d01c100010306041c038000380500b2421082e200000d044c10412070b01803030180b04d258102e0300104009410719440d0308a40029402c4640d15030540c0e03964201c101419103906071101050640c0708058028642001006068802c000e040d0354001601409820340035180002c2c1014559058100141c400001c17050480240074002041c44c80000c041c2e868030b40ca0300d9030445520f0300c0c1d8104d48401c0c11052015100a0382d41004481807007a40c3d112264010000f400180025049400782c810b0301e241121000c01c00045d0082a80112110040043c0402c00c820407854500e000d0140004090b143c01a41d1041c15900e622500900006680d4880803444540c1c814008400484000c2d021100082d1200716480d20341140140c0c03c07019005001d00140f5981c4a43c040780d21442c0d1140456141c9801c1c8081264160401010390424104075650100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 265335269 1250 265334019 265334039
    0xe0c0a0302041a1e040e07030b0601141621141b0a050a0c032001080f180d030204031703090a0303050a0f06080604051c0e0603040501020f0f120105090609010303080a06 74
    0x404e580c0107920070b600b0780c1c8280811203035960070003000c54101580a00020700300e500607130b411110919103004220041d800707520007403040007141c81e88800c0708014641001404401403031380181800b4405062807080e0010b5502403140304a540e0007071000c0040760301450140035400c04c9072010204856581c4001d035581d52401e4140711003640c509110b07030020400c101c40c041c0d0000c0c60388000b603541c4a0501c030b04000645100400341103800580c0074000001d081e0503001c0800400440350008540040103280c1018001394014002510072540060307940c002e00c9400700440340211402002001d00e40c2d020f4070b003240100fa0161802d250306841c1d0f02001d0003c02540a450701400450340030309202e0030a0302d1301034640b5581c884071890218a154401900c1c940000040b401e103081561060381c6d82d5600e00d0710500a208841255942c0c00780801c000841501c1040604031680816505806a90321030040080c004011a070440d4016414030040c000644111140b6800800004012078080d4840700d800c9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 265336519 1250 265335269 265335289
    0x6030f03050c071208070b090c09011d0603010203060a050904060b09181e10090503070803010806101d13030314010b03070f050301030c031403070501020a120e0c0a0302041a 76
    0x180015502050b4011204824010394000b00246100a52210210303a0340308043e0007007440242175440c040f0000740102c031003401024500c1c68005c146083d00e68541000d0f411184d480748455038841e20b05400500c1038141482101d0107070000401005503d49410108002c83d440100111402610345075a05091f40700d24080c240030f101d000700d40000c140f124180c52441c0c42d40d01395031700042d0f100c18000e10703000250100707400c001400882c101084102040c2050387c6140f0070254020000003001000040075180881c42c0303170103400e081807490ac4080e99072a9284070b40c800d60078217031844c01c144004110900b065008001c89180701341400f150700e000b0300030070841044090340724003101130000040044043d8041032004400c00f072030034240c0c21035065480318020180b071800024003424031082910402c1d103040099030110369001c3d00a554480000320014599540140c05003099800e050820817040b0001c0b445015130900a0005042c0600d580c082201812036a080e010001c80d41d80001007041e26200489 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 265337769 1250 265336519 265336523
    0x9101205030f040f09050903090f06090f031501030c06050c07260d0e0405070306030f1e020a08010e070603020408060a0c051b03130e0c04090504030512040b06090a05100501030f06030f 81
    0x134041305881c04150405031080104015401d4104100750070032603880c5190703c9110710701510019200d6100c034000c03801d0f803100c0b10841e5515200c1c5119148100c460f8800d03680c10f80b0b20443c1502201550340b20286c4080c016074954041da90402e400c184030052890490000c142108002c03514840d03c0404160709200c9050a9500011074000c0860204e08260140baa0009140c0c80c0421250f891b60311040c800381440712004040c2e061121078030052140304102c1560458000b0901d400d000e41d5205168024003c44c240c020160259060014109010b4400c1e50120740d14040900b48603510034014600078210700e5804000c0c00003e21980e0070303d501c0500b154225082c1d0800440e41c0345045440c03e00d103100300d80e00c07803d0559101001c00c81e034414400d064404560401c8000300711601c07186030640d50350254048074148a40c80728108000d104c1c1200300340c0d006050981c0e000050782c071040001c1007a40d0381110183e0204990f01810003c42d40300754055007041c600100001040b9450340d650b501065100d40b01 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 265339019 1250 265337769 265337789
    0x1e080408010f0506060a05040905090106030b09160801110706050601021f0212151c06020f030f010509090d1407020a080106090507170105010909090212060115020c09101205030f04 79
    0x15440c04941803007000d420036000c1781c40a0411641d50760080c810311450085490107600e4501003503070480250088c0c0099544400c05810b2460100106507a5a540c44880d2140b00ca90300f2000800d0f10040c82240100864540c0c41442e00c546511044c002d03103000b6241074110b20400c10031503410803070518002c01e280d51045001d69201110b520380300e50050003402c0c00324000c2c02021181496a1120001c42407909203011402801d56a420604002d00802160395202d4400208012002d100ea41105040c0c890443d102c2502d0745a1b001c42c10303951240410580086076080c0e1f00d16102205080183c503039148001d200583c4582c64068142c00e41c0ca0540c0441c20060b114001d1041c000d4008000120904440083e0309942d890310b40002c0c2240e07100d214280c0150703628040716095484202510701c24055100895429503541e030001100070020211040050041c81c105510f01c0c6487c0d08254040c282c60540140c0a07401e0504800180500010440c0c00744400c21160644c4c0c0500c0340980000c0c91880320b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 265340269 1250 265339019 265339031
    0x105040c080108030703080c130602030319050f0103030e0f03190c061d04020a0e0607050601060e03150105060a0201060806100504060905161d061602040b0a121e08040801 75
    0x50009603103942a0303103800e10000e40010b02c58440300109480820350107280c00c1540313464200c140d0b00503104800d80b00c68a129a0b49002c01c0080d00040210b0066409841650f0301040c3c0c500700c40b00b250002e56402200c1e90710400100f011910481071602c0c82c0340010704258100c01000006843c201c1403420480401c448801c10f4400d0101184540c401041e45d402e0411a503086000010030030401000910311840d4082000170007140328a10180c0c402501a0525075900300b0b42c00d209031780e001c09104207400241c61000059850402240b280151a006201560142d0030201008800d0300402c0d190400c640d41c2c1c941c005a10f100030002d0a003e84482082420490f01784818042504c039550006040359040809029180e2120146092140d03014a06191403100740c022482d1a02c888083c0c20f90b10405c0841c02c0c401c007100c044801000103200319000c120051501092000c00f1180d40300c1d0280142c01d4011490218812500d0441c1114400e01c0c2c6c00d604080c150340b406459005508801042e030740d506 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 265341519 1250 265340269 265340279
    0x402040815060d0209070f05090405010314100b01120b0f0a0f080d030c08010e090f060106120e060f040f080d0c080402030615240d09050d2a11060c010504060501 71
    0x80c001e660071840a607500100b03031440e40c01017244050301401c04400c20406140c1c0c041c80d184581c0a5808801000304103201c1940c0d40d00300180e4840d40c0010001a0b4080c2c0c200102c80d880c59885407803000c64040e110107503070741103280d01380b03000b0130025498a4002038100d500750f00650303c513200e42c406041440382d281480740c02c00e025107161000b141c040c403052518103c25602d08940003081241101c0014414140c02d6650100d9541410060342162318213101e094004940300c5c3e0812000625950b40704010001d46260140c1c3c556641c505072030b102c0a9421040104020900c80c40d462170071280100000c500d40890b000c030090480300c20028850010f02030101b4481140380c1400100c0e0041900070302a181c1c5450100052540c1c0003540e0a80c4a08806003143d49008c407620064400e62105810200030036130003800e0142d140c452500d1081b0024046015040d80d07007031960842c04481010040c1303041d0010301d1f561552907402e4800c03031140d0302c04810710881c0c5c4458800d01525114034807400c00822076501d44 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 265342769 1250 265341519 265341553
    0x50a03061b1701050d02040902120f150c19200c0a090905070510030b041d070609060206041106070506040303060f080307050303130201090e0a05010e0a0905031e0904020408 76
    0x1e540c0141000507071922120b148500d80d0546054800c200c80c0101580f40c1440010014590079000079000461508120040c82021442c103a0300340304002a0392150b90020b603614880d81080350035034581c01742403204145d080084608038081c90b01c0c90420307082c0305100d01002840348070010b00062265200e4030480e00c0500b130880040000785122401441038403040e070b5030700d070311052217028240c000c151450110744854804e411120203408080c0080180e40b07506061010307408401d00700d400851040c0200000e409101e4107190045404503405409140c48603034401c40c020700011202d680c08802401071401003902401201c0c0100d200782c4000a02d03a2404011080031046588001000e03007044c05103101107903000c401c03030358042400c0c00c0300d5070095958030040e205007580b03800085000910324108155043d030b41e0b0003030f41078841c0500c015006684241550301914070b0400000c0aa41081c0003403134a106505109032204070a80f00181e04180541011400302d0300568042c40f00c0b030b0700c1000084282c2904d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 265344019 1250 265342769 265342811
    0x80601050a0603090b040f060f0204080615010c050a15330b03010605182b051c0c0605180f011a030705061b010e030304140c1f0302090109050a0306 65
    0x150405200711002500e818801150046c00074080d02000b11240d41000240e1b4400010013401002c1103484a0b15085916610300c1e007202d14050b130b01101207921441c1d6024400f0303202c120303510400400c0e03244450340c0d558000700101010500302e04c0c4c5a1400300301035180420074030440d07900c100c081604240c000421041007003c603404141211001c00c018040389900000700d5040c01c2d08450300c04001d21441c40429185069191503400688041101d0451044c80c49103a581842c02101203c400c2d000e0b01240d4200400c6120300d0307001040102c0d8140300000c3c0380381c01c6243c1c000540015850112501d1158a040c0001e600401040365035a112030440400204035031000c03010f0680003440c2003810700000c184503100f80f480c0307103030003106800c05505462001d40160340c030f0114000036070b501e0381880e18100ca0b64642c81d00c04104a40035070302801138035041c0400c081600e031404507100d00c0004940032042d0025070211030990304000304460080b440340c8421841c08011445840c000806a4000758400c090315a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 265345269 1250 265344019 265344029
    0x10f0e03060f0426090409031404030803012c1504020c0604030f02070b1602040902060f1615021c15080708150702070f050f06090904120917100c050c07080601050a 72
    0x1e000e1400d5640d80e0400c801d407968179209aa0005403001607080944401c0403a01903000c0e4064005800301c20448800091412101c4e41030441c03503060001030b09901a968402081248500e034000020507001150040b0351030144050001031903c1d2890a00ca41821001c540950100b00c26190a2100c140c7c10455400108811100783c0e0034010101c882c440c55034080040a807060343c64004c01010343d51914120789034905581240341d5942c08100d54110100c404241c165001d0303a09036050260074925000f154640503040d00340c0c2c2d01e07140385580050001e0441d214020005000c4000c007040041e001c006140150180c10003d1000d55440c0b91203050b41d500040000045410203041080b4030401c0c69200020b5410449003c60b81842480c0801d03224011441942d0b400003084040c40140300b040304400000075115030701e003401161520445442e0325041140221254441c00c80001011059440003452004d540f81042c5011001480365241c2585a00714074116040400104400e10f014406c2d03100402c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 265346519 1250 265345269 265345313
    0x50310020702030c1003150e190e0307202e0c0b07030504050c130902090108210304050c061309050f07090303030e012405010207050609090402010f0e03060f04 70
    0x400320b41e010944504200f24414001d101c8441e80b1030450340645c1180511194114580c410180c1d1410403100d06c00040c0c40c0a040c2021203e00003c8030296405100301501d1a04021841d2240c0c69444c0d2040d8014070079807490001d080d0045074025666280c1c85084415010b85112110003504820300c0110108501030044c00040184040002c9654070302c03a91122840c1800074540e13540d410060b0401516031500766112094102c070400c01400d03079000c52551340c001d803111543d81c2c0c0ca420f807581d076611016190441e044426007a94043c00049801194850704c07600035625205811000b20b0016041460300c074192001408050040c8916440b8180d072000402d1803c48150030b10030b02c0680072250501001d010103032544030300c81c81d0020940100151043c145400d0052482054590500d40440d00510740140140c070000901d9181c140180d0310002c400810040043c1c5a5500540d200003080802100f80403c001d400c1d1140e69050040310300c28402400c50241d00c2c070705441c220000d00c41d80d0444c0300c002 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 265347769 1250 265346519 265346527
    0x60507030306050307150f1b0320012a020304080d0804021f1e1709010e0d0e06041401121b03110a0c02150705010203090708070609060f0305040f05010504030905031002 74
    0x81c041c1c090140390100e9240c00d1136010614585404c1708c1c6054070f60f14010f18902c04400ba9010550b20094441e446105141c5a00c0d0884481c02940d0a0f41e40d0002204441c0440400a41c0d0061064410118112160048a103003540c5c44c40c09a08140400c0d440380b0126040c40300300000d40c20820240c1c819106520040601c412601c0b0700607082d40e0504641d07440c1080940810b110160050740646032000c0707a00848801450200c2e0701c02e02030000500156200e00504012500f403501400e2120080c0100810740b50601d1300f0481030030b10741081441c07558101700741610380206030601889080365003000804081e0321a205549c000e41035414045581d0b880c2441000941c0a00c0d0f8800b610072066641114265003220400d08061030f54040d0140140403540300100b8403404c80400100c4c181141c2e2408260343c400381c1d9680f829180700c10644696004201e0a0601c03400052007584001d510912443e095800e182d082d440d554210b40040f80d04a0104070203c1c404d006900e800c108108109862103019480c0c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 265349019 1250 265347769 265347779
    0x5070512030409021c05150307050d02010909050411060c011406060703081305120a030b04140106050301090f1805010f0b150706020f07140d0f05072406050a060507030306050307 78
    0x502e120742d108980700d00e940418800a085214696142d45003d48141801581004013500c1a031141510b00c1c035100b0b116826002805060a060311100c0ea03805171548404603140140c1e00014080040c81103500100544c2d100d01d42d80d072404007170f100e0110000c0001401323880d10054280040009004148503260900240000990002d11aa40441d0540c2c1001441065150003407520b80601c3e8008000303500400c038081d0256041c2c0c810036144a003160103011a5548901805107150207001c0c0000044040005100106554000f61424032181d940001d1400e842841c80c00c002404d0f40044400365107a05041c0f000019a0098111070354003141d507420585100480301c0103900c60701000404658010a103103403040c44c0881610030060704a002d0004502010507450b4450207031400000120791200c2405508500c030300150b50850741c0c000915030700101d196007040c1440c6040d0501c1c01c422900c0302d20110700c0f5220030050794024607290310780644a1445150240a0300d41d03641000d80258007515003041 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 265350269 1250 265349019 265349023
    0x180102040e06040c120606050c1002030112030c030c2f01080118241205061503030702120f01090b01050a050d0816020d05010c0e041406090c0a171305070512 69
    0xb400c4282220000341c01484100107540c40100c0c1c0780300c414100e00d0b10a001800340d40240081849000107000c0e51480b0a180c1040e50490100703026485100b09c4a40145000a000383d000d0009140241003903400000755a403041607206001001071120344055010342110704103031121800b480c0c024240712800390705203103848107000054074030030000584502089a018510002c1703030407176a580b00c004d01e0081c0d807100c5240d841703596064170446107440b0740d00c00142e51000007542c41984500c01030203149072454607000c100e2a2501104140312074000c106442000290911034414204e00c00c02280c1215850141000f6024285520190045010b4801200003a0000f42141c0034110302a074560000182030010031070039400344500605562810b00f40180e4560000850800d0980407102440b049103410400c821090040c0c4070150400705150100345c0d0500c0910182400303840034601240322240e11043c00c200c0741c000f502c90103111304a50021000b40316050003900007909040c0e80c2c1139050418201259 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 265351519 1250 265350269 265350271
    0x8060102061608100b040311191206050c16030804050607020c01120c0c080d0204030b010501091d0402040e0102071b06020706050a08040218040803061306050109030803061215180102040e 82
    0x2010042050001000320380b90007a1000034100d5174840030b407a15101d1030022003950900306d03054403c601280c03400344545184000c0c9010303100d140041c214071518503501c600146c41c01814903070240700300344080d0a80c80e0140080300b00e414040c0e52406c1c100c1c10241089410484050f10000c04c64200ca03499268907600882482c03080204400d0001300068846812503080c00d100c6c200a0007a030001518041c0c01c2450703000b070400d03680101e000308445d90707030362005484602e182d04c8bd0000315009031246482c409007030f1002940c050700144c004511668210011422644a51000c840e8845040200042c1c85200d011000140580e40000c0c80c4032403c00d8000350136405000084c40800c81042d0003d030031501d070190110690071900d07010686500b41450151090b80044842900400e070921840b00c5080d0140150030031100c1c180c64860949045458600e42e41d0f000400701c98003c007240b0701291920707900f040840c0c01100100c0d045049424105c802048000e40b04060481587c0144070a000c1c0c0c0c0781c3c00c9141 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 265352769 1250 265351519 265351561
    0x20912120708182e0305060a050603060a03020616030207080604031704081603030b010f020c22150603061715012d08060105030705010206040b0a090206120c0a0806010206 75
    0x1803616502980b400120010550f070410b03800c0a5001140c5071004040816801021040c813480240136403001c60403000c8450480e400741e407240044404002c00e09009000f50382200e400f61810712074607165000310301c0307590144010a20202e00003ca003400d02d54117000c13a0010b088e086001e400a07003403545000300341c45aa0044103800f00d150744003003010041510708850191094079051030150070070382000b40040145081c12404510140117100d4291301c00700b6940e00180c8010038a01442009082c40409040d502007005481562190709512080712a400d038002000540c0d0046541703810050340030b640b0005601d112000341d01620707400f0303074514041800030306540d196080040b200c202520580714001554110f604c502c0011640490300d000003040c494140e4200707030211030300e0940d10001240e40304000c4030701034103a00000010401c4500f042d00301c80640b41c0002c2425081070030542c1120ba006d141503030420320036200050b07a02c1c25580c00c682d0040e403212090010f0402ca00c0c0a0b807015829140f19589 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 265354019 1250 265352769 265352783
    0x16051905062503090303030b060304020901091e090807020307050603090c010507060f0207110a120312090201110609011e0c0203071113110408120906041701060909060209121207 78
    0x707500b0b5148000d0302c408011403000040401c1c0900c0c00e000c0d00641d0580002e8000a0402c1d51403500c905040b0102d9000315809070008441c0d0f880c2102c010002d1002a10940b04016207944070b030020102d50056900c214001c0c903903070342c0e2007103107104161030049650300403070140f1028010440303038101c00300c1c104024540c00e08100d03aa0300e00c1c074036118000341840344208041138404a819006e00020214284003101e0030307200340c0400d5444000004600f801007900070001010600e98039135030f40b500d80080000030710604250744040da008a0071801c20b00220340c404d015a40d00c404580e0500c803084061001d04816080c10004050300030f200a403a8415050058071701d000840300d0026540315079810600261050720104a200d80c0c001003800d06501c54070862500b44034000441c18001202000c65001c2c0100030400d5260074680407501c04207506041101c2c025540c0c03443c1c000740300040c030700403418018414680140e950014400b040141c000303050405810b0b5120078000d60f421800e0004550649810400c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 265355269 1250 265354019 265354027
    0x80d0203060d240f02090d060e1504080d050105010c02060a030c140c2d06010e0a1b08190614011808010207080310080a0b040f140a051605190506 64
    0xc007041d44003030b1502009001c0040c04150300c2103103420340e00680e404032442c0307001d004d29a16104ca16090740980000da941c00381540c22a000000c40c0c69211385407014900040d078011640c02c6400e41d2150800f203905076140d00b000a198040509548219070250100f42000515400c1c0341d004038845010b10752604041c19034403412000c90310700903002c110303072204980c8803190780b180c0d100c1300c0507141ca0358002007054104402122244260f49158602c00c10985140144900d82c0b92000010329440d001e0301c401e4040c1c1d42c540e002c1e240400c040c0942c005100310f80c2c86491890400c03c07948604482034154a4450380c0c5072500901c00848441c11903404184240780400800341d0040420012003081e60003843e60f03610001340e1500704070300c1030007441c418441c180c0350300c010765503074420651031300110f51004100c1100000040e00055403400a58501c901800300140c001d030061403120710f0281c000d501510355600280401070303103410b02030920000c1c1400f40c62405a00e036015000d85811185030080300e200f000041 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 265356519 1250 265355269 265355281
    0x90b0f0f09030703050f1605060307140f0304030201060608070309030206010e1b180109050a0b0702090a0b040e06060405070912110d0206030109020301030b130b0f04020102070510050309060a0603080d0203 90
    0x203070340c01800000d060701d001c1c40e03880c60b00d2699848074105862540c003804d861070307405c041c1d0807044504480000d40058070795551240219090030704140800c1c0c0c9000c0508c014841952004003075803149110390000210fa900f490405004c919008200c54105810040003c00207a07021075001e044030aa12080142c507183c440404170f04402044481142c01008600c604880603070000e00100310030b0a80b5919200c0d5260b005103c139401080c00340c1c00b00701e07400300000801030500441255004283c13078400079042c03103203500003802d90340f100f1080402030b48204248882460648156a0404418113000d084603103000d80c00080410f40c0c220150000d64140c001442c0b07519041c80610707003e5401003032a81d8030b41e12807898000940080c08282c2e4900580d40011b040c100414180110f2150001113102d000d540c1c414441000680081c030032030450180c403800040d6030f241c0c0690301c00700002640315642c691800c039049a07e000c100401d03124400b402e0890400114840c4c41c1203038150503e81d04056641d030340c0c40c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 265357769 1250 265356519 265356547
    0xa0815061b190b0a0b06280509040207153606020c0d120e030304020108061201060812220311100905090703090302010b0307030c090f0605030609030301030b0106090b0f 74
    0x8035100a206800c0040d00b00108107480c1011845a001d200d4100540d00e4000240301903130180e9089032940c000e040c45001480e4000b1040c40078011920700e00a45003e500704007007016038001880468600180f240303641c540c040c0e03501960b0303138500070310210340030782021100240c8003100b02c0200c85003100c4071091818148051501107402c00000c0301c044854110900e43d00400c48a0441d100740c910700d20303110700c00c0ca03055400f204a81c05250140d644a056440d0803040025a00d00c848082ca801e40d614100040d04040910900880320f0860f0b8400f61140c0e800c584000554191088070107032030b070640c8410300020341c41c000b0f140364220081d0b80d503014003845090160380400c0d294026917404a0040204618240d250b00084031280c480c1d8020300410794400103040d594043c9010081c68200d51000501800810f54071103052555038460104003669181c0c04a41410810341d940c01d880c1e080040180244600d00a040340103149524059040c545048440d4615008034007451440303910010b40c10498142d6 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 265359019 1250 265357769 265357783
    0x513090819110a030c05150705180102100606050306040e01050c0a110a0b09030405040f0e101104121b06020706020a060f09080c25060e09041b09020a0815061b 70
    0x40b65046509045480c1805084081c00300c000304c0f82842100a4181700c940d00044281c0144015124281490440f510060544084a00784c50461050058120304000389009a1000700303050388589580382000000e12050302c0c072000300715140d80c0c10101409240542c800032564425010318240e451002d062040c54103000800c1009402d140240f000c0c000300920100041044a0003107034104808a869201e200c191101006100e41c00e41210901d90f118506940260880d4020121540d26260304c644614000070300307103082620703181040c98003169214025403c00014010070b0004014291500c0c8000f5602c03403610500400140e02c5901d01601f610850b0080001e09910900d112703242c6413071059107513890044400f0704803080a03020303071010511007000854044c1e481a940d10250825580e0a1280d000c0c400f9000321800100c2c512086859010700c1c980b103000d4045060003507683c11a244d4002c100600140019074000078075041c035010340d601c807000c40e00111a03012449980c00c0080c1072460600742 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 265360269 1250 265359019 265359047
    0x30307120b0303070b010332061f140d06060b220914071103040308041401020706110a02041a06160501050a061d0a0e01020d0b090906100b0c0c03010906060513090819 73
    0x12600b231b003801199004916103204002144225503c0c9400c6078101d01100c490748524140132804428107a960b041072801d0301c0800780074007404684199201e144c1640c0d644110380e06103c55448400000a402819191500800300d035034007481603981d280c2c400098030a028060344140244101d00709018003040c0150381c0150340100d1102d413150390f1100c004e040e502c1d00c040e02c1c0340140142140803a015004190401c40c03000140000c1030180b826a0a000c0104540301c2100c1440317a800f6201907655443c00010130641c05c0108101e10803004c80e00e0080d094550180c04011044c0c20076000340112084180c503856003518100900c40e2988826070100300500194640101e10b500004280303558120a8000211a40c4240c4801c25540c1e00c0c14800c0f600c40b0170070f6861814035111f4020400020701c0e210090161091600103840d803803100e030720010f400c640c0c509804941c0544c8590040129281042d5003114450302d11030148940398165035011042d2040c6801110082c02146040802c1071040c0c03941c01d1041 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 265361519 1250 265360269 265360343
    0xc03020c0315011d040309060e1201110a090801050106022a0301050103060614010e0f27040b0406050a050402150307050d020310170f030d1805030307120b0303070b0103 74
    0x940b001d40010000c00e00b40160302d03400030b080039080c1e652400103012511850b096610b10090f02c0c28940100c5112100c3d00c0e11a50204510940382c001366020b1090558410a8a011656803c203468000d094020a0760024180d645000010803113580c0102c2e10348a089070a541042c01707440c60401000050701611030321505903281030008003c001860b40003205881d10b0800c1c030380d0031495a80046503480d10078400c0d40d821100c50048a581810404108080820500444002c150121030700b40950746080300c0584805402c80e0500c0103000c590300c01c0c0d40d0030440b46041400140340540204a0050390750740000c014110000018041c580301d0f00c01c1d80d403003140c416020356881c00d00c00044801c00b0110b0060110300103440c50018011134000541ca40c0c0c07482c088000e14207003103000c00880000c00800010030041c010310a60032001403020300086110716040d807180903d602d20413400a0440d0203005007140280d008004080204503020051411070b64422500058140c100c401001201c1050450003891 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 265362769 1250 265361519 265361533
    0x191211010203090d021c1407050f030d0203100608041101080405330603070e0103080903010603060c0809010506190b090324010312090308250b13170309030301060c03020c03 76
    0x100303c010071219440b184590855640103c5005910301c00c0916000e20400702e10004400080c41c10300c0c4001d04182401881035909140078841e035a0f007103a00c40d00c030980b003466001040280c03581040e040400070301402e2401c440207240c9980e07084442c2d007000078203034140700c210720000d810050104000d014806982e42c05200140b20b03004d80840100a01c4400c0740b9598500001400a050000c2d00500712910001c5814440e40f07036807a030808030360100b40400c0d015505d0381800f001043c0c02e4090302110b02956a45c050b410300c1d240040307501316800500098030400d922240404c5508250300d800d01900c01c0341c16095038420078080020b2501082c42c80c918a81000402c80464628000b002241203c1c09000402c00c00c08090408071000704090000030099001804016004003040d0705020300000322011008641900d51a251212201210100e08080c610104201008009095001c1d845841a215400e50602c6101940c503404140545c404122507140080141031080003000700c5018050152601 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 265364019 1250 265362769 265362781
    0x5010c0f14070305060c120601110703050607050c010507021f18021c03081008070b0702030109020d050105150102060402030703060e0715030609050610171503070b0318191211010203 80
    0x110b000d20b201c2501e0364024480002c8400d00c140f81290190f502902084645641e00401945c039201c503100028502c1c8980000800001c43c10000140990303159140e160716000c40c00e400600f9900024400d4085400c80000038412a08414802d46e40302d404240200c0c00050b1595410801d518240001e90f101d0004e2000b403402400790070807025558065500c540c441d42e601404070b8426011380c89040070503808100304000c0e205100c4043d0030424030060012a0040700354000981682d8804005c2c0c80d16550b880c00e01c03800c01d544000111182e0420b0014006614090300080e4aa004511011b40110b03140d810805040d501400340001506103511511400d10b81c0982c002c0082c4291b020f00d4a4007440d110100c1d513a40303401c81c0c08400c101d0090f6900705400c01210800651084050044044000b544201c2d501a42d400c3c090304018007030407a0380d25103e00c5c00700d0440b07500c003003075034065009600a2541986200c8801100d40b800b01c0c5c00031080608030700b081c1c10460b032100300e02030000615440170040c828 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 265365269 1250 265364019 265364023
    0x601030515031005040b07081e0403121a09090d1704030905030609210405220e0a0303020309070501030b241204050c09060a06050d0e010905010204030503040608160905010c0f14 78
    0x201984c00b41c0c06d0080b407952114801c4d50028001e640340301080e02054070130000b4540400b10503502600c00e19003d41000c0d03c0d40e0560040e140c0d450306484d880040051500228244011a90791000810006028600013000040e0401c0980d600310000303d61a00000f40c2414080e042503002000094101d0340c3d280f81c80b8114548991281450303840d00a481c0340e00b908004840d009079015990000c200103c03a42d03025010741c500c80d90031084102c10302d840d8200440b8500041c0071803040300c0c1c0a80c4016070742c3e10381382d000d80381044100d4100506061034902c1c146202d850b07024190844801c0c0381c0e6958006001d9a0286850340903102c10351100406100800007085404107410850f03a5081d0b5559400352610810800c034070f4050b001d41c100040f4140180d0781090220340140f140036441c0c0d000003a00c4e061035194a401d980c42030f002079405900000e03040181991120340ea9030b22005c030381090b4818505080c8020004807240c8951030402003208114000d210000301884811035205009024164111290075 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 265366519 1250 265365269 265365271
    0x20d0c2105011104030b07030b03160f1409040c03020d030e0a0b180405090606150405040c110f0102070201140304081306021e0304082d0709060f14090601030515031005 74
    0xa895508201e00860f0041109041d501034952184c07540f05c540e0382d010b400324004c0c00b10f00c62190341403003040200c6030400b4800041c0c00107088440300d00d110080c100544d04900c40d025031252030181c80c410f005c201c0401e0108000034250f9a040340c1c4600420381504040342c0b9901da540e0140d900880a6200154203d8004010540c4002c0301120a4460030002e0800040700c40483d20010f05400030340000c8d0845c5082030961101c64001c580f418103258464012908444042d00110b0200b41c1500043da803948040040c0c1a808451500941c41d1a20540c0000e144421903540ca810b8800040007150821508000751401c4807100c1001042190b41c4500c020340d9950f9034064004500031603010301c12010300200443d01030725440c20041c04840c0034588000c50917540c80c9002d0012103c407202648071900c0a00072403008241d1841c020410a081102c0c841c801c00040d404601c0030701102510401c5d585440442c15844182401c0025656032035840c116000408400c00c00d40c503014409c407010b070303000c05a0b00803 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 265367769 1250 265366519 265366523
    0x102030c09100309032a1a04030215040c23031911060708120a09140a052e0c030204050324090c0303031504060f03291003020d0c21 58
    0x7840c40050300c100380c0032100d100202400140103005900712051010100510f42d50001b141e420008450b80c661495030340d10503141e40e285d4141c1606110605a04104580701d4094104103095503007010f43e41d0381e45a1185104140001d81000071620098040001d4a2034204020b401c0e1015484078045508008041940464640104141444041c00c00c10240d5807847d0340030811510705001400c010885080c000c060302c42860312070400400154440400d80103010110008215002c184d15013241400c90500c2c41d1118540041e00105030b01e0b40042100c3c00150303590300300150145d00510103e001c0d00c40da0b0440364140c07007040100312090600003100c00c0720801c46038494070035441e070405241d03c0d51145403074913900d40c1c170500c00300e007900080c89400059000d0017800010080c5d80c2c1e8110400c40105a07105a030220036068003056103040e40c201c00c88030030b40307501c2e4079000501e04040b110b807038414280000b038060348251000700e040201040841c0080d0500d0a005e41c800c0c4500f02524501c04004402 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 265369019 1250 265367769 265367779
    0x5030309100e0309040b0a050a080a05060a020f0301051c050f0304050306090d141c05010902070308090a05061501032004060f03090309090f091406060414040206030a02030c0c0102030c09 82
    0x3070044003030000d00c0350152000d400c601440c640301200702004007030072100c42c04551001600340e00041c140d84609c031000041419402414840c07465007803107400c003403000344041141c0d801009058111502c220484c5e064038801c507404074809a200c61207800c01201c41c14014a01c4c80b0b8030310024840e0b103000014004031202141115581e80e5130b0025203840c0da0403100c004010812880380c1c840c0e00d8512130003505101d40c8c103c40b44002c04150561120688500782d2068070000c1d4001a80e406140c1c0c0a201e80da401515000141f04624403665042c2d511280140f80385404090881d41419684c80b079003002880036660407081518200b104c1070440d1543c09481018046aa91908140e145019018001080380c054880b214450300e404880380150104041c0c2c62100d89d62502c159000405481d242c508419454000307003030074540304082c0011640501d0700e41d04011441800c02c40107a0fa008122a40705010240c00b580b05d0319401580c02c1640260024040345500100c1044080d07030441e80985100107040315 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 265370269 1250 265369019 265369033
    0x1d1608010e070f0b2503050a0f08061e03010e0106030b07110a03090e040309051216090204030503032d0412140a0c111906120e0f060403030c031805030309 68
    0x14180d030341c01c00b41c8102211809109410002c021000000d030001c1d000307105660001100102c20300582064400d4120007165000c64122215607006001c1c20741040300e030602290a041c414001004083e9903060303040d8003a007c0041650350740b001c0d08a03800d0414000020300c2881d850340f5003ca0402002c44011740060800354000790750880c0040c815a4071501511080407260400242002d54100140160240407602070001025140c3c80c0300c0c4260f81c1c03242400b40030b14801a400c3ca241c0d01440e50f0083c0d01e4180103000c240302040c800710860740c01c044c1140c040382c13415048960580c80ca01c0141d100e51000c1030f035141008184082204141222080e1790381d00c04061414210011150284054080011b540d01101c540044c400401213120b0309030040130700c801000040041e428010903074100320005807a05007080d200c86420301584e014010702e14064003801d000b14424a580b60001080903003015111248000c650703000b0b5010b00c0411050008502110140e4148580e40ea44252603050086c49502 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 265371519 1250 265370269 265370291
    0x5010609110d0b010c030503040b1302090c0d05060102030f0d021b030412060b0a14090a06090c0903111203070206070f050307061b030b03030307030911120a0c09050402090103061d160801 82
    0xc68460080c0746d2649405080d5100c0b40c54200301d104000f032040d48110200121032004da42e45500301031207003000303008140d0b0300c0c01c0380110802a6134019107560705544c400e20a0b66003507002e80c0305440d00d08101c11801a2201c050440485c141c8000c6a01264140400140071402d803400e112810115802400c05000e44440032080c0305009020303118020410003910030884891929400351600403041100c042069a00d8024120885100071290300c00b04203040000c204010f0b4001401d00c2040302125007141c0060745e8143d05407a4416410000c2c82004009410700401c4030740e002d07464410f5001030881fa10780201d860302d00b00901001e6041103225983c1c00a403883d00d440f81c013540d0f1010030094065811500c9050040c0c01828102030b0486001042e0040c40010b502c072103000303101c4820780e41c005010440c3c5500b098540d08015400c00e2050500740b504001c090707241c0d15036482c1129031120000a1519032803126580111065503c81d4072409452183c2030b01418600400301a03401e1080200a006400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 265372769 1250 265371519 265371527
    0xe0a060609150b09101103071202160806010806070509030a060608010603060f022113020d081306110606010507060b0303070f060b042901090515030a0c0c0203030d0905010609110d0b01 81
    0x3071509107501c10f0003201c420301c40e2031003941c07145080440502200d040044076510030004640786040080140e001c1c040001c541301d00102f8100040000724045e003915410540d840c0e450b9a0001c08200603c00000341500d69038508003c00c006064214004001e41da84601c0024040c01c9148070aa9206050280889180105100301c40f40403036166801c042d0300714400c8a54642041c01844000403040d50300e803d8026840b54000d00b40c00c503100c0c1d01543e6449074440c0542d260114260800c00c1006648006908a00400038025401c88402d090003501c0b920540b40c03200181005030a882d0701400045071980400200c04901404148a2001481000b04004c2400205c0b2140c1140603000044a5108200400034040108070243c0600d0000007840e11400450007205144072244003125001040010244140c4200110400e00e454070051800041c1c0009a41303000d500d0005011a42d6101c104040200035403290000704520f640030f2000988165a0107081e80165250f140c00c0c2d801c010b0929025841 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 265374019 1250 265372769 265372777
    0x1140609030c01080703020c0109081909061b0510020418061403120904020f0a05070b010e040305030f18100204051201270305040302150306010e03070602100e0a060609150b 76
    0x75009102100081e00115100c0d00c0c0a0a80014035034200508010700900b8010300702e0f400d0280c011240d82e1001003001c1300740d022501ca441e604124000400b0b210456021402100402c000080d1118141eaa41005810081c9030030110740748a100040c005981d21043d10390240e0401140342c200419581c2c0c14245200400c1d803040c49070b261300481e6681c0e00d246034120142013031100c054401410013a4040300300c2c1460344100d076a43d010410100e80d035000c1210b00703c2118090455007201e40300760306159134041c140c0d000161070451801d007130000148404601c40100034070306144408503103505c255544584000c4d03100d80a182e00842e0203501080d0044c00502942e00541c1c04644402d4251036440768910000c0018007045040110030400040566288068043e4140d543c000e03095407410038500241035014000c03440d82c0039410080c000c0003165000300300400000c901d0807003c92104022400c49003005400b000c028007191070040301003403c03056a032104800310001000410350380c0c1c541100311440d000b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 265375269 1250 265374019 265374037
    0x110108010b19021005100314010603110111150f07090806150607051203010f09060e060d061508030d020c070e011202010309020a170d030b01030c020601090e0c030f06011406 76
    0x1001c0000700c900b80c1c00301450a11526035441502c03283e03100f6003560f40c25243d083c0c07220824100c901c1800d00510110ba903003001040d0080c002008140d2540d81d40c01101d26090113424140304c90801c01300b0710310100b4130880b0002008450211030b50b2400c0390501d15258020340d600d40015110141c081106080001c1d0f09004d00c0b034184403018000040010040389a10460086031240144400310b01003505010142d40038040c05a682d0340a1802c014026040301c44542c000c80603d10f2480501c949034552044404410350800004240c5485501031802c56407031641c0101118400000c00403955549603000e050540441c00c182e51105a503000111f9004000f8003540181c80f01d420070240c01036001e603010340011072000d0100c0c40d45954458100079113090780c150864094108803282101c95a141c49481504842403c0c00c10049605540095840005008203610f159542a50202c0d10104100e540321180f0010100c41d01c03112081e000d240c80305030a2080014402070860744484d13503d80750b015100440 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 265376519 1250 265375269 265375289
    0x60406090506030901090b0a0c030c09030206120c130902070b090a05030f180a06030f061e03060509070b280f1e090902041509050a0e0c0307050c160311010801 70
    0x38200000c100b02c5a1000c1c0000949640c0c54042e035000a840801051080c0907000c0c0024034242c2c640e00107000c0d2902200702e03c0c100b10200c0c20601c01070b6129815a040000c052842c40c0355580c031810041807902c2442004107404c5d0000600190410703c43e002410414441c440300c41d191707240c000c50103544d002c000300c00502d283c0092001a00c001070f0807018001d05903051820040458640020580c144826008000043c0e210040300030ac88455005035001080505842c14415044003102512003015000040a0a4036400490110501001041d01809c18010040e0b510602d172410307131401d20100a111070342405600200d1040b03038002c0f881d40410b03007020f032510319540600740344030b05910352481c0100045c000018408501e20301c0510142c0090032100c150107011008112000d090014642d02083c440c0102081c01d20040384c1c2210b6094001c1840000d02e03440351540c69040d1035502650f07a600d0820300c5010b00d54800b01000c07190b0303982228001d0085015110841c0c0044610310001d0103038002b0302d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 265377769 1250 265376519 265376537
    0x303130303080702070e01060e01031a011209050c0402040e090d020111120601180f1707051005070201050d020c150c071a09160315050112030f0e0607150603030806060406 75
    0x1c01d00660400ea44080544140c41100d500c0e0341e81e054074080d082c0c1010300014001c1c601c1d26050b5030948100c5001c81000b0b039146840c640440f0000300302003070f146002800c240e128980308003041380c10401c6821086c002003055465036200c1017030030240c04003140c045113544a041c805090490061240e868000300051798646000007002c2080d8030b0340c01c0900101c0c100058010084e0f444a030b024400e1016151900c0c100d00342c40e241008010746803001c424a0140c4d40c000300c404011540c0d03040741429603101241019a102c00284c001650540203d0b10a004103d0000410850054000c10005003084d03a100340d840c065200c2e83c4250040380100e0000030014012040c0c289107944a6401f400e5001103140100c40d0450310441d0b44810101090b803040300e1a40300c1c940306540b407180782c0c040c880c0503054001c050050421141c40003080321440e00900804d000c00003811420685800040300d140300d810201d904001101c418154000b400b01d80710560000b462a008116145481c0c011182260031540e1280b40d1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 265379019 1250 265377769 265377773
    0x11a0301110f120c040306050a0c0f0905010801090905010e03030c09150f160c050315061509010503071223070e0109050f1302071b0e0622020307030b0a2303031303 72
    0x88514050f1004481d04c0040c131002002403098094180301c2d081c40d52022506ca00e0010010703203218515111070080c031070f0381101800a6680700c4800ca04680313044901003121b80d03050600c1030050403101d132100030034000002044500d1540314000e0500007000d031458506095801d400fa503090103000c1003555415001c004152940e205641d80d404114001d08400d45982c0d030b5600024685041c1044030b101c08082c0b40300304865880c0c254600c0341900d966155070361500f514000000c0c41844010311040c02d12483d40e698030f00200712940415003031016204050030641310203003c0c00902008030707034820001e1408100c1d610103501c1841403070215800a408482e10440102c00c018648008180b118102130b4223115003004504243c03581510001904100c05006040c8400d44620450003400c00b405190340d4004c1e070b030444480c1c0c0040003000c4106038005881c1d4442d00350031809880e0481c034150380000402c1002c150b40007149a401d0702c1c40625910000c10703104101c00c0c96107030b0181911210b545001c07041c00b000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 265380269 1250 265379019 265379047
    0x708070312050f0a030b01021f09110d02010807110c060a05120601020a1104020a05120a0203090d0201090201020604030815040c18050114030103030804030c06050109061505090f130e011a0301110f 86
    0x1b0b02540500542d03003c5001241c0004070b40754409070801380c05440340200814000034180c061310740381e425078605211102c5500060329501d4098211410441050700c4908200d505003c40181c12800900683d5503080e10b000080030b5070044044404103103e182c01081f8290700000d00c98004560210341c40404505210070040250880709021051180410025401c4610684c03841e2065040500041c0c0b20304108580500d000c0c2448110810f5a2401020340c0240c0e030000340d455030003075040c58072441c030766a502c2541c09904400d944594020f81410740d80c0300c5e601c0e0041c4100c0414000064420401552100112585203020b54000c0e0030400c20801031020078030600304107600502a003042031503001d556036071800301c80c4240e100c00000380d690481031000401004851712a0001454420f082207842e20002703107007246544e01540305941082c1054081c100c5500220920b01840e0001c000c20183c21003003e0540c0090715516110354a040099490901c105054070050245120428180b20380b03801050 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 265381519 1250 265380269 265380281
    0xe030105040f1401110c03071406130807020406080a0b0601020105070f0507060b030a05150609070903120f0e1c0c060203030106080109050603100f0b0109050609100e120708070312050f0a03 83
    0x855505c03002c01c66003240e032000003013155000c900000e550300c400c5410704100484640b66100d003140c002e034040c003109100c0c00f040030a0144d04510384964a14031361001800a102e10b506c03514860155040c1c03941803000c0000c000e84145000c2c0c000303008aa8917007034110740d0b000411240b280855070502021003c280141d02c0902034003005411114480707043d845d803030300d448443e1414110407001030040214078100840010b0b00260f03e81028204141150340303070210154020421000c0240100131040d40621840300181d0801001d001120300902d00108040304001d489002d80e82d60b54061000140580300108072412a0469581d41e1400d9003446c00800103014003600391640f40c4554807001c2c4c0000910711030440c24031350b0050002041c0801a0003d01030b901103a0049104002c240801005074845014081c4180000d2410040c00000900000d032650302d80480c0c405603102d05000851040000030b046800e4030b004040720b0f03190f400811002c40d4035229110064141c0c010034400f04100d54083e4200f1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 265382769 1250 265381519 265381553
    0x60f06060a2303010b0a11071d0a0917040305070e0c04170708010213080c010201091e0f211b1e082101060f03180318090f05070e030105040f 62
    0x110b40311041c1c14040e00c199007084e0031000d41000d0000d6080e2213181c11501c1c1c03000d4210040090450b0501c1d10b50380300807000351f0707200401140c05050000f13200c152203540103402e000c0d44606044035080200c406106140c10900049603244512240881c90810b220039151083c031520403600d140c6400d080002c2025501e4062070f02580c0b20b11400803507420407c1c0058440f030390024030100d81c40b901d001841807802e503d485086055914150600c00401c44030703880d4140708040350300b00000c044100d00e41250050180007010704040d10b90303000e515000021030150000302e24103945d00e40d684000100821501d0040c0c840007400d0507103145900d642c010000b0320f45134a00e4041e404403070903d5502c442c050000b0082145450609200303400501801d41c0101e041c41821001e403504102c1080c010030460406001c980c0c0c05000e02109100056401c0c81204c00d40c0302801d0b80940c00d1000c680100b5088024000c01c4c0c40d5100410711603901c40c91036050510034244995003043d510b0800380c00d251103036a040d04e216000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 265384019 1250 265382769 265382807
    0x40b1801030204270503030a0506060c120a0e041a01030b01210515060318210f031015090509060906060703030e1e0a0b0709050d060b1909020c060f06060a 68
    0x1c2d113690110110800703d400e028001441d0b82e4034041140d0811280020009403044000348002d41c80c9040c0000d021000082c240c0d9126614446203105580141c1e001c08071550103070514040c0e00800701503042410880d0704c01e0301c060251803103060042d1101018400f001018116040d5002e05445241c0c00851b00000d21101e03143c100c049020100386994030443e08540b03140c4101008901444040010754040e44410b080000841d0180208000030321400c081302401c80f8000c0003295540c04c03001c040d0001411080e0b2802003c4150320000340c08010144143d921030000540090014142000003900c03030031006201d40d03d068016902500107044190169120340705022003a4059403028035a0090300d0710900c0203001101081c50b1984960500801100800a144004203e40c1d280c4000c0c0218280d40002c0205041e1200400b041800016529903c2d200da140540020680c46503070044c01d51222550594440365504074002202d8142503540582101e0108400143c080c81244a62200c050f2070403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 265385269 1250 265384019 265384061
    0xa12050601121107021519080402030c040504150f0231031401290f21030d0b13060312050c10020705010b01022a01030e0c090103030905040b1801030204 67
    0x80b600040f10918240070203200e80006181082d445c0800c0012000041940503038900111400c061825404000c8041c00f8056200c1c042000c5541c14480e41484140141041000d46040c0c1808865103082403030380c5120740d1407d40f410088070058021548000302c0241d02d5010f0b032480e11205400742405640d01c1803401c444400100000352480c44014005001e0000815403940e48040c071014404049803504058003040c6840b050380c1c42d2488241000d400032245c0d481040a200b80c4124850366030031201030319000020b00b806102c60194812182c0c00700030344045042086414580013240e00c2804081e1050b07040c51280b5101c1c51240c0011b01885116006581e522482c1c1000c1078140e800c203101c110b803542d455841c03059040d68100b0402e00301c40c0941111102c194200800d940c4003a002c1401e1070304242d2124005070510034100300c881c0d0714640180498000c1e6175282401012211a0f006081c81a42410480e0030180b0308105c054040880120310312005919640c20031000700100350b800c20444007442 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 265386519 1250 265385269 265385297
    0xc06070807021f0605010f0e03060c0c0f0f1b0102030703020606060901030609020c0601090e0a0309090908070b1009060f08340306020d06150507060b01200304080709020a12050601 79
    0xb82650400f404050300403582900344400508007807a80003410f020488800b060100a681c0060100e4200d4a0792a1559440000000700790500049541000f4540700c2c2104000c5204000512000743c2071001c1c440c0304041c40f200c4012070700c7e8420001d0203401a44040d012440310300d0508014441d1910504001440e51b640703415180c280e80194030461840d4100e0720040005d01c07441d000320b200781c0900102030300080009030340140ca010b440c0e004280c0d0045e5244e050340100310aa800f1030761440d030040c0d26521149442e40b040c40100040703008041d01c141c14400000b800c18413040710784055440d07410280c00711900041c0641d907500d802200540d0242d4407022507090620080007541c01440c0101400341e507503614040c0740401d4030280c4d0301401c500d4590862003006194044203403049140d100c40c01244980f80e044c0102c2d1060084070100121100b2000001444080000280704a650420a1352481c0b80d642412004a00818031031201080c90101245405000c0341d011a500c2941410464a014024 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 265387769 1250 265386519 265386553
    0x1061d210f0f03030a0f060324090f050102031504050915041a18160308041403070b0309010905190210200303101e0b1c06050d03030b0a06050c0607080702 68
    0x4030142c801c198100005001e11140c0381d01488000c403003954002d10802d0b1465642d10344420b44801d8650021401c0131685210364240e4000382c050540141c40c0d44244082820a94001d500035141c503001602040401d80480c01c1600030288240c842d003015041d0490251180d0303da50100a20480e0307018000708a52000b00120050540115201c001110b00c00c44c0064800785040340311040c4a810922100080000602400842e4150307000c10000305072103003000010a281013199000a101e020021007003094086d4154040b090190050049800e0a81e0007250100d04a210f00d0002e9040170f11260000d0744203002e07612029900710032440203085660b24082d03c6040d5042030360052908004a1801c10101000010085920407620b126081040c07901400d40210311a28426601c80301c600310602604814130382c003600081001804002600c107007031074010010301c19200640c0c860994120049412481141503591207034182c0010a104e03100e86c1310580b42c08900030f0040303003148100400d0034100050 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 265389019 1250 265387769 265387783
    0x52107050114010e0106021506040b010c0f0305030a06090b090402190807080d112e0b0a030f060501060206090c04090f120306030309090209030c090c0909010e01061d210f 75
    0x4411082d420750600c10380440030001070707220904562101c10b4150b00800c200408070340094049800141c01040c01c0c0068480348880000a4001e0f0701d5009c0c454107140c4c00c03100031880341c0307800481046820384a086030405c40ba80c05c030f42203811140103000540182808480c9082036010085c00840070b40e65500020300d0501c0380d8101c8109900b009070310080c81ca4110300c403200d800c00040b001e050a04140d82c1d034480c496260b110883c10141c5004c2d01075041c003545d0f50180461a5014202c000601d80340d082c070380c051080c1390a044904918000000562500c080f496500800c525030103008030311341d043d0030030000e061b510344150b404c054020040c000064000e211040d00c4035098401240940c914107000d84248426031221086500411900d0010b03580459040b05d007103000c0f203603400c95440d00c10b600e00c014014082c0382074205212000200e04410200700650403a003450341c0310710b41c130340c20b1000c583d4041c15203401c84c541007070168900b44180030880d4207904241c0d0300d40086540c50f2034000c580f40d18000d0707 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 265390269 1250 265389019 265389041
    0x6070203120610021c051c0509070902090d0b09011104060e010905030d0203070f2109031401060608012601020307111c0503040b0703020c120405040f0501030521070501 74
    0x1000140c410000d6155840c4198402d004a800340c51110350300d50040d403500720616041010303450540180c0f101c40c2c041c074292180170910b0300c1e028842c0d55000c0003010080409513441d02e41403040010000380f0307100c14002c1b07400d210000b90004044140c241c0e941200c809010300016525500c40c80d4001ca820081406000288520f644418505111100141152510390046d44c000d400510300b030304a40f6000411903422303580c07181045440b21b005042c00c4100147d44552000b11200035010708480a80c001415016203000e0500f01100c41050030240d400c0389d075503100b00c0c0c0200f403c1d4001000102440c003c820082a040e03e182d100c118000000c07142280e00c06c03240b1601140190304a150551001c1110440026010840403501b01e583c0b0f0b000742141c000248010070140200000841407442901074803556090700302140d09002d004003080c40b6580040c000c0310b008034941500480c1da440180140c604880c0c00c2806003290414800209142260086100382c002c0410804400002d0007407185108e915 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 265391519 1250 265390269 265390273
    0xe040903030504020f030f07120206070f08031e010f03110d020d0b09010b0a0b07082d0a0e0603100905130f060b01030c0f090e070c0b04050c010801060306080a020402070f05060702 79
    0x202e003d10405c54811888080b25001e039000719080224845c0c0054404d0a42d0b070b00d1380500303014a00f588000f6843c2d12841000500038100c1c4c1d00624104241d900142d4042e030300d607003080086045296035054905800340f0694440310015602080490082081c0440415018000c2c46a800f13164010900d14a080c01d03003211200035230340c03c00448400c2803003003104001c82111590034162070702207001014003c1140c00f8009007000100403060743c0c03580003003a0002c1001548840ca0358182800040f454101020b11008943d1070028001107103840803c4900c91011800c7d0b01a0442c04d20304100010030300200020500e940c1040030402081030074a01c035090900c43c40d130128900071810001426110310480620030302000312000031800f500b20021005580341112600160340d00e104045540301c80c01d010141c0310410003000d210070302001044c03c90348002d080c0c8032801c003a681e40700110119101d40c13044e176490750483d0820400510782500142012409034045021a17081034950030f04228017a51400c007d6 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 265392769 1250 265391519 265391521
    0x80a0b1303170606390c010c080d02070203121201050a05010507060e120705010207050d02030301050607120507060203070c0b06030f0322050a0611011a060414030111040626150904030e0409030305 86
    0xc5c2c010004c901000d01104000d040c004103094006080854405401021110007241942103034a0945c15100003640080441304100007c1041c04103551040c5c68442d04222800008501c50403c04295002c80302e041c0d488500c0d0040688962005210460308440f5030700034400c2d503182d0080e22201802d140d90081d000161358070310510740300d440d0240400420065402c2031004021036682c84080c2c90301140c1000c0040d41c102c283c0101100c8600c03542c000280f9651020003807101c0315502940142c3c0d8079100382c01c1c07400c5a88401d810541d44103039a48030f0761042d0b4070401a00501c5140e5031443c00c41c0884145190039400c0c0c40d28000350039258aa04440005000034401444a900c240149940c1a07044e900d14812000d500b00070805521590181043c0c2e403003002d401e030000f91801d500c0f1152414810078065115030310340c0b1000308083c854105001c00521552408403d5400c0820701074040c8001006003284001640103000796840000c000b941444640b081c413001503201c0e0300400c24554841e0741c0000715 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 265394019 1250 265392769 265392847
    0x904091704050a090b0f10050c030d020315090c0a05090a0806040b071b171809010b0c0106090e030d180f03020d09060e0f19050604080a0b1303170606 66
    0x3c0410280e114003400d5007842c0c140b100648030b5806035a500d24007591100405440c4120a0b03606216040c20009140301c006a003104d42e81c01c55002d5405078561482d903070408401c44082180020f019541740d000790400708006000140503000810031400c0141122010942c0c0d40389103400c0c144111015100351000b2001c0207105940100840384010962101114203215130f11206c00c1d034807071841181c0d80000000b4191140000950001c0f03a00b0100500c040659a11044049059000a003131041d266003800340205680d4014001d060b10f03850300c0e000850518030407034820005000d8518505000d00030340d031540740200c3e48269a03001d044e07020350010703e0440000c941c010104246648070404010b0b24404c041895560b0348c80c0d10400aa085a5114812000e1200302034844142c3d4441070348400c0001d400a801c410110300a510130740188032104043c2e80f082c04103401140e11000c01800600304900035107a401070f1810040c0c010304080d00c158141001c0348600e44495401418419001c0e030302102482c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 265395269 1250 265394019 265394029
    0x5100902041808040b030a060e190c09030b13060902090f07090b040e1f05040e0c040f11040b030403020a0f0b040b0a020a0f0c021305041a09030901090308090409170405 74
    0x251042026881140202094030743c1c00c690b010314012451924000408902d0300c9805800101c040e00300d281b00b588580c10160228400210b00d070481442940c1440c84100103140503402010440e600444011059a00c1d1081ca0041c400c0c031040445103141e46540c4000940c0740d0b1402c03144140040c485031030040c20808400780111910f03900001c1c22075010001404040c0c00403a40c40d0f04204100e80300c0752202000314002011480b02d4202c80d400515240641c03800c828000780d812445041594108075000314010450160b611000c00c00e003c10a0402c01008601c051200541c1d000b4000e10590381c520f0000d0f6500103813150314a00035103c20307030100b06000902403800c2019802920f0000214a4030314005c40291800c078581d552300f001d0200c510a00b0080d5110a00100d2000440302000c10040c41e083c03406404c207441c00c0000d10110f0203c4000210341c080008211803008105864441c40c80d883e550701d090003903010402c040c0d00a6164900000041e02c00b5440700505007c0b1440d00c0c0d191810001405 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 265396519 1250 265395269 265395281
    0x506162a050306060d0b45030304020a0302010c0302010f1125050c240a051209070302030a06020a0507020406090204090b030c0d080a0c080d090606060203031b090d0510090204 77
    0x1803280e0441e405002c150368070500d260054950000880486d980c55641c00504503104a0f0002e8108011a40700d4914a01002d880d46004002c01111108245100002541e90008643c001e4005032081c038180701540c00342c41d1a09866200b480080744a81c8900081d030150f890000c08141c10300e1011070f4000700031400394918a40400e002021021401154aa4075528400c41c4403a5018001d0940600580d00c0d0007030540f2071030034a44500c1c99a50991324401440b543c450900200d2041e40d0030046101440007050b000200c0c2c1e0000d005207003900c2c031619514025480900303500e0610804100020058996000310001040340301c40c0117031a03a00e001c0c441815696440c0300705120b5040005050040e50f64100c0742c001294100c410103464040040342a640b0300c5ca12040601650b20100342000b940c001e07900070020b40c0384180002c2c44480c2d56614242d03178070b0001703035042070120384551134170344648a803200030b000d9400008103022100384082d164a801c10881002c03500c44030f903d50b0218029800e02d80201 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 265397769 1250 265396519 265396529
    0xf04060e010e130c0c06151e0608070f030e01140603010614030a06110f07060506010912120804030e0d060b0a0503070b030c0a0314010e060112020a05040506162a 71
    0x60800340b41004001000009240c090710401070f991140400381d14402e0fa4106502e41d40200100701c4030b684a01c8200003082d13207205100b4128004028180c221160042c08000c03180b450300c80440540703620034103650540208030f40a00705551180f40c0900700200340204000300204400d12141c905111040c1800c1d220103402948059a0b400340009403900d00080f80b0900ca500800009100100010032240c00e10450a250f204550046a5403090204c15841140251030980b03601c0c440070b0b99803041c8000c1c030400d600c021b408100d029002d1400c40c0d000d0040709910034801d2400103600c0514500144000001d22401d450752a03170f46038140c0860802c1000c51000c0c00c0120001c080c031510744a9078003964800242100030f00c10003c00c100d50014020b811545156107070307015042c11980c41e40e0f140c0c1100a01110261700003480d015601940c04000e1003110304008150784e40b646170034101018070901c1c0c1c0c080442c03102c0f83c80c2c07280c0003040410b401840300d4010301c02290a06004510308580c1422000868001c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 265399019 1250 265397769 265397777
    0x412020114062112040f081b010c140f070b090406170703030f1202070f03080f0105090c09010210061202100302130504240608060102010e06040c0303230f04060e01 72
    0x1800b41d035075144041c00c9105a400c5101203860500048054140280c3d01500e46120b00049004114250b0181042040d40c6400084441c3c1c0b10052458468003c00d034455136011031034280181c0045401c880c002c9003c910000111640310f6503080c004d901e009038a6000454220000ca0010b07103902d0b080c0a804014415036801c1107110750081c103c2a200c0d50684002001d002c0c040d86075290442c0260000e0751403482e1400c0843d15007d503401d2031088005c050a08a0000d041080045c18592107400c1c194160345d0090b012210541d82c03241800540d9029480e0541584038002c0d60065600302401054080c0c00180b00b030404100c2c141c41408040e2901000880506d401400225601604480c0708022075808890214801002070081111444201c0c10049030900898000c107010742c224415034010082a4002c0101c0306080000640b00c1401342c0c2c008010802c00d0b0000c01c0400c2c401e00001d203020395400c0703414141d0400039090714081e9001c0e4074040344018022408221141e0000d140da070080c002801c0c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 265400269 1250 265399019 265399021
    0x30201020903010b0303130e130f0c030b0c07260c0601031a0c12070302130305010c0c0b060f0607020d030e1906120204080a1401110a0905191d06040b090412020114 72
    0x5281f014055105900303084e200183e12404113088901010390402e8901508880a0a00a94400321400260307103c1d203160b070124003042c03050742c12105000c0e0007881d91088250000614800c1440c40c2ea88800c120a003070010107100c080a10082d030007513228200021981942d03449400f0f103054010040b040c100414041c4d00300000707400c40c01e02d5111025181c01607550390078140159140042d80c00c060f00703562910032090b52440d04040301458643c002e400300c449a0342c2e90010480c10700e00501c10b403034220006000440041c01c00400a0034014030070b003002c0f485c0181c5a00450340f8050f220039402615518000100001c60300b140c14002154102c03003042d4a4141050072140d80c54407021001070401a24400904903100203521015241002c800c6c0340d80d0740c03240c43d240100301103c82c2c01803602c00c4012044032100c0f0f6902001441c111800082c5104d00c0790003040e010482460001c0074642c00984400c01c0b0f41c51a9540c10641d44590710a00c0ca203500702e21003440090840d00610440e90300034920324 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 265401519 1250 265400269 265400287
    0x5030f060c070f1505010e070206090c0307060302130b0f0715090209010b030a060308270d02030607081005090403110f010908031f210201020d0c0b04020607020402090d030201020903010b0303 84
    0x1c030484040c5600107804081054992900c00b00c8803000c6050401854075200001c580d070030880da600e47c050b44150742210a992075001d4007507140c104100c035450707042e84410420400b540c041e4016001200041030290f0110342d032004064041d51245600c01502d07513001620404001c7c0c0c8280301c8114100c7e41400b0001c0503059808a1408001805070106c80711000c40040e41855249d088080a1075102c2090b5403104503454001a0703442048448100c0e0141d07042000141c1e0a04540c007104d915001001003900707458042040e00d4103030300035060700300342d00007030002242a03151814145d002c0c07440b90381d4400c0b1403c500111a0b0a003182c1d03014003030a50341080061000301e003412082c1c0b030300031103030807801c0f0030b1681852100d081d841d800791300c101080c2c6036103103c000c102c0c220b946000e01107074000c3c5c098030308508403184210381408212170300030680e241000c0031030058240000038081e030a101410041c901900301c400280c162660100480041c1e40000d0074003502e0030280107140c54000305500460401d2804 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 265402769 1250 265401519 265401541
    0x604091407181403160303080601091a04061808010c210203090706110102250c0b1303080922050907151403100b041805010510050d051009140105030f06 67
    0x180c03040300302e115404030310060565030600042d100c011a000c0001d00c2951b880c80c01510341c4004072500350105018403c0090b0050010a80c1c503000800c0f80f005a18040c2406410f940c94181c4c2c180000440480c0342001c06c07054000d11425102c03601c0e07900c480070008400c0c1080b103904450110b54003606801403040c02801100090044140e4a240c1046030b401010418154024080c003100720415040890f04800b05824014001c401c1a0051307002050460300c50b0700740030262048101c0c200504030101310400c08640c60314050320740c0050090010709924030460316407100c80101a00c0303140d5560340b00300303104041c9010040a4001c15104c071005120b00004070703010304103a071600e500303018034000000010210031404c058500506003580016455540b00c251168106030246409d0503418641000170400f89803074504a00322480c07541e0796514090507070650300f020f8400079007a000c2049002e6808103c0c42041d0050480786010310010b00002d40c9010201490310342e10100081c12a00501d041c48030390f09803 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 265404019 1250 265402769 265402817
    0x71d01050d0506040f0311100b180f010b0a0c0b0115090905090a020d02040f090506040605010914190b090c0d0f150e0c0d05040605012606150a050604091407 69
    0x2611117810407036904080d40d0350107054207003600c80e0203404010103482d00541c0c00428924410348854081c070040c512045480a000c0d10f050880e40ca0002c010800544220000e200810152428000390000fa80e12034202d01c07802c1c0c11902c200c60031301a440c02c1c0755030300006040051001c084284100d0501c0b000c000e8840c004c0700d038040d000fa484002c280081d52116040030130107101028080003004801d041154413a20180d40468000e402c0c5400020320004e9801254001c1040d070520a1450b2104403001e110400c08128031064291035440f4610f143d0746042c000340c803c0541c60fa40f196101c0b500c44c01b00c0304031140c0142d0355100f107260480c18694200b00f1540d00d400d403a1320004110840d02c03a100303030155078010012401602403e150401003002010303040203040b600000ea90012045041100700130004c000d00088a542e8030450025007500312404510f0002c50000d41383c0d0030220740b03901c0852007a9100b508820340181d01c4000c100e0b40301d6900002c0703030b9018a540ca0449884210615104d0418403 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 265405269 1250 265404019 265404023
    0x102061506071a1017010501031a1e01172509020a09091a0901080a02010c0303180b0a0608061b04060e060418060905070f050426071d01050d050604 65
    0x14002c56000100500322042246041c0c01a012000d14542072600701044141030090031242c0946081e80d010424050103068107803640f0020003142c0408089420b04c580c3e100800b142c100402c2c0040c00c0c6091000c8e460ba5038040c00080110b40310220000c0e04040c54005075103602d8041c01c42c05907403001c80c0181e44414005460b15410090380e07408500004480344103030307a04520485840c1070600600002e5241e0b5444084506030b80040f008e0b80d0314182141c46088801c000390101d0101c09010000034440c1d4080c0c0b6045a68403104084800e041e1a144207403070046408001860380c0300c8091110752801c00540c1d80c800c1c0340164203206448031081d0307070440f03024a104020600a40e100c08d0081a91540140c4014007151141c594100b40007084440c0039181e03600c075a000251800c40400c0c0041c1c030524104402e40d04640300e16207881d14100d80540c0006140c0c41811307501c240c2030708070949803100380f040c40010214000303046440368420401d4080c421043e80702034441c188460814000500c0030a4080d4065 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 265406519 1250 265405269 265405279
    0x50709140117012112020c03010f0501080a03110f0f0c0a05150d020706021e120603031e0906040801090c08010b0f01080a241d10030803040f05010209041b02060601020615 75
    0x2041d50807450242018582c1c010000000440c000000590014060340b88460231402840340c600d49001c003030200c2d5000e01441e42c403604542160004a0b0081611441c18a02082243d08210400340d8150400358075010741042500071000f804a18034090340b00e400070741004c94141c3c85105840c1d0080a4030b11403047d00e10450383d0013042e400d090168540c180c803204a0301245101d07010720b005009002d07652003d400c088281c181400405c401e03042c0001510304290046d40421540c1d07a20440c07000b0740d90020700602e5417000d0b04210101e407a69081c041c50580074440d086840103a810010607a0960341170b540c2050248103210b0300b0195a070782c05005142c0041c024400054407a041500072180412050794040301c4207540080041c0c2d03001e8440014a001114021060300c5440d118502c0c18050100d100260840030140007207008504103d80c10709107588038100043c038003a0901d011406903510104080b50003d119150801c0e821380501c805030b4040000d101802481c81c1007440b00c080d900e2071841c058020 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 265407769 1250 265406519 265406549
    0x30e07080a023607030e0609030d020702040b0a03140d08070509010c03020a02030d0207210f060b180a051b120a0b030708030f030108070b0406170a0f05070914011701 73
    0x341540c48000e01c141c071403007a202030100b0703146543c2c03140b0303050540d0708000080c901660000c4a00003c1800c5000e500b00001561604d014600041c0107504007010580e44540e550800840659840d0740c000c000790300c128010b8400d00d03503030b07400681230408407480d03181401a80342c20408050b500c042280c80480c1c003400c207421096050f0800700e18203410108000c0d050b10852144d903460603000150388040362015640c502e103040340c501c0083c1d50500c0b1004000e01c014005604500002c101ea004207984030b0014051050341151070390a034900d03010070303181c500c0c400e41d40b030051000400540d14801d0314041d20028003450040c20b1501401c58403c014440704801e96191400480d9075410300c0700d0b500809814003140c7c0ca601040c807691882c0c0d0b200b8482d00060f841103410000740c0200e80c00c1941e003154051303205d40e041c898401c80080c0701140c004281001166484120040a50140c481c0741c3c080d91223a622820a40d040070341d4100d440b0280c82d4010306100c10214009051200d09540505448030803c201d410 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 265409019 1250 265407769 265407799
    0x106050307120608150a050106020109051e2a09060603040b130602040909030201270209011a0d02040605070210030e0c0d0204020906040e1515090409030c0206030c0406030e07080a02 80
    0x70003a54104001d14028800702440207002c100c840c900804041b0300402039070b43c1c2c440060f401c80d20f0101004104d40c102814400e80d0880030f594000c2e2428001040d1611034058030018060700350610603116200720142c80e411254140185241d9001d030054504078a5820180c940300442d460080401940704074880e410010010725406542c01056000414040b600c01071801178042c1800d00061007a0440c0d06078075180c0724806001d03000440b600079003a400140d0800641c2c2041d5251440000b80c070b02000c01401200040510013803004040e59550952102040d10400c00c44490034050f201c205810030751024804000404c42480300d600480d84003009a08601c00702e4040e000356501c45900c20008200000e0391403480b11040d115590702d1019001403100c580812480141d00403621314983e00c144401c28450800c0d41c06480224003908110b0741c00315040e800200035602c21180b0015510303000c0f5041101c1030309400340008802040c40a0040582800081c1c4d9442c03800f0040a80305081200c803080d5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 265410269 1250 265409019 265409021
    0x121e0e0304030c060f2a1b0314060f06130902060406030218030106050a060c030215010e09060a15121410020c010e0a02060f0906040902030a14181c1709010603020a0e010605030712 79
    0x2805a000c03031f52940150484680ca410410f182c80181c0c0c000b1010100760f03042c2800800c40703510880890075000007540790724041c0030480268140120075541d40e95452030160b60380d000680014036003a40c01695170280f0a54500b200038485040701e000c0d030f04122081c032a594484903120180d40403072a118582c0200350400b00e1a11200c1650071340d4880c1080004a00b08001880d550700c05c09aa900f118a5505c80c0301580d01100e04070360410010285800c000d01155010341f214810b106d0103003102c030302c104514455035410b080985981d690001d900180c14000d2100c28041e0507015062140604003040d0550085407141c8582e691284400780c0005141d0b144d640c4544c1614084c0107010340454491500380c0202008110b400d01501440200000041c401e000d000c0e11039851220440c00b9003122445046a290030a000c110002c0600604c8120300c8540d03494000620b12500702c41001150f51891401401550707149900580146281a40103024541c2c0004c2100d41210242c81c0142c159003031803204070 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 265411519 1250 265410269 265410347
    0xb25110d0f0201140412111203040f03090504020c10050c09060f03060120060403030f0614010c0501020904090308160203040602061303020705060408012901121e0e0304030c060f 78
    0x3031130200800b07003480140300001c505441421015183c0640003c080740348103580e1200032100d111200d01c20000100000e050b1100000036600c241491352a064840000034103030303040180300640079400003041d8000d00c0c0440c013175030303800200c181612840c010303006011811600c168100d80003100b10000c045400e99118404510807c1e444044681c0d0242a11107403e4980c90b080e80c05400003402c002125624200380c2c0b00d1070046801c0c2c8040180b61130784440066030400e203004026240c5541c03e10218140d51100d0042202c1248269a4175141d8905545290000b06240c0c044000310340c42444240700c0d1580000d203d940000d04092503100c81c1140c1e24049240c1107240c0c0100382c0100d0041030001304414150041e2140030341130340844802003038903c0c40000d254003940d080c0b030020740780c41e030b4080542c00c1987c012001d0366041540444090001034075a41130b04d00080c40c10074580d000090802c2030190842a8502500c0c2503e0501c40032600c1c50302c010f02210001c0d0030021080d407d100c10442c920302c000340a07 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 265412769 1250 265411519 265411541
    0x5091e0d050d0f0801211506030212070e09010504030c03140403050106060504180b01050405041107060c2109020a060807110f07060f0903050d080c070b25110d0f0201 73
    0x9841602c44010000c101600c4240120041034010f400410080e201010403411003030140740395846607201d5164170b072458030f100350508483c40c1d41c2d21001c009030321000f0f020384440307200b131005141c150300e04000050481c81c0100300c04440e0340b601c0140400285d0003c0b0710700d10750350145480f49403041d1905111a00c0d1240d50700042030396203803460001e443d60f0090060700807145803041302c421880881c4c480b4400c1c1c03085070b504240010701c01c100602c04d80c03500e54031800e00001c401000724149400d60396900120394000c0c0104000c112045004142d031a610b1011307a91010080c00c05001044c8070f94007040a400c1240240014460900c002828491085d804035400d103500c2d40489403810020607100b40c548406004490000f03260720f5003400c00780e02403802d030f004aa502c40018584c0c510048002c8950f0000500300d00e041c018100309c40d4002c5130300b82d4912401742d20b000c01ca4085850305130f45405c040b844481a40002e000c0942010078240d81c0100c1d4851100015041c1f0410744000780c00d040b4018030000901c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 265414019 1250 265412769 265412773
    0x4150b030709020a1d03030a0816110a0c05040b01090803180111100e10020a120b03070e090c040b0405040506060d0809031b090117030a050d02090a0e0a0c05091e0d05 73
    0x5513901c440d0780a0002007240141e0850032032003035803c0080c15164401e10000d00007050a41000c514516607404903028606601d00d005c041c460b004081c0d07542071600780e2400392140d552001c010701041c5041c0c4110f24940100f42401c1d000e8074585500c0540b03078041c02010005420003c2801007050340590b44855414a900381525001003141c01441c0007003150760801e41131403040c4480b03030311000002d2003280c0c00400280c43d00d141c840c018104c1907000d806a815101e8140c0603a110005103040400c01c02802522a01c3c05800710a10490500081740c0d42d12010301d1144d41440c0a00c40821000311700f498200b0010358450441100c5820400740c01d100e082c11139a058840e002c442682c52400714400382448900710354002c1941d917104042c640b05001400410004d401c1000142d4020b40901f0040c492054150009070401d211a40050190500d80e40b2165219407800c00708511140c0342e01c21141d00c3c03950f46c01c051b82050a40c0000c0303807048031981394081030207803070004242490ba02c600d100c80540d0f0340181 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 265415269 1250 265414019 265414027
    0x6060302060d020d0f02090607170f0307020d03050a090f08090a0b0a030c030e0a0b0606071704060309021206010608070309060f0504141b030303070807030f090804060e0904150b03070902 82
    0x91940000c0d800000d03401d000710f00e40052060301c45540c1c02160342202c0020101405e214038ae44441c1d01c02074211202c84018081000b8491a028816018501c103040f42d40180285964141d400b078262007000744900b000314500400600021000e0815090090700480a9526907003a000456128486500041072204003c5102008650b16420010050780940c2c1c0502c44040380c3d0181c155102c903207000082c00380c11910001400b40c1044800340250501940201061700303100c90b050b8a0170380c0250450b80011391500840c00c15810905500718015070840010009d070340c981900205040d101030720b0807040680744e001c00d0085c082103800c41c15841c0c0c04c900080059041c60703d4102400c0c18030009000d0b00307005030316840d0005000e6030208a140d06000e001b551455940040880d1102001413a41c810300d80d880ca01544809128401c14805911420a9aa5560400c0405850700e105600c20904c52003a1400f00302c000303840c5c0300a403005814420f4020601e03451a600213030070041c460704503e400510200d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 265416519 1250 265415269 265415287
    0x31218060204050a06051908040512190e090f15131b0e06030108030f030c0c15090f030c0a0f0204061503060e01120203030a1211040602160503060702190606030206 72
    0x1074010000c980e03040310402c1c4000c1e0f581e10b0580341c0d030180d002d400303d5400e2194002600326000d10784250b4030030320030700c02da600000005c60100030b035400008000ca1b1003a007820300307240841d4004003080f04802d011a8198406e14005400c51180c0b0001410000c3d19102c0001c0740040e5195400703000080800c010042c854121050450494100d14140c2c14000070482d4dc070014450905d44201c9040c0c41c1007102440c5003480700072060569a0010340030309100807003004100302c6004188910041701c402528141c1d038034200f26062501c0c16405140041c4a5001000003494081e0000307040c082c115030109202203030a406000040041c0f4159002141c0d461040c20030845080d45517000d241600c8402b0402e548c0e690f2140c101944458140301e00a42590081103907034841800f42c001e00841d211040703c0851084c03202910040e03540c0255201c640960300c1151000e0b0600401c00004001d40005c4d4024421844c11140003555012034511284502c5a018148820b00040c0d0700904050b5402900f02682d9003410 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 265417769 1250 265416519 265416521
    0x61220062b0b0402090a1418090109140613110604081917030f01050121240801050906011205030c0a0f0b090c0108011502010e0d0302070203120a090303121806 70
    0xc00e40041402d1030542d50040600d443e10945100d690003900007a0128203010b404003420940000369503010190306c00001d654014001c400c0d201c6c144171400031510001d80d103403101c05d00c80341814058003030304080c0070014a030782a01c80c403503c1c4a03002079040c0010074002c40800c04074801c035002a507250040304c00e194a141945541010194881e00e042c3d03032069824030600710140019903062085040d0fa9004000541c4a01004194505000103000b00c50038020600021605908080500c89060048248140d66a009100b00901109009204030314101e28203986403041401502104c0c82c0ba1400402800010410340e003503500380b0350846100403d0350400c00307010445043d041f01d00c140c0f02070010314030740c001081600b00c12506071550f4035203900f404100362044c81000d002104541d40c81681a40e81c510810002c89146142d403401030340c8660030300501d800d0605040900c1083d4104000049126a00c000341c101101d8061410f0304039405c00c8002803002e00a003810b100214000306440c001841a1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 265419019 1250 265417769 265417837
    0x80a0302060a110a0f02030c011e1118100c050109050717011a100201090204110903070501050304030c020907030921030b030c03030d11070c03140106122006 69
    0x9400311920799581c980440d05888940c6892020307035100780180c200c0340e401070701c401820292500603641441480d520032030840300d0b14821007000005000d0941100ca5a40c8222044100c6140141d4a0044900c4500b4030684410041d98001c40030003e10410720741c42648003443d4654028000d02034030b081401c1c640e940344036600a05254000144003c60030760070520604030004000060120f60581c0182040402000c6034601c100b50354036510030400694941c460100c034a2840c01c681a200d603c42814103107441940e4001c1410f00000300305210129400c802c1e4190040d5040702e40074801e9550050480280c05e1545006200940b040c558038814400c801400700600701d175542c10086a400d80042603540c80c0c00c000c02d280c00d41c01c1000340010960194001d080c0c000440320803e49002116a521707c4414203682c01901c243e1700c2c0d001801000c090a0240200804001e070b4203011918032522200700280030500701d04080c841980e135601082d190b2000360b070a5200e1030031000300315854010381c03035100c408 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 265420269 1250 265419019 265419023
    0x70218040311010b10020a0311030d0213030c050f01081815010b0d051b0901030f060f120b13030e1903060c11010b120a15020906040f0e25030209040207080301080a 72
    0x108200390072200d030802e09420b8171580a030361300601003052140c4050381d4080002c4081030282c003041190000101490004111448906041d40032052a5040408221019410503849030300110b0315280c15070303404a00c4540109010300e00681408030304107418603280c00e11908541504040c0000a502c40ba184054010f00480c00030500c410703610704241100a160300081e0340700e1030600707001074000e5505c2035106c4052080c1d005000200c0c00c0e104d14050300810115407150689080700c0c808441001807040040740c000386040d480340b0b1004465a00940207401f031380500d5000c2c0c51100032004d9a400341141002c011a017080c0b0800c5101580307030300207000070f124100c80d10140d802c114100c1264206040c0030451071924402600d454015036074ae00c0c40140c00c0000c601c104c55021701c84180d86070b0312000100001c00c0508680e1000c1890080300000100004102ca0601807001d001007100c00030008086408207030354a80166a05080d00014009010740803010b012150048008280c2101c002a81c100b40c0b4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 265421519 1250 265420269 265420271
    0x1d0405040305221518080109080702130e030d020a030f0501240503040206030612150c0a120b03151f080f06010e160c17070b060a090c08040807021804031101 69
    0xb107882500d090f5001641c4070380b00804942e41e6002c400940b04640c1c401c04041302e0000554880d036101009030959000e04810f031068400001c2600852400038039a90491b00855030a1001c4030380003541949a0082c2000d00c14855000103408420038840d85c01f601140c3e203164010803540d40c55480488400b42c244500a400420447c042d45415001d081900e1040c0d80c02002186940d840005000c080700003a01855860300c07808407504101e8421020f0648030b05940b140309501c9031005003008140801c1000210410387c0b400748a05d00303580340071514111200d104400030300151201d440482d040c2c10319071811a40000c1c04503010800280214440c3c242c0411841112180e17600c40d48244050501520300703c003010402c4030316680c014002c00046022a000e141e40c4041038408460320401c0342e0003680f04440700761a0701c08000080c0b404207480c101601c5001010001082c0424010300804c0e8080d2018080305001b0603203500710359550110090458880c2e40000c8141011b1402400c0e034071150740350044039 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 265422769 1250 265421519 265421557
    0x110d0903030c020f030930030304150e0c09150301151508010612093306061103042105010912092304230114010905030601060f1d0405040305 62
    0x120380b0008481c04c4101245018603d021844d03000c0010f03842409070030381c80303500c680340000b200250700d00b03540d409014520300910755920341490900c0080d88881e5618024034649802000100300c000340000a40c4002d8410502c5ca03103a1244011110003408800ca51641c240941c0303003413980b5554080c82c122110445540446084150b054541040c00d0007601d00295044910400b103180a07041441014000d6540c20030350b054040910260201a906069050b41c0088200c5000c03130b010302c80c01c4002c1150380b4044400d103558240d85a10780c80f461181510100e5810b004903010342200c400950103607400310082086c1d8519150070301c940c400361400180854405040003443c030310b18105042820446203840c40c01050b02c5810000188a1100210000c80b0038003030324914050407a000742c0c0680000b400309080340d848a0001880024542c2026000c0e422503001040042d4000159185031003450406a8012890203c0412031001d501c0c016130f4000c0c1800f080c0024140c10500902e040c0341183d20ba074501c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 265424019 1250 265422769 265422791
    0x121503013e09010c020112022502030d080103020f010f0e0a0e07110a020f0603090a0b010b1e070f0308040203160f0e06030d0e06031f03050105090607020d08060105030406110d090303 80
    0x1075805a516080d0102c0c002407940001584540713102085258444001401c01c9106060b2143c00110450480c400c030801511440542c80c0c1000320215000d80744c5019511503055501164114401140300c0f810311001c185507085090041a02c03a1524034090400e0340c8495482e102544800c6003039521601007440101c0c200c08100300403d0301c50032950003800d01c1078140011018028940d0004011032414094808c019002441f01543c01d8001c1c81024121a1542c40b408075048499040b1519410a0102000100d000404210340301c0b0000f034041c00d00000594aa00211382090440041c0710b5540e12013103c0817401d621041c0c8000284d9041480460311a6a23000a00d55109040744d01360b40450301000401c0c0c49881c211000b103034010700d134903006030310703c0e44220b910008492150801c4565035115020415824020403020340d0242041c401400790303240b2094040c01c0b020018026904010000000a0a0102c40d4004022100c402015581d40301c080c013440700002c1011590031000a400c0c403240e40341e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 265425269 1250 265424019 265424141
    0x20f0d050a18050c1e090910060815180a080313120c0302030d0c0e0a2306031e2d100906140d0501060302060a0f0306050612150301 58
    0x95280e0f000000300700440303e20041043c07000702802c0c004142c0301d01e50300201380c5481e485085802100c450004122842001c050041650320b00d400910040d03110300c00e15020038816407501750308603141058120540e4002c142c040e0030400048000780c00500000148003414102507403448c981c500903440403c0000000d5000c84490040c06000b034010b0f4410701c1401701d200942d42c02505080e1503400c00f1b0500e1805900440c1d03141030142d0214201c2c1a4184d900880004409840001c05208a03540c07443d5190618000c03100704100c10070240584440400100301d60b07440741501c1c00c00e05400508924600c020322028081740001c50320b89039141031030030300010600c0741c40c05003030244d03481410605403050003e401c1c0300d01081070b00c5041e038456484034800405611017500030211501c0c1503130341c40e51521071101e000c0c1c1664402d5101602030902006015810f4005580700750f084403c1180d042002070703110000070b024004e000c1d07d1403403899164442d00040c4000400c5c0b822282c440c034410341120560048215 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 265426519 1250 265425269 265425311
    0xf1801060e150301061703040305010501050d17030903071e120e010207051507080417060106050909010902070206190e040e030712051b0304080307020f0301050402030c0f04020f0d050a 81
    0x8410026040220b4402603101c65400001080a400028460b07070341d41c000031048806003e4100a034200041c1401030050038060a40581800e03a44009c11402035038805280051030022260146400704c003080d500c3c5004e2046821158200b0485d008162200c40440301d0707122480012111401d4040c0c03060089030188a89030a8040305030040d2003058904014402c0d640340d1841080706a803020000c035030000d40a0006080940121340e503005280b10014000ca16003401030700078074103004003840b208a032b6940f0715030a030b4103684001c0d0000da00e803205803001c1086130040c140c403001b15203598002c4024455000c101c5c1c1025103011203040c0310a00f094581c075501c2e032150f01030203404c4051a02803508100c5c040c200500c8041c4d82c0088030400c2d402600300203811034005400c40031080c1c000188100c290b240c40009880d4194046000304145d05080c0d00207a03403904070700c003403900407540c02c400249a070351698159400351202410f411740e181c201c0b58000b0000c1c102200c100d0300d0b851031300300c4884201003070400324 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 265427769 1250 265426519 265426529
    0x605041a090c090301020408150106021917090d02060d0504122c120304030c030b16020c0907140a200705060d1802041d0706020610060309020d02090f180106 69
    0x16a000b516064110600d50b4001c907a000d40640d02000005410207040103c4281004045041c0842d5414240001c0c14000804031494103e92041d0010340440c0b020380080c240d500800a0070341c0e076908032078040740c03c441040e031001e90b000001184246008103690052442984948040d010301040e0b0f41d010b841c01401401e10304011400c052813201c10042c4164001011040101210071036090b2051070b82ca598080d1304100d40c0a120100304108011440000b56001030014098a88002d5850f200959035030303103215135602c12101880400c01c018000c2690f80303d0704100703c255a544c7c0840c4440601001d000e080d1907c020b03645000d440710743c54004103480054a8008003c54580464143c007600a0810303c030b4800d00980c80b904075880183e541c0c2c42510441e144d4420702030039100c05101d541f402e04160350301c10401d42d0404020000f0a601900300b01013622894103000403000010b0020402003101c200c0002d42240140d401e12a0a07213003580190312460440a00e0040324000701c0c0824240d1b0f07424860 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 265429019 1250 265427769 265427779
    0xf110601080a06020304060603060504080406110a120305040312110909010909030c02091504020415120501030210051b010c021606110703060509030c0d051903110901050708040e0103060605041a 85
    0x103402c00034a00b60000c5130000e0003440d0214055407a6200d4200300d40c1d09460840d03440800003000c00006400170426606041140058540f80360262603000020b030036201d08d1800c040d96030000900b010700801c0508140105580204400513169100e0710155004c8254584181c0404000144900b800d000d9550000d40c1961800342038000740d0b0034401881070103054042612084c29244649883d04c1c80030300028500149940600e41503014080d04480000c28065203071400c090040c00941c890568800c5027041f180380495480c0c0c5035044001c10002c0d0050012125402c3c4480d00d000240e0005039111174a04000000300240e6407a2800c2e502040d0484580e016a0448102080841d0362a0300003a400414141070780d28040703c0c0b10b900d6080c0080046003c012440c0411100c0302e011400107494101c500c141400c10940b0f9407607401e9501d50043d15000c81c10403d000842004001c00d1405a60040904001e00b003801e584900d4024090407240c02805e0056140c5407400380d01e0950880c107401c0c800c2d00a88 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 265430269 1250 265429019 265429033
    0x80c1501030807060c0504120503091e0f06030c07061505010e030d17070302040305101d0d090902030705040806010305030408060c0a0f0c0302010b1908010e03190804210f11060108 79
    0x560b080103003c04021042c14821b05100020f4014240004032281d81e114501070f507030710041c0300200712501024850300e0885101c586482e00d030315145c0c000321910a000843c3d14503207035170740c80700c0042c800e206050008100e00c3c2401c428000f00240c44580f203050311000d07210507940072003901c10b16541744000c40702280014013482c401c003009000b5561080d00045a450091324003038a0351501890305050418080ca100c0e40c0700325942c100428401c0458600c0108006001480b4081d40014062500d6016030912154000007080708640140c08403802490100242c0e8055039407410629140d420a00c502c0b05103002d040c0001d40c9284880303040301e171030301103688030317a07466007110b101c11181850700310000c4042d50340c0c3d058001c4042e940d851031010031401c0680c0342d03100c050400d01c030142520901c0381c07540c100b03600c103100f682400c501c034450140520086152100c119074550801003442d020044002c9940c1c484402103540c8030780d109040c0d6514010355201c803000c000183c20700e01d179a06401d10941101d500006 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 265431519 1250 265430269 265430273
    0x804120305070509060a121d070308030a0207020d0302152a211005032a0613090203010b030411010c020109090c02010f0528140a020304020d0f080c1501030807 70
    0x2030711075030708401107190160810340c441000c15110ba00840701c0ca030106100e00c200402040e43c1e8000c130001d805103200c4070010103144c070065070742e51041408028140c510120000300c0c8088254141d81400e900102882040306580c1006500e5035002c2c00070020848410300040c0c0e40d0000043ca50404c90707803506000c5100c50f8200407103180c580222142c18503d400360503201504601050401d030241144900d8800e0103854401014a06609030500303000c07581c0000d05010700d0418404c2c0000300210269202661102102406a201195070700a5001070b4070210010038401d0401c80518810b5105040704034004140e980152111041d1200c0240021001001403001e440c00b030300070030300c0c440b92400080b42a0907800307020f805403402115005070b400c00302689140811006128500c140b42101400c000c941d81d4100d101e0b0a4690040001d4115a00040864111b445140300c0c0a5020b401611440180c9128908108140e118500700d4282c0d115020b1800c0c18840c41507640c6048952009403940717402c0840d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 265432769 1250 265431519 265431521
    0x50613020d05010903020c0a0603060317070804080715140702031218040912020633180f06130c0c060f14090312130f020d02060d0213090c08041203 65
    0x2400320303000788040c601880000d800340510161184660040c0400a00010034084d08100642c040c1c010107007022410000b141c2481c007a00c6040401084540d0303500c0c980d00b04149140b003960301c242190703c03c0131800075901c1008001c0111401c401e5076003950030a000c01d49100d8900400d1030107540f5400c080c4a503203d1420040041003c0380c02050b104403540340e014006001c0703e1000360256412024141800030150b814400c2d01d81c44440180c18100840c04502d42d450b04c0041d84a80125851240109000710382c1c40503c00d1001240098502047e0316144920001d109429148a400740d404c034807a540c2c2d01c1145020300c4074124440e03515204400c01d6901e6170070282c040440ca0450303490343d07000e4560f034003481010310f5071113070094600031961180000c940c0420111f000b442d6a07680c00c00400003000061941c10454806034044030030481850450000408510072b0000410324940b0000f00d05614052605482d0121102c0e00d2041021029001e004d07503064404840003801404038903841c8010030b0103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 265434019 1250 265432769 265432801
    0x5030609060f0607060506040f180b04020a03060f020a2003070305090604030807030206090715050a2d03060f08060601270e040803010503160315020a020c0303040f050112090506 78
    0xc00705400c407440c5601140d61980004000c0d540300f500c1b04100220790820f13004000100c0c1c01d1081c20400714800e010b03210008080143e0041c080b1a04c030010400f95920b640072a40510340204080194031140b003809802540000720000100e103070365806418101d1001d2114200c0e071303030100280d40f07000c400e07a401310340540c40002e00c541d00c000180008404108810003501d00c2e14401d13001405c150400505d281d00d80b0380b05a00c80740720394100142d0103a03a9a4400c0560b40c406450b0308000c00403c030b07061102210460035102c0002c00c1c0300352524050700d203541074100e2802c46040d0180ca455103506c8130743d01500c581c2e088405501040710355511500201e20580c1b994000720b48403c264503820748a00a501b003940054074161500b81000c4018012880e0034042c00840f81810320b1542c1c2410b1959444094a4641d41078200c9501d0740422030310140e90091140d03041210000b000e0302d550719251082448001d50a01896000824000102c0d1800c0c8051092001c00f82d0070000810300c40c5d03903041d2450041c0035 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 265435269 1250 265434019 265434031
    0x50c0d02060715051803030108070302010e010201090632061005070309030510090b0702060f0406020306010e0307120302010e16090902010e120109030e1e1c0b01060f02160605030609 80
    0x41000140003040c00c02d10381100d4803052030004215030402c8501d03807020003001c1c05c1d8904150401c000403c12020005401d400b00d80e42801d00f04020898040181d00400c01c1540140c5110b04000102c2c510400000c404100d02c800a0001c8004c8501c680701a2804041103e400d5041269558030407000c0f03000f140501800c82c0f1a00d04841510f0300e030750396117003402000c9100c8c0151700e0f26154540100004084003590010b881c0c40204003618244c3e00741040030802501c060310850380000401c000b039200b42c003451071510000d41102c40b01d0740d89821607814001000c90030f80040d441c0c00080c00111401040140c919102c041e017580c04a0b007881c01040c024060b06600b00d05010040041e000c4070f8440358900180eaa0355800001010071490030b0180030b0300d41d02e1029900c1051000128095601c404207403d2043d1001d803845141c04081100d0070b4599085904041c0560581030300016516078004024500501c11340e090b40d429206103842c82c0180a1940548001b003203042c400542a810f00c40c40281e0303c01 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 265436519 1250 265435269 265435279
    0x1090e040602040810050919020108040b1005030a050c12010b090406050c090a03061b3204080a1b0f050907030513080f070b0f0621030910030c08060904050c0d02 71
    0x280e8030080c8a2a0139540d03400300103010745400800603900424010000090759075080403230400702079400249082e40c01800141610190381c08181c0066000000c0340180ca40907048401d450800c0c00c020b80d850340c10801d03161140540c0c401071003410a040c02610008a00a482c440a644039590340c2c03000ba0070300806d81c8644210520010015a6038014001c0045018940004203181651204c044686032001c0520a01503845031142d00041c6031402042100c1c281805460440c60300c0c07620085500c9164002c11603481125005424803032460b18880c071164100c25004000c50352104490310040003445071960044000b000562058026040940d00401d85500b20741d80103507680d41c10106030010503841175445808980d0804005520742410381161411101240c0c44c1750400c000760034041c50003100c5000551081d24461038010400c2624020351000301140c9028041d034000900400c0461079220008a450780410764900700b0102c2c241c09680c2140240c40305510070024000d08107240780c0102d0f080 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 265437769 1250 265436519 265436527
    0x507080903010501060f020105100f090209010e190e010906030b13020f0310051801050c091c0c0801091709012708100b01022401090b040905060f06040c050901090e040602 75
    0x1076a00307100d801c1c080c1069450703014032080c5c00a0000e0031118000c02c90002601482d005100010704511030404440c0702480160f660460040102c5900640310a85900503400040440d8038508110541040c2c4002480182060ba6500403110907144507200c0036000d08184408a0080380030200a2500540090030020310300d146440424075114445040c684081da8500a00010b88403068a01c00304059000c0244001e0500a030510b00510030028030602c02e60a00d40c0c01204004010b20600b221500035040e5071b1b034a5502c8034880e01070100c03001c0803102c91034071001c1d61003080c0400b0141d40491106a41ba5889909001d82e170300b400395080032241d8008503070b00c0c000203042c100410502003405000c0300045190000d0f0800680f415108404030381c880c95164811581410701d1ba842281110f501a07008509884001d0102d0000c11500e000917005000e403004010880307281820082c0145030568041100a0061070229036034003401100500041000408000d03000f00c00c002c40e504140907010044c50 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 265439019 1250 265437769 265437787
    0x1e080f0d021b010e0f0a020918010b030a12020d051813020d0c0e030d170703020a1e03050f0601030b0d06020f0d0207031d06040b040905040309050a08033601050708 72
    0x4001521a800282a911540e825101204c184400328100e1850f10041c80320843e0390f0f00240c01c0c50300060804400c20701c00101480001000d400c9540004030180c107680c42c002c4d0f5407c0c09942030207141000c2c1c002d0710951404042d50b40c4901e003200e03441410440d8080b83c01610b002040009140e010100810726001e202c480003d8619220340da480310643d4607108210301d2402c00707040c01d00360301d02c0d2040140f0070038003001c80320181036200c82176006401d454010ba49040310f48040e14040d44843c007600620034101c43c1a002580c26138426030150324048501c45456942500440503148050442ea8008540d1107002c000a402034001d4501c07031300303400c0d047c0303003041443c507841000c13078010f58415000120042e0031144400136500c407030040e0700d0064500a1a0030308040a12002e889a48180d08001d0340d42c038002014544221203982c01340400404c2c01e81203d40d210f0110b0303925041350007216030002040e4199615110500000b58612408551450514000800542d00e98003c01070a90300c840b800c01c280380c8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 265440269 1250 265439019 265439047
    0x100b0406120b1908190b13031e050417010507050a0f0c020d050102090108010911091c02090a0509071d0c130b030709090b060304050a240204090501031e080f0d02 71
    0x160fa0754040000343e03099241c070340d4440c40d200c0a544040940400d908038000401c000852055000c9450031402424040034034086036600200242ca28034940d484041048060340040108211581072a000f0700c1c0700340403003c990894109480c000d0100720200074056445000c2c1c1d1059011b04114108100c100c0d1040d00491140c01101c00b044030180d40c0084c5055256800854043c050841404100000c0307200446107041e5101344280c2e64411043c03544040420f0301c20313146103048540d010303001001508010446101030501591750b000680680100496010040b50443c0804401000b224007640c4800001401c1c1d40d021810306140c01c9010a404540d52030703400300131409844265184601140f500d2042400c4541500301c2c2882080100180000b00b0000102580c07001d41000e0400b59001161403c46404c1641100d000c007482d0021070000b070091216800603048038015402c0340e9036112100103410341c64402070001044800144515401302c3c00b1803020382036032a08042d00619100d04010909 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 265441519 1250 265440269 265440289
    0x40b160906030c090f180608302505010b060f120601030b061201082a040509190605040b1605030703020309010b0a080a11030102040b0f0c01020d05071106100b0406120b 74
    0x4038101d007807007801039101418411f02c0300408590000c0d10000740f02900701c401030341450002c1c0307508452402090710880b4080c411669000b602d418503510700c0c070001451544260100317800f41c0e041d500c0d00c1c100300344c1403c000c02119a200b590700711300b91401480d0080c05040d814013400440c1015521150f0318029110180200400e4107014140803d641c540006140341c0700f010419150004040d95100403046001c88001d001301c8412039000c0380070780c0d440c0303038007840c00e0480c81c09031074101155804135050000580c4818000d81c084c45804c80182e4409080c0c4110b0400140ca60700015000c10018001d280300303031b0141d60050b4000d00003052412101d00040c0f20b8405e41d400200850300125042d10402c544501c00010000b420350081d401d00d454031001c0e0300740d405290318208001d5400103c4240181081d8125500180b65090821117814183d10041030f1011000350500584200404030b0400c250081040044441b081c600c43e00d0301d42440012581c040414451035103442d101e10710075600c1d540d252540 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 265442769 1250 265441519 265441529
    0x1b030503090c06070f110f0a0308090102010b04050a020c07140a031b0515030114010903050d030c03020705120a0809012a021f0b0109140a051203160b040b160906030c090f 75
    0x300c40240b45d41c00d242900203160300038540320b081ca400c0822101e8560340700180403250040585a2a121007400603070140904468056100346003000304a480c092075406030207141108000c864083d07890f0352040b0034908000079490f41c07000034900c00b0400a21444455501c001c0303549600781341c0a60f104046005801c800849590302000813005000c2c94802c5031003000780f03c4003460f25041c05455600c516880e404c1000c2c4c8038040544660608102c10b0090b01114005944142201c0c1d80600304050134913160000c41c2064001000e00011a000b00014002c01e40f580c010f9240728000c84502540306800c41900083c10803d6001307008501c220a0b00b15144144200301c071100200d030070401e80c800140f041d4115003084501d000281d1042c416a110450711005440081c0d81000e024050303980d100d031440c045c4000940410421841c0f840402c03691071040f9018500c1075900c0f00054480c591180340445100750142c00040381005d04000c41c91285d0000c4401407140c0c02d0404082d600c4020b9445249015044 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 265444019 1250 265442769 265442783
    0x1b01022a0f03030f01060f0806372408040803060d0204140a06410418030f03050c0a1d0f0a080304081209030706050f0405090f060306071b030503090c0607 68
    0x40004c2500400c00700c105005230301d0091142d281280015144105107180307203401d00c03051a541098800348042a240042c1503000060260b9030700c850008440b0380400552040c0c541020304228a02d004070390040c020f96124003500d045507110410f02c411007102c0002030360b100c1d4440098280b404515024280500703030308040411803e00340380044035078121402c00400b080390036850b01c000c1c1c1d01d0078403c044001a03140200c03c0303803000600001809080e000c880490011079281c2031030304050700b00f4080f401080d217a44040c04542d0f9401c090b0300c1c640c09607590200c00f0481008810504040d01d40700b80c049a200142240c017006265004907000c070300b0310340040e07815910000e0140300b650400c203e07d01c3d02103000f200862030400d00a0200341c5885d0300b40701d040140003001c602079030041c404070305503000b40c04080d0078004240381400c01c0202c101000d40c5d81900a02071170012450081c86902424550300d01e2041c1054906a16502240c01c3c0d400108845810700900e1079140190355000c00130b003100c0b07018000b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 265445269 1250 265444019 265444021
    0x70203010b031209090c040b0307021018020d02010503040f060218090c130e0a060312080402040c020105040305160c0f0e0403110714121c051b01022a0f03030f 70
    0x105240c00c40300e591102521a5020504a9a202c0b04a00440c0d000316070036560041c0da03032034428807000e9500881e00904030446001c0304104540b44e00082e18400520700c40c0c400d000c1e0100c403031411544e00404410194100c01040401000b650043d80190340045c8035a1880c3c042d883e03140c50314002c81c1c0000704d645074448280e40400301c081c40c1031542d00b03800c511510481840c21440e40e40002c480e488511074150b01e80c4010700054614080c65020000441d000840710080f400902802800c0c158116400c07482a0319150303014010340d2052140030310856054840c0740c50a664010802d4074941c0c038003811220040e1848004c120919400413920090204042d02a001c0c2010702d00036105100600d440551580841c50401001501e800107880c1d5641c103071a51502d01640305016810700455041b000318600700c00e49d074900311652000c020601d001544510980701224803101e5401c0c0e109885003024070000c00b01e2040e025900c190f40010313207007031940111052000e10328085402e50b0000c4881030313003114110f4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 265446519 1250 265445269 265445273
    0x70507290123041b09050103050903030a0944070c060e0402071a010608010806190515040911040f0e070302060c0a05100e07090e03030f060f0303070c09060503010902010c080f09130207 81
    0xc05c10000d02401d007011b01c064641490007603624080100180076807a100c003450f01c18081000c1d500b500d40c1076100c0a01654600440011801ca80d110340305480c0500483d0f007000504200302c3c25105402c0c0c0c802904400705203070003400c8505400c036810b80d84c1e0140e42003103c10001070040240d00390000607001d5080b19581740003000341500348160b01000c11078001c102008500d105482d5601c088085640c000100358540d91b005440c1c400e0401d880540140c0740002e41f1090025140d444100c011040b94140b240707842000d10a006c0d22651840540940e200b50014001407070020003070301101c4007103000c40708054000c0e114245807160f41c80c2c038001e446640d03880e8a8898401801134802a00f940304061100f0380b00c41100c44d6803031100608000034a02910080340880c1d0360482030b50600c81c0010308032503d808484c100364840303089900c0381452491421400061904042c02404121601615180441800394a0700482980448080c210058003003150344995500c105500d100840d084100680b10300c624 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 265447769 1250 265446519 265446527
    0x1b03040506040e01150203040305061f0e07050909070221070206070606230103060617100509090f010e0601151d0d14160e0a0c030603050303070507290123041b 70
    0xc17203a600031508100b2007440440c0001442c1c54100c140b140c4c907803c5600c0180c000010500d0180c2060482800f4041800425580140a800c2d00d00d421a0201c903140c8031014107983d9444501c02e844111180355900b42d03040c1941c2000380403040d0005d0f090500d00b000c1580d0340001c44030990440091200c0c80c001e0007004000d275124414047c002030a0820019040010282c00d01c4075810044900052000014010308000c0414100600000e84110850300b44050040e031100d8008414948941c0303007920340700000800113801350403104100103901da01a0f900b001110f07510355582803502c051481e000c05805a840d44407140e00e5480c01030742e82140031103441b142a42030542c000406200008a84c40034014040001612604084a4080052581140d18050f0080c181a5201510501010042014941d00000100300180c811a03410800f2040c40c1c00c5000b40300318a051159180880364010301c80340c2d501040306d090320740b88881c50360a004000302c0001c0a4459045200f090f0181240a00e1541500 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 265449019 1250 265447769 265447799
    0x602060412030e06060906040e070326190503040c120326061f03090803010902070c0803040b07060902040e0a030309050607051c0b0105130311010f0509061b03040506040e01 76
    0x14a814802070808480342640c916024001d1403080f40881b01041a9658a91004501c5078a403030982d03140c1d91f50b9050048549070340c02c9080718007510404d0f00c0320740c0a50350000c0303c5540b095400c07584407860070340404a8941d0030040c81229149000381010480c001c50b4448038003064441e0b075982c401d070300c1d884038000c280051090303030f0741d00c441004c400b17210055507480c80b0040c0e1a090100311070840314034820100c0140846103409061008000004181d60380d90b070b00100303044c2d40100c0c0e10a00203552a0480307544d03482a0b116100c03103041c0c148541c0000420503004880070500090000c1244d01c004410a4140b00c0306c02e400720f010995510f064001c00c00c0500401e0b50110150401904025003c0040100021072070280d81c440c0d03030f072000580c1d41e61303000384240d0302a41e04d003441800910340c580c5403101c2c01c024110002c5d0b0101c0d8402e00da9a6110744143c080ba1140c24002c4d094a041c1103500410034048200d02d0b246164a00040c070002c2400e880f20400b400040000c445ca00c0c07100e52400c4100428050 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 265450269 1250 265449019 265449053
    0x70606061202040509160504090606020f010e070513051f1d18071701020c06010b130b0906070b041416091a06031816060c050d0e030607030209061306020604 69
    0x2c01071000308401e6940308199940088085600380e5103906c6900300300d81c0380c03240360080c26144e850041c001c24480c2e40000c2c0b032000700d031000c2d00030001b8051301d0340556030f0b034401803082c503900c5a60f0f258002902e084a8200d65001a40c1c078030742d1050200052501540031485800ca08100d48034a070025008094410416070040c6121030500c2903985003800d41070b141c0456014100620403540e50300d40c01c0700400d50440e4511007880007520900d5842c7e070329221981d881401010003d1820005c0443c14101360380880e001c0c510020700344c0389042480c4d0342d148890100244290740d400c003038800d003200700c620900001c600e00f0103104940709040d09280c1c1d180101d550540c0345e00e40b610891b80071040710f03407a02c0e001c50b03801110b442c0c840d0080904506c02c0c145801490110007101c844143d40001c0e5280d005500030304c0c46031081042e17403500c1104120448061140c03012659040d8000404198543c0c001c1d401400c00030006003a862801c8282e42070081e800c4201d500060059000c0727403c210502605082d030701c807144 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 265451519 1250 265450269 265450271
    0x1203090201080612060714130b0408160e01031e05010c0509030d081504180c06031a0103090c0b0307020307060912091505040509071101140a0e0c0307030f0201030603080706060612 79
    0x103250301d40c22560350178014444414481165854032000ca8101c040d00e88513100040c0c00b50809444e011040c0c1250818400c806140c800c0701826203e00700c0b83d01c1110b040da8081144015160f10310303191054004005030024021458030014803020400a00400d903000034652034036a40c0c0c0880c00c060501c0c041c1561740132801c01018505001503c04201c00700b880d028400c0300c0108600d4100c06490080340219400184403079107503c000943c0e69050b4021240f00440c02c2c021741d10f4041c10800540607505450b000034450b076998101804195140d00107181c220031188116414410f46a50302c40c11518042019955060480100380d0120b51102440d000341103111031025000d03031a5800907005001d81e0141d41d201e030b4078020010303039024880c0500f02909100c0200903c8040e41380b81161030100c005466076000e6508000c103240014200040f50494854054010800c081c5140c80744500c0107503048049040684a503130010224480c1b00240045501030040084c100f40f50004c081e0150b4002c0040b841c5007 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 265452769 1250 265451519 265451539
    0x20109060302120112051507030b040c03180204091412120c0a050711130c03020a090b0c0703030e031e0d090e01030f03050309010b1c020102070b0c190305040312030902010806 77
    0x2440041e5443d130448100e910826036002e0280b8049043c940c40500142d0021244403c12960641c50f400298120308141e80820100039000c2c421020745000d00783d208641441400c85000500389a030011a845000b140301400e240c140c1c0f03000c1810507856000c00f8101b24000b064541d421105800c006408c0030b41200c1d2980351910b10107001c2c00a004100c40030702596003401c504410390b100d42c498242e9010700f013030003003040c10602c0101070001d40040100c0400100304101c0817500b410007108a640040c0d09800411382ea500d169000c6446107045a065034050081c0b0102c01050480d0001c034a1a1040c224054524035025000040c83c50303149a1112060218640c01000030903201c44001c1c4000750149480c564a60f52002201d01402011001c3c070380200c40c00031840f0070704450b1018004410b20076800d903803807160b0702c1d00c50a0490240300e04941042c1c224111030028196095004a1000d02c207041503410141d0300c0e116241d201d081c42e42d800d0f02007501d50b401a0110340e84028a9640b00300221400004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 265454019 1250 265452769 265452787
    0x903120310210204111c0605090c18090408190c0f0b0903130e010612110306010c14030409020a08160207030b0a14040f050609150408090112051003020109060302 71
    0x1000424410039002000b107082d040c603039034504030b0266016900504240304602c9010b210354003550101401028600d50480c1001e0510018002d1008842008100c0041600c0b0484001c40c039a00041001c0072985100ca0b1b801a41c2d103070148424031a03070003030b08019154411440443c891a8059012030200304ca444944e00024104654990805d42c010340fa4095603502d0840e940d1030f41c811a141e0110b000301c0300000048200e03d04121506075189a41d80740048800184404141e462401650444140601c0025125417150940301c86003806588004080440e8460240c21548035411000c3c01c0c0e80c00160f00b240440c1c100440940054282c0f903490b81a840c0000000d45500460200621a07070043c80480c10440d0141c02842d0a600d400304e07941d013241010b261407410124040c0d401c9034030340141c4d00058202c0c0b07408030b80d500e80c0c082845004183c035910f6070303103005007070b800fa90019040c020044041106039009100310352141010507a24400c0390704600002d002c1c5003841c3d1211081500412030541 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 265455269 1250 265454019 265454041
    0x70501020604080a0c0c0e091b0616300f02210304060c053001140603040303020a020a0602040801051005040203160806030c09070909060e0c0313050109050d020309031203 75
    0x1c1482c4145c90001d03450021490500b001c1a003c0d80000701c1c918020090054a500c0442d0020a08031030800c01003001d0140b1003031000c00c2c044d000004180258914110001c1001e20604121945021902c22030b03075100846036110302c01c2e8007202400040c000c0000410320a0301000a290311a1810040110800004203804c105120040c801001140c4452a80c0c250b1030107001075421002c0c1d600c4600c00e150804008588607002010085d002750320301a000010400c4903c40c03038144c404406001c0c0e6166556949055000c0e500c00c410f542c9c1107204410702c0c1e0011480301d2000e44081d182c4600041101e003000c000300804858203800151160b84100140080002c045001142e000c02504028009981d42800242819249807496404c0309031582003120702076000c00f0380000d4410f4540200841031301d64001043d0554207c0d207c0c0460315040001c0f50030baa8941488605051041002041030031307031a41c50ba4142686145040056400480c080a86e0301d402e00c4048c00d5808401001d900b503140400d000c40e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 265456519 1250 265455269 265455277
    0xa031107080a21020120220609031b0b13081b0102100c0c080f030f0a06050d02041116060204060f020f0a020d0516140a050f10052a0c0307050102060408 67
    0x4103d1030050b03090051090b000f904041d40419880f1400d10b0840c80408101c1070541c4002c00c0b88001c40102281c280c0300c082c0900c182415a021503980d15004da0459480802c130740561050302409036401c076800154401844014444400405440d180b0185840311061606c0d1780349442844455a00f08807079041d903800511440240348e9510b01145047c1c400da01a51040d0102c88041c00105000403503e4251001400550081d100c0c865424150380e201c40340e560850b00140109540038450350005c070007519040e007007091908400c400003860224548400000706030740410845545402050030009590401e03a044086501800a0000105880f41e1240c40b02c40c1d42400906c101007500d6064244102041810707043c0e6419444060456120390b001c038100195031289502c03c410f40c200204403410300d107100e14076030040a03001c250680d1080900761a2030304404552540030107090f210301001c1404070300a100902030040a040b07004429070a240c241591900300324103541c40360051000144c007400c215 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 265457769 1250 265456519 265456553
    0xc030d0f0c1d04090f0b1e04032309120c1507020f0d08130e090706140a03050a11041d090a020102120d02040e0f25091e080a031107080a 60
    0x1c450b45110110009009040c6100050a590f62800c0303000d0030800c00451190294035103540d48190845003c814041c42c50701250002c0c0005c0780b4240d2000111600c042c1e0080c500a04640d1504200307203400410f40f00d5031001c001044562100c0c0840520303003002d02402645620a1403000e15200039500468078541805403098041c1010302504c0007403000b04010303212030f51200e8440010007540d4485c144565079054841064501841c100050302c14043da05003001000701d403000702e0038454140c2e4150010607004110039592a181c5a0070302c0c1061500c0000c00150160608851244820400c59201c0c00c500828110142c0e024420030b801503a000039142c00ad003074050021680d104c1074040d03680c1c0a4041c035886580e2802008003801002c00140840174480c108071203815076207600403041c2e1403c40540d244500b0114020000500900490707e0f0390b283e4103980c2106000d90555101c0d0220302e0000b00030011b90015900810705d0f020240280442c3c001031a05000618034041191100e6a01d00248404 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 265459019 1250 265457769 265457807
    0x5030106060c151d0d080f070801060e180a0204091b02071206020d0501030303020306010e10091404110d0605031903050a08040501090b0c0d0609060e010302060a12020c030d0f0c 78
    0x32503c40801c41d13000302445125030045000c07003400d000000c1d40c0c0e8100c144c1d0140003040b8400c0014010905150301c142c490a425030f0743c0d42560b440c140d4295900c158214045420800c44141c81c48901c000c02666400b4088800005903990300e0203948000f00c401003001d203401660344100440d05281c2c00030f801c405a41c00700e07030704a0f03643c1c50724549007000f84280030080380c4440c20800000145501079002d103208080030703240c48102e00002c1d0304200074211316445178008101401001d025200307801c100060194005480050303000c0b920580070b41036421035002e040741180c50701030510241c00d05000c0141c4c00c0b608005519203980180d54060030600640746100b08005100c0001420302c4000d400a60b4442d030042407203415820910b8074041d05038031020103d12401d007410000600750f41c0c64420301e01201d00001c2814030344d900310b0b400c010181d4859040e09c1c08020f000345d0f0f003d09191140c0b004020003032a07400115a52850135406030151f07410034814460480c90540260701440d0020340102d400004c0b105 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 265460269 1250 265459019 265459043
    0x9060e0906031b0607050d03020901090608040209070e0f04050108010b010906020d08070f1e030903030e030f04030b0c13060f2309130f0c030911030d0f0507021c0303050a0605030106060c 82
    0x4013003485800358100c0901280300318907500c05020b0305540100f10614003aa80d20034245d488203000e03295170000391402034100c012a000100b589105585010030450300414130030404602d1000541510401e80100740030342d56800c1804055a00000b0043c02460070740046c029080038010090300c0000010401d0007480000021340d031400b03101e058001441c41801c00340041d03101580c00d00a0081040c14070403008245040054220000c0c008250b54044c800303012000c4c13500b0b00310b40d911610307034001a10f2002d0072201400030f01c2c00d2540042584000d00600d80c0e852618a405c00d0009082051040f00341626000c02d030302c02103401c26208102c0b082c141043e59a04031140c1c04440c0e0500404000c1d42c0410340c5842c0207140707400c290745500031f045a42d004040060741008058200354a440d0207099840206030f800303200010f13860080026181c541c0c00100406040745c601d41100182c528200030441c00a40d451042191030070440c0300d05000380070154000c000e0641402d00c007514014406001a102c0038000c4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 265461519 1250 265460269 265460323
    0x703050603190503040306020a030b030714060906070c05040c020a1208071403040f06020f0a18080705091e0c070308130206030711072103140901140714060709060e090603 75
    0x1304540c02103510840441d540c1c911a00000c1c002c002d0088028403e00900400040401c203042022400650080042d80340c02c0f6050b00708285603220b84011900700e5090070000030306a9072840303101034822094026000c8e411140c60642410300c0d0003922001444629028009442d500051580b2100812102c0f81c1d900d44403400c10f664805081070000b4992400041e04103156030340100035221b10f9160fa21002030103216804842030403a05030003180055401040c0421003894004002070708800c00c003120255400c0c4058543e441c00b0021a511241000c00003000010142d0210030a03601c000014034181c80300003250700040c56840050b010b5001c101d0004042d00300c0c4d21042c0050b0000b0b00100300340280342c00c4111004403160601c041c040e000b080341c4100801c5401d1000f001c844104805a55180b003c809444440c80b407a000548103680e41d03810010420dc4101c400c2000c0d5004e18026207940710100e01e0000014801e20710485540c1c01154001c060216945001540b2880321501070010b18032a4001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 265462769 1250 265461519 265461523
    0x507030e0409030f181a13080f0307031101151502150f04031701120213060e04030905090907061d0415030303051e041a0603010204090f1407030506031905 68
    0x4001126802850503820208054201444030708504980d19500181844955800d148149070b1040a00303d002800200c490b070401b5000a2060a59218469446940760342038249000b072000c1d0f842800d0f920014903003091580145c0207050341c01e50ba100a010a2011248145c4000f02501c20368651106001c5480901802407000c44181c00c00e018940156285c2500702c0c05c503044007030790242d0110724800110a141800030a0300e41c161880d1100291880c080c0c0c1c0d007401a203241c8018600b40c01c03503995001040f249120203140b40214041d03a2216441d500341410002c0c0b80001800c0d030003e9a01c0094200240d5400005403022001e074014515a010349940c003140c003812507240c0e0000615400c071004400c064040d480540200170740c3e000d6625101158000c00c2c074010098030301030090003d6045910740c0000c0b5110711384d4054406000036040a54881c41001905ca140c20310545142e02c602120f8100c1030083c0050741e016200c0d15040c0309a04000001c02e4a48400e500304072111200005000c1c148142 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 265464019 1250 265462769 265462787
    0x11010e040b150417030c2119080601020c040216110a030c080319030522031707020d03140c030f10030b040b180f101d03040806041e0c06050703 63
    0x64030340c1c8503418200e02070b082a07901901800030800150143d0008000000094980781078004008200c03030514032407941e42c11a00501c0c0104140820008150044100c504510b6014056140d850141c1171542c00a4107140c241d4000394061340c814030240c0b094204808444003026002400c0c8808401003401040d10300d502500b0150424202000005050794004000c0c01080c84074072412030b000c010700b00110103444042d10b0340c252000003801d0301d041800d020b01402c1044c500c24101001c40ea0a03444d11950103040c102c5040c1c01503041620f020030920b07050300074000d400591988043c8580341460840d2100d00003e440008100212000a9a40c4095822400155030000741c0113010380352901e00010710901c221900c003008102800000d81031070001941d201c050b0700c4107010f403000c50090002e0000901625000c200401a1504080c0c100c280a000400207860904007421041c41c0500340480104840c06101e448900b142c040000425610040c48060361140d00e045955800581011a10380003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 265465269 1250 265464019 265464041
    0x2d06050702040609091b0e0f01030b0a020909090303060109090b06030c1b01111306030c080a051e09011a150d020307090e0f0103050c04090b0f040c081b01030b0d11010e04 75
    0x2207000800720170301c00800c1280b041b01c0980703900e100c0d510340c40390601d08810b1010f440300a0314409038401400081e40c034452607580000c4a0400500304aa05c0d400604040740580740d800d00b40e00000248607641d640050f64101400f4140c50034011620310310085a240d1100800c1080c1026001c01c00c03c02001d4407040e030708244100d6034002e200704205038610500342d500c246a500007280100303900140e80c5001e80102c9501c501951105179039a602c400c94a00580001800d078000726100348a1a1030000d81e10644500400940d00001031070200c00c8100d03641c845541808074410104003d06221080d521021200b500503555130141c0c494070f8004040d9907800701c030b401c110250550b141c204110340d100400654100e0780a6011258043c02140501048601a18014111143c0c00000400a503050403035a03400034445e5140c2441a0381e0317050514100f503503440c0814405411a004440103603498040d04104500840c0c8544086d81c10384c3d142003007100304509660505c13010307085020655440b9445445a89 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 265466519 1250 265465269 265465271
    0xc02091008070e0907060e03060f041712061c020d0303020708130321051819090c020d020c03070f03060e0709110a0801090b030a03050c0f070f2d06050702040609 71
    0x1685030340f461600a14222052007480c424400c000031b01e01d03c10a5041d440b13541c00382c09840304d81c840302e2401241e1300d0021f005035600c6204a00d0a0410354007100100150100c0c003a80c240a802d00c801000148510851031900b59602e4840d40400b685d5452036401030180d040c200169101c1e50303854a46c6003400754540d030f00c130500021a03000052001c1e44d0904008017001c0d05240107070f5a488601a200c6006141040400200c005051181c034141100072070350344050140e107036039155901d4160000780c8441c804000c0040e00683e4407034032a90780400010b41610f600320082d1070f04908204501e0100c00c078030b00c0040c1a06031110041d050b004411300485c00a402c6105061054080314070724000994010301a00e40000e06207030001420319070034440c2d080c00d580000d0140c0140312064600b1500e80d0440c1c5103812141c0550fa6514416040801c202c00081401c805a550710364900401c00058041150300d0707510427203600d8403440c0c4500c15004600c003501c805040c255141c0c0e40c40d00100d4001d14085e000f600042e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 265467625 1106 265466519 265466533
    0x7141b0106030203010c0c05060f0402100e042a020d030204080706210204032609011205070504030515160c050c0906010c05340302010c02091008 64
    0x6411094004184a51290000f0303003142d800d00d0182d0003144204000c0002c00c00140310310303030380140180c440d1803161400b40c01090700510300769410340801c0301050060050f691a40d2002d5200d41e0482d40c186100015006072544203011845030001510440d25820b61032882402251b05460b5000c001d40b48240c504a07090300c0c4400000f60009815943e80c81c81d10380f0149a00c050310055000d0b82c00d000c0c807a0f0000c11064001555020b5485c07a45008002e10415030b44c12518001100010704000501a41d07008003c427154011351b00020501d021b41c0369034410403114030030b459024400840754220500c28480068603403041009000704aa0080c0d51920f219240a084183d48440d0604190007180103a131b940608000e69032080f080c0d140500000301401000103041e910342051050300159020381550000303440c0c44400b140091085490310000382070461003640710801850018203e50316 = true := by decide +kernel

theorem cover : BRFrame.Cov 265287769 265467625 := by
  have h0 := BRFrame.cov_init 265287769
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 265287769 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 265287769 ≤ n) (h2 : n < 265467625) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
