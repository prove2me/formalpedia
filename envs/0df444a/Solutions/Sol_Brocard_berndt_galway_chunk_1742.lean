-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1742
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:30:37.953998+00:00
-- url     : https://prove2.me/submissions/3e743691-edff-4454-85af-89b94b37e909

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 313129496 ≤ n < 313309352 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 313130746 1250 313129496 313129507
    0xc09020306030304090b0301020d11030f070e010e091b1909060207031e0201030b0402130f17070e090c060711013c1101050f01051201090f080a17090607030c05 70
    0xa90f81d000d540228a451a035806418080e40d80c01d504550300a40c10090520100203018015145508103e03445210710341010001200640318000c24025418143c55551420380050244840203400030b180103441c0104490310f01c2198050b00c041c161020001c1030300e00e40c01c003030f400c4014200f91031944184c0556204803010b00004070b40b01d401c9030030780807450380c400c80710700c00b500040340680b14180c280d42c1c2107440016410101142020420151120400b18201540d607400c580551f04540700d01c00d1915030003054050142d60750311090039404c41c03240c3c01102c001d040350300c001031901c1d40000011280f83c8100c1c10711480d1940c100c2601c1c035001009190f9a03c121040752000141e6894840c582014000c1d11180c42c903059009192021020101030002c10540c60080443c07840c2c5c00f003c0c040d1910030b202d11040140c01c070205005400d02c0c182c1c051a40301013002e5660f128011500030f440850309000e95000d4414030b24951811044c42040082d004010502b80783c20041d040750a01520172041001c01c010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 313131996 1250 313130746 313130749
    0x22080102190f020613020d051c03020c0c180105060306180f0a110703020a1b08010608061f120803071e031d0f030405060a090510020c010e061c051012050a0c09020306 73
    0x4521420303030147c85468006090f40707001d03424106215024107205405144083c101541a80034001007414282101c001a10500801114504090115000405480041c400d80c1006000f0399000800034284820800c0030b00c2c8983d13464101200c045107406401c000b001116246802101620b900300a0450f10302000c03520000d44800c6842400340c04040d4800d0f031004902c0d01d035000d010041036418000c000b116113480300c0c07648445042c1c403110711841d4500d0280d4012902e0030084402ca6900c0e100107500603150341d440399841e800040800742845010040303102810b076032440d42e07040030f400303a540003d601c5464100c2c50001007a80a0201840c1e00550b000004403000208840c1910b404852a981ba00c048501c11144208103410607138004119292003100c0c0c50300042d21f07030700c00082620f03600200c0080009214250041826030040c2a4401802207540c000607404550422201086080d8442c0c4440e40c406090008036001c0320b05601900d02c4a0502401c810150050181040b05616500f0840c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 313133246 1250 313131996 313132021
    0xa0906050105012c0a0f12060c08060d110f130914011a04050405070302060a02160812040504090f0b09070501030f0203010302152206050901121122080102190f0206 72
    0x40764025001c100b840d841110707a505e4035010001e00740a58107042c07494440c05840403015410358212121030800159003c03070b90180f11141d20501c0003816258130f080250300c0f5403c03034500900340d8a800099a908118007620f03000d003200403190200c07001007070749103c52030030140c581c6c0012080c3c5810b0b45408542c0c0151940c80c0c00c040640072040360040341030340b641d040060a001e45035100039400100003036000f46a54006c00c41401d56210a03022810195444543e00e44440d56411440c00034003040100b0300080c5070a52014400714060030000605100541d200c0b501e0440984040983c3e41c02880200181e40c0c0c5405048101744140c0c609504552450340841c4ad01090301080450345d070f42c0440c0da2444d140d81c0720281c005034803525010606440e40e03020058010740c403800c00343d800201003100c0c0c5070709042d181c014480121290754180b86400c000c9050041091a04a0300c06c04178540c2240000c1d008009001030000e0006a1010034114808240b025105001503001d000640d004401040b907440e2014 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 313134496 1250 313133246 313133297
    0x6060301110318120c06011505030637091b09080601060e030f0a060507080117070b210c1209150708060607140c0102010507170103080906070b0a090605010501 70
    0x4400283c803094044203d5041021050540c041c640001c915600c0b440c400081c2e00d81210803082401d000840e0390791007280c103440101ca80740d400252804081141541c01040240d44c0b4080c9040c032a40c071107800d103003407203952956840700e00704c1c5440e035292a003035006003403519000c6820340c100440100d1070715404134fca07800e05100d0300c028070603403640b89082c0d038030184405401e040f88001614030040e124503151004020a0300c90200140c180c40012035140030302183c402d07020f007240b001070050351328082c803150041d80001900b880c1400f040102c041b89581d108245400b4801045241d44c803489051590b9003c48001410036141d80e000c1604440c0d4503030403000c1d560b006070b040e1400141aa4411012500a2090340303001011109001011600b125000c83c441c10360032001d034002d0049880b000c0d82180c90001000c0780e081547e0a08004000042c107034002007034070280142c81c00b42841c402c2c0e01d070020b10748412101104501d0302d9052004c2040100d01c1601d01500003420000002018550704105031040c1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 313135746 1250 313134496 313134511
    0xf0322030f0501050115020102070512091c050105250e100203040807030c0806060a03031b1b0e0f2409100e0c0c010605090f01120f060c0c1e02030c090712090c08060603011103 77
    0x10310141c2500c0c2d52580764550303545103400b200d07035030754915055000b010100ca464b0b400c5800440d03a480e0700040d440c490729600909523590003107480c0010401009010404a5806500c41040002900702c0b0501005000f1401080d40006191601840342c0c101203004218a201d5100c0c403400380300194015124100d507840c951000303c040307403503850250b4040161b1000e04400204c5070000203845025080030f50700c58212187c14040d2603c03100d56020b018801d07411000c045209601945100d801c064101607482910300c41e09215166603882880d2040c42c00b607030b951407903000001c0c105140c84804d028840040505451100c0c191414000314100407406024103600c40800590160a22101420329500c9a80000d01044109500d4902034085d400780441120a0124117000201030f5040c04105030b071f080c2c1c026014100c442d0080c000c000907148000c000c0c10038006518460f94005510384a2240702501c1030030300302c0708142411100e510300361004200c0e0b48aa81802416008141000701b41d0b40c0001c1c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 313136996 1250 313135746 313135783
    0x60c07080a0306030206040b0a020c04110d09170d0b0102060c071509030c060e030307090e190c0207030507080c012c0f0a03170d05090f0322030f05010501150201020705 74
    0x11101d1044020700110381c00030b9800310000c50003040b215a800024503200000703408a8141d00c2080307081c001624800003403401c1d1243c00b8824420042160341010b00c4480c0b20f95041d002035003001e49005030780d4010300d0340c081c00f1030703992015207000f541c040254070741081451190074180300656940000e12919190080820303501c5091315006c02d4010442c00000c0c55004401b8403c50403011100341d582e401c00ca0b5a000000c1000344001860900b00c1c02c00d90003071a860849008244021070424003500d0a64100001c44c442d030000040480c41c18003c4030054a1598040c268070046c0e1000149140144450902c0c0c41140c40c003002c41c0c003500075180e06818281501c2c4090108020070018a103100c00d50300c041c00848000394071403118400b050091805a951010400c044c1d01e844210a685130801460400c0560041104100003e4030560b0380c0b0740c40080c1c003020501c481d203d9a40c610b00f162010b50480342a9114001888005510412406942000c1c0700031420321006490b482e40c4d64400c1c0104074120350 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 313138246 1250 313136996 313137007
    0x1201061716140904021902100903080f15030a05010c031104050108071101020408010608030706060801050c04180b041a0102101104170312090f0714011706210a0c0503060c0708 77
    0x31035050079030f99561002001151140c41070808000383c54200b080c4000180130b81c11300383e400d1040324429000c41e550141d07940d121a40d140003001b401c004001d0010b5804100701040b10419950421000c44464403800c00412041c01c624406001d6600c3c035003401c40070100a1206001740d0b40e0050105a12160b0340c40c061125001e20b0003890b0081c8290f4100c140f29500340744011030032603000401013401500c280d10400080d66241d19503822500c2c00e46200c120201d08110400a4140302c242240d440e080d22480010490700c2100003a0031111a54810341501c0d480d900540001c0d078061288100100b4401008e0241d00086000c406880c821400f800d00180d00e02d00b00d110800004000ba91026117100c0c520084a003020045103642d410b1a541000302e034800d5020104001804011103401440180c5a42145001801e0030310041d0000420407504880c80d078400d20a807040003a0a854614080f0000c1c0c60146458100b00f21842a03541205010b5800107040c4010000d1000487d102c854116810b1030300c52 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 313139496 1250 313138246 313138277
    0x303020d0b041b11010c020607180f030308070e09070f0309050102040302090403020f07150801060c05012301180612030c030908030f030f0906060f10030f021201061716 74
    0x4000204405800c14580f101c00c1c9a0503d80065500100155855036a070070320b05998600d09030350700905480010780140d0045540c0a01800701200c3e15490351000d0600c054030f4603080c1602031200c0e8015400508c3e08010300000c160015090280399009541c02c041c239250144014000c941000000310802d503907103644000b0310a0a42c141d4001d598001e1410142d400c29040c000c2d5121800142c450460064000026111120b11400202550300d034030b403000e44e40c0c600102641e003049003010079903455498506024400709003032840ca41e0b1940740328800440d175042c00741c90405c050300824498102490007500303021406190704410300503a03040c58040a001c0c041c0c40c046442804540c464002d510010500b0000300031504c01a40c4541d001d14840e500690303a10072001d558000a441168201c50280104a09400c103d290303100d00748a542008165240420080c0f4202e9000410805010360068014410760707901c80801e44150a450007140c0e15414160038100c0c1e6141c20005000900441c96800c0c3e151 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 313140746 1250 313139496 313139501
    0x80904020c100903020616170402010302071a040c090209030a140f06090c03010c0c1101080a02090a0603020702030105010504200904090f15051609170c0301090f1a130303020d 77
    0x25a649000b502c0c000505100381601801420604030090b0191000188070740000032844481840c450b96801c1143c050600300c42801d540c00b4105078109074080010401245440d54090254014069101003c1c507080c204000d424003182c00a103143c900400a60307480ba0b0340000c3d14100c06406c00502001a4520485249885880043c10049015800400c10280804100c48203550010350080c010110300c1402214143d4030043c00506040107440540c4495106500541c5e11103400600107182014607030000310030f643e4640c072400c0007a40020386107045003803e0042c607004010070f49040c0240d01200030041400009081100d40e000c40200c0c81c1121b65456801001c00943c00034905055122182003030b00802c4240710a00c0031080c03c04000c0360840002007100344039100c6a65030086400e0424801c0648105400e401a0705486503050100e00342d0340c01c2c810307100d01c50321801c407030f03000100240340c003c5030b840707403001d241c031a440c01081000111081c0c1c1c00c001d0745c008ea0520340141d0f1825201c40b01d200 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 313141996 1250 313140746 313140757
    0x3041e030215030a06050402030103030f0f03060e0c0a091409060d0602070803040602091903020906040209190b0c070602011505040b01051e0a170630010c021c02010b0d08090402 78
    0x1405040b0711004080340003a940158021544040c0a009294881c0c05002c243c4c072003840000c00051010301d0b1510068840d1940c110306c46228500480c8541d40e0304107030046d241054980c241010301c002607103103d160700450090014114040e40ca94104c0c03d0800081d42e550300140b60901900054844100b0003026a04072017035150300ca009582c403401c190914900a401a512990003040e1601000c081e01c0312510300001203035030003080340140c0c0e5211418400a1741060a046401001c0c1100840708010303070040b040c000d829403000300c0b5180c800382181d0914000142c0d2288042d64501242107140c0501401840d00340d0b48142c5010400c2c510100040352584241070000c840c01d00daa00b500c17100510302800410101820340e440144034020105070055001c01a01d40d540e0045480341c20580c0b41c203281035452103182c810074185038100340711000c0600b901d802d00d0700718006812504c20b980e079802c44642d01c051040d00c0d92008102940700c0d0400304141491980e0044c2441101040030552950f4075012940c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 313143246 1250 313141996 313141999
    0x30403050609010203070318350705030705250b1b1c080a0b0901050d0c03080307121104032307050d06050907060305090703030804020102010902062109030c03041e0302 74
    0x1019450003001c2c0ca4000c1d041660a000000d003802a0080340143c10014504d091750812440003a201130400c030304007200300150a541103c0614880c8403a0f20300003001800709603019031301a5a44813100e182450414004040f03610070600e54140224804140c4a400c03416070301d5030403006030356252403010240064000c0382c042c5654840d030a00c0c0081c417401c28200040a810030788602c2c7c0e40d84c4a94501400f84c5030307005c111a07001582d00004010034513203001c840d5891801160030361200ca4980e00d482d0b0a9034801c0360b80201042c03101d80b090f820a10f082c0b040108503d10891814281425030355040d0a800b100a603540b0782c002104001c801404060022800502c8014401032400e012850000d01518089610465030b0140b09400101903009019152065410b80301030318a90b401e50345c05484105002e0b0060f4115036940c2602801600c2e40c90007007407100100780d10a90103030031400e08004043d0000305500034a8200b072120480c040c0700001503c0036205c64580441c961100448401450001648042d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 313144496 1250 313143246 313143253
    0x601120203150103051c051603140705070608090c010203160803060a05091e13080a0c03050f1c0b012a020310050c090306010b04050d0b060409050a0309090e01061202090402010203040305 82
    0x100040011440c40941c2035801100240c6c65420041e505801151b40a1042c544c000c140d480000c1d2141c154104500060071040d8101b051680f01d4500e487c9407a005680810303108801e00c0140c1e40c080010a00c031810900c0110300d400d4161084c1100c00c02d05a0b401072860740c0c0440810710036070f610b8240324040d01c0c003e01300742c0843c541164429003400c0c181c5101d01d00d0741442008030f040c13080108d6125240e10303003041416151a1080d04100c40b5505000301c25810094140007801e460529880180720002441941e801a0000b5440707960071a01500c400070305100648401500107408244041c40605500890503804c09080c00441d0408184c0c0c40501c1d522480c0c1400c0280031621140034081014090381242c11300d0ba207c09a91503207101d070b409195480084140387c0c90000b032140032280e40c000b002810200d080340392651260703d01840e80c0d404a000c20542ca8003400180c2d0188160010911880000e0207440c1c0351a4800d20342c0c401664020b4001c410741c40000c1c0030741e4004c004480c0150381c0003044 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 313145746 1250 313144496 313144499
    0xe06211501030f180f0c080703060c1e120c03180c030c06050c100b0d05010e01050604050c270d052505300c040e0a0c080a0506011202031501 62
    0xc100203215200304160200346020701110f1212070900c00d12910100b04550100c0803407140e25102070115041d5021603452801e218003242454041c044000114031136400030840c841c01520203030500c4509208140c0b031120880e26001c1203a444400980420040c080008407402c0501089019003012421803a0329035814040404210302e02030b403201100d0040303410329402500d0301c2013100d6502c10070404400c0755100211030341412020354025850400020401c0b030082505644240c2512481d80a00350a40d548d1020040035090500945620442d51001ca074076090101000c885803540684030100c0850100ac0c104406031254110701d0070303041d086001c135000d41205c490440c414105070003001031103180d44035000506041c034100302e03a18880000c840810801c0d414010100c680d411406e56a01d5100f20820b0010a485501c10b05111412010203020101400d060620400e0319603402041d841c1c0c020188032010070340108490341507509281080603125014000240744c803902021400500f00c05400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 313146996 1250 313145746 313145761
    0x405040c230307020312070927050a050603100209060708130f1505030f060d0c06020c010206130b060108130503030109060e0f040b07051608120601021209010e0621 72
    0x10300c03081c204000285140045001040507809000580d400c2c0301580c024411107004842c0c03403103110745c03203207051501c0d074802036403000310801c2030541c28021111a00c24590317150040e1a035001301035024181e60400c1c0300b20305241d004243d5a99407000740300203203503020403c110b0a640310805c03200519000180540c45640380b5a125000c4006071156000d298408040080c0d0a03000e850101011502d035101c903411a0794125041e04642d20050a10b82d1100e55608410001010714951901401042e40207000401050380003a150840241902010055040185002a84640050703074400030a10301111181c8070544006a140c0003001d0007000c038040440080f0780286598400b404840c00c070095881d017521000b860805060b0180c501030310060f0702031700003a1001c0c061002003001045026142c4c2c03200f203513070321140e113243c10072040c0081d041001c60a20005680c10081010040c080f42e48851400d00c105d40081c081d0035590b411180120f4001c200c1c8010030841c0d02404142c8005014011281e140801 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 313148246 1250 313146996 313147007
    0x1b010605060d0c0f0212040306020703020a050f0f0c0307050d03030c050f0403060917070b0103030f020a060906051614041e05090f04140312010509040620030403080c0f0703030c050405040c 83
    0x2c04000a01c5003407040c144c50303c00100c9180508845400030328090454690300007039032000c0019020f52044030b1085000940800100d0120700301000680b9005040080c0c0505041491075194800d40c4943c10503c00d55a483e41c2d00c8161640c503040c0042c0e42030265506451a00502c0c004203034003400818000184103894219a1605203e0624031140d4000b454070000b00c0c4c0666000500540d01c60001480000e000741c2640c075032040716004441c628202075035000b06460700d441c0100c2d101f42d02d0744188034041d070540c142441c15501909000709a600c15128500c041d004030301c9007101003000c04075000e40c0119003883d103002401b400f40c801c00311454034000120781c0d480c05171021180b103035032101800154400802558481e200d403503d800034991034107041020b000b0020348152507859840c21404804400c20103030245a8158800703107510303440d20f418042c0050000070000180304004000f095121281c2d281103403034051703060500044908584c82d044481c5d0249400c0540c005213023805000c0003a4001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 313149496 1250 313148246 313148261
    0x5060702070e070914010e041d030c07080c011713020d060b0a090204180f1b0f081518040606090e0714030f0304031709090717070206010b1b010605060d 67
    0x1042e4010a6454102c021500f02900d4030881100090b12880c440c8590712501ca5a01c0c110f05c0108040760701d0400c101403031200c600d481042092903000240b050000002030051400030b0600c040641248038a0100203230406085060503035030340303025a0004824440d03d03c450031019801a004004c000018030300031006080b004542403180880c10f03400141150140200c03801d81d0520107212039080146941007029100700055850641c1d00c50000d08100f20720740300c1c040070a4a1684e500c1252003810030003e4140c15020706101101145d40d503c0848948031401460017054040c24103048503034503410003100911258004a0010342000340103a44690001509025108280f03881445e0500c003604055490b11981510303040c64005110420108d000d0341403010030260441c00541c80d0014804c002541078808640703d1020841c0200084039419940c24010762210341e500040105506020701c403000c07802819100d00b50003401c20b281081060f800c0d001140101000340507607482c0c132940d071078820141104 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 313150746 1250 313149496 313149509
    0x203040615050a06051b030a090e0f22050a120f0e03010501031e020a0b0a08010f080c03100b06070c0b041d0c04060f031b0e040b04020f090d020d0506070207 69
    0x802500d401d1a88440540384101d80c8000c0410129a10302002590385401036010300c24444014010310118040500061800d02c03a070b9170342d1003911410401100d6114401812034a180614041042261035807001010784c1340a41c03004400880601e4134200e40b501500e0031000302061114241c22441582144001c08821210b44954078803030000000c0c1400c80b0030904c809031203002e200c8900c10f0b6450614400c584a64006001880e003244c55074001d034200d40c0200c250308006103103c0c004210b0181348180747c0c1d010381414805002c40c000701d407000aa40720100c410b0b40000741d81e280909050f0341d440004448486601004c2e10b4445c0703544201031314094105100b010400c60b4080801d0038450076109880f4420079140b0415070501d810444100e5074204030408003410b160f030711146401c444500c48030400300b04400c0d549541c204e80d1040180400da544c42001079001b980144103089903120303050155660a64252803000c90308131580009540c01042100260142c05107100f4001e44543c08a41142034885 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 313151996 1250 313150746 313150751
    0x140d09020a051801090e010e0a0b0702070302120610090608030a0f03180503070b06060406020a110103111803010f0b030c060706020d05040f0b06030607050d09060b04050a02040317030f04020d0512070602030406 92
    0x11101b103c98242c07408213074114034a4101c100b048000a20b1642d00e550400c0c0385104507500e0035143c1d40410070520258a009895a100c002000070240403402c030030300070f444015002c0c010140340c02c17102541d074001d00d04502c09110100701040c1c0114400c2c2e108138240001c000c829401031a490a0154980d0b0001c0819a001c008010000704039040000c00c480c1101c84d554018a01c09102d0f8587d0f007aa1070700318070340a040540340c1c4100802894950701828012101901040c10700e4040c2c0101804c4428004900b5001ca0401d1000010342c0d0b400309001000c080d0544034550b4580039490303c80003d100d43c0e61100740d05484c190510041c0301240c1c0f0000c1401d4032175240c084190315890708069aa03141100c0110000740104543d101703151007030304282c142a1085030086540303050b510000f4140d950880300013499650100b0304100748220009030340466143d4660051079401c203003202c64100c94004000ce8042d0a890611104200007001000302502030032a10548903c8585031140c041c0d44142e030b05541e40c90 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 313153246 1250 313151996 313152011
    0x161805010504111e0903150712061518030c08010213090b0607020f1f2106080c040915060308030117030a020d1209050708011506140d09020a05180109 66
    0x1e19114014082403400c00c92030a01d0302c8080e00c2c62800c06013054011075804140103900381c1e61400c0008503108500c03c00300c00d03101d00c1e01c40c0c4c00a21001d803059100600300c0c1060020411030183d0b09640d409000c2038a0b00ea00000b100390b910243d10003240d40000d040d03a0001c1c030000340040f0b065000d010025040e000c60880c00d41d413030a02c07109642c4590308256100c1000c0010781c005281035490589110f101a028980940070403444508124440c2c403d0804030741160010f100802c42440e052000c1311070344108005680c06c1540903580e403122020344600440e600d841e12010310908071055000200c80352030500c460b61310b034900030407207400c00e01ca10010f1b0004001c1c100c1d82400003205503401240a54010300d1805d0001200310341c084000340e030292100d0703514150000440c1051096001501074000080b440200c80d42010920241700d500000400000304101c0d1030706003c80049841d10045000d000c200d0f880a400018070510950380010703400f010a0041c40c514030303001d42e003003412241c04540402560 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 313154496 1250 313153246 313153249
    0xb12060102070b040e0f07030b10020c03060c18060a02011e0209030d05030115031e36120309060b0a180b0102030a090504053c0106020d08010b0c1618050105 69
    0x24000d0f8000e2017074540e8410000b49802c0d107130111160340407801d40760205401c0415000b00b01594458607140700141c000307005a0309281401c028880e000880606032914000c81c1d01d100d02036500550402503c00c079400901d43c01792620075040407110b10380034546090416000388040000390707c4114400c0c001c0c003030007903030507010b0b0301946c1624100d40c10044c03100080c040f0701c2000c03401800c1d502075154203107503030382032400e034122183c4121b82c09150040d0340c4134000c1c034149445103143c00c1c0080399640300c20a00b291610004e00d111158a503050301c6401d001c40c40c07100740c1c503202000c1d1001c05120f0b40c000500c200f0010311054a00c610006200541004200713005000c401240c50b4400c2054103030200382208000c21281c101a40055400340b0030728a080d0809211665440707081e100e0342c0c0c50283c1a005080361407400082c009095005284a00040c080c50306c0000c1c0160020505100c0d90102d1170004c1010f210032003003480854000007a00c280000c419403101c030040000c2d208548030003002c2d4546000803450313 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 313155746 1250 313154496 313154519
    0x3030f0503010e010b0a030e030a020102040f080f1c0309050a0b0117120a050702040608010f020403051203090a03030506010c020a0303090810050c07080a091e060e0603060a1505040b1206010207 85
    0x16074141a258603441e80c20020100c4032a40408003106c10140d40d42c1071a82050310030710292080c44419400507a07245d14010520382c081001d50050f030b549410000c44000c2d10040000c0300c1411141005404100042668043d03004040071600540503004143c428420800c080402d40c1c10303284120603404000003010101e0b69200c4841c01200310310701003084a461402c0c011409421480d1004002107045034480e214582900e0111641c4540507801240c18010414103100c4010302e00140003e403411840c05445440d036035002c00c40003405055407100881d07010b900c00c904400020341c000e08015442503a92400900603020780c410000107000e4130007604c442c042e450040a0140806400a5003480d019071100c02184e44140524010702c942c91800040c0c0d8100d00c000d00521483c51452000d103249042c0020f4507020010640500c1400100b0800c00c59549203589030b415180e821038200203800300804281c0d414407039500300c40d000250104800c0e40100d01503c4240c0314040c20307425103411980c4c5011050a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 313156996 1250 313155746 313155749
    0x1409010c090608060a081002092e050706020f0c0f01050916181b0216050402070308040b040c0503100905070506040b0f03250c231b041103090703030f050301 69
    0x1506140c1c040000742d103d00411034000000801c0034444a03034421240b4030749441c90882c9407401d0303004a154201460001c580313010151120000c00041c2c03042001d800d07030601c06080c1e07030b50030300c0804101c610500c0841c1d41514a02d010b12a10750780c0c3c810002e80001c1d86c61004180d0b030240e41d0300b070600007800c00102040c402030090810081643d2030b424400942c40c81a4400002507005503114502c0c3e100340c41104410018021a402400e2501e142c00d50400236071010f030300300c1401180100002c03000658000d034510391281e00030b040b1580c03e8540785003d60014280740c0c0803a9141c4104607d810300c1000c0c0d9488691040c0c4660210b54255544070b05010070b9001d2071040b4800860140003030040321031164011603202c4100c034034804044581d49030056414000280c80c0d0300080b60044e000c804c010725250b03c4086444444105286907102117501c950b540b0080d07201d10141b0f200180002a1601d0340e4124000160310301114944a141010074155030766000e120503000680c2000e001c2d207085010320116070 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 313158246 1250 313156996 313157021
    0x5120405010908071113150909060e01050c0408070828150203070908060a060b0714071a041502011b1b0f0b0402090a0c08070c051014010f140a060311070605040501140901 75
    0x1005601d823004800c01020200010784000ea11100c8580c812842031184510405d00e8142d2962202c1c10f003c0190710f03124290b044100d9503801480c858211031802c00c94040391078034050301c041500850385400c1c20300403180d2440d15003c1d800441446080e80e0010348810036150400102e40c0580d0b104c403000800e40f0410720400166550030441c1e000031840d4017401200810004045881160341c8010316a40404e031041e040880c248041000d0114464a03d40f00300c2703c1611b88001c0c4002e29807500b140c0000c5651100c40d40074840d134a800c0310840c0e5010510400b00f0703900030045030741d01142d80c1850b920002c01150b040f48148040e00004500d804203100d10f070150b8032a03503100c456580d070f03014040c1c400d05085074050303d40340f0880441040e00c5800b030040c0300c020311100c6000c54031545850200c4000e50f500f03130000c02141059654490f16902c0e001c400c041103035828580460045c00b000001d40d01c40c45140800f400389803c007400c00052040c15084030411843e02d41d4500d8181c1d5424031400c0c2260440c20310b01 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 313159496 1250 313158246 313158281
    0x309010c050418050c0c0a0b04030e010f270504050a06031115090d02040e010510050a0f180506011b03021507030b03030d05040203011104080606030c06070305120405010908071113 79
    0x602c03440b0f01942c00103600c00c8042c00910320303000300803c40616100da0204110b60f9011590200003c0540c0030400d07407600002070802c0001c10001500251201e00d524150360413701071900311116a011400c0500002e28029004118a040c4100410301600b8140020754161401401c080410709100340e00c900104041030145081c503401508002003203142200507a4000d441d0a100b0310480c20030f102e01402303010801014440070f890041030003001000c99000302c244000e014030030400c00140c10503000015a0740c50b00025075969440058507002d0a0512550501507905400000c05400040414800b010701081c480c1c10381d521001101511225111280c00d50414401d001210080344c10060300548001c0011a0f86500c0406860141d08150300416081d4041c0c020b2000600f8240403182d00c0c0441a2140c1d8a0120240c401a1003407251404001c1200c0b070641c00074050181c01e51121080e45c0d4071501e190359034034490404c21504449915001e108040007002300e410020180704a00c0c0201c8000c00d130b0b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 313160746 1250 313159496 313159529
    0x40212070501050f09060d06060c11030106142b030c0c090902151305091005090c0f040e09070504050109020a0315061d010e090112050d020106060801050d03020a170309010c0504 78
    0x31360701e050708141c5403182c20420a1019441c1c80385d2a005807409002c4542c1d0b2000b910b000381c1001760800d07a40c0b14509009234940901441400c4000107400090b000950b40c40c061742d45400003410300d080081103688902c000710104a0708051b07004805800c001c1c020341b10410400d803115400c070110f8401c418001d40c4021040881d0304100311610203001d00c9800b80c05152022a914404100300b451b0440f0b46c44c2c103001c5540310501491400041c0c0d107070448050015036042500306a505101c500c118004c90111342407400010f00441800c002540c00fa2101510600a950395203100030003a4100603a680d011030308120510807030322010700c1d80008031241d641d2378941d0103aa0400001100c1e4072400301d2410030071201000c6030603490315003401c5c0c001d00040c20f02500342007403420901c3c00c1c40710100780c000031641005820000242d0002c1400e040d81d1301142c2c2020103140d0361505919003000d00b40018407011007000c501c070030400c000020b1440303030701c07030000034880f000c1c00c0081181c280c4228041d101541a02402c03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 313161996 1250 313160746 313160767
    0x20f0303071d030d0f020f0303010308040b070519030203040905090f0a0605150312031e0c070b1302130603050f071d07050c060a050a0f050601080411041b0804021207050105 76
    0xc805005441100c00c2c0021456840c012a04019103a100480820105c00103d08510341c100107003556071901c0b0010b0360a6505503900c01c20365205034803440b210840003203104024040180840411410300102c01080083c1c2e515001c0d44035040380c840c1c03181551500f0300054000034003081a040949010000c0c00b0004080d41c0d0744001840003130b1500c00100c041c6100f209058500708489113104499980d1103031245444050a00030500c146504032410b41894184100202c03000c0641d981d0a62001d1381c000181e40d81000000744600254020354045c01c00c041000007280310754880c0055070300075030584450b03403a490090395070b0721805d100c0e15805448154040810049164400d6045900c9141c006d02d0142040d00b22032500c0820340c0c800c200c0b15a42c0e130902190300700c1442448800301d45458107000d039141010018088040041010300034885003842c1882641d00c03640254010900c43e0020000c1034000c081c020008413048900f04d00810341c00f60030406074180001d03071400301d07801607540c0d600c0d102d1100b0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 313163246 1250 313161996 313162007
    0xd0309090b0a05010f08100b0703170105060403020d0809060d0218101407140c1f020c0d0f021309140a03031113270f0c02010c0f02071716030f0210020f030307 70
    0x80c01d5401f05151302ca808038030700c285103000b020064040c4c2e560761225102d680340d9000c81c0030183e20291088104220400c0140c6902052040c195000010310740c454007d0008500d540c880c0074a4235000394030004001f400318a40c1c00300007210303a00940b40000c608105410a40e40e44034959030b54400f4400a111610021701c456004200645508040d110711040300703004600c00381c00190360940c02c10319100d2200481c41e13042003480d0302040100e4081000c07204c1501d50760340c0c1d1000c0140180c000c01c071404a800c0700c1d10060b004119125406400c1002034451103c03010b0701c401038000c0071000079040c1220007181e040f11001b5a000303160b0703414200800a103411842c400030005220085e082c5040c5c030741d01c4003101c00746203e50a107800c6d1610020a065880b241c00074210740d041d00741c0c4424051407062400d1004e50000706003003901c0c9501000c11a1910b0b29000341d150070030b040c064000302c0300c0c1c0350785c00310800550903c0c203030b410b80c401d07100594002040b0000b030340c03900c800d100f49011650090000030300f41c030300c03c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 313164496 1250 313163246 313163251
    0xe1201090605040b01050111210d2009031009050706030509120a020a020f100e152b05010f06051801030e0f150c0a0c0204020d0204050d0309090b0a05010f08 69
    0x110001954911941e200000e40e4400c440a480e1001c026004000550304180c2a1941104841c081d114164084460021030024030030340d2500c9400106940d0340d206420352158a4243c0c0ca014a10702d00c0202040d03d4200394440d03c0d20502038003c550b040c03800c040c0350340620800150b22001600c01d8608000e02207006005c018040c22b0301e48141c6085400317030007039403000340340e40082c6030702a1103c1384032801400044030032482824028590104000302c0503501441c3c88444203003c4407440d4540e19050030345c1019000746251004100c81440e02000300d0ba8a00300450b103c0c0107440800e1040f60f030307103860b02204904984500000308104003e0811030703002c0e00000351042103050400041101103000a146008400521840d00e90700c1140882d0b150000c003040e03198001220003851b4609800c0480c02428442c10342d00007409150041803114030400c1170b4040d04c001d400d001c1c1141180014900303005082c078003207206681c1c0c15450030003c1d08450038150003880642ea01a161200034015503034003100c200000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 313165746 1250 313164496 313164529
    0x3080901020c0a0e040606050904020105070b0c0c0d0509030706140f030403030f020408100e07050f010507020423041b0308030403230408010c08100f0626010303030914010603030e 79
    0x103280280d00705039143c00311440603201d104241d4034146001e1900204032403c03504464810017410080000503030f1310000300e8981503444400c60f441904d840ca110b03441070007013050b51050780c000d24090410300d07503101000e030040190890450700341907922681600c006c6034241400e50100070401101c114a10003a0065402510034038000400e142540c0c1c1c01c0d01241c00c65044a00305130403444031043c05c82c84070b0003008510413a0f08003504484e45028001590200d40b610f00c2818400c01090000540d40c03203030b0100060b5450351021f400d100c02c10381250200010b003190308980066401d405000400400c08080d019650b0041c042840d41d1240e440030f5440780c6109500c400c03202703c049054001c041c4401c0280000344544000802e0181e0100000740c12610010300d1140341e0000c441040140c1451010280c04450f0903061003403008442041c0c81013400074070990701c003030640301c034000104255050b4031801d28a4007545000c0c2d1201c0c00036802034241c0b8418030025000030300c080e001c0803551521001c817043d100300 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 313166996 1250 313165746 313165753
    0xc03200309120307230301031104060b16050f031914040614030a0914031804020c0309120a0507150807080907090b01030e0118060507170f06010c0212340308090102 72
    0x103411009503444c00c1c24560903040a20b0202c010000c000c0c3c400d801b0b480303d2710112030621400d4140710780d68045010b07004000ca646401c0d4100c032018401d06004031100c107017600040e0b03a580e81220b80046100c8424840b01c0d00000c81c4a1000610702070884207903801d80382c40b03544001424a144891f0507543e0000761021040320341c0c5441c15000509a68114159110100302464a460380034501991460714900400e0040d1b00400420906e414040304540901100300c80c401d6070700d07030840c00c01f505c0c0c04040e01004207144220303c1b002c240a00922040300c0c10840650b615003156403005001c58000e10103403081d1070950f0104405105400300351300400514101858000f0740c05008019080c00d4420b482403a17410000644852028003440d4020140c0c0040350341480240003044000103034484a00a01d0088015424000300e505a0b00c1389041c515141d800600b072004403402c601807607403a1000765104072a4918490300c4442d20314500c5403d0860700403440c103c201e185140d52203070803040d400070300340904500 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 313168246 1250 313166996 313167017
    0x108070e041d0d03050a05060a08070315140a0b100c0506162703020a080a051509071508060a05010f09180e01050711062a070f060c03200309120307 65
    0x108001e4043e5041080c0e0300403030503043c000c080400310342001c0c04090103540c852405016803440010301c2001c880d0700003a054000c1d049a0f1420004000c000c81041e410703d4440f080c08480681c68215100d0214112852a1b9020458905031490091254024165001100050350000440507851201c90890804d40d62803404408050303041305140c0070b0214080002c02d410b109600f08901800041c000741c0c8010021040d85465182d82e440030903220f0086460101c3c00640001c0c01445098024601c0340c0109480c4c004015000c1d02d09003088943c5e0307010b0615140c1c0001c0d51341c403d40303006094080d1a11102c004e06d04000c030100450030b00340111001e4546600444680150900c0f40034851412540c0e13504600000040e420705000c0080c0c030007080f070f02c0401068039140804810055003016902c0c4050717540c4c0058601850030301845800600380714a003620352200b958041d04030b850111402c3d4688420035140c200c500416000c2a5008071040e8420b58407103941c032540c1c4000310f421060b035040110298 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 313169496 1250 313168246 313168301
    0x30915060d06020a120c090e0c0f2a0303040b0601110109030915020a02090c030708100f05060d0b09040b1e0130080705030a030501150c030f0c020a0807060e0108070e04 74
    0x12001b030241d16001600d1440104a80601000b440ba08208800c012602e0800828100c890714003980384030007801d000081d0072500b81548419042d0707840092a05507070b20f81c07901e400c040240300800c5403118003140c410340342000c13034000620529040d03641c0340d10341d680740714204000c15240000308101d0754107500c1824000c10150740c171a0031f120302c56146a080d0581e00d14021000901c40c0c200038043c11500d1580c14000d01442130f5000b410011384e401912483c0d1203c810002c00d8024088080e00107801600e001c1c1400140b0035071140c11031040c0906810624440c102c0c400d6201e401600b44101c01c04064000345094001e44070030b14241d85503912070000d040c2c000ca02d03180c0900940c06088104c0b03065000040d4681d006402d4050a801010410484401c0388001c81d0b01400c03c0701980700040412030807010008a9a025440140c0165009002030740c42c40c1d118541c1300e558603403502503140413440c0941320320915032203688510b225900341d90300c06005e26001d030f0074040500210740c0e107540903001041c0616400c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 313170746 1250 313169496 313169501
    0x1203150d060203061903031b080d1a01030c1d12070503030408030309060a0603020906040c110a08090f060306010504090e03070b0702010f1401080d1101180305030915060d06020a12 79
    0x10030303000d05001a503908210b07040005c0c1e0190020b800ca108070083c0b00c204042500140901c5080000801100c21103c0516085050b44158409014410f2400b91030710100b072841003500001d200280c8082005120202c001d4460840c0d010450b1480b00c102c2190151500305080078484030fa2000007114070440e01c6030300080c04d45e00190004400d03503201008200b410305041103180e41041d00c44104001482c199008514484001882180900d0300c1d0b660345502e0178850442604c211204030281c8408a50030300c0d00c642ca0350b00a10710355100e454410340040203460306034100c030300942050b150301e442e091030302d809500a00003090100959000030311000c808500b02d18083c901c0f409a5a00014804540c0da0b1484102d500101c03030500301d6180600180b221060000d4140200710503414a000c005410080050140500c0c000448540170030340180010503422a02940c0943c102c1400d640900c20b000d00c900c110304800316080c0b40d01420343c181e1000840e14030350090400495615050190282c0d4410f41400d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 313171996 1250 313170746 313170769
    0x61c020a0c0606090c08040b0601090f060e12062712070803040209090f1b030115030c180504080702060c0c0d0c0906120f02011b0f0c05040606030b0102120315 70
    0x101d0444a40c4204102c2e4600c504406004c50000030001e80302d05410041c81e00750005d100500030903111000c00d01d140c1c001c04080d0003c081c1a07441c801c40ca40c5810004000c0380e42d01ca0010b028640aa00c2d03090310036030100e03071144550001c54942010b0340070000c05c4650491181407292841c042c950114106202403c01042c00c203002e08151985d90504d441804020100200481d41a07007000842550260f40461540c00d218141c00b0310082e90914840020f00502c28207414070103401d59520300000f041461380100c021284502c0c030a40c00e44038038208202c2504c004480090003c6420401c01005107440809002d600b00f10381e080b100c41040050201d00c0d0986200300036100070000010410180c2c0141c003520000c0c10904c0785041d0103014960740d540d802d003100840241801484d01c6c10032025461040e180d92a16000615201342034824109194a40018064140118103000300852214000e0090740202c00781a4000d290840703080003550b2180d08050401e00b405026030340000d4007070350b80c8003007000c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 313173246 1250 313171996 313172017
    0x1050c03180f010e0907050903010e010e0c0315011505070809030d030b030c041814030702060f0c01050c0715051b0708120609041703130f0b040209100f05061c02 71
    0x1440704920408000840141c00401810840074900102c40764503400b1381d00c0c0c0c01c0101420440c3d2984419000280507090b41c2100e10280d6103440e0b1480c400307040001c0c494181501c1a801c2e40c1103d040510340c1e019590090140e07d22210349420184001441080100490f42c01030502c00d05041d00c03100041c2c10000b100c0031780e80000c1d480d628800030514040c0f1941201c240d081794200030046003c034603036603191492800a4249804040c0304114100280b04440c4a140e0040c0110340c0c4001c014400041340c0c01c51005032200d98a000000381c104001c4c6800ca85041c2d17000b21700f01c410011070542c030038054000180340700e0782180c03001609180c82d4921030140c01038a200340c0d0700586452a50389408101c81c0000d00c80c501c251085428000810645480000343c0400e910030740da41c1e50f45100000b0340a9a000b40000c0c03110450102010a00a2050320340d4003451003200c400074181c84056070305040700300b40d01038101d17406c011580070005454128001d000b22150020341d8210f000c00d00c400301c02240c00004098 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 313174496 1250 313173246 313173277
    0x803060307031a0f011e05060c0a05070e09010e03031306020313020a0605071713120503090a0b07061a06031521010204050108090f0607030b0f1f120501050d030c0201050c03 76
    0x21880c040d503907050a014021100c02400404006d01c020424a00284075003401200b00007035000b142c210512220b032030a50807008854050b0360321000b0750091101200d2104880d440c21b842001c22450200449000345261442c00000b020309480e100c0084d0310140058002d1021a107244006031a140d82e0300d402081103403580c030788843d180e00b01003143c80340005a040c0780340c1080002d04822800c154190080d22101c481017001c0c03216624100c0e1440c46555911584411490300006201034400010b040403841500188001010803c10700085003042c51603036840178050001030382c0080b841e0760b8079002c0340d802800102c62003906682005074041d0b1032500c01c503e94000a091029503000509160441d100038000c1c00d509404048098507200081d207000205529046141c54541e5000c21401900c900200018540031f80321059075220304141c05642c0105002540c4200f52842c0f41c4a1541201d401500c4480c0031040c5660480304070f081602c00701c0c1441001c0c800200240010406000c02c50b080d00d105 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 313175746 1250 313174496 313174501
    0x10323010e07090806010b070b1b0f130b0721090509160f140f03060a09020c0a260702090c1903090c0e01080c040b030c031207020f1005070803060307031a 68
    0xf084842960840d010541c4800c4c010020303c40d4840489105a4002c02c1104c440d031101080032412241010104401080c041185407030703007000070004c010000c044000d490040d43c2e40c8882c0b8110780510031015003076203582010601e000c1e440320501c0941644500c0c1482d40940c64400050402c0002d840d0040400e040c0121042203540044034100301c00c20034140030440e5400d410101c00d02c1d200380b031303034210411502101182c900e840e0001250040c080041d420340d114918045602d07915010a88250342040c1902101e0000808803403070710911064103e0624903045881e000d008460340090408480b40604006a4a415540050000465206980100d0f484045007049840d100d06500320001440d081c00040092040000e100740c102e20301520042030507124000040e0600815880075a018000c9809810000c1614001031095030701c00c0b1004010052020203202e10344540c8030403140070035800c00100011071000c400ae154092030080481e00003a0b101d079a460b1440c206a850382048403483c405 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 313176996 1250 313175746 313175761
    0x9060e130209220b040b0d1e1415100503070504090807021c030215131118100603050112030e011404030804030c030204050604150501140d0e0304062a02010323010e 72
    0x2031110700c000d0445d01440781c03c00c1080094688562400020031407210074016100c00d280030071900b041c1c66001031031843e12000c410000394548001c054644203035028540025126902c102088047d6a80907008001c4281000d06101c0180313801c407000c0d41d01d0042408040c0040ea10001c1c00100d0546103883c2212640c12860080d103442c40c2c143c2c140f40c4000f503000c20808004035410305910001c0e00044484d40380e1000c0000300340c44c10302d800d000b81038030701001c404c006840f903488156400710307042580e04001d1aa0b858020340070038401580c000b00014460000c0c068150b00c12220b50200720102c0302d282703141542e6903a6407070702680164012141c0384800303c0b04005501d030a20a00f030f8030010645043c404d09030900a41c01c01003450f400341d5418402008000742d06005901c0a4402e542458002040f4a912441206135a41c005200d0b078000034001006030201100c50302020740400451541d007500c0051258010f40260194951801d0f0301d520295400b90203c1d040d600140c000e100745840482c040c1000c40 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 313178246 1250 313176996 313177001
    0x7081e0115060e10210b0402070f0b0106110303061f091d040308010e040c09020a1106041407050118050402070f02030a0b010501080c1806030405150f0a05010609060e13020922 77
    0xc1e80a00450802d80c4c41c030100300d150800f903040c0040e00c0000381d8030a5040040c00038003a102c0050500841c44803500e0070850890403c80c180c1c0d405480705040c000403111101e0380d078401202c03041d0f0003011805400f1f00544110f00c5080300c02c0c0724b90906511454545800110401b01030040117640100e410510040c103401400b10750140100c2a40307039045141a444110043d4414899046100d50005283c100380d446522514042031802040d5003290070941001024030404504650690040d8000096950301400c0e000050f805a1982903205501c1d11042000a405c0200142c48200f81c61000000583d010300c26200c2c010b1041c02401c003654100710004010f0b80740188492484031042050b9808246132401d0f02d10101001ca81050713407a80e4500c0c040d401c188582d0b0340981a080740000344528820384102d6a80300308210031040001daa80d40c10b00700c1c8d001080348a000701241c210043c2045a08119521200c191242c80c805468154101d002c01c4550100c010b14855403c040d402002c1e1140090 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 313179496 1250 313178246 313178269
    0x60709090510051008070318050c032e1518050901271b15020609010e0303150d050a14030408250512011404110f010207081e0115060e 59
    0x70300c19002c140f0705180114802d020110b028105000c181d600107407103c0d12907007000440c242c50200c0110303461164a046640c854001d08403030b1081c014001006020541005e81c00500030782e240e07441506d11040102d0350010001c9121503400c85d80d2440340803c0304601c0c0341094904800913280040c562900242090840d80ca649150000304454441140d100725041c100146850700082401164682e080e51801c0c0c002059010410305160034412001035034000c6212841100c82c0802442092030840301c094413403004a64001e103061400382d02d03490b01d051030078000b030106104404440040d0840c0c0c981c2090007001410007502580001402d0101550500094200c0340d140e10601840d07905201c0700d40c501076802c0c014280128000281a035000100350042c04266851010030012428a03050000030755034964510742c000d4140082c18480c95200213150402c6075460390140c5424004080003100300e1136610458605e035901d4001d01305000c1c441d15005070040140d034940e0981d400409050241d0f02c05030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 313180746 1250 313179496 313179511
    0x908030402120a05060705180a06050a090b040806070c05011806051b0f0405091015090603061d0109020a020a02090916080f0c040c1b0b060901121e020f030607090905 73
    0xc411800001c07400256150070401e6405d1203525840759408c460f42654508110540c40424500d0000b6805d4204004010054880e60b80140c203e8840c030480c4580d110740d116001c5240d000a000a280307070b2203501c0380092240f16100109181021a0301c08d040c0741840c039400d41e101651b54082c0309000550100c0341e400546202c403840d0901d4030005a2405a0059204041c018038110000503c11040c0b0200754010740011f101864940d0520480248102e0040c01001d010030f282680c08541c100c440c4104140b241024030b058441a0308001c00314019402c05000502548034200310000142d0b11148514403c4c4100002810100e984031180c0c01c448119034000b40841d00610341100050300c0114080001445c01d542c04521004e016404448840a03400d03251400310041c10b0704030400c81d6540800d0b028801c201d07081825640c80c3e4160201d840c40444000b003035540450a000c00202101e8240110030b1700043c078802c07074442032001003400c01d181102e91f20b00051211700d0601c44860715116241d0000705 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 313181996 1250 313180746 313180753
    0xa0509061503031e0c070603060f0b07020f040b04020904021810050a08040b100906060e01020d180e1306090b071206030c050607141209041a0105030c030c04050301090803040212 78
    0xc04000b00b6100e104400441c0001c8250401044890301c03500119246a0703642c00448440503178481c8000d00a2449000d8a00d01c0c01c010340000400450075025154113a8005051500d00d9103501c0420004103401207805402030780a00c04101c0329611440940f0124070344505914110031090f040000d00300851411000740541400600c43d255400608079a000da0304c03000c90409611405041008948039a01002c0c615041c100040b41090780101c0c410090a03081e0222100c03482c42c68402c1e1007030132490707511600134440a04204640f000000116401114801d0060410240c40e21b402007a2240b10360242c036034540709801c1c040c0c2190321a6181c0f00603145c005042120078110f0740c3d401d00318043c0c0d11600b840340401203140740921035218011720600b244981165140c0d21035104d0350202e42c01150003503114515001204101030181414400c83c3c0d501603540603d10b9507465100c50403a00003404008200301c0900003c215a202480b41d50103181c00340b030109840c2e1400d071040182c03100c40c0403510140d941 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 313183246 1250 313181996 313182031
    0x40b09090319031b031a031b01030207020d0606080304031a07120915090b16050c07120c030f08091002030901170a150308130501050c0a290a050906 65
    0x36011050301c0250703035002d084089003100000304902800d0300e40d0000c0c1201d1200d1a520318501e4065100300007245c0c1c030b681c984007074548070010140c50b41c00000c1918140e10412150075403e600c203038001d00400348000c000105100b61900c5160845180380c010101943c000541030003440040640c03001180b800b003014203c03514248100401e4545c11344402a01c0c140c0301c0000500308400300403050301c20a8680030400c14401c150074140010b880c140d42e0800e64510048100884900c903000b00c03011540490010700d060791900503044101314003820b099075041c140402c00320010341807814000d00b16004400c120f4072514908100004600540411405d6500030001c0100c0d503600803105144c4000d00794029501c0781d854503802806070204050341084502954004020041c1540142075078602c0387c030925074100d450700010f4559120303540d00d0fa09241d1041070341c036001404035500140005080c04410300310108403244039038104402e5540316aa2902c0d2000c008100c501008101c0c1c2c41070ba9100c0104812 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 313184496 1250 313183246 313183261
    0x9090609130b1f1512051306050405150702010b011e09170303190e0c040b0609060f1b0a02061228020703080a02160b0a0b030303240d08040b030a090818040b09 70
    0x5c140003844103500b544c848000031882c03803014a0030300031242c0081050000349450b141081d1a04901c45d0604070300d0b0140e0001c25202881445886120303401030b11101001c40d042218455903522a102002c10003020100200b004454610a1030001001d6401540c403820640c04501c0c4156121511845051811048500e003520000e401040c200056030005000c8074000081550361181d401c56940151001603003000c003444a40081425580c0400d0f6600304a034440c0f4125120701803070b5000f03584014140860464807450465080d00000556070703035041402003907103101401c107406555020181c0d000c6a204245500010f4196000c03020700c404602d004140002c00d40e050420307004c00f5203043e12004c005405541c0a50008003400002001c41c2d440b03161404958001d0580094642080d00e90a18a4030140c14105030800307040d0391140809051500f040705200c8644c00040050010584801c0d0760000304040500804a8011600d00c62002c00400802c2c003013940d40d5404840d000710401000c10000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 313185746 1250 313184496 313184507
    0x30d0807030b180112020901080a020102061f0905041a07030605061e090301110c2b0e030a0c090c0e010c0206160c09051f0501020309090609130b1f15 66
    0x10803818100014107401c250041a1901c403003560703440201c0c660400100c1c0f00c624444c5480c98131803003100e038007020b40c1e2502c0c401341e2100308030701d03000f40036034450740200f00d400840104404070741d6034152a10342103903900e001c0c640c25034006403401d41d00c40005240200e0309010108506620810030f003003e12005180c80046101442802c1130001a403241c0c16080380d88121071800c40d0b0620000400030b200c0b0315802490704060340c2c01742c11440c135648a425090000828a03284407240907403000e00c04500030841d40d00a40e0000c1d550609943d06000311000700700041c110b41c458002814050f000042c1c3c08205400c0503154403a0620300c9414064410030f01401640c58100b01c55801d54004000e11581503145003642241d45180c00c009001030515007004450034401c040321b02e464180c0008101d0341d59a51005903164801d414a03507030032500707200006405060455000e81c11003c5c49d444141154a00d4550154041040d1240080043c819003800c0d9041e001c110080041d003002c0700302007021410a08017402 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 313186996 1250 313185746 313185751
    0x62a09061b030e19030c0905090c0a1203030203042906030601061d0607060e03040314010b040204030807020f0a09020f190801060c060b011206060e0312040b041403030910021506030d08 81
    0x228400c00e6100ca02c69004c070210080086a200c240603103616110603100d40a4802150761003803a22503854054181e2a04401503002c49002000780128402107840c120f001c0e50000704203840846003043c210b01c02121203500303410301c00b0814600203e03904058040500304038060740728500704a0822024501c08800d1000c0030b05030741040700c61030340c0c42400d0f25000010301404c00544143d0302000c24004240710550326200011607480d0004c000030041701c8200022030081340801f41910000b401808014145136081d04a0804010000fa03c16030b80da41095060303038402c51468030b120b0b1000c03410300d4a68220600d02070702010b2a0074500800d41c1031000040a0100311800503165076107440030b006c596405480f0380700e4072100d50f20341842515100c21025001d100007246950284c401c82c1c030001503040244040d1003da81d60000b5541c50a80743c411600c2e40e00d900480340d507a00d0300040141495076a504000d0648509260300030f402083d02d0707443d80d080055001003502d80a5084001c20904661b40909d00f603a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 313188246 1250 313186996 313186999
    0x30306150e06070f0b0c030a05100b0a0e0310021804050f01061b0c03021005030106020607090f060f030612060e060702010b0d021011060a20090607062a09061b030e 72
    0x140c03118104d0810034543c000d206809000c40900c81c05014480060701c00a501c29040e00c1000c8c411074403282e04520111419219400301102c09208403070307400348103205e900b0b40d49a0060032200000420b109840803a1700c1440f40d900c1462101c1c170420b0081c1011f0141c02e038420000d440800496141403c05064a0030588034a07821103424140c1600300b200081591000d10f4001d009084840307070040700901964800e010b000c0251207900006a0028031a010740340c207441001e41d100384903924106080c0c500e4925032202c0c078285a180e80c2e01040c140a1404030010b81c6015040200c1d4152224180e2414014058a40421a4104114001251211130751010400c0d4140c9491000304005030f022610114001e44a40d940c3c0200d00511141c120a50001904c0e40020594803501d501c603c407507288a4440e2115268002c0424820440820200da212021000e0000080002c1c41d003907142d0341e00d0082d40d0f41c17841408180b030300070180702c0c81c0c0c3d0128480102c880030a41907401d140071601d0103003c0011280c0c0a6 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 313189496 1250 313188246 313188259
    0x20c03030c0312060a031a07031b140a03140a02070b0615031909050d0c0501060f06081501020a020a0821032413060320010201061d0a0b0616030306150e 67
    0x2490b41d240d41c43d104c0300030354100300c050741f80101000ca002c22a160a03a865070000341080d200c00403000320070001d0186500381b500c1e100c0e41011050302ca140540c000c01091400d141d51450308100e500b442807503c0e0f1040990000059450f0440d1811044145000d40500d0050b1400503915000c442840200e130f400010150f005891600e0905510300a0074a400c0f008055000e41750800202c0b94001314144141f520940090000c10b40b103059024020b505407044600103070304400421101d20000c0c500800d00380041c03040d154480342c6500480e084100e20f41c09446694001040300c0307501200c040340c00003450703502c50500e45541000b6201601c00c0c09444203070155141c1c0c40f4134403455992400d418820000c83e2030000e004c00c1e0b03502d050000e8581d03842c200c031541806840d0080a1158418031648040d511010003d1100020304407209056a00051009440aa40c2e0724a8501599060050405103541214002003a4403c0c030b0010180c031801da0041d05560902600d0b0310b0b0b0186c03c1640c403080c02c2c80c250b409 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 313190746 1250 313189496 313189501
    0x415150314130528060501141e1c1b05040b0a050603060307170f0f06090604030c080d02040b0c190201080c0a09090911031510050d030512090c01020c03030c0312 71
    0x80f9003040c0e02c0e03010300546202001d528540000c0c01d9140e2101c5540a2032080000740e994690919400b083d00000561055540740901d26104203e9494411b0110281201c8540c080f00c0c4c030300508054242c00c09644801d01071003581401444a05e01d1005440151000e0281042e0080400c420103414002c8621901c1c0110011300c442d14100002c800030103035410b01c2c85141c1421003400c2d4035911400c401300c485010301c0310f454800020015600e4081c030712071801000c456030340e41c030200c070120407000080303c3c005c0f820081081c3c001100d001400143c20094002c96036502110401440c02c030510401e82c012803e0a0300c1440981e8020041552003688a02c1903591501c0707001003107a5007080c58000c030390312516055241081c0040301e031041720f81031002c0c0c0480d9103544070710b40c85181e40f000440366803500c03070f40581d41030025040041803654518401d0624504002d00f401c05090742d104100c074100d426502c51907a070761003503074100100701d01c014040d40a14034003198441050341380d119021041c001c42100c0303000b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 313191996 1250 313190746 313190753
    0xa08030f071e03020406020106060e0906043909050d2f0402040801020d060b03010b0f160b0f1f0b0301150519020d030b0604080c010c030509041515031413 68
    0x510001c2c2038214000480000500306025009401c68060100190319090000c034460340078501203607840100611000c0b10303540b06c03c1000042c0c40c2c85011460b4151901002c5042610000c2ca012031690b80950000d0210340c82400c000c2404419602192017030425498080110b401ca0003032010003e142c14119000021001a460609240340c0c1c2d0280c009100180000d043c150640c0034003c02020b00131306001d101d0791a06032904500080c02072040c0742d0010420040314840c5440100101d011140c82d0030b8100300503844d51418618210b800c4480b00a078a000c114141120184520700030f440180014481c50500d19a8130340c5d404140030303d003840142403064005403402042550641003078280300c1d01010aa06034000d40b5841500d0607100807a0900c40ca0b20014948482614180c07105540144508485100110303403072080e00d0000d905008040050b510961500c0c080c00d2400e0f013803c5012141945030100c00b54140d0800400e80c02010b01e0060801c0b0725520080d80e8981208082c206080003080380d08 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 313193246 1250 313191996 313192007
    0x6030b0a05150d0605180d050f0c07030f061e1107020415091104060e0f060702040515030709061a04030b0103021011010203010e1e070f0c1b090902030607020a08030f07 74
    0xe041940c01004030f40e0100c00c110058010a2281e01c02094100110301c00e460100d580d5689418240b020400078032045580d802c0ca0f1003c1d160b420103001c00c80341820b85d2900e41c0810380302e03042c00070784aa60311a99075400c085400401c034204003a91140c1008403c8545c48485061701401000a204945a4884041c407068114000001e445914010010803004404d1003c3c0b507481031048a01240700000d160400e46400c6c04c854251340000f8100380c1c83c0010550070407000300001010540e160b50305103010713110f13504c0410460014100c840800624141040e00d0341503030401c01e450090403904200410b00024141d9404681100c1c0c0c192210510110035981c2501c1d1800034501c000382c80d600c04000014568141403049001d03600d00100d5210701070980040301801d01046441c0004100c0f05408110131a1003514104a01c60203070794407102c18041d162001d40c00d07183c15031214060396100d105110941ca010300c2244c1c0c0103030031400200040c041555130701c501c1c1d000c014803004002c541c1900003a0941d0103203 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 313194496 1250 313193246 313193281
    0xa0c05030309150f060d06021b07080708151302060c120304110906040e0d05130906090c0e06030405060103030c030e120d02100b010804060f110d0506100306030b0a05 73
    0x50036241c07030b840c00d0342076580e07286006008a00340f40e50901c041403420040300301c51401040e016140a034600b500c1d03150200a03500c0085020425490303200d6692180c10103101100c058030724600605a05423504c50708500c3c0914410742048800060700501940601c9412075501096040d42d0711501c541c1005c01c2c0d281084031203c0d2038440554004100800c01000380c28214880c0e808036840d1040307807101402d110883e08c0d082d1040720581d21400e013040c0c40da40a0030180c400241211004030419490700b05400030b4444c1503104071a910b464920a030441a044591f01001c80800e640c00c0f8194501600d13000d41e03d40040c0f00140511848240840605201e64000440c61710007402c04940d0f01000c9010f0f0b07544000c1e1502000041c09040c1076591118500d020701c514500e01652414030036100d40d1150f4005020507030200104640c0c92440c001c040000300040d056801c83e8100000c4d86151240038010709017400c2c07420174201f624055051001a041780e107040c0d000040318900003820341d02d0a8040b102036454 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 313195746 1250 313194496 313194503
    0x60c021201150806090d03020f070b041707030e030106060f09060815120a02010807051e0306030307050601080d0f0203030105010f0e0f0402031602100c0801050d0606090516260c0a0c 80
    0x42d50004100c1c060006001030043c2e1200302200c1454a600c1c20071001c9019052042d0b0002c2c2080001c100030503500c01c1001c1e0400d00030800c1006007080170103102d509138032140f0214041048149482610710302807040d88010309140c00c0c0354002c915101002400c08100d8040c002c140180000800c41654504000e072420304806088641e08074085050240c0d1070b103942e1400c070300060b100700c00150902e2044080d5081c2e640c03c1c003459408001b250104d5400ea8100400d0250580f00511081012803c1004501d000381155070150512113240b50000703001c1340c81d0302580015580b04100401c2103036403188020048102e9447c14800810030790340012018907aa0300e480f0360041c000b10601920b04c080c0f100458111800340c084940505164030b200c01603408540980e000b040c51640104084d060054194281c0c0d4440c0c140000d110303840c0e00c1083c00700c0390240c902d40e040e183d8541030350031102d801845101084241410158217400404215078040303800a104d040c00707a0000c1200203000d03000b110030704140da0f803 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 313196996 1250 313195746 313195781
    0x17010912110c04110406200d0314090109030206010e040204020d092a0305060105010e1c030807080a0506030a0305130503060414070e0f040b060d05030c01150f060c021201 75
    0x441500501e086141004640709020746011050702d89030034841e546190322024883c0307080602d44103043e00c07615880180e03c4442a010701c0210300504081c440310b491072806440000c0c4d00c400c10b541c1c2c0c4885800c010001d0000343c1c0341803459000300382c0000e2514111038030314031a944c01ea551480401d010f4010389148007000c40c2080c0d143c400b0032002041e2040000c0b42840b4901d45149007800c80054240188009401904040018041548200381041c60b105000c0d0001440c00e0004102c83c205401540301034000460031010300540c0359201402507002010306005010f641030540c00a0b485030a96140141880b00015014400c2406d241c0e8000c01008010142c0c1c0d00d620745800c12420262400c3d440203007030700903078030013060092040525500480b0061284501c6981d5a039821005400c094515030340301441c21074060000d101000107140c1c440302c0700c001003101c080d412209220400d464214042c405404030040c4600b6510044c0340340010b404652140241a100e000c030b078014a00686540d4030f003c0b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 313198246 1250 313196996 313197023
    0x1090515130e0c010201090b0c0904090507120501110a020d270906050f06030c030406020c011503060b0301060e07020c060708040b031006020d170a0507020f10060303030e1501170109 80
    0xc0c1c40d48401840c14000c81a10101c02c1c0d100012400ca03042504028401da01101c01b094116680401401d5411805007000030182401e451382440e11846a00c030405d420740a8000c2c1c3d08021080c0903584c2c1c412482001d040c100800b401019440d1f000302c4076050200701061202120307024502d0110f128071321001180e405030b240c40700ea44c04040e10990060710702514040b140c1e540d03181802d03000c40e0f1207a4401c5907000c0c02c40c2c440c0d0380d900c000f950005411099542d290030741098000024103205000314465000080d034004800706050a403142c0ba44980140c100c0300d000c100c0c5442d000308140c0c098010850303680c0c1ea10341e140d00d0594600d005580100c032200780c0c040100700f040081709414606690a64007207968450400c50212004071103025414003103078046021808242c8aa0803160304070f119801a5540c0356103040426161007070342c0d01d950a1194441c60200281030f00740c490460014060f00140140300c10f011501c3c8d46001c07040c8200d43c00c0381904294111445000c2d03002d0550203500082c00580c06 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 313199496 1250 313198246 313198279
    0x1a1e06030a0821010e1b0c010f0c030506040b030606030309040c1209050708070b030603030406050d09050a080d0b06030c07020d0c081005040b0106181502030708160c08060f01090515 80
    0xc20b4000016040301522002041166440300780c079205140d106140c1c100301402c0c0c1501c444030741000c3c01040303241d900c6527036031010305045029580c0c910300d182d6000180c0c0d02d4148100005c0c3c0319200003840c082d4000c402888001c0d00c0c0032007220051002600d022807c4044580d007180ca00410038050681c8a180000c800c0800c4804a03012040758011002c8800e120780326402c2c00341e10b04c401e441d202c0d45030744100803c000441c02400030f0508108044400142c2413070640380c003404c2000010085440c0c0000107860b01c04440d04d442480c400000c241d8006055151220705550144503404c800381c4501d0f80010444d00b0440e1000d80750002d092034805075100e082c4481e2086000e400155803c80303c050b030840001c143c141c403804450391488540c21012280703d281107001960703403800703506240440c001004080c000c640c0e01c5e0000d01d0401c159000c0303001380c0c2081b400d0210a2030300b1500603040503000303c1e087c880c0072a4000a524103407410860009600d071103041100e810300119400c45074015402c1201002d0a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 313200746 1250 313199496 313199527
    0x90616060c08100e0415020f13050a1a0904050903130801022502010507021201020f0f070501180f0605070302041d04020109080c281208071a1e06030a08 67
    0x41070803515200c405898501010a50221a0041240e00d030400c00010340455185400c403600350190160062401c12403801100381e5a110003044012420204010405810a005071000a010282c3d440c05182e00c01c000402441c40788040b0780340305607142d2010a900030000c0c0200c0d603111401c1c080001c1440e0351041c2ca503020750421527001d140c000c603c5462448031000e21900e038102c543e050795092702d800565801c1154040142212540c0c0b50340c00d20601818000110042440101700461940c0300c0c00750b0301d0100d0a45107800b81000001128283da400010031304204030485a9110300302081541d5404c3c0200c00074052a4001810009200d0040700403914100e8014007541c002c1c0c0c0e405080e25207134189941c0c2c0d07490b01450a5080041071100c603904000410500c0b5040c112034105060a95544041140b00440303903000f41e13504d003000180c5001304a00a500350018030465815101945007400051030305160340e8041081200048001404555050110a20f103035801000c568442c00c140464546 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 313201996 1250 313200746 313200761
    0x60e06091206101d010b120405151302121204050d050c04020301060302041410020d1d0604080114130309030609020607060504060f06080309100f020708070602100b010f08010b09061606 81
    0x200701c4c050742c3c8500460700002c12031816115012500c41ca01804010300c42035202c0001e105540ca03015407480700071400c0c1c500a00b54007070480019680b04000c83c600400031400c05100e06606c6550104802e400c001642c00160b03401c403030301207805141d49040b41c00c01c14104011580d10301c0c2e010b48000004184640c166004e8015a04105080d0007100c0c12003003031000d80e056240f88080075074080e0011340d140900c0f541c46007000140b8510b940f4a8040a0004125035412035006030311284d440d180c0044445000d142d245601455010240010f14401c1d1405012580d03107000207000940c80e0b903e4403042d034a0702012030310310550001c004c20151806051200040a05c079070741100040c1000400509000d00000740c841d40e001c02807060103d04903802068500c5031419040c1c00a501490400059414007403001303500401c8150050030414040ca684031040303a200c00c644a06000629042c55091940507000ca41903940c01c0c01040c1c0d0312045200010b190b1700586030540001c0c1500e048420400103603801094 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 313203246 1250 313201996 313202009
    0x2105010602070315020a080402060d0204050d0803090115030c180b100201090c0603060b22081009021c0b1f080708030909010506090306040b19060905060f030106060e0609120610 78
    0x901c4904da8104541a80b2610490300d000560410201d405484d00310002c2c8600400c14400500d405d036140003052800910b014283c0300e01d1404820000040828010b1140441042070b14180700750450351400c11541450103990600102c02100503520b8400368400e15a1100080142178241c0c2d0940c8024040c29003401c0448213403140100014009000707005640a560010780003504020800340e66090011400c03844020552641d00e000136941c0c030134450241d54070441503001c18854041d005014a80ca0078800c0d5481d6246450110404550036a602c2504901010310074142030460042c01048001c0c1900509046e006181c4005100030000000340542c0740183d500300100c2c0c0e80c6c0c1c400c0200d140240d050345a09078205100240c0015907001d415580f00814511405030f4559040c1440121007464021030f004555420a020540c6060440707224074042c210000d00c132490030507000030003448603140180d00400380402d00c0d150380c1e0b80301d5008005000854040b21810718200340d4140d03101c11180300c0e24 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 313204496 1250 313203246 313203263
    0x512030d0606050313060e030d1118180a0518070801090308010801050c07170d18020f040903270306050f01180c0503010311120109060203150118050121050106020703 73
    0x142c6980100103803403092410408210f550400758440a001e403060209100113800104010800008203101e028180c00020424686803004c01c1c0c62507050341140105035100d01c0c02522208040310341020a03030751013404a10046040e884026010362400d006550620746400303200000b04190b001540700700d440d10f000340e4401156907a00c008c0e0300c3c200c4a050300c829070907140401c03140d40880d018500840d51015807502c054540380300c0d00030f5134003103910040346a12000542da1810b4158038003120000b004810440e41004070f5420350ba0080c01208103402050a00c1c2101c0b40c1980785024040040d9004503008a0284030500e0a0070705652031280c01d009141d1440e034950140e400025091003110030020660301c540c1d10316401c40c0c40750720004c080d00329a00c1d0301c04040d005880c003e043c2800b07084011442000c02580300d040c036a41c103c01041c5000700441c100500d443e10300d245c650b02070805804581003820aa00072070349900824034805d51803c2c3c030003012807e007800001c5081c1d001030f00300100c1f8042c00c2003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 313205746 1250 313204496 313204499
    0x1305040602131a07030c05030c01060902130e1302040c0e09091005011d0106030b0f030f1b1210050402041515140a050307030c051608040e01080105100603050603070512030d06 77
    0x2d194110300ca41181a0405014001c104c001703401403d40180e402d0003034044030f0401703a40c1215282500c0700380c2c2124225940104028001c40c0e00000c48501500050031000c050b8900803084030711000000e000030b8800ca13122110104d03618011054081c40101c003402588440c0f511701800b45d601d02624407102e500f0344c5003000008000c1390f11501d0604e40e0a0403031040b074a1341d00e40001100034101c11518658004164042c4003441d6a081000e034051110b11405004601c03000b65424004102107050140182501d0091041120001c1070b0440e0040400b8070014047d155400464001c000d052130a003983d00c1c0ca010085448010858000041e0380c40c0d039940080e0034038560500c10a401028802c801181c024408100d0b424002e401005500c0c401d450300c58140700000e01c50301d90134a0302e528182d8517900001401e22a100b1000c0190b400752044100901041c2440101c01c000250548140c0701050f5603580883c42d599070900c498401440c004041240e00308008103070b244c0380c0d440040040f2403540741c003e0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 313206996 1250 313205746 313205759
    0x60601020c060d151205060a060b03131401061e080105010605180f01110303180c0301060815070e060403080d0b0a0806070f17011205100603080d0b130504060213 71
    0x140100d014030302a06040c03d044880d0381180280038065114010101d0004000c01c1c903154944245505501032401031005007070610052044034510f400c41c1c101e1410400c10403540c0042028080501c0380d102e200c40c400120a00d96082c01007a168000070301401c0012041c40381207412030380c01f0041c0e800c1c0304002c010b1644c0c0e8000030342e024401c0507020b02498480e501d101c100f40c640a24003444001781030400b811840100b050f041d04581c8200c0c0d4600b50280c00707881003400f001d03040100d0310205900f6070080207418148200c050340c1d8100f5201001582c1448000030300180d21031200d070110f81802822550300c2d00d0b10b134601401540c00c00a4007a0202d403401d049000d06250400456040b15046400b03841e041e150040c04551746030461507030109102a8141110000c012410094020048600c0c1208126603e01d4801d0900c1c2003034501035002805d184d000e0010450381d8080751a90310140400041e512201808520081c01d80c1101e038004601d01400c10045c81001e030000c000540302e21205503625602c440 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 313208246 1250 313206996 313207003
    0xc08030304020f040522051c0e0d120c050709060302040513021e061b010501060e030a05060c03070c1b17030403030c140304050d0f15020f1c02130306060806060102 72
    0x59002c0e42c4202c408042a00a003403542c061500f00380c8100c1c1d102d20700f008010926140c4070503c06c044034158086501560440c400100801559209141c03d6212194030300000c0c1400460010240500d0004601e122005000c2c2c0b200032500c582c85820385014550b03c41074400208610310040e4041d504100025004824800e6501e068641c0100f5051915501c40e81c2d15462032089802140c12031020850460000c5101d01d015400400c03107000820b540d03041c031200a0090400c900c03198020b900000b6441c00050002c030300c450340000c1c0490040d0302c1e580c80b58400ca890340752001000d4458410010300b0803500f62100c0c54001903c2d0307440040c20342890840060760f505c0c4100d11010300050481c811900014100301544c3c000c0c49415000c890410381c07030341c00264022600384809c40d80d6210540640042103814091701d40d03c00842e0504500b0014407007888005440342d0552603111259000e011403003512590706403080016041301c44010541c4929090f0001c080c2030169070703000c0c030401e03001031030543c03000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 313209496 1250 313208246 313208251
    0x6123405010822060b18041707031b0f020a09020a020c030f072705070c0b0601030207020a030b0601020106080708011e0c020a031b120e09060d02100f0e030102160c080303 75
    0x4540b510b00030b442002401520a5a0744022264103071a5800040c0076506c01e0190b00010005280c00341c0079003068907005501a10552079055190310a01070800483d030481a190070680c541001c0403080e00c1d8a14007c00050090b9500030750007001c4007000f00d010384260b80a0700340a1410f800315001c0400c4c1008241c0e568940d894084a03a9004602c01e10418440d0010320944071440d0a1100d0b0310072100c00803030706445d0207c9000e400194900212814042e680f01d10a400000a0030110b1070040340e038020601840b00e60202825408d502004210300c4d03403003580190300a14594003511421615024001d000c1d00420184003100c4403410381070a8012050700c82c105010790b464004080c10701c0c0c5a0303015601c0104030440124580444a2140040307600015030108102c03003a0f4407003209203190400c111840078007800d0f0714050008040c481d00140c0322180401c00704452428071010382040c100b0211010240303420b40036019400843d018011034038014000442d40d200f00e00c0366010544a000306503403030208 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 313210746 1250 313209496 313209511
    0x9040518010b1915030e1902090f040c03030c02010c06090302160e100519090e061008061b13030611070506160813020f0d030809100204080303061234050108 69
    0x1900401c006013441060007424503c594140403d217000082036441c1002180e420010341d44142c221540c0842c80d0148681c0d03880b007025031481080b8149500c1d0030010300c55601000301881590f0b01040b040d60b0007034440c502282d50080c02800a03210b81d103002920780140340e521040440d088100459980d100398003040c41120131000e0603140515102c1041040c0f001d03800100413a9032100c4002c0380c221840c3c00341c1c44105032100014403031400d0400044200707030324942c0300c1e1449400c113800380700085489100c421200320003041e6450715503204101110b44115203500003020949800c040d9010424543d026141d41c0e80110f00b038880301ea4805400500d500030340040480040e1032940010303041c16050791400d00b01d900103048141c0714001e180100b4002e90ba240010750100303200f036040000e03030f0f201006515100b0006079400d50804d40b40149a981d42d001c05406248601c44410410740d00354010008107076a4504085a5a10b003103035036255411210661002e00580b4130000320200d203550190110600640c013 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 313211996 1250 313210746 313210789
    0x6074b090504140609040c0e01090b030d090506070f0201030b04140f070804030206040821010b030603070504110901110a0804030308151804032706022401060c02090a0209040518010b 80
    0x101c510800c514448020402ca03050847d5410210310301d1910794065010304008180028805c0040c010580313440000b4500301e0400640605c280070f140c6030700054500c510f070b0104401e0250103482c40180e02601c1107aa126410901c1d00e40d98030941e440703241c02c0d03034056400040da0240680318030504603840f400880b0041c0c007580c03007080800c00054900c2e00410000202c05100707843c20181c8020390305184021380c00542120000b00034030060780340070b0141d0350003000126800c0040410301d410160351400703100c00042c10300030800d400c045c05807400c2c030841ea5010340c000301840d035440c4c0b28540a056003100360741d01c1d0b8240c039140d208200c0c00d003000000005041205884d4108680d1142d0b0115801d002524807144420b1040000c1d0301411990000d6101070318640e0040c0070010071003900d070f24160203111a00c003100c08503000104030362900b11000c1c030300d00d58050b51100555901c81d07441e4000385c070509e001507822600c0c00f0300b0440d6070000d80d0880380505402c03800a001010800702040603c0c06441c141520590 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 313213246 1250 313211996 313212001
    0x908040b030c070203060127090b0c0705010e0f0a1403090d140a051507020d0e09010504090507080322080a200118030c06030b010206074b09050414 65
    0x80c158000346600000b60741c0c01d28603003140783d804039042683c00c0c2d112502c1c8a1a030121807c00300225004d18040e01076000c01003001c040740b5141d00403041d101500c40d0b035200341d0002e05141031081c00c0d0420401c2c03802010031111001a02c480e100d65400c850007054a500c0c48000c0e401882038804011641c14080003844c1d00000c0c83c0607291110290030b40f0b103980701584079003a1241d00056042c060460002c00c40c0030a00c10703500d05400c01a04210900c400a01007000000d01444035070b80f0741081034150303a400d4a0000d10384800d850031a103014455003040461748808180c90b810841c81241210007202d0000c0806507060b51421007550380c1100500040c08034000000c280e803495407052481c0c240200506d4a807040c8040381c1010038480c03250b504141c3e19141900b40034080c1ea60140a01181031400380300405051030140360082c440f00c80000441141c0c0f5212214125100c0001e14000c889501c40c03503460803110b0506004c2c800503030401d50441c04200e001c05c000070742d4a014422a1249040b0002c1e103140c0e50b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 313214496 1250 313213246 313213259
    0x51c0f0308060612160f090503070e070203040807150906030b09040201032a0c060b010c0203030d1505060a020c01030f0612110a0b070b1506030402421c090804 70
    0x840010212500440140254130b8103d00f00c0c91640e004110899020805c25040c41006151a40c2e41c01d8080611114135010800e580b030000340081142c140ba00180c0180c0c60720b04c0124210b22030765001744400d04c1502800320b030340c504031000140036207040e1f215030110320f036035410541c10346145000781c80e480a0b07000001009540241c01581d84c001c1d01481d600d00f524030802c1c251140071444950400080c1c0c02d550b04c40d0800109210f00401d1304800d00704000c01800c107a0000e641c070b10680c81ca0a001e240c503080728100d8801030503c0c040107001c004008549a0000b00002503496158252660002e07040ca9804070800300b2500c90201a140030040200200d02c0d541c643c07451005c0715111140d001441a0000a00c50784100c0117842e405110f20440170756818241e00714100c1880207480c0c1841b07424200240401070b51610200607407512001007e181c007802d03812a1100c00100341c403c140300c4c3d9050610081c0c840910600824052101e81d00e10f6001c440311441c483d045414814004207280810041840354 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 313215746 1250 313214496 313214507
    0x80f12030c16020603071218050d0f09080d2d020c1005040e01031a07020601082a0a082503020d02090402060d06080604060e011506030b120a0b01051c0f03 68
    0x1151440b1200400c40c2c203a5501090590b071045580b1000144410b01d600d0211040c0e000d14404644204500000c0c0d540c283c4525841d0f1680702805400d01c0b481c240c40503080750240c0317203580040c806101640d6142014220240c44040c407040d00b0845121928008001180c1504500500481d60381c000c04d10114004107004244220ba0b21090600c0030a010019603035150071403103030180d44913a0724030450003074802c0007880b800c80240540013550030580040c444140001030b5146101c1802128003840d90307640e1140701c0b260950343d040542021001e4070126881000144010b40780341a40688003500d00080c0704816070131440e0000a62103d60a4540009407601c812100e4100e40000d0013189445104030140c01145c2c11603000b04150f810a004000070712209100340310ba0a092080203211040314660510401e000d107000c0c10f01456602c030103035500c60301c0301c8803c4210602c02d0822a03040c07412605001c40c08003002d1180510074000b805010100304c80701014088845e030f01c0b141807142c040b585c2c1e605494 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 313216996 1250 313215746 313215757
    0xd05090a11090a09060e1b180723030f090c0a06020316080909090d03060f180c030b100302030115050a1218080d1406060415050f0d060f080f12030c 65
    0x94541c5405001d03020520314825140c504810310001c2602a55407021f11414040e401c0b09103114803420348008103421910a8040d600c00d203075150011507144d651500c03046150b0031480282d01800007000304005011403071091405807102038100e80c80718090000704413004005002e1540141c2090140341c181403941c4528a141c079100341c80b560700b8031000c0f90200361501d5080390400002e42c0464024145e03150140b1503100508101401d0344219824030009030100d54280302c1d080306050b51005089015032196100d070500302801042e10124a200d0f280040180d0000e005000d204e81806555140e5039014100f1500031001d2501d540c102c8000c4900d554004180808400046607186001d40c0c000030484402881a0107484074000791100c541c2c00000c007030b0100280468019101048203001c020410300c1d469440401501e4000c1da210108501141d103030050741d008076122402c0110201c1c2280080038081c1c183c1d034041e4100c50319051212001542d809036020f1506d00300e0010004141c240994800502 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 313218246 1250 313216996 313217011
    0x3090409151112070504050a18110324040903080f07021f290609060a02070902040b0903210702040513020a0b0405030709110a0f090b0408030d05090a1109 68
    0x581c540d6450070a9080d14500c0c1c40c90748600c1070016201103600b05400f041500140c1d1480c00c142002d0800c0007046201c4031900841c040b605110b120329040400c207030082c06200b001941034a840e814411603840940214606800d051021813100c40d11a091600c2000090f03605591520010740b5044034840c0d2103100030309080e045000d0341c0000030006800700d00d04240a010b0600c0000d002810072042440c0111610030b0100c4a03207020504040703684c800080d07403a140310403036000b6500c3d128036209901c0d29541d940140000c0b80045400030b000885640513004000d4103400340d48901621800024402616042d0b14004010030b01c400c2026041130380c040c030750010904c82403001464041d000120324040c03580c403000107071070000350a10031414188a104d00074011050f0600194030500380c50440c500030070090f0010804807a0a015080780b260100c10b0042404230303442c0c0e54840c0c8454883c0d44a5001c034054124240c144001709a5001000036402d00d250341143d46c014203204071108021810b03a0151191 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 313219496 1250 313218246 313218263
    0x80303150d02180408090a0512070e0a141303110d0516020d02030a0609050d090f1e050a0e070201060b0c0d0c05010b1801031a010315020a180b09090a060803090409 72
    0x18007400620303c10a5000b54001c0c0c00540c2c03034560600800c80800b031140c2101c1d001d10905c401c40d44c460500000d1400944210054082090785c403041c2070001020114103203450302e4180c2b400c1c068280b10709040000c1c160300980d0b038094a03403079044c01251b0b01c01e1038009080000300200951080c64035008002c2d01b0f240d1005048503202000c0b9000245881d46814043d514641c0e130354880001c020003000101d0107420141000f4441d01c1c80c241e14424803103103a00c501e42006c51000c086142a0010860810203840020f05100003181c03213114611143c08221511800b542c41d1190106417000058241d0f000607910b44001d280120540e80c0803a00d9031b2110000b11010364961204544554400da600d038010141c502c10b5407101d40c07643c24a00c0d0508040c8140759821644000144085540d8424008034545c5800015070345c1c01d1406022219210310082c0102c0d18004002c01284004180000b080d001c03008035082001ca49a0100b847d044481c0751041c24019030040190919508181c0c00c01c1e1400740c080d9845 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 313220746 1250 313219496 313219519
    0xb06041509030209070519020c030c06030402120316030e0103020304020a051c08040b07060b040b09040b0709030c2301030614100504090608010c020f0a11010e061c02040906080303150d02 82
    0x2250310030400352101404104003160480d07e403801582c1008001c00b461004110082c54040400e494402c1100440d0040c640000050150b4803051114120010720104885e982d07008482034181729180e0010440005002d10100e0271203611074025240031f00c0c1c0003445407035107a184c2002c01121094000d9415110902e404041020507400d4000c1d0000313204541d0325a56034800ea180c100e0849141c0000701e031050346000917510854450010f0b159001d5440940a009500c40040a60f600c0b8030700d5200802800d600d6801141641e0507101c3d5801030b0151540c0301540781c0c16000150241e52240c01540c65515000070300090030726144101d0031801c4100d0070080c1c9015252400c05c000e455858100d421160346070300c4035450740f56041051010740c0501c440a00840c806030b607070740e20784111000402070400c10111061807903540d070107044641031000d40c111103c4091034005582c020390010701c42d01c24041c0c0ba1280009143c00048100c81c411022126002c0e103281d8900d007002160a150310007039070015045800c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 313221996 1250 313220746 313220749
    0xe07081305010e1b1c0b011202060c160302041116031821051e030711040f0c020f070906081906020f030c040f05061c0f0213060509040c030b060415090302 68
    0x30b401520030700304030701c20404c00101881075402c1c00c400f40750141e1080003950b601161407200444d043d1041d080441d6039012384d0340001401801100540c1300f0f14045d000c01c1c3c1c104003030215040ca0131203100b0745060060380140840b01c1c9a501504c001e040202d04040203210010b8410680c0451204101c20740d8003140d0346944090401000041c2c1a141c07070380841809905220741005840d1000094810b8028290b0789503100742e45901888a0040951803003130030308070455407107810003100e4095012003000310008a60000795180c4450b28400800c0c0607600c00420305456a010f080183c401000090080300c4c0d96082c10146c0f4820341d0400d45500e46d09000b80d050300710207040218000e4500c8a0b841f600e83e420600d2602c51008170341d1003a88610800c02814110544408054544100c030100024910482c08115400382c07150710804a40058480c6001c01c5003904400079044c0d400043e942000075440f40c003415400c40d0104040140c1c49801440108914408076003074030380007001032405d0760300c5030759070390 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 313223246 1250 313221996 313222003
    0xd0e0103110c0a060b031f110403020603250f050a080903040e0117070501030213140d060c030608060a0501050a05102606010e01020a02130b190603020c070e07081305010e 75
    0x7030900100c2d08002d43c0941030121500841108440841c0640080e042c1c014402c00703118030101d2006806612206000c00d024514000d8030011078005e0202c560324500083c00c5051040c0a500905200b02168a9095103034400c283c00c0c0c601450544640e482c3c10640c050580790350f08001e01c0201113101c2040302103103a8405041880c000c04100b414500b410b885040042d00b81209a006181010f02c1404034005820074211000100c07120020000303e11341800c80411010407a484010301594240404404403d40c964800380031a00c0c80415100300b510b44201c5042036039800e21510340d100103142c10620491411068000c1158014288100b00040c4007281c5003560079400460502e16000504010107942c10090701c1394050380034805003071f212030a640062081e40f8041c0340c00c44401d40c2d03010300000e60707116468007400f2780e4a41417014800d150346440042c065484030340c01403024000e420001814514035080540198055150948503a8868030f200030903460403201610343d5900d0710104c080489090 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 313224496 1250 313223246 313223257
    0x120b0604090f0c0906021504030f020a0204090b06040c03050609040605130b070f090608040b0712020d060f0306060f0e060402033403290d0f1502030421020d0e010311 73
    0x10000401d05140f100b00c05849a02c40354440320a41d00701c03604810a030840303004820761041d0305061000405030f009000303c0c034009480340c0c02508240350052020512a00e90a100c4c070814085405001000e000c24088065800907202c06810018136400706000a0580e00982e903c0b0301617000311030f010280d075118030070012002e540b000c000c9014072640d510041d0b48510f001b00a00444e0805c1c9045090039503070811505001060782041180291206620303621a4040310201030f40b5034410300100340c9445180c0c0000d0040d10045a106d4642000082d0503580d510002c002c840da81c2030041c001341e580724180b06c041d6000800c060350a502c003226010a10004501d044110003030681148000d4503207a40140c100c2d050500a42e45030003071542d00344020515001400c41c4110103540b030b010340280340d1506041034020100018100382c84070403071000006603a40a14802c0b80501d60340e41b85201031422088081c0c03403e642c5800140c003c9000415004d001c2e240c0326001c4030042c500010101400440c080085e00708 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 313225746 1250 313224496 313224521
    0x30a0203040c0e0c0307140c01020a090e0612070b030601091805092a0d0c17060907150f031e0c020f150c07030c0302030c030d020c100b01120b060409 66
    0x31041c8028000940c0c00b02c0098000129a080790381840c1d11040d070180030003040d040810a000101c8030b420a441d1058500e080c44c880001d544404038440701070000c1915000b00c032003542c01c05000403030914004c0c505040c078807002009000c1003420512880c0b080c0e80024a864188070300b250001450480403003034009441090100040c607030800c51429410070303100810480030060f100036140c5195050f200200e4108000321080401c3c1a010310741a1040c3c1440c0d4895020103c200420046554003c10050303c0342601c4010b4524540d261440090f0010800261360001100d4040c1d14409501070752040032060010041d4071900c100c072038a042c0c00e50301c03d0804d00f1b0040e0020f505495103510b040004414085c440c15500c1440d00d415104401d0b180556407002e82089140c2c500030003418001c3c000c5074940d0030807005990740c03644400e41c90b070040c2d400310703000495520a400c44c81c0641881480390181c80381c07050796825458103024000e800544480003026501400030000000c0d400f415100d440d114824 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 313226996 1250 313225746 313225751
    0x180f09090b1305031c0e030a020106030201110102030f0f1503060411010306050609150a050c06130201080a0213090b1527010504180c0e030a030801080c030a1509020114030a 76
    0x8186840524101d02810032010341c00c2c01c940c940c1c0040d034048103070f0768003060b40001d444c005140000803001a0850341c02ca03135691301000a105c56440ea064210100f568000c0c0c07500394a810000712428200d110450b002c001141c0e00e88040352418451005080e0410902030304100b42100040001e0b040c0030341518125040111102c5021041d41c0500401004100032950381d41030054500c0880e0b142d02c650003c1c8040c030034002032082d0340c190095054456200342c620403a00c0318503080801000042d02d480050780460080000101482d819008a411060004d8100c018403850002d0040c007070b00142220b039a010f0b09403161004c14a05600181c840c030501c0c168400f10102071070720b80c44040f19118502a04100c8100814482c07440210309040031450b100708000384118800c0b400f20303650640d81015070b83c103010305045c0d0001d25900205a5050b618901c1c107441d0780141050401d6039400c00540b00a00341c0321121095a2101900c0e440324440d50300605105058a00030032101070740754000c5070040ca01b9503 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 313228246 1250 313226996 313227011
    0x61312210f140c0a021207170a210204150e030708030c010f0b0a06021f02090616060c020d0212030c090406031a01140d08130306150e100506040303180f09 68
    0x101e100c5090b000024411070ba0320300822001c0081d02e130341101341b2a03034070301c2c0b4005082d1041100d90703000d013a2450b03002c29665407207224016005101a81c01c1c0504441d407101e0510a000600d030920031134003194040781801e01c292199210030b544030707484000b260341d25009840c0000740701d11091000b0044507990000000e20050315161a004940000310a94001c0c031101e0340521046800080040c402c45081411441c4906641c00d07a5001c1e12503828003680012011a1117044d00c041e0300518444244101c00600a038850740310100e03501c0022501800050b40822500307040521170b4070045400c142000207030351410b1200307001300b400d6807410341c021030380e1504510b1002c901d040c50103901405803081c0e98940440e12020400a401c40800601c06441001c000502903014402500000000c6502180070301020f2080310302c0a001c80c0c030600c2242c0e08a48003800140140d2a032160b034400707440008025901749400c5031002c4620800d00120021001c0c2c103030b50042007003c8901c9906000700695a40804c001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 313229496 1250 313228246 313228271
    0x21308060f04030e091b0d140906070504170304081504150204060203091c0501050f090c04060317071b09020a090b0a0210020c0102070b04080c061312210f 68
    0x49005120500701200d400a000c00079600440c0d04020b03a904403101882c0c1d841e424059224203031001c2007140402800542c220b211f01840e003080b10041c000e08031f0000166900d5006688800080301d04000060081000740150182400d180d85d440c0c1040c02224140360700ea60125203080c0c050030802c1102009802000300300800754080d8500b80030a4942541028682280655213002d00c1c0000c910039650f00c1c440c8114400070018050007150000001e210350f0a141c4104000103405907100302090040e0500c0b01e40504203402003004580c0c0c0400d656036071288120120800b6044108c2c11038642c1c81c020780d407840c5107115404610250082d05e900681d601081d03000030380701c20401e030300c80000d184040c002e48161540100e682c85084844607000759aa0441e90f203043d009104003000200114000000c0c0300c02d0003200405005940102d504541c21516105200f07404200d03c154021300581040c90b00e2401a44038406041c905a030b5440104502040c03042c201027a00c0d186240100784680d40c1d9408901d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 313230746 1250 313229496 313229503
    0xc03030519110403120207060f0e12060f01150903020d140a05030f0904060501031112070504050d061e0629040302090414070608090a031805040c11071a19020c0301021308 75
    0x1726041400102012032421001520044418000c40d060060030713441c49060b500c928507000c242c00035103000e44880e0710304640180c50342c880078011510207001c0f0340244221980524080ca080d01d40042c14420b404a10742c1d00c0309580d0a2004d0304403284c1c01902e00c5200094820400760416080000c0070540350038101c02803004541860703001c0b138101400c000051400350008012141c110f9602c001a00759030ba9404400c0d20188160380c81103800201005402c03041c840740d6030049501c5a110741086d401000b90301d003450b059843c180108941107109002e180c0019070a8005001c6966602c02d039181000da4940003d2050302c800c0341d0a07909280c54118480d40240f081c0000c4000d4851400d142600b8200300e6062982c1d040701000c0201400409901c0040d11359126295100500008100b032041d2000c85074018009007120101160a1246081c0828503000701e1600d1000306180100041c00c01364240c0341011200141400d8105602400301d101c1001d403020300041405519500d1004101031401031a9880e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 313231996 1250 313230746 313230773
    0x403050604030f17100632221a0706060504110d050709150c0203070f03081b0d050d020a0309060e010b120307051509030d02071b060c02010c03030519110403 69
    0x4040201c401c104240d80c00445d8041500d000d440d00c41d142e150002082c060040d5101443d00c4900355000d001104d500c1c20380c004041a0712200a00c0c2d125624400c8130000c00c0c240c50080b010259544044c4807084141d010290018a01480d000300b601079480000c1400c94042800344111000001035170184411a4012540c02c2402e40c580564041e181c115100c14440311104982e0800000420000555a040117a0740c007801003800d048070f034640d80e03103001821648a00c1100f5134284521207859505000440c28125600c0141ca601d494040c0c0702c203a003030086d40b01410b01814580d43e0a01c01740494014400c01929555a0000185030402402040881480c07002e2000c00b6500800480002a00114035448145c600340e04520042d00d40058044c00c0d801124110300d140e41c408101d80b408e10000540400401c80082d804442164a07548201d03206090403901134041246402004002442940032560180382640c58220174502c0c100c058083d1000080d2000322000041018024028114080340 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 313233246 1250 313231996 313232027
    0xb0d0207020111030a020a080c0705041b020d0c1a3114010603030c0807021c0b0708060a12170c010603050102041e12060e03120405010c08090304060905060f0403050604030f 76
    0x1420117401c11802551040c0c480802000c90801146c05500b5003401c010140140c18003c0003405507141204c1880e040c007481d6010800140f0440413070700000c6000d070102050141d0442180000200e1140000c20311f91800b030f210a880c0b01015101000408142d402c00140743c2c031403650550100a5420f00350419000d0750000989a407418004200182c0c01c081d000c0c281c40e034407502c4551104014000201d811680c0030014100c070a1301c9890404006114003450702c14040e90315a6900f680b111800d204044c01c8034003038070007071144503041f030000b2038030302c4100c240760100e4008402e1502469007640d0f401d54090fa401219280e4000c03030144503000d01200d4190710340d110f0042e8400201c1c90080c403a01081c0b00f115001c1d110030354403000001101018001c455413140d00702440005420300c2e1801c070703000380800b401c00000079044070045890001c01000321030896070207644205a05081c40200300c000d44c080c0c800c0d80201c03c4100000000500705129041c4a207001e605d400184210004000e01852310404205 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 313234496 1250 313233246 313233253
    0x606030c021b040204080102071511160f050c060a02010f050105060a1e1407080a12050c0d0c02030405090915090706050f0702061b0d1119030f05040b0d0207020111 72
    0x1154640e60009100c0800a526030310b424180324141e010034028480c580000c81a9400000d10109011700e6100f13401a0341d051801c200201c0740071f025285010701601c0b400115200a000c08440410752909842e5020350151050340c01840040e4000f80c0b541e408204088050313511124600503c060303074842c06005081c00d442c000d24120710810700511840084c0e09d040f04541e00051007900840c4100000a01e41c00c010300103d58a084d00e0078120440d40110620710000b80b1320a000c40610092400344600500024030042d0910404941e208050480e004003001148003d00001489603076070144940a00d1310600a05100d07602e110100741d00e900001c02032106680425020040207520000301d445030795180344055101c1ca132034400078015201e025812020184011200e051a00000c0341c44000b440050302c5a2005020340210f80d038882c00c03104200304010b441100403001103409641d0f590b00700c14903458001c1c6803544a000c400300320742017000425215580801e000c2c04558001041003085c7c5a1003005 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 313235746 1250 313234496 313234511
    0x30b040612080304031413080312240f0414130507050a1a0306010309080a0e1c0f1e050d0c0b0c070b2a0a030b0f1f08040c0504050c0d060603 62
    0x2080c0c40d92101920003010000c600359910201b501a40030b0702d1480d03070351903950410300350b03100d80d41ca960307070001545500c2c030401303120204002c4000b40c04842d2040c10501c540e000722020310000c00c61748098441c003881e0003988a0551203095004000d00070f200e40c2e61203100c21848809801c00724a04003844c0c0002e03010f0b20b8001020301075000c0040c850f580c009481c4010655039511100120050f02e60444020030074039011888a803425007041c2c1c50a000c4205407101840d010320008141d00e0721000881c080c0480500008050200b100003814085021404015213002413440c1c1c0c80528164851b41c045000600003180c100030807845522547e00194944040c60a000040e01c070710f515014060000c136040014110900e0015800f143c00f400600503540300c1c5034a0307050f00803016001e0700d00e14461510a0f40540603031081ca1a041000d40700d000e16500c0c001e04500048001560403030409001503d0280c9a04000181a5141c0c028123208142c20a4041d858060110710748017610100c0c0c014001b41030401c0740 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 313236996 1250 313235746 313235753
    0xf0209031504020f0901090e1605010504030311070f030803091c121a0910061b0804031214190f02061506131d070f03020705070303050d140106030b040612 68
    0x2680c0158407aa01c0000540d03488600c0001e46055944000a8100040c0c03000050380030302d29486030100311010703004d07150100381d56040b404131040c0c42c1c081c190118500340000c2c07000c42d01c0f600001104202d003404a50520342c0303480328600d02c0c8000f64421164100d002017008401403040c00020a007200c0825998100e0480490150084010700b80201e100740c3d9804500b00c4c6510b1480c515408900c02400540f05400c003120710b9951000c03103000da00040340341c4801d0ba142c1c85041d09411102c1c103400101c05c0d814203040d0341c0ea502c18103183e6080c1d1810065500d8098403c00d51402c0200100782c195090f00c50494070034a8050034070000300c207050702550018000c20400b03030702d26050711000316070854510703907501208050910100e045401c1034031881042d514800000110701801c034051101e98442e000030000d0242d08600342c1c402c40c50000d10355000a50108000b80c0210042e02c1003200c0907601140254020783c4910b0041001d90110002944880f1000340c0d9003814403c29001d04030a0b000c40002920790b45 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 313238246 1250 313236996 313237003
    0x114030f07180207050307020d08030105010e01081608090a08040b120f0609041e0812070801050904081603140c0d030e0312040f08090915030115230609060417010f020903 75
    0x5154000b055000070f114400c0000500461702440d60050148900035618107201c2801d400901615001c1445030380c0c212103c0d030044e42924455890307031920310a07025549500f02c40480000e46000d46510903959001c0005480001a02c042d0003000880364490321030301402c000d1030324058800c1d11101d06000074006141c4600744110707402600907591450a0b24083e030b503418126001d20004c1c044490118900600e450407004d01c0d40590340907941d40940b66201c2c42000341e44c003400c0d5070083c00c03403204201804413100503050321b0180902034180342000302403188811180e580710428203946c1d80c0028807620f41080c4c241c483d152000501300300031400c0c000310700c28103000700f40042c2000d44002c4410800301c003042000000c98408601c0a0070142d100d04000140c040304603284001c0503c6942464000c1c19503601e200700c4070080341e0b002120091542c180440904d200b0182d0590290805801c0104a407075459540003003004041015400750820300540c8030070700311b0f03090410f21001240104100700b040e58002 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 313239496 1250 313238246 313238279
    0x70e12030a0c0510090c09050c0a0c060c05040321180602210904090515071707050a0c0503031603140105010e130f0f0203040b0604050108060a0c14030114030f07 71
    0x500b051038420750181051498450030801002c2c0f21810403040b40100048040110b003214039451041c841130b01e9121002000f4040c4118090000703400301c4090010840640020304120503a0902e5443c082d12521800c18417042e1440c9045440c210740d541e039007250f41c00002203920f000c120100c400380a04154000b522070301200c010700843c84401401507855412502100c14018006204100028080c03600036117850711907804148150b04d00c030010301e40e11700034280b0030143c850f0720300c62008a0f07645031801d84682e00540014810003500c1009a000134200b00001e6020b107000510040c0c000c030398520b008041c0c81100d03d04000380c0112400410071640c02c0b2000103940c503012650700c40501203001b6a04001c08038141d80313002c90703805c15a807091180e45c643d00840c05140500d0905549035154014001030b00d01c00c0c400e141c03941d07201400003041c0405503840b02451400c24509032032810798801702c0c02c0d03554100307030004080a42055000c200784d20703040000d61204107a100140080500d00541c690300c8a002c07 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 313240746 1250 313239496 313239517
    0x5010504171c0201050103020109060c02090105040f02221e0308040e180d030f0b0303070201080a0e0c0909060108070e0c0301050d02010309120c1115090f1c03020303070e1203 77
    0x2005001200942881501110820000b1200c689410010b00901070034082c442680820401c0c640420b60a2244400d00340301600070b0041855a4a04800c0c0700003010b8901818074525400c1c8440c0100070504407041c000c0007032440740b40d0049130400b1150042084031001072004580d21450400000e51075409440131900781e0349055182d650b078210398009030b107041642802c00380100e1030900316294041e800859000c04500d000c00c41459600103060366032003026006400b00b9142c60005142d0a07450704041280400402580c1c044000b0f04040b4482c488165500e5034290030420041c46062400c00054008005400e8000d1450400e074810740303a51320041c0501801160102c12883c00d6900a8000320b0302140e01c0744403110014141c03c070040840b520803d045408003681156218540f405030031503503a0f2104041c0d441c0c58180740000b0410006403584510740c200705500794140200005c3c80c00c40310414081d4000d55030300d2500f1480100308601c60307069203119560207240031030341000010988064005 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 313241996 1250 313240746 313240769
    0x10060c0f0f0c08030301030c0906120b13080f0711090c16030c0218090c040605010809030a03090c0b2107020616030f0b091501031532090c0c06070905010504 69
    0x500b000100d400741a0021956803000200000030000a500400111024590f00308005512403400510a500e1040080c145100701c82c00319004114940002d5103240c81030407480c0c036114100748200c1701c540048400380d0f8892410658115203081090003da40301c01d03403101040c074050000c102c240308200240d401a04106c6c0c0e444000d0110f440f0707055805c54070700e070035101c4540b00c0c9841c102d5240e070360029241c101d00642c144680002c1950040b8100c0e030080e00a00043c50420080c5601100103054614041e100680040c00c00101c1c01c1e41cbc140200003c40703003103501202d000d004000304081020b01401103011588181c04220041d02c40401c400c58130281480c2c0482d80501c250340800142c51503401c000c1c4c0c40078080050041040d118080342c070500ca8280c83c107110340d1758041e42c0142c210707072541318606681c0d02411480b045121007001c500116152a4210006031261a02113003c0410841c0e1002e804403000074030200164040019503444101441c020403030701d00300400200207000314429801d5810 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 313243246 1250 313241996 313242023
    0xd0507110613031e2003150f070507020607020612040c1d041e060c05030106090609050d0201030b010c080f0310050d050c01181e060801060216290c0610060c0f 70
    0x1c44001c110f010a60000d50108400c0107010501c2e50f8601d2425491b0b109108511018910783d8403003462074850450b00720108019511a20182d555900c21002280e100b40704010030001a034035800500040107004085102a14140c5882602d00b4000d80240c030100400381805d003610461650355640c019845100240b949020b040e001d96540b81a030340041900b0b0820803180911075108010350b049444640d03c41103801c0e130b41d8005403902201e60180c2d5800100c00f138815030243d40290030201c0700e80f506161100604683d504c0b043d650360404a02130080500000a101c041d00034400890701038030048401d4419611a5a40c29507210070480780c8078180a1015094045c0c09405160701e40108174440c6030142c0030380c3d800c02985c0780c0262070060f0030100307035240c0022400510000d0a41c900780c81c9007482c00709113410704c2c040340e0b48510340219410380410406e905160107951000644515922200180083d04141c12004e0750b11080b40c20003810811106000e07000300d0343e095802e215190f0461540704609 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 313244496 1250 313243246 313243283
    0x702011b06020c010b030c06043516030204060509060d03030e0f0a030302213706060509040b09060f060315042906030f270d050711061303 61
    0x246204000500600d201107005500f9038410f400c00309501d0411026501940349040c2080f6180c0554080d0840032005003500c582103040803000c4004a0407888100081040d88481041c6000042c062008010012207810411820a4015807001d014111000c0001e8500300340460740c0c027100cc6001404040d1119881102100c0c103020410b000380d0750b072044e0f5501200c4d40c00c4c013030041e60049a172580007130000200d03000d520703082c00c2880340508007103a0491001c0c40c0007a03140c0c0442c0e2109440300c0a41c840400c01d030529014910500e40200010b85800e40ca844005003004115400070a06900884605040112300c1d0340b480c0389c90703107110001c40d100b50b201d03154903420408414003098440e401074500119070040071000484803034202d030341c10654100d16140d0024003225010030f5502c032209c2c203070041c00710710079031a040e8004095400302114452025185104c0310f26182c1c1d4180480b02141001502d070341440401865484c0d60070055078801d08c4e190050b2001b010701c0d003d51001030300c40710400e039220402 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 313245746 1250 313244496 313244537
    0x41a0703060317130e130201080a05010503060c1b0601030b06033d0b030d0e100c510605040213050d020604270c0c0201122706060812040b070201 64
    0x10b0700c0c840317000c10b00c1e500d019510481c4051031000180e000ca44000c000858070400d40c01814142c4402501030500307500d130b00090300195040008150600d156150310b11074030b1384040003014025805401e400d806401d00b1070503d400c000028507884102c4458144001c100d192140c0000d010b110781c0a040040092030448840c02401401c01d000d5040c004e9807500d0f044164025071041310320b0000c03280c0f40074032104010f00303483d01c10382200001e00390120241e4480329802d4080c10342001d18085668414044111101d00721030304000140440b500c40711070002c0c10480c0240c8911005007006540842c6816120000614176440f0780c81803a21825000122400315110340f0700380d0b00240300780e42618850b8031940d050b050560403203188424080d40341c04905d40c1800d210700708680f225901a1031340040008001c1e03944001d0300140c8545500c40c0140c001900c50010200c081d1004580641f07000240581803020481c2032112807460104400070502c004e0200ca1015812654241d0b0309003071501006d05a010321055 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 313246996 1250 313245746 313245749
    0xe010b0f0907140412030315030308060402090a0503011803030e010b0f0603150d0302010e010f060e0a050702031608090f090705040e06010e0d060510050901140405150405041a070306031713 83
    0xc400801301e0700040c0c62180f440040f2a03513109031401d22084215800184e142c6c100f0348005000142c542005c10751904056000b00b14440010307284100b0551600c0c003107403d4030210302510070034a018a5a4400b130550600c1030300c030f100b50088020320000b5005400149095201d81e00307240715a0380000032401045045104411b2580302034140760325200a814003074000c01c0b0032240c0d24001e50825509250848880c0304a00a4454064007581c194407080050030040200408210540c8010017420002e2040f55640c0c50b00c00d44500007a907a143c1c0d9080510140341d0903e440b042c06480300d0014401c145030824140c80c20307180c0e0301c001039840c0d40d00d070303801222000030b6500c01c00e400181d41c9001006005858000c1c0c1d10552458015401951b507400910000d9030091080151014a44281004501d0542c01150f040b01e448051403c82007402c2000504031641075400f2910b4800f00150044c03840445a00303d6803150756401c0801c400d524644880718580303c08407200e5115400000d10118040d0801007120 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 313248246 1250 313246996 313247027
    0xc090906040917120c1201122a0518061c0c03080a030f0c080403050d02070f0c120302061f150215010611010b06160b19020309010b01030e010b0f0907 66
    0x70f500c2102c000700a080c0e5070041940d00c1441d980d031000600c1140310041200e099000720003148406a05e4800d0408140303410940450300d1100321445000248a0301c0f5580181c010400c1849030308034170703101c03c212000111180e400c0440c1441c00c10016a51765502d80d0103030312a034840311050301801d0781c5443c0f80c00016507080204801c40200d499458194180c1c06000c801403451802c07c4040e410702c0c03095550800441d03000303001031420004009010f0301c0c4c0d00030b42206d62242c010410445841e80e501ca16244c1030f508445564408200f0a90505904002041c1c1082c2510071880c80110f41d80607003002e01d546805564030f010b682803078040031607100700540641d40440a00d201c200c3e513140c1200409400c2c007910211040d60a1520380c0241d0301d0590111818a90b00c00074030742031035072113645840032004020401c488013800c0e42c1c20a000d001b01800258030451044000003418000440050226034000c0e00d80f8281c0e0f8982000d103820741d125500303018a90081182e000d80c903a40e5000302110a83c12000010 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 313249496 1250 313248246 313248263
    0xd020d082a01020909091506100909051303020d050301030f0818030f0d0f0203040803120a02040f060c0308070504150804230c0f15031306060302040c0f170c0909060409 74
    0xd110481043d070103000b0070201150b00c109103071900200d203603071040d01800d241050a0000d001c120240791904c5400d1a244190400c4d00e1300c1981c804080c000c44108540394645031721400da580040550500100d103042ea40307428030034150b50440d01d0750303225044000ca000f0001c80c00040d85e0b01c4103603204004902c0700c5900504403001e01500d800b43c1d0b81c44000c903c01c040d01007a56281441c81301030001c4150b03010785644100541c240b5500443c5000405000b070300c40e2069590802c40410300100800d0800c018000a1300d0708600d005991500400d02240102117008104090009100030310060f1130002486d00546416036442d03c03241800700d0242c6200d10700b442d0f00d050005d404032180d0ba000c251030701c036072000f12890703003248104905024200800e0082070230304d2141040003440b00f000ca9044880018016880000c240d42c8a0340030804988410501c880441c041950103001036600003060004a1041c00075480641010004070100d070041f11501172040c0348032000100c194540e680311403003140c0c005104 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 313250746 1250 313249496 313249567
    0x100903030f290307120308040c050d050f060609010609030b1e0907210b010e0411131d070602121e0714060a050603120c10290d020d08 59
    0x2101c0d4500d0341c4141044038032418a0700200b0381c5404220350084500c2e0142c2101e003108036580c2207602c402c009000b11074445c05e807040403903170744c603400380341d424080c8210000c00e1540c03002d4a14a1800030010103040c8a0517440740148046544694903100b02da074030080307002540d1140f02a440300c24100440002c01ca40b641804c00c01010000181c6004442c1c2d0904040702e068094103100030702d03c1030188054450103112004010121014102642c0140079810f0500b0141d601d40002e900c0c001002e84504045440d41c0107414240c50500c0d001655008410042801e02c1c90820065118040404242034603e0081060f9140314032245031a072614807034400150350b0304024a0b04a141c4c80a400441c401d80c07190200040d81e054140c4252401101d005005102513444030171812140e0344031400480941c01596801e84c0c01c4030560088482c1d5541900d0803c00d01d08880d0042c0035400d41060b0400d11a0703e42c0c0003100c0150700e44641201507903801c00e41550361000b60609503802038119074100100340340c54451 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 313251996 1250 313250746 313250771
    0xa02010c081b161202090f060102070e070305060405131a0907031e110111120a051207030b030c0102120f03060a05091003060f0203090c090402010e03190507080f100903030f 76
    0xc048030100c03014500c4021003a1205014a00f503200c45000071b4000c0c2d50700c0c02064080e2212114281c2c040414411159102c0d1a03210014005905883c1c0001281d21101840854030303240c01001ea01c418000e02c00704504040b901d40709541c0f5050b2035800404100c04000c500b21050602100700655001103074038101210140c030702826610180401e440c03418903400c0b59481036109030083e1602d01c0d42040140006c400d100c1c00344070f2a034021551042481000c01041039460300d0701549503ca50030710703100003070320708100c80074541040250200e032811508240f9002501c0040441036070f100d03048554000742c6a50b110350115500501d035800403a1701041d407000b00f01c0301032118031100042c3c0c0e00c01d0030240000048000200700707034041075900c403465402040403d002405c1c4100c04540c8280140742c004a40181040441d04004030301d20b04960003030003010715001f480810003820b0700030121840103080385442c034400182c480180e0210220881d40b1190038a00f41407203034001f904665500752041094010003007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 313253246 1250 313251996 313252003
    0xf060f110f0d05010b03010609031103100501080d03050a020f18030a0609120e011b0803060a0e010b09150c060106140f180301140105030d110f0a06050402010914030a02010c081b 78
    0x7440c51880b50304050000c03c0030480700b800d80e030484001c1c0d290140d0490944d44da050701d540c521124590140b0450200c114519418010300e4004d20038040075004207200504020144c5500804030403109004026604039204440e0480e030401c04601e1304a030802c1c5070100003a0400600c51005400070b0704050030a01484072100310003069100359250800118034400c015034240c42124200300c52004481d62440114001e20015a48810001c004400075515a021050002800e82200038540300214840c40c42c1e0412481c1060907403040380d9100d0801903510f03900c60365480c0500400e001c00107080b890002104103082a41d000f030700000b060ba6110241c2d05640041c0030702c01605184a50b0a001c00442044001c119041c1680e101401600a12455400513100d103e1142d0032640c0c030f48621358052030103101c00c0c0f00300d408907881104041294101400010124031064200100c3c1010315000071030580d500154541e40b40340c2c2801c02c0707108210241080074242c000d80342905500d20401074030018508012 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 313254496 1250 313253246 313253257
    0x30f0c0102060106090303080a0216060905030405040f060302060d200711100f0905010f02030405150703140412060b0f040c08010501080c0f040311060c0d031e090f060f110f 76
    0x81e800c440d510707a80d81504a07404c90315444081c01013030b075180128440800c9900188001c1510304d0450241440e03564580003120420001581c25810104023800030780303081e0283d40840c1d07100f1003090105c42d095800280540c0f00d1941301c04851941e91035021540107841e540c00c814141e541051513202c80e51428114240082118007911481c48084040700250003001e0064410701a41c4e9050515424040151a00c02c580344c90001944810302c40050107030f07a44840100c44084800307031552030302038500e0003910410380e26001403034001042c003040c00b194810792803c040264001101240c1e00e031003c80491a85a0900784494006060a4012050715041b51085040740c80a0782e030001c856403480070488160041c0c0d4440d64500c0001c0104001003038520b064031034021801020b080c81c0c40b0001c0000b074940f094402c0608086900c40a01c1c40c904912a2003610001060803c1400b103d50140e440b0b8410081c5a18010328540d0b4415114400b4400313584070900404810074050350718140324100c0c90103a0003a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 313255746 1250 313254496 313254499
    0xc180f010c2018070806010f021c170a06120b060604050409140d0513270c020706020c04050c03010605130506030901090b130503031801020f0403030309060c1805041505030f0c 77
    0x10703c510300000650280382d90744034010301e507100c0c01c06031540380c011624425190035440c214441c00840c0e204050b04030b426003105461a85520340d00c040ac3d00320703444880c000140a0512240307880da08101d11041c60040761103140c0c1c071100c142582d565120004406004640046401c41d190003901c10401024800075411004184200c4e8030040480b503080380d80b44507144030100d076003010440c00c000000b180492240c050242c40901c420f543c42808840003110a01e01081d4016030100c1e00c10000c42d030301488030303031041c0070306039800d002c2441c2641c4821080d20041c4101010440002007502c100c3c51044107001c0980b0740103000640d203007014a003590180c60001e4060324108020380204941d244510b10081c030040c2d212000d113083d0798480340076645404c00502403000c255000c1108035540409078004001440c480e440001e002149070800004984988910301c1c24412280c0043c0320243e90300f081c520807180304075004a10a04003035030800114100c0c0d4003540d00761090140141003010302091200c0074460 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 313256996 1250 313255746 313255759
    0x2103030f090f011103010806100b19020f0a0f2604170a050607080121020d02090402120f0d0305070e031c0302130b031803031e0a06030b040b040b0c180f010c20 70
    0x40340503c410708513030940b003009101c510420215208a08072f04048c18104003e0050341c144240d8000c0306410a0f11420b03040f103426103854070001c1081910003503824290030150038940441441c213016102e0703103d14041c1400d801002403600403034440c10044901c203940d00c14240c4002e4100fa00b4007401c8450280142e8884a00e030003103894264080302142c880e01d0360001e01c00541143c941c2c0074032800c1c08001d801603030824562080d40d0b10005081000b20311640082004040f40c07507618000030308803103002d000042005807a5108a6031560b000800000740403c44100c035200c005904c00680007441005010351131246160340002c0c2d1060381a0246110741d44021410036007064032800c803508c91008840b54901d60041ca100078405001200030298480d00440001841680300d445440240c84101c400b1106c0328045000c010800c00328103500e80d00700c4000d070384941c1040c2464500707000d01e0450013a620b000744040710b00b103049a0301c03a0b11041103164110800402c1c400c0645500251844141c819034002d04 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 313258246 1250 313256996 313257001
    0x1b06030c0e030309040b01030b06040303090801110c0a021302130609170a1e050a061815380a0305030a0e0f0604030f020f090903092103030f090f011103010806 70
    0xd0207103052882505000340903602d0210408100402404400c064504050b5907082d02103190301c64400a0014501a031580010f55150801141c20f40d0500450050111340c10300c06481094000904580c500b641102e001c03901c0d491004090000340198001205200904840000d003a07400c08106000c2d5040000f0307184071901c02c3c1c0c0c0d80b43d0341c502c0c090300000e00c0000000d006090104654800d004668030075010764003090690b40b078600694005101401324001c202140604103d043c1c440c20080703808010701400035401d04000d1011452160001180d0701c25503084040070300b14407007404120030400030320a00c805500d9017800e517500e8218403901c1303021901240a0200074940504002640d80b0010200703441c00307055a503400d2400e40305103022604085004451044c83d0b440f030151a01c902a0300004586403203943e0208008072104100381c0d612411b2080103c5c1d08110048100c0303611100044506820351588541e00d460070f61481407004c4075510f0702c0b40c005c5405807220000c40c100c60322003084a001382c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 313259496 1250 313258246 313258271
    0x60c0507050d080a0f05040f141c0c0b0a05090901170d14031303020f0105180706051603030c0c080c0102130e061f090e04050601260c0f06071b0603 65
    0x1509854006000c00c0e00034030013400f074107100741402c0c80d004642c0e2401c0c03030510f9035441c0740394885031150304000301800c400524000320307041190048801405121801c0741d5203000341c84203040c0700b01901540b10030380400500303d00300340d004200b1200000e401802440c42580c0d240c40041006d003080e9081c01c054000d5481d070401e40d80c803d072401118543c105503c240786480b00000803d43e0a070243c0218290f009800780d5000102c405e200d120312800d020840c24018540f841e220764200b6105070040000c1c0001480076080c008000d09032411842d606080005211007481c0007a1980c03410580014818031000030315050907201074025021f01c0c1c82d00910301d1112920b50410071114601190f4803038021101c0007400d613425081204540302801d050030080856600c95034107802c51803080b0703415070342a804007004120b41101c6055640403c2c50f01d03561200c40881810703400e41c68181220409100d60041c40c0c243c0c4070ba603030b00011a552940d01801800b07089240d0003459107200118030454000c44c0c41c1090040b0320 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 313260746 1250 313259496 313259509
    0x30d0b06040621090b0f0106120c0c060504020609090108010207021009060c06050a15060302040e0708040206030f2203030504060c050903030706021305192c0f04170301060c050705 79
    0x64580e0b035180e1604620004280c10200b941100c00f0b85a2151149603880114460b02c04590082d1070004940300a5810000c010b0306103141041301005052070241039147d00d03640184245074156104070b0104131a182da00002d19280070b2540c8903517020014400005a411056004045081c0700b0303654405184103828050f0341030b11262081074080740340324940000184040e4032050344042540030001c2d8050145483c041c0c540510b40012010980c00035081c00700c0225011200e0303101f07015103082c0d0350a00e00755022802074080603001403058060b400104c0c00680144010102c0e00601d02c2c0c9604081089040082c09844241e5042d10024a06500200c10a1080301110303071509018005600d001c0ba19a941780c000c0d40902e00408003034004400104043e5510081c0002c03101c04d42c82041005420450305084107080305220440c40700103030404580c01442c1891041d40b2074a4013010f0187c55031a810702d0000e401c413240c02d000d08101c00100115a843d00000140301e454080c0088038000c42e1144140001c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 313261996 1250 313260746 313260749
    0x715021f0c090504020d060f0f051503070c1b0803070f063605010b091602060a0903090303030b19030c170604050318010504030b0f0105150a080a051f08030d0b0604 72
    0x9540031024051404c0c260000c0004c480c0500001450300d40d10710040f14006051703049006450745464040015151200116581800b140800b51039420105000b41440b103100d8001806030a064541007514100c1c0d03050b031001049408141c90350384070346107031501074031514200445400d0324100c200501520724a004da440c200a0b025100c103c0d091070001d501d4040802803049070199210540e40c001ca4550483c428001c00b215007850184c0c4040c90000381c1000300051031400c0c0185003800d0140800d5201c0000700440780c060400164504200d80410300d4810544129040301107024000001c10840d00507403000c07202c440103c5d4090100b403031040c0d51294000d40300034205a01c2444103c2413410b265402003032400050500916050b540d0740d4406070030104a0b03514800c0030600004100c81d003460400000b6030f083e6000280e181c02d01000020302407490217048100030658850004041c0b805141a8080c403440983c4440c84280d82c500c00103641e43e2160480c21046070401d0050b50840c1800020b440 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 313263246 1250 313261996 313262021
    0x120201150b0c03070204022a060702060406090303110316081e181c02071409060607030806040b04090f020a0e01030c0e04020d08040303020a0b07020609030f0c0715021f 74
    0x4800d26040048040d500700d90b40303402c0140400c002c0b00005940300c0c401080e4503451856007402c800c80c0080441c040d22588008200c0c160008001c001100ea8003007440c551007940501c0001c0d41e003806013070403001030a031150038110118000041c0040c45101f0741000007442e5980d40d03043c1c019590a83c0d00d003403a9030150307045415520f4942c04a440c2c8050100303108803114245c001c4900c001d0b0040b144450b400725006000d00540c211100c01e02054140313130300880306142c1c1924981950309202000c501c2c548500d2902400b001540b001050155130b40e038100701900c000003803090012090509190702c41d002c07003000403441009003600c002070405065482c141242e8024074070390001840e203410014030007001031040b40c0c4098403c05c801d0000381d14602070400323503000743d00429018800e4901418880d01c0034220006651080e400c100071568004100d42040090b03500d69601d030500c1820603072030026140c1140100540b00c4201a60305540001c0c0320084c14140c501100c00c0040783d0480c481290011010349 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 313264496 1250 313263246 313263281
    0x20a0b0f0f09030c2a1507141c08130b070327170705120708070209071403130812010b1903060305030a0804230102090f0414060f12010c0309120201 65
    0x10702119144d41082035140b080003003268a156600d40c005030118088015040c106e550218014061082c40314000942044180041c4034200408411941d04940c40d0201c004100d50000010441c21b540d80d80d01101550111160206080218018010f03140b007540e80c0b4107400c04824070203a00c0009044100001c0d812140c02d09041502421921050b48090f005443c0c0c0d2141c1b01c1c4040030110800010b06200313004400264996002d40b040101991010b003004080200400100b2444c2041c0710807250003014400710121440ca0b185001142405440d40359880403152200000314100000010001da0003543d08a0400201e20b003c150200d5116020103071035035005104000f11180207842d100c2c1c0160040800d40320031b00d00c002e202d041007100c1000313030141360f50080b030300070a00d08145100b45070303030f001c1110306001148a40740800840640280968881d5800140d03241594841c01c0b844012000c4d00c40080c001813100103c0230707020345000e020071a81d80f000240d004c3c046502c11f00c5240031030088426103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 313265746 1250 313264496 313264513
    0xe01140301120c120501150503010c090b0a030e0313080f0d020706080c1b01060f060c020306040b04030309021906090b0a0e010804060204051201090b0c03010303080a020703020a0b0f0f09030c 84
    0x20580303a00e02c4550071100580c0e02d0070040b41050301c041c41920094030a000208251030700304924103aa400a0b4800e40c0240c0c100304c1942100c2d13030040603200955000007103807a2900c80d11601140500035181c0c02c1d21080c00001100c50f00d40b0000103280c0255022071080315040b5080d104c0003580d801c003204048005802929042c0540e903c624062a003100ca4440698200f12800c0c01d405a0b40b0850300c580c41c4583e43d142010006000c07021001d44c0141900e00b00b03940112159004030340c0300c2c071f002440248807608410000b81054081d0f40079090390b5802030001c2c4480c1c44580034038402d21100f8024480803a28009000801c91050421244084a55a2608401c2d524200151805003000d0000c4403869000e12001c0f400d40c0f40c131180066410350400011030141040d05012034240d80c05810000349441c10401840405c0c0c001c8035a54005103440d40040e0b0f105402d0901300e080070f200322401000c0380e1000c0700380415000c1e40e40c0840d0007250b84200003070664803031644242d6280700e004032820081d00300111 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 313266996 1250 313265746 313265759
    0x809030d0506012a030e09092806020316140a0c03030b0d0b09010b090a021305060f0c0601180b010801030302061b0c030a08100902090901180b030a030e010e01140301 73
    0x94210b401810300780840c505208000300c8004110000e60200310f001c41d505428141e10800c401e0001d4420b5a04d0401c80c101500c0b85e60300ca0125117035119282e1200d0f862403803d40c3d6401a09900d0b45d4124030308544905055106400300f21202a5010001c0d0f00c283d800c084002101c0c0865030b038901203440c5c03441802075a64040c0d000c0c001400c04c0c903501902c0000c000707010403103174080c0071301c502c811100000720550721000304160b00c0006070102c0b0906105001d0710740d60744400c14044040d107904442564691132462030340360301031242d00d884001c03a015503030000a03440e808031b8801d840c220310074005000710b0a40340d00458030701c40d0900c0040d00503801507000c20401c1d5945204103180c2080072403a2460900ca80e40054a1a400b03100302900041c50f0310100702c00748400f01c0d03900000d815070700c00a5107451041c00024115040600908001e8582500c00700719808860b800355446060140c241e8601a4050070302034001480d44004a010814907142403455610407618103901856400c003081c1580d09260 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 313268246 1250 313266996 313267001
    0x210050a08040209060f0d0b1f03050706081b0d0203060a090e060601030b0103150f0302010f020607080a0c0905041404020a050607030801140d1a0108070e06310606110d0809030d 78
    0x1800340350845012420400c141d11490044101c07d401000c6000740c50901c46102c04020344610030194940590715000d000083c00800c1315411a001d0340f90000c480c0c0c8072a28502201000440c00d40304811001400301c687d1440c580281d4810601242e0400e2516900d440b0392041c0c6c1c414150f80307640d9403c44000540c8660003a07104414920b410b240020309100c40c0e1000114482ca00d401460345014051010411917a0044100c01c00701507520141810342841c80b00a01003440241841c556191211401003030310b84601d843c0c1d0300504d070052091045007240c00d2a151040826507003039001d040007100104090501c8412904000e03410f9541a11aa1070842c8214040744250440c40d4446808240d140c0492003040551151403411000c82c5101c0d4504811245801c00a512408d001201c150402031607a881c4243c024100c01081200300021403a0948818940701460104c00e11618007800401e00a50045521100110300c80881e031b810314106100b91242801214075503140d604c1008040300c200403a8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 313269496 1250 313268246 313268251
    0x40f110f030a02041a060d0207050105090c01080106031107020a181109010207140402040b040b04080609010606090e06220903020c09040f02010c05010f0c0f0e0904022d060f04030210050a08040209 86
    0xb05801c1740c6490724079001406540c030089a0b04280307a00401c0803018030200380718164003c40c0f140020480720809100103003d401c01441313408241950b514690205480e03603030860305e19590003000c2515041c0c03961181c10244032546803800c0c030340e86881080c0100360030783c0301160ba0000b4160000d1040710702e001500451086814211034001d40c007803000040704c1005002400c0903162000d01c140d1109d00340400e0700d1424400900007070b0160f0402e01c1c01c00c0b800381c00c60034110598800c0c46002c0c5c4156550008148484050000b001041e4800c261501d060f440c550302c100b200e144203500340c0b40d00840040800401d0101a1703805083e21401c1404080107600904409c682039120740008180000a00c07142c0d0708544460f2480408501c44101d08429168041040000304208a803a040320707040a4021401000408103550112418a4400c00d8031001d14a1142c48041000b8a0266074180228550741c2942043c40100e008030490f5000f0209039018505030740a6410b15603410489996130b408000704007c0c003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 313270746 1250 313269496 313269521
    0x5011e0f140a08011d10051302060304140607031a2b0314030f04020f06070b04080306190803090406081b0d0305210412090e0412020f06040f110f030a0204 68
    0x40c2e48001515110070f000303910822404480315021521300d918a01e00b80340c01c080b25040401c0c03802c2d0030000540440a508000913406407800740e102d641d54038000742070740010052b4041ca0f1003402c0401082d2030780341d04400c4031142c01d8640200030303038034900034016001a1034400303010780034040009440c04107a1185910b0503c0c081d01d030404040e2044203001e00164400d5803080400030b2034404000c19410581608880000282c03940c5141002c1500c510b1600107000e04001c10018000003c611035941c2d07414100c0081c1034141c07101e041075035680c2c54256030b544000c2d000e502a03400c110000a1511000c01e40d40a180700301c10001c0f141e55424002c04c101e0740a92001141481014030000c04104904542d4043d0aa42070076035001031706103420b004804200b0061044200181d0030418846500011700d4076400940c400b005c0950381800010076410094082d02100c03040c0726080c204400c1c060b0220005030000e0144088a03a0740c035402e414045000120000309405a210b02805c400504040e400404075101 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 313271996 1250 313270746 313270759
    0xe100504050409050c0612062b061d0d0503090f01050115180905070302030702010b0616080d0e0a050a1b0303090501050a030b04050712050606031003080d0f0c0305011e0f14 76
    0x2a80c0000b40300c0c7d0403100100201046140070040a07007000c024880c0c4400303203546400d403146031400121021010142c0300418054a44041602d0480c885050000e600001802d6074010002440d004016400444107400c2e184500303070314280850411f2080c85d040e100d20900344869019216010380c1e184070080952403aa0030000c030002800d081d10300c01c680c0229103c2e500503070359040540b00282599545080980b291500f000700044101002040d0380d100e907130001380c0540320742c0e0700310070040200301255845840e03000b440501e008100c8040b800201091040e06003c405d0342e50490182c00425482c00001c001c2035045d24184a03d43c080c502400c40d01000e490085513100d020310100f410388034103030b0f03c0c580865010000501c1b00c000501a00364826800c0d51042d0541c600820a006c0207829840003034485400000d03001486501c641007035a10150090781031100d088030140050041c0002d101c0c1a0505103810a2000100c0c0c030f64003c0340468030f030281c5907442c40c0d00f40b80340213811040b910002e030381c080c5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 313273246 1250 313271996 313272013
    0x819110a030306061101060e1503010e06270106050a12083703020906030604020703021203040b04140f121b0f012004060c0f080d09060c0e10050405040905 68
    0x8100300056a0214440d41c1e011404524200700a4815060b150105d8441d906000c004d004805000700030740e9100d01500148c000c005030f0030021034010b001324005030b1168061442001600c0c40e2006a52090f04117996507215240481601315080316050b01443d540013a020608200562008446074441800340c04402e00c0c041c5842005194180d1541944805208135142031804040b81c0110000390303156410705525298105000610a100003440c19108660104000307040c180300700700720041442d0009880340d80342090709107000c102504403811030700346036008040c0300f070319801081200b08010590021301c40d803202c03402d0410054028100c150802c10440200402400c8100140640c440c002400040e580c000380c0408951349482020ad03082c45401048208101d5521500f201c042c05d4010800742c081008d146003c04651150810058919003089d28100a1160703e60000c0e500304819224003140400744010b2000d8000c0e0801c1090204405000411850170a50003c42449100e003040c0c94108 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 313274496 1250 313273246 313273277
    0x3060f060a0206010e070f020a02060c0114070c0203010605060703051e090d030305100801090c18020f030c0c06161407020d0203120a03180c06030f06050a150305130819 74
    0x642101c0035000040e8400801084401c1e06280155005401c034a800c013140c2502c5a400396941c489540000c4c003800c000aa07441640c402075000e280e050854926410950400b1031008040e49200c04040c3c1c0b09519001000409181240480f00d085506031241e83c200176112080c5d101c48103000114480454003008098101d41e81d8184400000d8800e0703c001a190a118480d0310240105810480703043e03260403c03903004120900000c10846901c88440c254580c0c071000f12002901a90402140110010003405400652000608100c10783d101c01c49007113a03580c4080d45511031000e81c5000103e01007442d6100240d1070301c3e00401d08079001828001603451968080384ca00314900b04003207a01c50011402d40d174020b0340346c0154001011400c42460040c11142c543c0b11180c3e50741d100da50300349039036030624151080309034102d8401000001c0100605690b9415401400c140b00b5504000003440c02e800540c45da14400b0075003400715003029400341001425020b440b1208010100c000c2813109055006940 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 313275746 1250 313274496 313274509
    0x318010f0315080a0b01080a030e06030907120c030b091b01050c1906060e0a0507021b04090b071211040b0711061608040e060d030c02190f08161d060603060f 69
    0xf0301001004058040b41d17401d00c541e07000d4040e00017141c07a401030f40f025000309501103001c501416045410355a40d071906440c19151a0041c0e014018a1414080050034402110060f608480c003640c0e401d1070594418007070303d44804485258014150705141c0c43c800f03e510410103400702c03001d01001c540001810030040c034800c2844150407100340b500c40740d00740f183d01d04406036550000e0f942c1c503007804541002c200194130b40c001007440035481e101c4600d18140660f100d0308455407480d048540600b0a003450140180b52448080b407a00003107041200111040044104a404440928a08600b4502540e4500000c40e083d9043e9039403004050007c604052959101820680c0c070030000719941d549081156003c5220080001e4850342c0702403860004280c01c641c0010406d641228509280e003d00c0c688452041c07000e4000107000510300102250111002070301c0500310041f00c00d02d1070300b2580c60b04500d00d28003400503045e4004010380045185410700c8800303590000002401c2880c0c480921011484 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 313276996 1250 313275746 313275749
    0xb0d0207140d0212070515040602040510030b09011208040e0a0605030d09060f030501062003041e090501080d050406080601021c0c020a090e1504110916020f0318010f0315 75
    0x50780d00070b440070403030542d0104940a4204070518200d030400041d9191b180d12002d0583c00c00007050818000501040038690455000d0f00c2c0040006450708243c1c5030090040041c1c800c01c4c0d024041a200100d10440d0007410b4a42131540200824601070921100304c660b40300240c1002021a01c461011845541c01d02165400004036560034503840c0c40c0840050a1f000300301d0902c024946000014081c0d00e9004108a00020300c214840079004100c030b90041c903510981c0d2000c5024102c020466120b000c03031b04101c504aa41844044c02140d0303c1d6000b66488004558540011030401c100c00c01103280100d4080380d00c0b40741401910300440e40c0c14800e89200c100c1d079500d0070028a200e4072610171490103c230309602402d000e030002c10080380c2007020a5a641c020307994480c01820740c90300103010400840c0c8000007440014029458030304005001e1740c03c15403c02403e5025015182841d07440103030000554003900340300b800400e4642911801920032a81c0241044105a05c1d03140d0318101c034080110500 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 313278246 1250 313276996 313277033
    0x20a030c1d010603020306010c26041404060b210406061503020d0f202d03010807080f0601170c1e040b01020a050a0201030213030506040506010501080717010b0d0207 73
    0x61591078014a800c0314041600302c0428548148240586039a100841e5600e4039480a09000703810f8441d9003140f18004d02203401a40b01000280c0801c144c20014005442802e0640341809491745031520000c5070b000c0c07071500705444844c00380500781c040c4200c00c856030401c0c060100001c641c1c1d00c900c0f500c81480c079456129070201c0c0e00058104d001c15214030035200701202c5580100030000011b8031500019040b941c10510680c4045496405460343c90300703102801c0c084400c2c1c0404541c162a500b29142c100740b103004441e010b248000184540041486080c104403000034010607800e11010b1806150000e6659085101d407040585c00380d15603082500d03a940300500c040d40040b500f181048240e51040241504641040000c500025000121851035030340c242805602c44188155120388035a190344090b0880c410881448103100000c280030341654005e0381c800151781d460401c02c0d100d500d00c050964001c00d949200401c000d580a6001e0040003085c64405881c000710f5813220600540d014850701c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 313279496 1250 313278246 313278269
    0x3021c0c020a14190206180402130e060307030819050405060c100b100c11011b0c060212041809020613080c1908032b0e1605040b060a0c020a030c 64
    0x30014481818a14040c8510f90380061000c0b00383c4400a808a01c000c900c001d0250310045190743c2d02084009a03c00d020901600c110749564800c00310100080c200d2082c216a00e502102041d498100815220103036500020842e01d8880c070a141c0c06010503005c10003200700078040c44041010360f00d0000030130110030054000c120325880105404106c556030803002c0c0c403c0c83d07401c03025035100760000260814160408a00303542c514004004ce80c1e80b014601d82c0640e071101d80c820803020880d417007050b101912a90b9003150708800d42c81e51458864400e07406030880e11120034a00201d900465006148911700c040c03c45c0d81481100840d18080700c205400c0f003801600b0605180100b400e19950302940581c0c0d505d034140c0d140c0c2c90f01c1e020341d80780e1092541940070020110840080521130f65418044801b50b00300c20001e000c1c0383d01169444031598050041010700c49038001403186068050210800802044180b5058280400303070340b0b4940c01380303041380c0188207480000007050600b800c210041c00c45e94200b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 313280746 1250 313279496 313279513
    0x1060e01120b0609150402071106040b0a091e122a17012703050909010f05010305150901091d070303020c130513080903010912090501020d08090d03021c0c02 69
    0xc60010040101024012021007007000b895440c5c1220740c4c038001d01e055500503990022801d00c500c42d0241040c40a81040002a0008440091800030701c40e901e03035a507c0d221059240c1003051007511244403064008442e9a00074400300d45a169481c06040c41016006c1413034018950000551031010741464520511040401555084540341c0700f010503031500030070a40340845800410407081d043c0e844010303840b440042c810513000d0070450f81130380b400401020322507075034a5154040c24042d01840b4000f906142c0416103035500c411403070900400040c01145181c0c2804421001407164100b8107107410802e12002103100340502281d00650300030343c09811401c00e074a05211401c641060f00d441054a03001c2009200c1c0311615010740d00360f070b0083d410766542094000090140c903141002070300351000f04101d250301681204008086070800c0c0c00b5968819805001601d6901080f26078401c641c0020358482da82c10f120f54000c04440c100c980b048440070302100d0301c1c4401c4400c1d00a0440150780410b12 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 313281996 1250 313280746 313280753
    0x13030305090f01031e1e0504060906271403160b0f0c030c030c1b012c030a0e060f0720040f0507021504050c040e0a060e01062601060e0112 61
    0x1c2d2281075400c1c2002d010fa0100000740c089107824650030304411a655004154594007005400036a40e121020300740500e042074182040201070340f00d01140e8840c0740a00c80c4840310b20002c084100a107080c42c01c0414030130b058940c03150400200341c8040d424041000180e0301040900c04220701a8012103141c1c1031440c103201e6031140c0c400d000d841c5100324130003442000758580c4c07040102d03944400074040755602c0c0c0512000300030f01151000b111440c1d5508015210811034001e9484181c030580e02d90401011013145103200b0b4892191465042c002658040c03040d00e00d0030100b000b0403c96000c0030206280c441c590310356024002c0b10300e014150218050341d02901741e280c03500840780900c0f9044810031403401c28a034040d43c0c1d503055001440390100300000007030078032a0a10071505180c50141050200242580300a40c86901032501214250318090546124a50501c20309040d1170300d000351122042d84100c00c003480c004d05144030354852740d20f600700415000040584540209407007100e9004541c00c516 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 313283246 1250 313281996 313282009
    0x1090605010309050709020f12040609031d010c060b0f09070f080603070e010e040204090203010f0207060e0303090637090515090d0e030a0b010b070c0f050f13021303030509 76
    0x140124100b605008070308011401c0403d09100700c44101c00c005135124000c080030a0350703000308221200c1d849102410002400b059410507000d00e403081c1e454040c030b00034207070031070060700300029403580000c200011000000701d10b03911400c9a070b10010100c034207840c45000004d2042c0000c490300000601d81c03d40c0c8681c0c03907410811041c0c000310104c0c050721141e401d000c1300350881e0340305104030050055004045000c0d9141e55003da23048940140c000d20095014030034410180d404221304448482c0791a50b000040340021050745e000310988005840d05444c0c400c01904955184d0380c098a0318201901d0501607400807410007480c50701c494001040c0121035040450811a00c18034005e500200304041001c02c00e80400e04d04904055418600d00707000b070b0316000c680b4021490300001c1990b0304250020590304e88070000341c2000751040c0402b40d140c0d510340c0012011196588906038101d54a40321148252512400302d64004281b51401428146104201050311004e81e0090300841c000090506c038509018 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 313284496 1250 313283246 313283249
    0x20c03060106020a0506150d020a032f030606040e1e15010b0c0706081e0c30040609320d0201060501080412030902060304110f04050c090d02032103010906 68
    0x20f001826149150b0b0710340c591200c000401e43d01d1b4001890402c1f8005a480c044100341d915005003c82e8491512840e00c0c00715041051105000e01d00440c009602c40301b0b29614042d040e034400750140210351220000d202c003070701e11555092104d0080314840b0500100e10003600c000c3d6900385004203003188110192401240040c0c0007000421001c124101c10380c4000100a422603460340742021550351002410b801e901103041411035910711400074041c0f03140d0800007800da00400920180d401c02c402e0b1110640e102c1a080c18040a44204000500881c45950141c5409800f0305c070220098039502c04411000c41c1c48056600c00303000f841c200c0c44807880e0b0800240300a007050b80020000079003024006083c0d040020303c0200005000c01040c0500b6201e0742003000e5203a0301802a0352a41420b15209a844c202515401e0040842d01c030713401d20910f4a80a0140100d07400406c5500d07000c0d05000b40441f40c08181400d0b44c16200700713003ca0261102d07402542c20a40007841030584c880d411b003880302059a01c903 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 313285746 1250 313284496 313284509
    0x20f06180d0c03120c081b030d020c0114090106030c0b1e0c0a050105150102150c0c0d0504090e062e08060114120a0b010b0703030e060a0209101809020703050c0d020c030601 76
    0x440c160700000541b4001241c0340390b9140805003040840c41c080c940d265110b2446103600c0b440c00810304030901c0c2d90541001000044260204110740da40c1d5889a080700d105200152070b0225104040005c4154000100400050190301c2020399130050f1140f2003a9000001041c0f2603071000d502c48045c42020301c1581d80105448580e071031103900d503000007591910000c40c85141d22000c1008210401c248104499000c204071044d40c40340c5003072620161580d04a4443d0312012801d14881110301400070071028402e100c040442c100240340c0003004100c1c2003c0c40b0040410f00000c04010900c14030400c22706008002c1a00d054031b13403266034824443d845d00a4880c41d02945d1010964100003290300d0081410341d454080c40311740741c919500b41200a0201601400d90074000c0e01d06012040b150742c1c005110401055448030103880441404440c80d039040d00300b01d810070440c035500303002403041a0018904a4002c0c50402d050642c0a1425400d01c1d01c2d25544001680c02415050300380e042c28850075005011 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 313286996 1250 313285746 313285757
    0x11010c080405120904020d150e18030a0807030b03070b040501090f0807030f1a070806041a0f060906070c0e0402150a05030610110f1018020f06180d0c0312 68
    0x242541d9090740e8404000d042002d018004c40d1880309038841da816144c0a802c0750105101e100742ca01c4061580d00203c0c02660114030b480000a0303600c4c01d19170003440080c016031004500d02203034494201c4c0c810f10007030714001c100368a44003142a140c6e0200860406050000841c80d030f620714140002d0202d105c00c1d44148441405114100321402d00031a410089a402040309010300c8010703d8401d002002c4402d8180b1440101028800b6040c0c1c0400303454402c0d4400d80302040303050b0407442d40e04000c07400ca901c6a540a0f0300000c641031a03040c101e024044c03900d00601b215090950980d50010b03100316075000001034503101d404020030b43c58943c0340a0300280d41038103828600042c0c02c40080503840004e1100c0d000d030910030402000c66220b9100e071610500c00d0000d135450304248a444503201c0f1001040e90300003900b0000400558801841802c017019401400c04512000002c180032040d040041d0ba840b600300303004071a043d41c2d1035038021461082d100b00000d40b00c01e811407500500c407000f0b040001d4208003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 313288246 1250 313286996 313287001
    0x1150203071b03120329060d20070b0a050a05010302091603060b0f191e1409040c03020c0c090705090d1e0c090e01050f0f2e0302030f06090a120201020f0a11010c08 72
    0x307c60008580d0000c0c41d25501007450811a902e080031f0441e00001c607402c104002070300b6000e020444c225107019140c034290500440c0c480c9a03482c17041d54001e01011354003280000100703c0803108520b1188030364007035050219180d070350341c03019221540041140282c101c20006440c01d0035504c40e0704082c0320b030405e4108000d10480c071029900d40c0d84000c12150050000c41842002c20505c03100c01d94204841c02041030103046c0c18244010080d401c1405900b040344a000d40d421203034606000010710600d10703699a18203010603901000100b041102e0180c8031102004c40e0040c1c500d050318000b44046004042c001d021a243c030765800c084600c1d1346451041d5924040a1200240d04000c0d1030303030010302420002c601c41d2a0543da0800c0e82280011a003242d40507209c00c0f01804461220b1001100d000b03c0c181c94500d0142240c140d101c50341200c644805412220407000041c4030900c080c41340c0115071000504220000501001c150300981c040070208111009800b803400090040000707640452504041da030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 313289496 1250 313288246 313288249
    0x180302061e0705071a130b0604090b07261305070801140705250606090f0e1207051906020d0609021801050307122301150203071b03120329 61
    0x1044040e04a104003c40001e00805000b05064010010045624010704134103000303a00041c9110032840403101d143d4500700003000c0303203094800c009100d0b030040b10301d038980c0e0781d0060101e648992140c1003400100b51800e80c2c101001003007000743d1007403041040443c143d4500b401c10902d004204e522030703c610381c14002e218145503400300703000ba0850114101aa22400e1000425880f0354035075034038044200240e6540000d00007503400c054225501400100075403c00b809114054504d0350058010035401840c64044207025100200000b601500c00d80d551008a45281c20365404258026079541c2c0d000b1807102c1400c0b40912920000740400f2074114a09000b074451040c05c10425050241880000710000d5115405150461000c0e200e2900800c0700400c4c1c02c5260116504d606020803501038440e00114140342e1040a42c01241200d400460510607144d40302d41130300402d18041c41814005060000014143c1d401140c4409102d440108000b400302040c00080140c1034100004400c8145890005 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 313290746 1250 313289496 313289551
    0x2120f010f1203031d0601030c080c09180111191e1e1101150806010b090904060b031c02010e1c090308280503040323040b0a110118030206 61
    0x442c1d201003608803009446040a90050681040e8080e48020365000d0300c40c4064049841c0d03050781d10420351003000c65200d075205680c400c6c040c1d40c065080425032020400010400c00c440d440c100014002144003080e0607076007030040d0000c0010410031140b4104032900f05400803280510703901d4101d204001d2170361044004201040d03e8495040c4d680d41166100c0d51144102d1328550003034240300080c44101c62407425800310741060321420109005a10002c1400807038002140e14404009200000d00e8480f0f40b101c4008020100c1c041c1c1c1c0c18070400032160301031060fa03801d080c2180b071590000902d1060308901c10341401101c0c582050000c00142c1d00c501c45075006050329080c2d139000342c40241c443c45131044a0215403000c3c080c82006041202d040301c100c40e030120085100310710a0382d56000700000003c440c80f003030b400540342040d001c0c0c003030106000511007e40500811682441c00810021805041c5421201c040c8a590800d80c0181118014180c0400c9070340e400034090f240103000080c1703c0640e03081 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 313291996 1250 313290746 313290749
    0xf06060503191e0c0b04081b030309010f0201060503120c0607030e0d2a1209171e0a021207080d02030c0d14070b0708070806190302090a06030b040602120f010f 70
    0x20707a0f4001140d1250012034500125105503002e01d143c1482e0b81c50307a41c025a5908580b141c80c40510a603400907407090107a00c0c0001e6040000b900942c2460141001900d05000107540c4200b19981c6000001d52590104040392030036104103c072559503030002c0705090800c4130041004042c5410004c080c0b049100020b0000d40e006003d2a1140c03c5022248130700e000510321204001c07640d004103c003501801a8003a21300061b210544440d01c0d442c2c4e5445a404068036441d40c20b00107604800c0e142c88800c0424505d4407584c071600320685160290550003d03c18948c413101500080d844030301c0510001100300044242c03134416000450900b6018054280d448107040f50310f00410540c000221070281041e0280c1d41c003950700c0500c543c80e502c1c1070345004140c604101c1d44a00018070250228507541850400d899002c1c095606001c0380c981103400b4800b03000b80c00350001b0b00c5169030f01c400001181b09860054007451150300d02603901c6088440181300808041c008414032035140c4010896040440c00140 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 313293246 1250 313291996 313292003
    0x3070207030b1306060b0d050f07050405090c0906070507030303061202150a0215040f030e010801030b0703050c16050304080709020f0d0902030c0402030106030b0112110a110c0d0f0606050319 84
    0x42654682101c00640d0350740e4074000744828141703400800c0a21401000d002c00c0c098011041125941e85078180010810540d80e0201042082006200c14106110308680c03003640616810f26003940d15002c642aa440280c065a194218040501c10180d1501401e0b00901c801c8000c124660030a8000445944148458940040d070002d42112403e009015001e891040905802e050b03203401d040500c900d4000403012070000e00c40c580b0f030504542c0110440b50683c0e4004c180c0c0019a5100c1c88240d0040001a00103540e80c04144004442e2808543c2211120b41c8200c018545451528030780c24070302010b0382c022501035401030103089091400f01003a076003a83c9198401040c012100d00100e4104034910712103e800500000c00400c1e580d0b00740d003103801049005ea07144121801c4008003541182c10b42d0304041c042e01010403032440b10b02c0c460b0030000008004c038001d07036141c40e4101c00064100c07420381e08210f50600124501d001480350512419009007420b801401140081c0b04503034180841501c0001c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 313294496 1250 313293246 313293263
    0x3240608060c2704020a050c0c0108010b0f0705010908132306090d0312060e070e010f0207050d030203040909030915020a030804120c060504140c0301151a0c030f070c06050307020703 80
    0x2c5850301c0d4503014030b03e804054001c660f40e0101c0e540050441d1700c4424202079a03c10248600699480b40242604850181c465035041010a034005c0055501554041c0c449648800c050800f203a4100000d0030002c10303400120058034904545600600e40300020040081440034800301c69131030703800c2228001c032021101041c2c0e1001c0d6207819200540310750380300608140380100104580c03031002d010700e004001d47d440b601c080c1c40d082d5004580301c4100001e5480141c0015000f000035081511042c83c0c000d200b070050382c0c2401d484000982c221109500d0a030300040b410001040112a00c882e10200b500306840039250790025610007038031004000c3c06c020105c000325400000110f1144032020740440e030001c42803040c1d0801c1d04201a11480640c1041114041d4092142c1c0e20320f814841c23113100207400c09241c03c0381460003600310903100580044007540c1204210010031180140020084030103030801498232a0b1f800d040c800720001c2240c100b0b4061000800c20300c09100d4000804400b00c075840300c00e9 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 313295746 1250 313294496 313294537
    0x902092a0c030a030e0a170d020706090c05040b0a063c0914040204051807020a080301270903050d0c031b02100e07050a03030f020703240608060c 64
    0x102100d403608050104400c040415a030301480000b10040c41e0300d54181e41c041c00303c1a04030450355140d0881c03280c0140303420b03400c4410f41c0342d8200ca000580746003580c06600600b410840d8480c20143c90107030034210340e010b0740060103200e81c1c98a4403c80c8800802540d1481e1020700b02440640b600f484400d01c041400c41100041072440ca2290b000d400c11391050381d161030000c46124004e402d00c2901d0088501d1301486544001450400d8801c0c0c50848000908000c0785051185a901c3d43d201c01a080000314025181c901d00445d00c640011802803030b0030300c0000000c24460b00c0c1c17140c500411003600c1d84028240345005000c294400151580f2a14800300010305060f0001c0a80c0100b00f40c000101001d58501d0055081c0340d00401c4030101c1010300c450500413001040141d07512443c03c0e01819901c07a690030810300100b8031400da0f480b02985240120307821680c69071101c0101e12106103412000702d01c1020810800c0b9010b00440c00140807203c000c00c1141030600150017940502003c00305412000d204 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 313296996 1250 313295746 313295791
    0x1b0915071b03061401080f0c0603040c092901020a081206030a02100f090f060206010308130b040b0918010f15030914030702151206041802030d110d03090209 69
    0xa807040c0089420055001d00c42d81c80c540480a441c500c0700e40c207859001e00b00001041400824880c0c06030000038003400d1039943c2e840801c1803a0304050320a4500c134030100c1c40440c0b07641c0607100c4c8415040d056103002507a90110b0000140300b5282206e16411500810180f07000280704106490360114000130311095540d070b10011074503140141da000b0794030100411000d80803681082a00b8201803d60f40c40d4000e030368a030018070784d0743c1a00c1d101d01d10050b03100f50f004001013078840b009068409005a500c048003541c80c0d000740c07010381044d000200b550000155010f0721b4604000c8181c98000c50701600c070709961401d4070305810048248902d0054084010f06480c80703d109034080ca118962000c003c059812600c511550f507608001002c0b8007d141e00d044140010100a05440ea0040c0807002c5000c16641d80302880050803490780c2006802e52054444001640c040c000602034140325640e089181444151592601d600f0b060900207140c80c02d503142002d40c40e41001d0680c04411011b0b4040c2407045c03500b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 313298246 1250 313296996 313297013
    0x28120c050d0504060f020c1305180703081824030901020c1905060705070c23030d0c02040b060c0309040b0303090a0e0610171504020d06030305031b091507 68
    0x150003400d60090044004400307402ca40600152403441c0c0d81c20031106a4260140d03541c048a00180c2d0348601c04014000d450700041c1c101c280e10407002c03004c0c3c44440000520061601483d40c0080354005404079a540c070311050766403448146003040f00c44400300803241451207a920700b42408104840c80000005850341e80075011104445000000c507142b5080044201c105010000c8003110907001da80085000584101c0079130381c2d103d8100c444401214940f519008840c0c007142e01c01180c182d8281e44888103551f00348440c10340c185660300c814030085014410441140c052416481c2311340f8062042c0c400c0404000142d40c0c030050140e900090f030f1140800001d00c0c0d400750348200c66015041c20b80210b18021101c0c1e509018009c10380354940c00c2d450000090319011002511590030903000400280104400d001e90120101c01070b0005250011852656044d03421503002640454800803d1041007200c0c0c0d01c142101c80140c0c01090b082c200241c00107160345030b1088800c1e5070841c0c0403130124180130200 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 313299496 1250 313298246 313298267
    0xa0c0c0f0501020f040b030105090f091b0d060606021506031b090a0605060c07090c030501141018060c1a0105030a0f11030714011107050303030112061d0106082812 72
    0x801251030356076500a46e080c41c0d000b40a510700814002c40410240b2540c030181d0ba009030701c40c0005c1c1a0b0700c8640701e001001185c030381046130752002c0e1644080011030020312810015041c6076002c2c0416121110350200c8a10015000901a41c8400410707220041104000b0251050480d08400d4a807151881d08010706261340050f0360243c80000d100d4072100340024030004079101020305204803101c1400075401c841091082001c0c52054035020306503031410f02102680c1901505088100e00d120f0140c6040088c41d0303411103c041035240c940c280038041800118034030403540746420f105540c1080f01080d141c10030b5410060103005810100d10400650030b10701e01c40048003600f12045140d45e5a604041006292201408610f2050014100e40404940d080c19200090300442c60b513441c0691064070240105006d8031100d640e14500c0402085000030005110050000441e40e80c0c00c101400e03040c401c804d41c81d030342c2109000021188401c48181c10400e6550080c0710074800c400400e00598906868 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 313300746 1250 313299496 313299517
    0x80d030b030a120804051513020d03120e0601050319080904180f03021e0a03020717010b042f0a0801060525030c0b09070803030402040b180c030f0a0c0c0f050102 71
    0xb0140301001c0c1e201300100d02c00c1d0f024800300c0d000c00e503038591002091034040e600c80b0110788202c040300b005800c0c000704855406200f03280c107800d00000d84584101710342c81040070140c60f4004800411031890100302c0c0f00c0b020f080801c19410340420070b681d100610700c210000e01c0d009e00e07204c90003081c190960341d034160000c5030004240d00c000191490001d4584400c40e1404d001c1b40c540440201012000080c80c0b030b440c0b03030705030002c080c040c1c100050110400c4070042a180c242d900e0306560030310740e02c4501071002c0b2802030b06903000d0300300b07002c2004c0703903da101d0b214a010241c0c005120454206502400c1d05044074050b080c070642d40c111f141d9511442a2003500210b104a07005140d0004040d8051000c8110304d001d58000702180d00c0e44014252215824454025103900900105026180681c001c40c080c603401000c0304200385210850240c1f80a0440d035000c814035000c800c01c245184a5101a036124500318030402c1040007038840607110350740301d0a0280101401c4001d0200300f01c825411114000784 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 313301996 1250 313300746 313300763
    0x40503030a03050709170607120f0207030c02030c06090d0807080d060b0a0e03060105060f0d15060c050106050d0c290d020c010f0203100e0405030f070f0201030e07080d030b030a 78
    0x10541c5019018000a5a4180004180301800104c1c46520ba90f18020003d41d14064411034a40c80e00813245044000c3e0748607034556441c0b0024034202103902c000c0c26210f1080d01c03030025507411401013508081c0140b00542c0079582c10400c0c400c00369618440c282c00381d5071041c0d45940b60791043c2003c5605004094075803640900e061004902c00c1600e80141540101541d140c0d621005500701703164889100707108441d0007200511008100c000c05002030046004030380381c0000c011101c50140c800b11000c3c1d6000c100415480302e000e80a000b4280942070240400399644020790303440c0d0340c42610030740091094902a12910258580266034642e0503801c920041180d01e858004281d1400000c0d03008121042541d8a0701c014155110068005c0c0ca10443c000b141103802c5a103041c2c1c01004882006000b1503160004100502082601c003000d0580c2070701502d1100c04440d90b9100140c12141c1e01204106580c1c0f04a2042100c1c40000502d034401c0c000a1401081c8003400c9004280b074800017160042c070444 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 313303246 1250 313301996 313302007
    0x330a0902030d03050603061b0d0c020a05010207230303040302070311041409030307021b090103060903091e0311030102030f0604201204050106120f0605060d1b0311060a05070f0804050303 82
    0x5515801903070241700201d054500640350025047e0150401c8040302140d0601070108507080075640c2d01c03032680391000f4016220104d549644007822a401018121846100c0f01c2b68059900c40082c80c2d001c064504030015855400c0c07a8038003070750f28070451200a18650004034480007648a80d0040e82c15150030a150b055942400e40007240c0300d4004030360580041c400c007601040e5201040028420004000e02160020390954880c00050150f8520641c244100154001000350010f0400c02c00307060032150f2004014118504411400810640d0900c0303a0700503c1031040e00c0d402d01581540003541202c00160484896518286030703a05940d114901e40d4000c596203415400503006103200310300c61002080696183e0b1808030b406581031001410018030766070310f4030004074650701160f08120001c0075001228815070b00d00e9841040d50030a107480100b0b14204100b004041407458036140f00071500c82e410501c19030700c014000c0c01401000740241d10802c08031000e102ca01030880d0090140a410fa0b03554a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 313304496 1250 313303246 313303273
    0x105060d0c0b1c0203092107030905060c01021209010e12030411010305042105130501090303050f03040302190f030e0603010506120a0f051e0601140706200409060503330a090203 78
    0x50f100100b070001911f050302001005025400211000300d035041e21045110386c200824003840e45c100c2e50074509590350030011141040c4008140920a045500000c60701060700500715003032503a19081600e00c1a014401d00001800507807601c1d603605c0d000c0c6000166070707956040004415164410119440aa92100b5101c241c1d02200419202881850401003199650011a401030f041e01c0041c0c00a8401d0109020118400c030007507400074003910481d030075210300e106d48444d1031519810403203800007011498800c160b00910107418181d4100c0b40c8508540c9820003003440c9114101806041003007120000c1d805101c2c5074040741d550f40010324100903a281c54081a6241401d01c01403c0002c108180065220f40c820030b4507010501c0c0e0402c01e40d042c10450380c0d40c4006440d200b52500000441d011000c03070322801d44e03800780c4000c000015003c501240f8210a150803c40c4014400002132030740c810b0800c82e0f01844203200352407002110884c080d0b680b8041070710014410100000d5160003100c4070341c0d040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 313305746 1250 313304496 313304503
    0x3010207110616080d06090e0601030203030f0a020319170a0510120212030307030902091312050703030b1225050a0303050306010c0c090b0f0f0a06030b06040906090c020105060d0c0b1c020309 84
    0x20754076191002c02c9100c8c0705c5089555560802d11009500d5841008580c2d240d0b281c0c0c41c003030451aa42d80c0100e03802c14800d01c1802c0e4038014410785000004039042a4107050700d0903000183d0b08400210810000c50508007044000405d10b80a11400b10304244030f920115112213180725020360305c8105507522401d20350002409800e50b0102a803041e070128002c0f5134200c2820482e80080c0b81c0c429082068000f0341241030b2110b070040d1906609141d41c8441e584042d4039102080440c0404030707001740c400312000e540701c651400440005c0c000c8400b80c8083c14041a26841040b000750380e00360814648030355640004903481c969101004102d1b91040ca40050341160603001404a44800c030f85003824525a00e013405501300d90f030000594400a46441080707910f00070f90000c00c8103000606420300d4140c0344c15030f180650303600390701020507581c2d207004410020b070303081c8229608803504031780302803c20504d502c1d0341180c00c0d140d0084a5150000080d0001c68044041c0c508580c454108029501e0f07240a9504945 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 313306996 1250 313305746 313305749
    0x2006062403040201140405101701060c030c02121204030c0602010c05090904020d05010f0c080604142503060306110705010b06091c1104240503010207110616080d06 72
    0x3034048021006016640d00c0104141050126000d4107540c0d41c3d030011541c003c442100925100410003001c106503c480b200c040711291680c680310000c0b0ba03800000d5400c248142d21a42c01c0141c00c4140c00002544100b514083d5501141c032882c6102c0c80c0b141460a104000540304541c07000014000300f000142d5502004a4040f0f030000c01c84005071060640c0c50303205900d61a9808100c4038001801803810400084c549400b4400010740c3d1701d00140ca010841ea500c005001c00726501200f000300c145403c0c065480500f8020b4881021402d01410612980c0e808a1105000600940303850051910a0740014020364205500748040300609070200c121342c0c080c9009844039400c0c0a8040e07183d0a100c811915600c601426680d41c180c60900151456401c1c5501120500900003956806554174012801ca0f140404000091040302140345030000710903510184c040d0340180030120101d0100304060f15040b0042e52181d60b1090b0240306868050300307540f8004c201183c042051241030549034040340 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 313308246 1250 313306996 313306999
    0x60e1f02030904020304110306042603070e0111160605070c0b0703020d120b06031003030201050a0504170a02070515041d0717151008060f03070b22030c030302030d0c0309051b01200606 81
    0x4a5040c0702440644bd180700840301e1a01180e501c84081805500c01e807070011701c0b03602d154142c45e400280c169218501c1c501552101c000110040b03054401d0003400100d03070b0010580180510b19144c80b580d00651221144480e40c03050001850180c1000c105a402140341c5490041260365a4540075000070580880b41c01306800640ca030100051502180e4850030740520b80112004405200700022488175070301c9030500c40c1c118002c10000041540b249240040f000744004040c50301ea40c14610750840c0d0b41e1140c001c0d9030920340303c02e0034814000e4120403003002c4140c0b0146010364591b1000000d280d884400e50030036401c40d61060001c10a607078401181402200b0484030070b07044064510030559a07040902031500700d1301d41000300810640f100104096032039008022203170070075036030380301e1800070211540103501580000660032542c90b018880d0300f013031000314103040142500c140c450f640e4405c5044010351740c00254484001c82c50380143c02c070410f1141c60300b9444201850b1300040c19110b400503103416 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 313309352 1106 313308246 313308293
    0x6040c0210150e06010c1709010509120106090e150f07020c0d0602070201030c0c1211011503060b120d050f03060103060b04060e1f0203090402030411030604 69
    0x2d48680c503004120152246044941c0b003600100404442c104040d140b01d1100161001c0304848410980c0942d035074541150f0001a02c062040c009440e030721140c240b0f124404148150000d00076103158103411311680c070343c040100d682d43c041d601621101040910010b0100803a0407a900d5000c1214412a4004484c14000c103441c0ca0101e5416184290001b030107030103650f050b015039010310182d4504081000c04030f0302c0e110040e0300b4840c8004104004500d40c0903000c502500400d0291901042448206607286003100c000d222104056001d129901c2fa1880030349030100f007815200b80c0a803a11032800c400000b15107025800200080e041c0b5542e20f601140c2039503410b0141000d810140c8a6113070316010b0104101d5455070880c0301100341c01c003944c2d45801841e4044140e51054001360b6015803607444a25061150750300317881500c0e0709807040808000c00d0003c080c86502080400d040310 = true := by decide +kernel

theorem cover : BRFrame.Cov 313129496 313309352 := by
  have h0 := BRFrame.cov_init 313129496
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313129496 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 313129496 ≤ n) (h2 : n < 313309352) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
