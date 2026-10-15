-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5172
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:58:54.518143+00:00
-- url     : https://prove2.me/submissions/c2566f3e-4a67-4067-be13-be735c463d61

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 930035971 ≤ n < 930215827 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 930037221 1250 930035971 930036001
    0x1b060414120c0a0f2111090405010f0c09090e0f0303011707050a141201050106021b1f080106170417070203070e150406080109030519121d0606010e150901051603050912010203 77
    0x1100383c072154410740c0c231402c0a070f000d06030700901640802d10300300101c00060361007111402540d031442c4060244814094100d0394407450115040f1701d030b0b00b00744010f01501c00a001c0b03601d001d01045040344e08182e20365000074603104040e0701c50340044001c10548009801c0c01c000b00030000413040c1c02003010f9031401101a441d04250020644440c0034803803840041c0c1e5620504a134200901990100c040a00c01d00140205e0b20a00414001c1004050103210321034891212510440d400802d10300d08080142d8001c4194109410490340f40c054150085601c50b905601c2910822040340410003100c00542484111031983c1c000f4951390341808041c4000c02e4120045900c650180610180c403c22201021500b541400c2640001641080c525030002e24841744c1e00c039507171100413068071410703103d00d0010f40721101c03018078035600710142d255000d01c1c4038080005014040d506040841c98446500c4081145602c0101c045003c90b40200b00f514003800c011100340140c0541d10700071031a500b0201040c0040d44 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 930038471 1250 930037221 930037253
    0xf0405100e030c1507050307082116111f1d01090c0b03130803070804030306051206070f0311070510051003050a0f02040212091b060414120c0a0f21 65
    0x1802503184111480340c13030000c0b01c10310b680101c243c0c0d031a0b10840c41c01001c3c69000311a040f120328000260f1448076280ca500300d902844c00c112000c0380e1140221010b41e6075864003a500905400340442c0804041e5907140c0654030900418000202111185241c200da000c407030514001984c9044004000650154001d0041d9001e40c099551251350b650006002c940b480e85004282000120900c01402c1e00054454010b074400e48040c00741a8854081c03041c858048805403081c2d40c0414040754075a40684002c00c102c071040d182c08210f0b16001e481e1300354035510064084620303a001421642403944503205854105ca01c010000d518075107913490b01c540c0d5414810018120700c441d03a160000319a6590304440c001c0042c410030036118034298034071941f122400f544c140c800a081c1c2c00c8081042c03030510111810303207105000300d58a007244082448000981504000028400c440429909590b00c0104200509001c0544080b040c24000b10340c000c8600c2d500001c280c0b00782041100009883c505200c10305d0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 930039721 1250 930038471 930038479
    0xf0501120218181b03162a0c03051e0d1b0b01080d030b0303090112090c090e1f09031205100f06020d1116290f0405100e030c 55
    0xc8621562119103004514086640310084800110a080c41510424401c1c0e2804074004c61004211046441c284002c03648070440016544030341803d140101c02891070550201448005d45140c041d106030502d101c2c21003650064810082002040000c01840c0198442a00818500e1000659140d83d0b10b844515460910500502210303005c0380c00807400d40001e800c41018100f5583d908841c0d51035100071042c4200103810100141002e007000000c4807403680042c3d540011442c4401d1001005052440040383c0d580c10b244400203072113650340110110304146901403e41e1605499000c40109400c0340c03514822350900c0081404242c01800d00d00e011065194041031075910007000c030a491301c0c1504592007040e41e0890101702c03c0d50001d4942c00811454890041e010b40e003030240f0390f6898800e0025010305001c15801c0c072000300321051a244500b10b90000c200300300110410a0b020341c02294403500303c3c10002c41c01b0486480e00315000c60502d41e441c240a40001e6103c404283c40e51001d07540c840c09 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 930040971 1250 930039721 930039727
    0xf071d0112081603050f03190c091809060608010c050a080112020a0303030e0a0c032a0e0411060c0307060c0f0c1a060102030c01020403080304140708211b0c0a0f05011202 75
    0x18140624100e0721b4900e85450890380c0c03031424600e004041030b800328100344180d280c51011040c0303501558482c016a038118422020801149a000e000340c40306103800c03190340b9122100005c1e014402d01038000500129280c050300d81e25114001403820350141d04c000c0714106480151805600d81403002c400b5640c01d840c01240c1e00b20080111440d05018500c0142603286c065000000d0010040740241c8121400c0d00707031030202004100c0c8242041c0b81d40500e00401c0040000b0800181001404a003074030b07005460503040c031103c81d42d480d0840c1c00c84102507400035154043c08440550054204c05100800d04040701090788a84404c14040c1802003207000d1448800c0c0401c1107130380208241c83c2c0984200009654a43c0c4900d0800b80741d410644080b104100c0700c800d031a0400340080740071802c0c1d0702480010484d00421f019200020320100d032400c01c076104c3c10400400788251511230b50403080d0701070004111800a90b001d001918075a5480301c4403045040e1410721403a0b0344140e00c5c0034035040c03462004d40c0b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 930042221 1250 930040971 930040973
    0x105100801060806060304170a0c06051f0e040302011e1e0e192123040b0f0307030603020405010e0910061412010e0610031101021209010309050f071d01120816 70
    0x400420801107232042d120700890340302c0c01198001d607404955803040c00140b03d642c40d2070030101e2040402c4110381c0c01c0d83d00d100034248520302003100d206034003030300074070000c156258214540311552000110000c1659140c503040e140348016031018640c500c5045004100e0911241c0915885410300380702500c1310450715482d0001c0c08040c1d64540510b242008036a111103008090103814503207040c00c200c0d140e4141c520000c9111029905481c11070781c404100318649190719484a00b0782e8001040b4000b85940e0b501c0200c0980c4841c40f030540038000419640303440342044082580703040b1044a900b181c080c00e1003000d2000c0e00407441d802c2583c13035040d50010303410590b02841030301601c86403074540c80f2481041c081080c0903040d9000482100d000300000640080320400490711100c008140c6031941804000d918486e51090b403060504c2c030300840507102241d40c540e88150a101540c1e10281d10703812620b681d1031259800040182c014071040a401c408000142e9414020303004030010340c05007606c1e21a01d04 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 930043471 1250 930042221 930042233
    0x10090b0f0909010b01030e03040f0b031801060e040b13150902040902040c0f1202070804170a060606020304140a050a0b160f03021e010c080115180b030105100801060806060304 77
    0x4641480201620720610700400800e00034013481408070b0009080100142032224003104840a07683d44000c0000c10358242104104a0345c000343c01d101180b203420449908414080c0700b440e01a00c0b000e0298031070360820342020071881d6000340c8002c1602d00103003c2840001e400c1000b842d0401d502c100c000c15081103d0002400a113403c00713001c0c0d0064184030609030901da00541000f0740301003035260b08100703c1c4807103015030407400341010040c86078100b00000c0c00300c1c4184134051008034000e80c00700c49030840780d5621081030b1039150b0311080c09a40302007414000c2e10f003001c1280b0f030058801d40e0a0159985004006421401d05204ac4140558001005841c10307050501881000e608100c80507004041454005d503200c10009142810800380c2c00f20b1010300f081030140c0296a050f07642d0b101c50503401d20320610440d400d60f103401020710603224481c0362510b80a1170403600403c59024069103070361601c4140301c601d840300002c3d0010800034600600000341c0106056030001c0e000e0b960207869580d185026 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 930044721 1250 930043471 930043489
    0x230d180905040804050108070804050a1b080f0708100c020a1e1202060a0f1b1215140a08010b060d0e24060a050405071211090a0f0f0e10090b 62
    0x1184201d04000070032042c44000001401203c1d8207030380322036060b607490204440c244002d660003401d0b07802074000407000c1401a01ea105e18103002d641e600e0700302a80e07008403900e488120980c0200e51b070451001040300c00d80500914030302c400c00020074400d103a240180291920050900100140c5505240c1c01c04003010910108079035a10001c00740c0c0012003e00d020356030f000c040b07451141d500e040c034014003946d4030280104441009008030800703d0b05e038a00015504501c5c0c0c44e4081c1900d80e0f80c0c01000107201c0041301140000c1030700c40c8009042807045018072403c00d841380c11880c1c042e814882e40e692280c4580e0100c0e600700888540004500766080005420320440020f5144004c0304403e500c008010341c60555402900d00302c6080820325903400602095070000c03100c59020038419005421100e03641d40100b20b4452601e20380790301d4192040700042c81d01820f9002209542c1050105114031181d03128100d01400074940d4010180c030700160030600c600324500070f081d14142c40e044504040c0c1c5540c850 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 930045971 1250 930044721 930044729
    0xb091605030307080c031b1507090b180411130806061009051002070902071a0f011a130f0e041a0112110f030105010b03090d090503060f07020708030f030103230d18 72
    0x40307c00508180c030400c0d1f507075038041800504114441d40400c240301e000f8001c1c00201c1e40003102240c145040510041131031500c0c501041d8001ea00c0d0b00b030100c2c40b91100c50003810082200722602d614982018a6036103050310050a060299412482040c0d00a41046030301049500403525402d0391100c08200b00d007800210740c400f580740390001c2100c0c8200a0302a0181c0301c10481d1a901b000303ea070b160404c0003903054003841008030f82e0092030300d40440100404010030729018031a4003551080e917030315001151002c99602c03c44950481d80148030030480650400f4002c00448500044554104401105800071288000b0321190361080c034800e6a813110141900300080040081006603035400300d0701d400d58000c590000e4103016018503000250700845200c020703944040e0042c189540e0346044804040400740144080d4032580340001901d2a0420050140418212030720f51a0b525601c0e01c088481580d506142048a0f600d1042d4003011000802c102200094078141c3c0ca0100f01079180c1c8c2646411b500 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 930047221 1250 930045971 930045997
    0x31106040315061523030a060f030602070314190c14010e07060e03071d060303090312180409050606040c05090d03031a0102011e1a0d0b091605030307080c03 69
    0x10b0802c010b54496000000711912040325a8084481a030201e4040b46203600000030441c240c1e100440c5020369801a5506c21500080042c0150303d40740001903d101642c8201c03070080d0001000b404241e4000944809032a00842c107905000100b8050303040441d001c2c500300200042c05445000b4070402c9030b4124a00c407265002045942c080f588807640792002d6000d84c3c13003c2a80110700c070075241000a0903070201c85225140c4101d00804800250455402500c0b0f99410310042c00904410b5500380194080803510b50700c0b00750340b0b808480304d039641c901000300c0a42c440d9242c1076040010481c04201035a0000c412140007990760059002035405009103546142c000161259490402da0580d1149041d02d1520805035150b070f4040004900307851071041011120300700106062081c980302d40041051200c4100c2d5140f01d1358503070300403c03864002a903061307422a00304801d022102200f0301c85024161010904829114100004a0b0f82d80c411210300074220301d800207080300025070a10030340f4420480c03c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 930048471 1250 930047221 930047243
    0x105250303090b0106080610090612020f090a1503060503060106090b0703111e010609151521050105040e0601270605091806010b090d080702010e12010e01060602060f010311060403 79
    0x1200906c040411a01240504050004100710074000c02132a0100c44240c0d0750861444159070585000e5003109041c00180c00d000d0107104120fa45404040002d02001a1041d4440c251b2000080907078038071f80d0081e0302a820441c010301c8103e41c062149820307183c00c04a0507075200d00502e403c40e04400085e02c003074914014402c202081014a003e030542e0f41043c1c80007449800c2d00c56260400f1a182c42e0444405178441c3d450800118070f010002c1c040b241c80d5400c2134410b04d00c5600c03c3c0d0322a4208500d1099400d6030b02c20050180b03280601c6900d41400c7c00000404d6a0341c1411544038800302d40015a074106c10444031204810885070b0043c0000c4c003070141c0100906d00346100072000e60310210810300258000d1034004650101c00c541503c11180c0000d08200208050341c1304c07800c45030700c09102039040100003985a002525a07482514078042c84000004030821802100ca003181d0258100c2811500604140810b084007004040d0649030009801c00c4482c0707032070002641c00d00c12544002c14209840b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 930049721 1250 930048471 930048479
    0xf0f13020a141614150108071d04050703031211070f060513030206060409081614011a0603010531050406060b0306030a1b05120106050a050105250303090b01 69
    0x80d4001d0040815103440754440d1145500d1104218002d804400083c03005501d90000410004000101d4582c01841922000c803217444800108501c00d810121040e07002e1001084003032082d0410120205102407041490f041c5650b0759500c7d151039120140800ca404040c580c0d030098690300105194105401840d40c4020070715181d4010300c5203d4042e1035481ca0400044c000c1000b1000301405507602d41c0c082c0c161540c2d40d0003007200914180030191391611090104555144540084611450040000440b650b81c8504800d00303492000020100d03108001050070225110f0b03606483c195001268800e007440c50000010b20040c0095031603111180c0c03226144170140d1642c2d40202d0289016503c00e010054443d0602d004a1000703550664040c1d00007258040803a000007c4a0550a84100290100d0b60354000080507030724064859801a50364070307000c102d00d140035294500104070a0804508081c0b0b8481243d03440e42c11142d00e24030640b1409403090801d44aa03200c85034165200d0b50b0020f41d5615 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 930050971 1250 930049721 930049759
    0x20c0f0606040e0a0314160b01030308060a060f0903030c060b150d0c0e010f0c02041d07060314010b0a1b0213050405010f05040b061203090406090b09070e0306060f0f 73
    0x2a1202401903242403a803d203012030102e4805440307a050749414600301c000c2044290140c2c00491608040620f81005800060b01188850300a40c0203541d88156801c0a00c100310b84140341d54000024081c403120041c0c511900008210304480d0181440e521501c030711304000c03000d010340180e4603a001600c52501d6016080850181c0206800080c082007402e02d0380b802a0754454003038560501080d00103002c42c0c81c151045920f146d5481c4040c1001c51001d0074440705000350780e19070390184c0007a0008901408020342c540704046508850f981ca81d60594034182065400b4030401803013208001e45801d1141400030817414080a05a0152038403e80640f882081c000034001607808459950038007516000040d054080d090269410180c4d50600343c45485c10802c4c0b1082001e14400c01e80070030b008d28400c40d03a55100d408000c2c102c0080100e410304c043c808100b0402c07401480e46051200d412044502d0703440004800d80d00410684041944810b00b100107450611308900841d0321000d466240300704031003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 930052221 1250 930050971 930050983
    0x10c0504080d020a1e0807211d060a140c030f0403031e09090b030111030a0c020c0d05061501090302060a02010b010807030212040f02150c01090b0105040c0f0f03020c0f 74
    0x28005841025510141c00c84c3c542e09200d0003e031100c0101404a20044440442841224400c0c3c00341031901c034055503020703038111101c0340310703105424a80c00169002d034000c80007034603800e040d0a0308195500e003000000c1c800e0249000f10005c01902550740300c8103049640032034845e040007030103d94036032112901001c5140e2250108400180c1c80000d1110500c8038003040d42c512642d1074407004411810060a000240034807002030394190748130180034802084450055004840c0c0c4040440c40c1040380307401034a030a1600003010300801c03610485102003040441d016400403100b010026200640900403501010580c00195206a001508902e46030301584a600240c5003a00e401d0240e03607560000343c0c00c90064426201c448070b8800c00080000e24104480402184000d00c0904c1e041040844401d2941161540c20420380d901c5602c8001d000c200d8104d9401813104940600850408070001049596006905810300c20100704004050b4000d4043c0c4007a80e2900081390009100081e0065540c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 930053471 1250 930052221 930052229
    0x50a050705130506012c061611010f020d180f06050a0f080105030a0209090703170310090203190c020a0512120c0412020d0f08072009040c0b0a0c05010c0504 69
    0x11008090042d0070a850160621030078050f1a00703100c00c0c22151600c8040000004600c44450321003041010701d0395213801404200803451f02c200540c0f0b2031031501e6030310065941c007040d062101600304186020ba0001e84190140310501d04010044034900040c042110705070405480102c2402000c912564010054410300e8080c2d40c40d070694000d6074500796481c54081c007039130341c254000d0300342c3c2000742c00c0c01c1c03202ca600084c01500700c40c20300d81c2d2a00c8a02c0c0e480f001032040c0041d000000140000d2100300085040a017410a20851450401e00f640e1412840104d240454864484e0102e100150080c070180c00c5154002d02034401c000030403039030041d40380d0000300707c03695020f402c0000c11000c641d80d84c1035a041d1040c500021a0108490b001c000c1c0040c4a0602210710200d0160a180095020705c0504906d51080c2080c00342010428600a00000030300c1d400780c015401c2908001c04200340045c1c0d1800c4508040c00c1555485c02c25000701e40c000011240036010b50300340806401042d0380040103000311 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 930054721 1250 930053471 930053479
    0x10501090e0c0111031b1203010603150602060c16081e040f060507050a0303050907170601050f06120a202208061b032d07090506070309030f050a050a050705 69
    0x91850b000040d941d06556a10210503a8401d2203c8481c1030032051243c00902900e40840f000c0d43c0104141c40d000f54004d070468070001b5212600000c0011354000d210f0050034840c00075100a182007103c2406e2800f60104c00000c0003070070900e100034410803404503a5848040c0e410714074454004401030459600509c51006491000900003450f14072500944020b56444000f074180d800003510100e01814000e044e072001d0f80030390031001800c80100180d816a4010070704c0a00010343c5442c00300a1741d0340c000c0d03070458000e440410015003100440400e0340c0e030050000c840000e1181d03641c0c280303943c9507403c054000600ca10000d0440d04480c000d40c2040e101511900400c64582c2d196101c2a484881c10388604200071030006030030011070a031401569122000c3c0c01109290380034001c40b00f072001d8000381ca00120505940502081582c0100c091025180683d0448e14104940c0c0d80100400e0061202600d268440441101040800c0c05400415500039049840141080c144280c503504944120780c45 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 930055971 1250 930054721 930054733
    0x3603060a09050c060403030c0b041b030506010311040204060e10050906130f1502030a0c290a110405010f031a220f090209060f0109030605130203070506090d1e0203010501090e 77
    0x2113880c00700201c80a403a0706a13601080c2e0710070f42d03440c2d95048101402c200c624009139044030810700b89407490a00118003e03001410b0652640c107202c1c2641058000c49801907004001c1407004603001754655240d520306603042e221040e46a40c00700c40c14002c82c110154003090014440021194a41950060316200204011241d1350340300c070545032648010064001d60000e022040d40e440c0035125a40c4054041d02c10580900d40309050703032203044040b41007060f0340c224060078400d4a44041c82840c00702c001002903c0c0c5003900b003000207001310143c0c0359030748109a01d58140246084c4003a400b4040d040c4007421480310040a07007190b4817046014060340449603d0005200c100030f600d8050034140b40c1d0087c09210064036000203000c81084804402c505009002c0b100100003a031920846208410201103603002d000c243c41010304144071540039906c1100184608111039035400307030801c0c0541d401480e040701c0380d85921403400000d200210103545546060000a51080907030040c05040c1105410b49035 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 930057221 1250 930055971 930055993
    0x10090b0f040b1b070204110d0c0c080d0b040209060c0109021302190f020a05060f07021006080d2a0503120a05071d040f230c3603060a0905 61
    0x1a0400c01180e01401c0c004a80307001c00d0103103900c14080d81d0b10103041001c8510b08080781c0c0120301a0307010040e21400384000010070031502102846175042076103ca281c0344490903126112401c0034020490420306143c0d0303c5420420390341d00e90341252203420015218075155002c03000100e00900c400c400581c0601c541d0b00c100040404684215100c001c4543c5030145c0040c8400c10841c0c00f100040d00e01015031044914400c0850004c0000313500c90102050805018030f4000e00085c00c120365940316509060a0002c14000c0304004140e0601e1001a4504000190f00d20716041c40b0091218421611650b0400d00400611201200506018200f4100c0400981340c00107114101c0380100c41420008001d0000d0300002401801c074011980c00003000812401c18000c082d108031607001030840b40400c1c220000003d924929103490350301c40c0f510152641000c0308905050040144408000c00046840c50f0741d14407048048155a041d03040034007203c05034a45404148000d1420020170340c2d0034801c280b2100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 930058471 1250 930057221 930057241
    0x190503060c0d0b031c0f050909040606090b2b080412060507021216030c021201110304060c0905100513090f020a020c2d0f0306070c0b0a11070b0a0e10090b 68
    0x417503191102000000c210301395041100c04550b205000c9003008020061402181e07281c60903039016500620700020803038508a0544200c501c2c1c102214003541c0200e44840e100300c000715121120100d0412042c9a01c651490f02e0642441307150000f0490030309801502d4103114071907010621600705a001c0f01d2000c9105d240c0c52195001700511480c1341a202104440024442c41b41805c0052020308111410344030440d41d54203480c11041c141d2134205003c8104014400a03004d60070000149003031000c19907003040c01141c44c0e00e0302800640300340700d00091908032410030040000001c1c0300c0f14008120700c0781c00d4841e032000f950000003c08014400d50042d42044c0c549040e0035031300070321454980306401403451000440c10740d460600c41e500c001c504090100d0340c0c5050046038031550180e611184610b81510706511100000f41c20045554501450032003110034401c00c5403403268120010340c072655141c548440c054071003000c1080030350144c0c2c9034440156029411005100c5c3c840c007682c140d10ba50304540c130 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 930059721 1250 930058471 930058483
    0x806010e060618040e030a020d0207210818030a030903050d0206010b16050a0b0108070314010b090f0c1308031b03090a03080702030a060203010b070c1202010806190503060c0d0b03 79
    0x41d58041401c00030701d410500250b0900c1900c1c1409030001c503104464400ca03900395040032030f45401681010500751a815410301c000000342481d44030401a40d40313110b802ca040d00c021400001c011010000389061040e98080719030b4522000242100c20b08013043c64020801c141c13074031003100c0c18810135100c071000c07500119105040c0d401c99030b4030b20f0900501c3e62114003a000500f00903242802215013940c086001412158043d00015000740082469840c03c040280108001003541e64902140111f0903562940b0b2540c000000c1e400e01e07030b40d58680c1d5000040714401e144942464001c500d40000301c1c40d2011010b41f504103150171031091080b81c008502da450f481502105030b40101c035000306000185601c006890168009822501030134026507a0b43c040740d10a0304410303480350300400e08104201050304d20401504604410600340036850380041e00c1b190001c0c0500d8441c0000c00d010b0401d6a288050003401407100404449031410071044010345a802080f020140d1401c04850380c445003000141c5c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 930060971 1250 930059721 930059731
    0x141303030e0d02300102040b031b0406050708030411030d020a02010318382a09030604020906040f06141309020a09050a021e1c0507050d0504020a0302060f040806010e 73
    0x2d0100410743d0070740480d4018900115004c460900c115190811280902c00791000d81100c0c3c50284d0b690619160746805d07000905d1100c451480d0401041c01310945c0001901c014540c842480d0384ca0340c94504c3c0a0000c03014104c2c5190305445011941d640d101c0d40050701240d403a000780c80400c41c810349101c030382d001c440f10320901500f445400e441010922204140b42c2140c0190f1003145008101c81041c421850402a580e58103450500002c154401841c1d0900e41524001500c0d0545818410740220f51036000060010384140e02800002d8020303101d64000404d481d01d99982041055241e611581040480240340f0b4000c1c2422207501241580710700c500b80110703400810044266181c40c210030090400209901b160503028010011070328503d864145080003001042516802000501d0f4032441c8411000f014142c04c050034413507500d8000e81120b9681e5104500400c960380c4500120744644650742c0001d41084001a03c98542c001d6440540f0a440c007071410703903880c0e0340e071105111308891003035403 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 930062221 1250 930060971 930060979
    0x30a050c04050f1203070206030403170106022d102c010c080c0a0324090e1513030e0a060804020a0906080c0f0120011a010206090705010f141303030e0d02 68
    0x4001407a181550040b0036544c0078a007180c0c81c1180345e5000c03443c0c64009880031404542e0340c1705980115044c0400490241c690383c4010310780001d00704a00509544020031046001d2080c612094000009108107078030003046c800d0a0000408001c005a01812000400c5a40c2292940b02101442041c01034a0030017a0390369402042c2d403a001036075502c0b40d11020201c018107503121103841211880d240102815201c418041c45c1d1645400c140360180c441045144a8035003040c1d12150f0385940742c110482e040710700d21403117107410380003807405692034800140c545a00a40107000003900c030380d006d07140d035220324800c1c0c030007081841d61499400d081e208540604505500b008070301012a040080480c402c01d00140b40400c00a000102000d03c61078030641c141c44030b651100b0502c004140801c1c0d812107031500030701c014469458800c4883c2c1d12001140100c07810040c10496030a0726500c01c6c10403a45800070080310b240c0d61220810b001e04228035070b210071030100f52088003568013803400768144030056402030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 930063471 1250 930062221 930062239
    0x510030b0a03031404080d020c0414100e130c081b0618040b0607060c030e0d020a170d02040b130501080703020304030c0b1b2a0a0f060e0109080c03030a050c0405 71
    0x241d0f09a40802c00c000c0400c180c0c050a02000034151010420072041d442690068070b00c3d2078650042c4015101f40c004502d41c07840030302041c01400d2507076200e00780441d00c01000040a549681c402c0c0c50306030074410005001d102100a000c203a81d071010500464030b00340b542c0004a040086810301120b4003401d080d20141c8014445002e010b41019005010042e00040c41c15140030f08030780d140011503210b00c6480e40001d13138a030380a5248802c00c02c180b80d00922140020814002d00b0340d540844003107500c00c001d02c8480c2c003240864481c0c240e9016074025004908502d80c6401e20142a40365000c054440d50780041d000b000816102da00900c2101c0c05541c056903440b80c0c414441e1252503034108081e02d40c40650ba400412140003d00c80c001801010b43c0740d00c2d8040f03035001c01013082400c001017000180b4080c0c2020710b5600000301c581030301429190380100085000c581041d5940c2c01031150400c0070706400b80006134900c440d00c000c8011882403003031035410000e64440318517114041c0103901400340c03c00009 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 930064721 1250 930063471 930063473
    0x60305061f0e19110a180b0f0a110307060612031202160807032c0306150f010809011413061503082506020408061008010c050301061d0d05070510030b0a03 68
    0x84506240f410300e61078020410500030200490181c2c0024000700004400d0319008012959144641000300309040c046402c0501c0c1072007a00040c460900c542c81803001000b9040013061040c02a5a6000d030011010482c8556481c51080c4c0303c10070600450003d05003150903070200100d0b20a80d1665034500d612801c3e6058113030b47c1c1c440703582d210000503014001d4644c07180c002c07140d4210307101e164491a0340650104900701824103181c4480030b019400b03030b03808103608110315843c1c98800000381c0710309103001c08135a1120f0024a004041c01c0300c6c41c1010b0104034080103a0841d048600c8000940304031403c000d00f5405000c40642d40031640002030810303c0402a440000d19903014070b02c00d0201558030380300070007402d85e00c4000300c0c0d00030780c407280d050340200040002e207052043e0540028a01d071402801807441c000401080761105000e042d0038070490707800f004e000c0001e5100c21101c0b540003414209500c580346c10300c907546818901c80c1a2080401c1410fa800142c401c0c02405088140685007030411411 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 930065971 1250 930064721 930064741
    0x1080a1a090a030f02031c0e010c020f030a08190507021605030f0c090a02040b040f140303040b0f130b07110306070e0d12020c03030d150e04020303071103010b0301060305061f0e 78
    0xd13030005001144028001c150782c0d849108049099100c0300b00c00019020314a003034481c25a20790003007030429900030392000e0a4084010045984503920703440c2203911981d0300140c01b203001358a6001101e0180c0791078204004c2a0300028070003011000307041502202170355102019501d075110803080c10709420002d002000c50601c40035180d0040034500300981019152051942981c04c00e61004500d00304001042280001850310f0914406040d0003841c50315090400126151103030490b100b0152800151104040d4400034102c406805902d210550710303079641c204504000740690355103104c1e02032000818035282c040c0b60480c3c622413005d8104c8480d0803154461810711300f12481d1140640c0105101a6541c0c2d50600050546a8181c6400107051185559440c140b840b19006a0301e428246014440560360000503240000e51003121545000c40440104c1d004d03089007401c0c1905582400c201004104000c9030185c401e0660749010303041aa2002412807401c40c0d00e203c0c0070442503042020904103c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 930067221 1250 930065971 930065987
    0x60f1002010b120304090c05131208120703020c010f061d040c030803091f0b0d06022a030a0e061920060f15040e03160f020901080a1a090a03 62
    0x55000004035010b02802050320102d104105070704903000024103008242c0c0900c20701010f9070b91882c00c5401d10305440300008400b140c5004a01070845502105c4c0c08000e91a01181c0303440066404c40e0005080019001c0d002c0e42010401c3d41255080815400c40b40c0c450748515000c54a051500c0510116240f10018400d08040e00c140d61135042c2c074030b0100200302d040c03005501130031094000341001840c07072034100100321200c80300078030941c01d046900c849036aa030f596501c1050781220005a590421360068a020b802c910b5500040f01040815048005004005010030b41d5913030f110f400900a40100b0040c161041c4c4900041c0410381c25800c22040307118003800d00c86d407014194851290348180a10078540030003203800060b0342001801308001d0550b8058446804001500c0501100404425042c0c80f07014a00f00d403180c2d2000c641440081c004500c4006001940141c8400e031256103e07031409071a50807105040d10300d108215400c0d40c101c446440701c24851556034000e4103501d02e096a08840ba85 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 930068471 1250 930067221 930067249
    0x181b03111e0c060c071208060d06021b0a11040e03090a0311030703050a0b040309051804030f120f020702010201050c072006120a0507020606031b040b061903020a17060f 74
    0x424240007030301d6046000c12119001d999013054164807041a403400c00201c0382451120300030000310009000c402e44410942c220600d501190141e11100d1940110b81c140740c0029109049200700700389041482903ea1901c4101d24050310700b4404c0c0203400362801e40e00c0c45110662504800410800c10108100c820581c100a100409540c441e503565107070706c2e103400298401aa4007044138800c0c4010103820034524001000e066600980150b005880d4181650f40140b0103400d201c1115007910406100e608071200244004008100e54100454036400a40061b50300b207000d50310740004201c0b846075007000d45407010741c044c41c4109078410300201074842c1c000e040e4205401403800c0c07010b61114174049405034810084440300183c03500d4441030081c81e20300041c00e1035000b9004001055800020b40b45505150070013607801180041403400070450320f10039018100c0110b103080e1041d201d41136041d002410000301d141c0d00c0e82400c00e16a021005003c20550744180c0c00031818004004c00d08000441c45552 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 930069721 1250 930068471 930068527
    0x60306120f051501090b0906090906040212011104060507170c100b0409020d06050403080c03060f011b020603041a0c0909010e060118080708100c081f181b0311 70
    0x10080300f8040c08141c1c0c10030703088040013075100c6203000050b0500520107984000116040249403c0407604282c9402002d0006030103003806081100b903101d425040700720759021800705e0b25170340c0d079440300000d2107034205000440d0a00b4955545407483d060b20400d030f444011a42010b02081c0b14030040c2a401031144a85041c0c1058451a041e00940d49191000b07010070300444c00482e280c6450318004000c170f08003c014540c0c0078401d00a1040540b0381d15550001e0800a080035000741c10f00101c3c2e003407280101c00000b980300c0c0c0c0000403c01007100040b09001409a00045e08a9640351485c1c0824075004820101360800d841000400030845c10b01805504894181803800040102c0034070b0f001d502103107030004003090380501d0b001c010f40f600801a511014055503010403082210150042440001800d415020048107002c00840355008140c040204003c40d403040520400c0114400509451810b42414502070381301580658000e004030415458601c01d0503240c005180180c500c82c05450010120f1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 930070971 1250 930069721 930069733
    0x103060510051228140615040902070f0503031524030c09060903010906022d0313150603050a0210020f1005070903140717030c030901122a0801060306120f05 69
    0x400e01c403021680710000c00c1c1340045000d021480383e42c8400c450190401e4003c405c0d80100107084200142590183c032815200542d55031940c0c20801a00c0c51a96070280507030100000b4880000c0301001000c511141c207a440301c0d07032000d124109410243c0d00855200111000700002505464618024808040d00500e00d070306242140000c02d00715001c14500302c0f00654005100c10001d507904102d150440c000c4080c10f10a021034681200407030002030451802290b4a0b030f2100100a409580c050a0281031241084495036a040450b038807007440b0000d0b805822610712018465101040c5982000c442e42c0040284016001d0203100620004001000300040c0d440c0100000e078285c0760b200c40044002e80100b400c68240350045211003a42d4840d807a07103510400102010050100c190b03030703d4001c01d003402d00d410703500e19400d400078010203161030f664111802e6910075109810b141d50541949140d403084060b80e00d8040a60481d941030140380312951084c0040000078803c03d600c80c110030321403019104 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 930072221 1250 930070971 930071011
    0x302101d040f180309080f0705031905011e05061503060d0f031214091c0909090c09020a0f0201052d040c0f0e040501150f030204020d140a0b01030605100512 69
    0x12044643d21001c42c0000d41508040154510400c102040209481c01410505250600180e0f41b01c036911000c0c090100000d6011060200179403140d031404850503c10030320300b0040410b0b18010007084403051b10030340343d141804150383d034118107891180c80e010740700110b5182c06480e40040b040d140c0030100c0402112104e01000100035020b0301144003180e2204007128104008040e04100f0304240c0d000904070740190301501c4a61142d0741d20708440c00071800048180240c2000741070141aa081244c030203000048032604d0b00d9202c40c6584075079400342e00070050b035141c969031043d5204401100030b103c254080d040c188416504400c17a6042032056400300502c664440500721111150307800500081d0b000402c01c0140f080c28050b0000e21802d141020710354078140f0518443d504180d00029029075030116100c0030035215070b40005012220003004044a250810080000d40704056801c0c0c0001e00740480001c0c142010040111004215103515003000f4000310b0b003010a1000400e198000741104108030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 930073471 1250 930072221 930072251
    0xe0c1b010b15090909060c1b0c18270d05090d05010c11330c09090c0a180e0408070201172a0306010c0314040e010f0302101d040f 57
    0x40c1150380c0c0385000c55200c00b020010003000316401070501d000391b0801010022072115420448407043c03407400c04000c0807170104031000c0c90039002456942c1c01c40700c5c4a01c00441030b80238481031885080385285540da400900481282c40700942d0080440390750041004103441c0e4000c00151011400240460b02d0541991715240c4c2900c4e101d0040b8004100a40841442ca00d000d01409600402d00c1312090a404002518000009400100b625640d0f4480c0042141402003500300c5000780340041038550360381802c0f601d900a075403256510340d001c1054030300c50b820b5100308074104200b1182c25014010066480792511219a4045d1074100e04102c800010080010b2030f501d80140036100c038a5000002c60304075103c8002800008803c150720715030178410800c00fa83e01a5044a210381e051800340c4000e039500d000c8451501440e0420035a0381e844200200384003113503180c6202141c0c0201e807180502100c0035070903203d00c0b0401034261181c6080c069200381d40d007000d410054101135902d50005204218032014 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 930074721 1250 930073471 930073489
    0x307020a03060603050c01180918050d030614040605030c0913080f0403061a030d0c0c0f0605031603090b1807030204050a0b043c020d09080d060e0c1b010b 68
    0xc90b04141e590b507041c02408810805030728a050300f07081c0a10081c0c43c05000510300d0343d8030720480c1e051a44456049901d1500c40112225040d0b0040c00c03034011003580d043c090054001405a2800f50907405640c1c0c0403840c2900881c800c4a40280152004bc0301e020284095480c00038245412140e540701818001074003100101900c1a0a0000b1501e490441c64940f05480d1143c000108000619984130025034012400381c0c0e04886505100180d00c101c0c2c0350000b041d2517107522121350004500000256107401600541c400c442d2408220350034003000905404442c0c04230005454114844009110078400d0b040300c5010f00d00100803540f08a5680d03000509541d81140c407880f1080c1c98600000490409000f48500e4100380d8241c00c0100c030109503c0030441c205032881d50b042ca111018020946040e690488021611189040c0701e0f0b00040c2c00d1202d400da02101e110310f80940b07404c00c00192001d140e0442c81c007411480b410300c0d00e401424030f1710355280d0b40c00502ca050f2656070f440717040442e0303a03c004c0da13 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 930075971 1250 930074721 930074723
    0xa1403010e0a0b0403090e0c030109020702150d0b1807091a0405040507090e060d1106090d05010c0206010602100b0105041205010b131b030218090915010b030a0f1503140307020a03 79
    0x220b10003d11300381c60000d0a040e16030340242c2c00818401d0600200703140420076641925001000107071540b8070703400050410b1903444424444040c0c001074040030400281c0110650740420341d0440d002450310202d48460003022a043c2c0c0000d8541a800d202d05c01120048280c40d11000060500b095103440004080307a02c142e45030341c08a819002c0800000c9101d40080e03a10117001c8800c1041e41420361100c0d4502100005580c3c4650000034214400355102e40c072031100150008001c12804159030030295841d4804c1c021000980704030402c0c0d1100e070006004441910700107035138031420145000400303074030007450500c2100c195407244d001c000d041c0c0ba100c01106130019140360102c1c08120400710325541d01b002159450800d40100500880c0000403075591007440010343c0d0444503a91460351140c1403581030130302c0d45100064400000303031100c501009103002c2d00781c148082100c0c6004281d00c504841400b0a000c080700703d0360700708101007040895144d00041c0c40c50183c0385000c0c0e00d40e0006007211000d0b04 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 930077221 1250 930075971 930075983
    0xc09070504170d0e0d030801050114210f0c0c0d0c1a250504063513050c010e01080f0a020f070302100b0f060d0504020d0f03020c0102010c020c0a1403010e0a 69
    0x80c2d80d40c0030f160f21002c1204002015690200b0760036032510000e000c0c41c0140105414418540043d600c00c2104200715440d40c10095204071782075044241c036203090001911911154410180071480014040742241c1166214000420302503003003c60540f03030410704505c00d8403030303040301d000314a80b070b1040030304081c410180120101c140c614460150500954041900000c0020034042441195009010030a405400c12003075010b00d40c08c04e00c04d0034405107201c5005a44d141c00d005005442710350301190100c2c0c0e40b141066900f1401c1007401102c000c0351851110340000d001d080803521102000101c0e98000e00351101c00b601c0d1811503c2009034a92084201f200181d1003803110303904420f13140c0b14050200030201d0ba1104051603d200040740e6000300010140000d540f00040380440da240102e48003050740c41102d100d41641c03507040c081d49840c80d0480d0140503508055640754840e10100c0c420714801030080c181ca03101c6081c5244000b00b19915401d41d40c156603500b4620343c89403c200621140d5500c194 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 930078471 1250 930077221 930077233
    0x30d0c020c01021005151c0609050601090f020906040603020a0c0b070e090108011104030212150f06030c151b1204151202031b030402030c0406090e0c0d02030c0907050417 75
    0xc40024075044565400540e40d034134041c140850740c0c21b1240b40080e0b40d0012100b8120800d02d82188040c01c84039201c00410781c41ca40b1480104018002c40d001e412070368014410040c00103100d16500c168816000041c0d40404200824015180a94064030065100785007030482c200b25940d410000b260196003640c0482d059805036019494101501c0340580a08002448002d4030140300c4101c500882c040240719603142c41300303442e601d002081500e810a0300002c0d10809070a05500b0b8030300c0341c2c005444060003800707140d012102c0703802d08000c8404264015040c0c5031401030703171244a00c0c041000503400c0c003141c050700711541c0303840711004045c00103408400151082c0c1a89000c0262130360482049507502140140104440440f02d40818041040307407403103075a40e0355100d1000030300303010303030a101c60381d10074603181b00032920ac6c0d16039000341003291290b401c0b00c0d0200c44c01d40801118103c3c41c7c4000b5810740c80781700c1d020307603e040c81c690450b004030702c1d82400d500341a2a13080b89012003555440c4503c07158006 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 930079721 1250 930078471 930078493
    0x80106090b0a0e010323070e01050a080313061b060207060506030d090315050c0408010e070807080a211e05030702060c0301120b07020f0703050a1104021603030e030d0c02 75
    0x707101d4a00340c0c1a0440c1e103a1141894031000e15444201440301402103d07080d810001c04130300da0b5110481d90004241070702c0c0366a440d0011080445828001c51340503840c2600081200e0700004100c44a0000c1c41400c190058601402120385401400c2c250005241201c40c0d600040c0a030300140110714800d003008a82843d204050514001d903502c0e08000b000801001040440c540c400d441d41301c2030441e000814140e5030407405170900c2c40b5551281e01d896182c018020b0002c400810840150740d52101940d0300301d07030798004c19a80c0388bc16110140c40b9032407071202c100c0d00000c06207000007011850306214a0b0422407141c45070030035a9201400d0045100002045100c80d0705000c0b056120780c03130b600400d00715410f00d0110003d040400741e00600880074400410840b5000300143c1903135502c1d20302101c0706103449142c004c0d29601d00410440c0c07007410240d01c0702210b241600070390b102000c0750700c54841c1082c100d480440140083c44c49400290108110640b045e074885d010b8561164002c0d0010071412180b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 930080971 1250 930079721 930079739
    0x1e0c050a0605180d0c03202e0e0622050411040e0f0112020103050723130e0403020c130b1807110115060e061c0c120608030f030705090a080106 63
    0x109a030341e40d114104c21300900001070f62000d030b44401d598000142d07400001c0200d0401418216a03c0965407001c0f102c010300220202c0c42c3c010440500b40801c0102840004503002d4417264030501031168080750600032403608801c82071174101803900764891b060440359120081000c0354100081c050165200150500c42082a804c040e500003980c41071042c0079600d48580041100b440c010020b040503194800710340702034404e210380703441c45c1020b00d40078801d803004c1c1c050704029602c29203222aa849241c00b00048440380300021030702c00d607010340140040d840c4410401aa111040d2200c02141e03a0301d6810840e40c2d01c0f03020000030066004424400300c0d051480001e4084000d429801c600350b810140e050703000b8114480c0032003c5036950300700310150054210002c0e102e07004042603101100200103002c4001070003500040c40d0305880c0e4607101c244192008200b005d50700d03e4050a403540d8010000082b00340103074030003507900502c1460128100003103030001482d071000c5544030784902e1391180802e22141340 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 930082221 1250 930080971 930081007
    0x6050405210703030c11030f0c0f030a0f03050708040b0a0512061c0b0c0d02072307080d0503070903051f0b040b0f04020f1c05091204031e0c050a0605 66
    0x2070319494490908860196032503a520035030000904000341c50b1040400c0000900640321103c0000702582e11040074815440c1d540d42280b10424451044d8450a942034100803401c0442c0d80c0e080380c0c2c003c40022140e1015a099802100101d4090104020004203c4c4155010f01000b05091b41d03603035500c0c040100c1d20010b501002d0304130f0703110f8214207480c42d041452801108481c00e85c08288560f4540e55070510620341d01922091002c80c0740001140010403080c14203d0840b18417042682c1c04d005280b200c076641e14a842c1c0208080740c1c0c801709070100910700030400b840c2d0065140c81d00050032910395075010704201080c400ca4400580c80c804294041d5254041d01c028480d095800b0082e0500700d100040e4082c103202c030742c64000c6a0020380c406001400504a5155468202134220ba60403803c040e440204800c645814660040308401042500c40004440c03c0b070390009090041d00c00c043c1140040a80040c100700c4490144540000f8691030f82100d8100038000707511204d032101d07515515054100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 930083471 1250 930082221 930082249
    0xe101713020901091e1104090f0b0a2c04110607050a030e0f060a0804020402160b09010507021207060507020f0607171503070b0d3b01052202060d0606050405 69
    0x745c02d0100000c81003404130034050769218916000300e2092002c4542450b00c2c452500912541030420030403000c0f00d078040d040000d080c001540d20300c141d01d40c0c443e40e40601d4980c880c580115500c028111300000707a80b806070300750094001c0320200c19200190700007400c4d50340406ea04680c0c40e00041134940030300d60040e54154071324805039440c11040700c4410010700c107882641c1e0b403a01800306c3ca001003429512240e0540300303d64904508008550340c141000802c0030400c0b2201640380d070070240050310180c40441c83c0c20080c160040c5e814280301040d91000c0142100800000451141d144000000442009018094495a00c0e4944101c403001134150b00701c0c0005225090b030b4002e0580c0c40340350340c60014926017103480d4040c0440d00ca0300240c0310b80c1d0150804000b0201041d04051408001c80b00d040c07484043c2400681883c4178a414101e0010700780c0c0d10403203034800107010a2250490400c0b17029404100688024202443d004183c000c400c103c640030b400200001d0000b00f0b091042c2e041201c5003441c08 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 930084721 1250 930083471 930083489
    0xf0501050108070c03030b040c020c10030209010503010302040f020d0c0f0917210d1b030c030509060c0f09060304110f0d05100b06040302030303070c20010e101713020901 75
    0x15814800060030008010b803590f030420001c2900c02040c1480380e4081d440c0361034014800d01c0f01c0005076034001c0d030302d1b0704892601c3d100d00005541c01c00058080d200320b83c244c0006840d45421a0300e56000c010052048584400809408002d010004c01c864412501c0e5520541c6030301a141d031110700c0c0104034104d548c120b045165030f00f1000c481040343c0081c0c56199455241d0071081603444010b0b864411b03000d41000001d8403410308144244018041814a5000110f03980070000383c04000011400c4d03070800e54a218032134102c03401080306840c1d007100500351307017810500080c41c004406020594581c0125010744d40d600320049a05031a24001816118402d03003290100300b2810641c50b00d60301d1703541441200c2c0030160ba8581c400c0c1c00e40c0302c600548005513002419241c407441c200c4809002c50840403404c6410391006190006100035120044d8080001030303603203140602015003800030701c003800b640d035509001180c09002541c081442d80740d8420440b0003038507624900c2c05e106110761820706030081452 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 930085971 1250 930084721 930084731
    0x90e1909060e031c180816030e030d08040605060114070f1b09050621030a0c230115061806051c0204080f0f0a1a07030f0c091d010302060403021215011403010f 70
    0x802d280070147c0b229200c081282d1a9024400e180544103040c02ca407607150507008400ea01090540c00c010000d1040c2d000b4403040c03020790b036281d0044803003440c841c0c01c4207140c040920080022420007800802454864514154200c2100203000191001d6a10458010303403a10104882c9060407045040c0c041e60b0501e00c8600001d0b5503d0701600c0307000e0308411004000701050b918040c0900e070751302c1602d0541030301894080410901c50b45406010f04003910100001c1c2000001449031089840101801025080303102d114108402201d080d404943e03000c003828011525220140c00d01d200410081c00c00c00024400d56007040041818616070b41c40c0008181c101c1c038541c2e4003103583c1001d600344940301e41b00155440d64512500350001c084000412901501d441040014a9004a04001950410724aa00003851801d28505290109000094000342c092201300010305119104030020000c3e4000da03810300ba2100c041038039966090b48000404440303204580003034107080c800d03030012000700901840 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 930087221 1250 930085971 930085973
    0x615030f1a090c2a01152301030609060603150e0f070f170720030c030909040c23040f020a020c130b12030406090e1909060e031c18 58
    0x300c92000c41e440340900e0070726000501d2070b00f00c070044440ca06071040b0300602500d24203c410741100c12207100d5140561030110f4080a0124820140302114014909660940005d41c6500c9403504807001c90b605050302e580011500c0480e40c040c000140c4001c0d500084d007c03440c001488a010020b81c480e20180542d8003d000400d5a4100c440e548000d0314204107002c50021182114222440000c03800502d0360700d014098403d03400402024103946c00c4090302d034810000100643c40348076189103c48507038000c01a80b8441d06004501b190300030302418600d80f080d0799607000c03075413034100c500e000440d900c454a40002282c5094400e6803400591400214205424017401a651712055074107640300b0022460416034442c0d8032303003003907031a40c2c8040c201c0080c00904242d0507949070068080c09004c15100c0700042254400da00c2041c3c1304841140900111030b1108010400402c41803000343c071002c0d2140384030403600a00308000d102003502540707000704900c004210001100c6c1c03c0528485074502400c1688 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 930088471 1250 930087221 930087251
    0x60509090a030309151d1b0616020d0212031207030c020c09041704140f0108040c1a0f1b120301230406080114070305011a0f1b010615030f 61
    0x1c09941424002800d030154141801c0100d0440346850500781444070a00400100d510904030042d4801c1c00c6413154400d1701440450345010100c4240c0000003880046804031201001d4654680081c000c50405601c50300414003070501c04034410000d6200041c0c0d0081102e801850705d074040f1151804201e15070884500079154401103034030350311a000f0384002c54188105030201c1e840c43c10101c2c2000e90703107960b50440002c00d0803a5500d0144030740310807505402d42d54000c05040d4030981d072190080000b0350800c4003055000c9649a5800c1c4401c0c0c050006124403148440144002001c1c00880c03002080403009941c0b428444001c0c91288240c148010444007400b00c4c40707071411010b0410084450180c100c00700380189001e902c08075403582880300202e82c02c03120ba420580030f03107065071b424070160ba200c00d011190b0144070102d000501000b080709003109500039014107c171360a011044000c02048070045801e4801310782020031a2403c0310740f104011a0548121183c10100200520400380148007007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 930089721 1250 930088471 930088483
    0x801030b0f25030b120a06060902070c030b0901020f0a030501080c03070b0406050c0f01050411010813050703060f090c08030301060f020c06041a040e01030c050a061704022407060504050106050909 86
    0x14484039150b0000001516020350088800900094003000070461780c5484103540b04a0b144041d20080c3c64544c0c0030a1b0703290140212070013590405010362103075165580e122812a8000c1c030004c0b50f03550a016100e14886000000c015880441c2c0d008502035042c0150345080a00610201c0d22035408500304101400c007403c1698100d0f0309504080e5103031502006c0b058140007040e400200c40b54603100802c410009003d0b5016440142a40c49884942e0343c0e1290200840c01102c01a000b580502000c10004503990440056145c040501241c0110195540c0b500203071b10360440b02007174101200511035541e101110520180040c80180b0452407a00c1c00705201d44600d0281c51810754000c000040207201240c110740081580c405000c1966035203081c95404400503000c0d040c40346070700c1c40300002e010f03100f69106e4141440c1c90014480c1c40d11190308005c550307a000c580c00d048082d907044a84148d1303080741e0060070325180070f01008542490716107865400c449807034225503c1801c0c0d003814404100b40010b41 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 930090971 1250 930089721 930089761
    0x1a0102060610110601150e030a0f020913060c0e031b0d0809121b0a15051b1905010b040606020a420207020102010c0504050f060d110a0801030b0f 64
    0x205600310a8200c1c1c22200f640e483c0c0c400c402c691091200001e00100f181d486103002c405541e44003241c1c81003040402d601d5283d080800b61840600e810302102600d0589005600081a0043c500514070607640f54000c1d654001e4905c0c1c0403c2c4007201d1001c060400f800049401000014000d0170081e400002130141c591806010340440e40110341c040080d110904404e5100101c40102c9110f00c0e41c81241400010f01c034503030f2901070400071400141110201c404500b4005c000d80300c01c2d0400980013201204803105400700007803841002000d907107020305d4003414101c55010703100100e22002614184800e840c1554030120466100004640c0810250104a401201120074081480c0b104001c0c10910380c0848048110b01222881214008100381e0b0043c03112038401e800074840c41e4038414060318180030314401d136500a5455031485209203001c0c4000c041c2c0c48101440082e206040b040342d100d15412841d01e030710200315030400620074400004200340d440000130401201034640450500c840d40040b040d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 930092221 1250 930090971 930090979
    0x5060d0b090f0304030506090d030920130c12050f0c192307061505030616091d060a0b07080a030525080a0e0f0c060a02030409110a031a01020606 64
    0x400c031691000c2c03101d110740c103030090200c80d1141d460342006500d0ba80e0035625400903114070008142818000e00900070b015030041540d80c4011071072110021040d982c0c109055001e50203c010f1620160305102d03e09410a00c0d54465201c1d840c070f14030003001c40368044c105000c403181117010808900301520071250346180c001680001c03103508a1060740d04c1242c1c22021f0309000b488000000303e189010000d042c416004081c14003c000340340f40c0c588162000c6008803034158212000158901514030309130b00d85444545010450255642c942c1c400c0d42c43c1000c0c22106405450090245a151088004000e80009049145041d40076a540d050301d1145803c803005041e102c900003000c180e50b2030b0007c1c45203514040c603d00300c15160f50004000900c212441d0001901e040c01c0e030b25801b903000035000040a0b40e680101000d04120b400c000880d00a0740807081148010003010510071614050407003696182c40f1036030f80f80c0306449000740c00c2d100c07190966210010b4001518615a81c0060603a80210b4152 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 930093471 1250 930092221 930092243
    0x406020c010201480305061503100515120f0702212712101b02070308031f12050c31060512030403170702011e05070f140601050405060d 60
    0x138981d00ea0f2904201d58101c540440c0742c22001950942c001c2c1b8402c602c1101c0814046161000345e40da81d010540c1d668281c8100e1440134000303030821040041c101c00081081078109020415081c00f40d0740100e88481c125171440d018011207540400c103103100e400003080c8440710424500710104660241c1c03d680521414107040f40c00c0a107030400307510245101b02601c02d80800382c40504c981c1c0d23107000306419060028a884642c0215030388000003c0764125103a40906426455038881030b05940001e004039001d8551485440000c040061003030000701100b0380340205040031030070a42e0400040c1440e280c042c1c2d800342c0e44025807a0640740350198040c0c0c00503403c04181903000d0710100800c840e40006412030700c0030413141d82c0068004003500840e40b040c0030b0380b040301407400401c800764051608000c2c0030070400100b200e002000410b00c40f6480d030852825500b0041e0548942a480b80b0002065030891544051914000030a0000601401058505000300d04044002c1510701c2d60a01028200d04442c07 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 930094721 1250 930093471 930093551
    0xc090319020306130b0c0a120e0102310501211506171611010905160f050d0209040b0a0b190e090115060507050a021906021b010509040e1507050406020c010201 70
    0x2488c0d80c522140005804006299104c0d440714001d51011100c0200e081c00f10900e289800007c869540e011661441e42065031450840150340904030358074840940d6074070007207142c07824000380b0030100046041b807508144c80f486e140c00508108a41c80c10000b030421210300b0450580c1c01701c1004400b0807050710380b6442140444981c0e0340105020400102140108900c0c02c80c603141c070220803c2500c0c850f001059003207a0300c41c00c101d01c0040700b020013504244071600003000310754600c0c82594040c6070104081003807840b017000906400c1ca05650b441181b42076100600481c105101d0302036005c332488000b004008980e8044ca14808001d100d40802c100d40003850740100001400048840c0d5405400750325100503200d0152250007488c01080d006102d50784a1403094034500055410101068465034541008401404094450341074444103511078141010102c0346002e035607902c03034002c95446070340b0340c0d0404100909002c8002c4103981103a040c815502002e51a60a10030b04143c8448580a103c50403 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 930095971 1250 930094721 930094727
    0x40e04120225061101050615090d0c03030201090b06182403011b020f03030708040f06060305030a1806050f040b09040b0d0605011802070b07080c090319020306130b0c0a 74
    0x10b40c0b0503480c0044140c821081c0420164003040060300d1290711040342c0d4182003c4c410b07080311300072034a641e40000582c44022a2072902402060240c2c0041c0c0b940008101e5500c1d629401a0194000c40060b952007060405020300e04000540018040329402c00402c01556024404030001c1c040c100e0a018006e501600402c510b0643d418007070018000b4064105039485101e206a083d046c10800350080d502482c007503400100443c0d00c0b440190720303001c603151640d484038402c902c80d0307100440e0840d6840d400072011807020805012a20003545d94408441880e035000d100d05011507100c101404001c0c030200e0031000b40b41040c5c600380c1d030083c81010b880d240048e00007806400c018650503044800001c5c00420b0090540005060b224014482800c0704880e07604ca504070b1265a101400c01502030002c2420f443c071070b860054120301c00c8002c1030700f03207003050002030306040319062840044526840004e003142018003007540d0042c508070102c0c81403040c1c0d80b584810404000c110303542102c0002192804180 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 930097221 1250 930095971 930095983
    0x5090c0a110f0114010305060c0310120201030f0906091103030a020a02010c050a17071709060702040507090306180308011e0e10030f080301141207140a152102040e041202 75
    0x7212802801407a000e0b444e04180380e0b00a0000f61054021100000e0440c0304280403280282c11031048110300c0c91424110351640f0682d032104a04054a66040b100090710710701a20300040e0166100040d10440c40c03900f00a404a0800c209000780c01c2403000103201500803400410082d02800e00078010400351801506044046800905941c1da482d07200c2400e14000e005080114403803c00d5442c083e0b9a40601d004e14010003c515a1180c0c0230000b030340040c00e042e00560303086201e600301050100d40380c0da140c109541031841d8590800e80d18010070000d0590180c2c0844c0108224810a42582000144201d1001640c0512680f11b180301020541d80c0c14480c001400868101c40c4e00f0315000241c1c079007010b6541c800e2048400d030130700075060349129141810101c03491207240c800408001e0701e4111900d0941c0e03000610140e0000c00c0400010349906a1060240301350741950301d4450360940c25080828981122259a10551042c03205001c1c10940c645540c1d0026045400302c4444034064104900d040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 930098471 1250 930097221 930097243
    0x126060d050319050c070911161103010f150f0e0103060207081b030310051801060e01090803190f080c0702130906020c0705150c060f06180411090105090c0a11 70
    0x340c0d6010482c40c1d0f8590103000303080d00c3c45085098a01d40d42c1c3e507030510b10982c2e03100d200c003220010b42040360000e001c80c1d019504070340700d200d500340c0301c00000613400190071621950b50303260300c05858031403040601c40300c200284060032201404004190030300134100111001400b00400150340000c0c04018015600241da6200e41300119120300015030200721512a001640c140c4007031842c41e8404162450f0580f58104840310a18080c0006d071b2038a030080390948060030005060200c00400850301e5201803008003680b00061410920640c51400020808040d040404007081202c90612000d0350203002115140c540403104003075207001101c0d1080c000c128041c8014a0036200061941d13100d007020620000300d5000300c903401901988103800c00c074030313110380409600c2d107410110006020f207060704213141e00b1420180c122000c0c10180b0040c050021020364055401051044444901340340451405014040036211032015082000b0b940600c2d020746030115088c012100c660381d80002c4204095004c01d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 930099721 1250 930098471 930098497
    0xc0212300a1a040902090a0b190b0c0d020105071e050f04080c040f0e1011121f060c0b01050603180d120e0105060d0b10030b070801050126060d0503 65
    0x141c1001c0c050880100446644940c042c004041e425002d40303064403420511980241521860b80d41d00359490b001000c00040e500d40c84501d080a0100f030480031545d10002d0724001e880b1550b2442c00801c0a4600501c0c2c1c5103150842e0b0401c400c1042003603100580c0c00b0301c103800b802c8004103203600610a8800340507103c140b910550020a0009620318001400ea10b419002d4404120003004180c20314191004086040c90fa031b070180ca9415a0185c1c9076100001078041c0c0c002044c241400344080da1182d110942e415501c0c6202540a04007072680c40c19040c0c000c10040c1003030405007403c2c0e0740d90702c00744030140b09203032140a0201c00918040c03522900401d0300544c040982d45098000079018291510f03246149503a0381c6809500448688140b14407801901c00030810785200d4003e035644c40001c04020610050208522030000c0001d0200307000c6800313500c0980f00c03205550b040c0310005042e520080400343c4204501400400103800c400c240e9a000a401d81c2c120822403e0b60402c54598860300e0038000316 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 930100971 1250 930099721 930099817
    0x61b0c030303040f11100801050d0c0b030f180304080703120e0d05010c1409030703060b060d06060e0112092a030c0f091103091207020d1b030201030c0212 68
    0x4000c9041c404c5a5018030403007008030190440380901185000d2000c1800100f070b182d40050100d4504012070030030840c42200d200103100e40302c0c251401c0070341094548603240c0200c00140005c0190441d801e1041940c0c410095007480d1030012515504e040510020f0408420740044d02680d512031100710ba240e0f80701a2904a01d0421458441d00070a0010403240010700c109603220501d0580300101e03036108000074024982103040d5140c2000901d0210348003a4003071001c203e084038080142c002e5900400c5031f0b0b2200c0b541e40c40260700140944400300e401c020203914100b5918001007000740d0304003066003001c0aa40454641c3d0801c0e0849900315040640301030044000041c05a8501041800340c0307483d00018002101480d4404007280411343d012a1141c0040c1005600d0540e00030151603002d000600e00301400107207890b030800184600c0c0c40485e003611942e801b4010340d609801980040359045c4010001610b4400a4030414068032170740d5002c20449500b8520030035407c000c20120704a0580d06151 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 930102221 1250 930100971 930100973
    0x516060504063e0f0909090a0c030b010905010636180f060602010b06030c0d0f02040810050c0a020703031b050d120c050f040302010513090203090d0206060906061b0c03030304 77
    0xa0607a42140c15580d0703aa42c2c3c00e074030f40c0444091405450340100202e40b00c50070100c0384010003c003504004c11349007991003010302c91b03c0809c0c1444603640c0114095046107140b941003124413010703144141c005034103008903612136a18401d40d15040e0500c544582004001c007050004c2581e020080d0f03a4415a281244200c259040450940c4140c9803c1e034003071800c20010340d545105900365011070104a500200070f00009040783d4400703004111804c0c43e03000000b80c0600c0c03c60140c01b26046a0400c981580c08607159a110306194828a40c10a10034442c85003080d484410095540b4201e00008082000310804408000b14078101140381a500c2410340346107282d5804000c0c42010710050301e4600034105280c2045190041c02140c02400c0071300c40c2c0d24602030464005450580c00b060302e0321800d0b040c81000003805e01162014500404484019102120443c2070007854034102038103040c4194115418085260b4607901101c40c0c013200c001b444502101c03403022590412510406450300340c040002000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 930103471 1250 930102221 930102281
    0xe0a0608010b090708010b0d06090609140a1109010e03031314030706110d1103070b04060209040609060b0406080421210c08150d151a01051606050406 66
    0x1405036580c0100801140d1008010040010410745004000c40d041100501c401e0350700b080209080b00c070220020441a6886810404036100d0f980201e01003595065a000c111011503035940c2c0001c1c9008040c89402d203243c0070800c01c1c0c80307641c0c0800d060007280415941203072400c2c001c0c3c03003000c10300b228103c00c41c0340e507030001d0201c80000c0030041d4402d015044001c00e00d03a0140d030200b41617001610007003034013035007044c42921104031035010200503100c140520f0001803901440f01d44910b110301c4015884200ca0801c1c0400da0f0090f400401800381451006d0104460b69001e5900b142d0062905900c40e40751800d25284816501c0031105024613a601d02050040d0480f00c0c00301136405e600c00d140c10324491500c40c60110307071042c50040300040391a804a04a9400d20386d141f11602c5000304004180700c01c0740d561120a040800e4401030150b00c0d08070042c44007014038141034034400c007820070a19284101a414034050a2044003c06507940e0324003080500043c1d90148400b01030b4901c000314441c41c010a01 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 930104721 1250 930103471 930103481
    0x90e0c01030b180f060117150102210702040203060103060308030411031209211218030106080c13020708161506091107060e1006030305072607080a090e0a 68
    0x10501003030038200b00c81628208020f00384449044024030020f00d8a4941d8129002d400181c0303c54104200703004592041c10a1032a0309015000600d00b545000b1700741000642030241c02d01a83c01040c6140603d812040c02c40703411500081d070304036401642c80d0f94480c0140c00408107030704046d200d8500841081b080000ba00112a0014001c408036a00320101481c02c3c41148101c000c030640002c031091041051541600c3c0000400c4616015115481500006c9000b6034100c98003a440b0202e500c440108035003020721a84003e04690006000b14140480214014508800040c41c4140c1c1c000341003014088904169111041003120041c1e00e01e200d07080090a861828400700c003440d1522500280310710301b502c01c10000301c806607580c030306081e03150300c601d4000d02d8941520700d858001c400416126108911461010b184a83c907465100c00c12410101c00c18030880750b03002000c55031801101941010141581d07001a848095147e4603c4525002c45074068640d00c508c0516802200707000c040301303058100d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 930105971 1250 930104721 930104743
    0x4030305030702070509061302160519020111010507021905010b10050406030f050f2202090c0310060905063007110d030b10110f0a0605040c0b19030c0306090e 70
    0x844c0ca0f800e454808020410105665040c0e06c02d004400103c21320310307a82c0182c00c100c2010071646029019075120385040004108844414441116071801150f800c440e80c8010101c10784002c00c2140703080342004e0340d5210101e036000c400c441c501545004020b030035000034200007005001c2c0510b450b151800a000c40d0031600420010a092403080002d07040140300d80351003800d21604000c0c8076154002e498000d945c1c0303000f5065034111052510400344e00c4050005006081c1000d010b560380c680414007080d01e155580000e0208401d54a04001a40d601015120900305091803261031301900c40503d150550b40d82d51010302c8650078006c10081642003240300132203c0117102030ba61000c402003411400c4660312005c0791b070700004c240c806805182c4108249070802d6081c200316490002003c008500d4a110300108403090740e12003041002b0010a0302000004280c2924228240002400c0010803090050b0741007007015540c04030301c80c10601c240c02010086c216010204540014203500c25201c1e0340c5502 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 930107221 1250 930105971 930105973
    0x90406060203070f06050606160b0f070c030e060f040314010b041a01050d2d1b11030a0c15240501090b03040b1302180a0e06100303121104030305030702 67
    0xa40015100e00101c1111034441d4401103107034603025035940310001070001405050b0098014005c540b56240e50a4040314110b000d001818528903002c01002905d110081401041080000c400350001350000c5240c00c1000e400c4555645a60070300d80d45082c1c6006540c40038103a0000c0c40d582e00e01c0b00c02d041d40540558902541e0620041811500b141c0c59040c10281c6140010ba08000e60042c40070207500c65030500c82010742c400e5041c007880b81320b851600341d200070070a100f0340c0e9442034503070111085102c449942c2c43c40c144a900c5246a84440340ca902584040209000f9440000d0041110b0248e42c081814400c050421401c1c46400b00868200c02c01c1980821801c1c0021000c1400e41c00780400c0400c6400384400c0502d50303551551540c0034100054055030010181072046c80040e915600300010100754500c0c00749940c90000711502c2a10440b01c6082402d030490000e0000c0b6606a00b018010b0726014100100c8540c41007004400400f080c60381e4055100b8045004400c2550103c020350089007d54 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 930108471 1250 930107221 930107231
    0x902041b140c10021308010e100b0f06070609060608160521070506071b060c113f0304031a100f0501111504051f111e1e0904 55
    0x10405a841d12940c007a0b44040d5001c1003128100000c1c40c0c004103c0d8503901004026465130f82c120190a4071000031070281c2e6600010001c0c3d0450000384112420030340c044424003407925800e00880d00314840c43c040506915201d161520902c001c507001540200300340f01c01c50b4900f506500d01c4070146a20360040c54400e01a400106c11109072201c40b050301c840180015250042c03401d8104042d50344504011552a80812266900c2191070f90084000b42070b50b845480b104101450800304c0c0c910004001440b030803d4024190401850380c0140c802c20100000d842c0141c191021107903641010010f807260148000100441003015101100411111801d007002558540110010001c1064050100d101000c40300400ca41e40c8180f480744a00400c20b0159000d184075400144070107541240c040d0f0b1030358071502d400c61071801c02c13003051440310f040c1600400c48000c2540d44607141780710b00c0304d07004494a032042101c9a6400240102c4440021650081c2480000f0700d5101883e9003260031090301c1140b0301 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 930109721 1250 930108471 930108497
    0xf09010b09041406090c0c0a06240b07170d0f060b0c070f0612020d020c030c15070309080318010e060f01060314090a1205091003050114060f0414040902041b 69
    0x44010500800c0b00800c1c02d482d07030755401041c06c1c5640061032403800c50300c2142c040c070300801c056214240710345403214805e11032200c3c1800d003602c40074042d43c00b0710200305040000101240d00b03010180f03070f44504126456601c91991822201500c030000c0c5540a492803c240060403003042401850b440000505454045503a46840601c070000741c85100046080d03081d001036910955402000b555001000c01420460b8000115103180c125151542c2540d100c81c0290448800d120700a5500c03003c01d240900217281c0a640c0d06500d4003001d0186e5035442e00c483c0070030b4550b50702904420001d241510446100c3d141a4100b940404428412080424076003016102c1d50313240c0312401e5206041803030041c004d000c0c1580d195407466001da003101d41000420300c4031040340d940300d4000340c10169a5680c040703101c3d410048503a503c0110b070102d291154404009419800641901f036a045a060120004000c00b0090200303021305035100b002503025282c00ca0074400c40c8074442c21a8440001c5988032104a0a4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 930110971 1250 930109721 930109751
    0x20210907031e02010201060f060c0b0a0216020d0f0209240105090607020f040b0a090905010f090c17101404030e0409050c0d03020f0f010509060705130909020f09010b0904 75
    0x1440c000a001e00c590700c648002d40d04035403400299114810b20001440b165207207506c00c42d105041d00b01e400000c100c86480420320500302c0c1c0da2900600c401d0b00c11440d01000822241d0f00d0340040f28000c3c0200319980c00482404052141c1690054018188809600d411180d021402a54205c403504105030b249640101d0b510500036100e2001c4083d000614080d42c43d002c2081058404009a40c4161200842d641c01e845820b03011006040084010400e01d06900c0c10354251072480301c1080407103207001c0941c40842c45010b500e0b41150503038140444000c445c0d1700514201460001c0541d07002d814050340d054906ca80030031091140d030280e514800111102e8007040280c4007070700c10240140e8041450504036141c03032030807a10b03010700c20300484100b00007455902d420070304800200d6503242d40d100d040000510045c4010307a071207856403900e640342842940054030603207418000c01c55079035510032840c421503d6141109203519802050004290313555548000e4940c000c50303085010b9800c0040d030020001c0b07 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 930112221 1250 930110971 930110983
    0xe090d0908010b0315180d0806030c18010e04050f0105130c08010c091509050d050109030e03150c0d0608150709050103110906030a110304050105040b1003030e04202109 74
    0x207402800390180c0c1c658507007810f20017040a4240f040c0c81021800803290340c00304112103a406070301074440e000c072844e00000b05814102c1c07aa25041c01120a500b03074103000c0d080e910070141900e09042601c465900c450612524051448210a42542c030741024001c0c815010031425481d40e129a040c620050340746d21543d0f0a0324529420303203010400c0c0b0442400f66501d00780c40700c411600d46260070318a813a07866001070380b0448006402e84941c2d5590f01007106041e441814822040001c5d001441c1441d045480c0740c52211005018505941010a806000c034113150000801031401c00102c6044542d0622016080c807410341d00e801c003142c03840310b001070702f940a0b01035088041c0c6040e1049051441450501c840c0d5440105040182c070380e601000d141c0b000191015500950140c0d00001c0c1520b071501e0040031801c00500014942804040e0800c0082ea010045480196042d81c0100d8260300368460912a1803104010110f80c1da03011603080030b030280440711850804151955a809034684412640d00d0328 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 930113471 1250 930112221 930112241
    0x6030d0f080402100302090307090e01050901050c1b0a021008070215090c1c0b16020106080c060a0f09051e0f120c211504030314010e011701060e090d090801 69
    0x8542038000b03409460060221260100107040251a298a500001c0d04082e1140c010080017a42c1e030f01c559888010902c07030680d01060410082281c2e05000c911311043d0302941c9071003c109458208482110320080c080d4500d50395003c0c2c800820401c81d28030107031035280d048070418010320510300c6400611404400d05405002c21030040c190480652052124403070722940d000234441c2d034496030000003600d88002548582a03920f0400f8422160301c01c024250b40b003a9010400c540d01440f980c030401e40d10b400456aa01d82d032800c1996030344800c868140d40580c0d4651200303070720511030465106842c0c210a4401d040e2a01152400c030413a200d40c080101d0030606043c1c5002e47d03480a1400c07082410b0201e84a24599054209942c6119101100c03900e403003684000404014141f101b0b0108060b0180500350000380300c400443c1c16076040800700c010120051180d034500040b81d20200b51411000c0d032021019001441a00100b4542041132039550030840c4c0316140011020400040c04c41c6040c031486041d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 930114721 1250 930113471 930113477
    0x9090f01050a090e19050f060a06050906120f0f0c030f03040305030d0c020f0109030207180203060d022b05010501030b01050607110105031e07020606090109181e0c080606030d0f 78
    0x4030f007011541001090003901800e100e100302e40b003005490364415aa40170491240c0d009005844c1d90342009410102c1c0607103080710b624208030050003559a40118154002829102880ba140003001110300d07004100301e6804e84e50260b0034446072900004a0a407080800a40c101c82d4155841450a5683c0c8a58403015200750410301402c001910981c20080b0301c1501807040b1440740d1840400d00b0b00310b901c2c1000440240c0d1081074200708028414100006a1142c4d0310110304603d80440407407460642851f009104031115066402c00700c1c008101009090010402c3c024140ba2500d8064020324080c0019585051100700024062070a082101d201d50f03030160031040c03102049001034071f10b074201600c903800f222884000b2403601060842d4840c46079400390300400107400c15106208403500181c001d02c1a41c1d0a114840c0c9001c03d20a1500807800e902103401d012004c1e13141e606501c850148480284140900400001c001d000051214001ca00c11010755050b50840c100039074040f02e80100703040c04 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 930115971 1250 930114721 930114739
    0x150b06070b0c090d08040b0d1103010305371a0a0510030f031e05130501020d09030f0f0209010303020a1208070c030f0207080601120507150905090408090d0809090f0105 74
    0x8800040b0152510650181508400b99400ea44581441d00513400182c90640b01245c020512042030148212103251641000d16550560300c44d6500c850640340c018204900c4608409000c8142c50101c011003240120b12841d00300d030525008880300104481800080703501e07404181c0b105194031415000c2c1404118aa00c00751031541d4540300e5a811500642c2405001685000700009810315604607400984e201c07985c4410111006920300e8042e0070a50441d44a980100742c0c49400001d000256030300701c0c0000b010000d25107488014004103500003504890350740000420036800080f0040c07814419848015140e8111900f140c03442c500300c4080300044d9105403840c020a0081c017490507504410320686003102c2d1a1180c02d03180c00401c0c0c0c80b0400c1c13485909580c01c1884414000e22000d13000004200801c00c141c400024220b4001d4003c3c02d215030540d402040800040c2421650b40103809851070305250940c1c20701d4840d0f9040002c1d214001c00500000568900044464a060303500042065171 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 930117221 1250 930115971 930115981
    0x9030c060f010f1514030a090204050708040206031b0c0a060c021504050c010c020d0203010903110c091b0a200105060a0b032a0409061502010c020f03030c1c0207150b06070b 76
    0x205100030501304505002e2006003007508218440300840c8500100140030880c90358510502c0210342000b846481000350742028407005075294000c0702c1c0c200e0010040d49182c0c0801e5040b68019110700c0c00a0551341c030801d040a4200030858102d9081d4800c9a001c2d200b100c00c0540000d5400700d82160002e0060700f111a11284940c007481d503595081d40040d080c114019596400319017164103d0700164085000d00007a40307440d2104010701003852109584001135030410015101024203515443d944c6440003040400305140301c0c45800107508901502100040420300c0040d00070705054030018010306030440d020030310202c16401c8a006192148443c8034040710714003c200352041c0184e40e840081d504000c0060707407045a0003070380094015038051034440c08102d00040d08540212180b00255000b030b1007808400b4602105413a8000241030004e581c034032590030340308400313900c481c0c60140300e501c0480c280040c0480580b0020020401c0d01041141c0300020081020394010240004c181c0c00f075040003c0e03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 930118471 1250 930117221 930117239
    0x1b060c02010c0c0b070c0302090112022103090904080a09050607030e0d060b1003050a1d0712051501060e040e28020414090604110a0f05061e0309030c060f010f 70
    0x14a46a01814416103e1a29803030819004c1e80060804d681c1010801c6040c015481c000e014640100341c00285550f0782e441e154085000402411400b1040c18209414603103c54018012642e501d500100640410f14241c54001c0290700004103080003d0444030001c10b07642080d07000c58035001d0305510740c070016000300f0042003102a80440100c171515190301c1c203502c1c075460f4510314444808481e1804076161520580303650854014030020302d03039164610480d0940100120b04401940d00c011181c00d101c03030950410382d2074920355807662001180c1c0e03400001880f42c0c0c4800c40860450049074180411850916600c0c0e036101c0e0741c40c0c040d032585114840001d00341d04c41c1407081411480504041104072000302084450241140c070130440d07400c400c3c204010030010000c9100c008200700c820b40030440c05c0c051200154143c60055501414002519900207000700582081c8049201c00e45c07690392030020619520f907000911160402e200d2680421a4a0300c104480c0c1c3c145e0300403002d200880d910f015050 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 930119721 1250 930118471 930118487
    0x317010803040303320409092006041502150106090e060108040b060f010e0d06140f0c0714010e0625090b030a110408070603050f22030e0a0b161b060c0201 68
    0x20140c03c81d400d217000248200e0003d4070003403030004e00c0001e0000a07400c100301010049480c50003101c0404001a10303642e102e1080d03505541d484603c1c80c64000c9040000ea152510420074546010719200c000140a9031090303821054848050031105503458003001515200744c25180149004201c80019100d418401000040c884051500b441554210000714100c51145901600d605407980f04841210b44c5640c00150031160411700840a89010600912240203083c4010200b40d10f4a6000741091b400f5041400d854408805480390340c101840702c1d641c400d50707030424008603601507039051144601070070800088455030401240745954003ca01002088103c1001c001d10710240400719054408120110241819440c00119030410b10301c0c074010308100520312040d003003844640101c0c4c519a205003400060703041c00d01c0c2c5501020100007803101c02c0305412459906002042540e0101c00d80b41c40d03e0580740c000c00c64017002640765402c032911000240201c2d00403a0390742c504131006500c20060 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 930120971 1250 930119721 930119777
    0x10903080412261f081b06040506030a0e01110a1e03060803121e010602190203012d0606090302030a0b1009110d0b03010218130902030a0317010803040303 68
    0xd0b4105034650300c0140e0700f02900d15106103403e81c42408000e80c10003860042401460b0300e500d0342c811140740401d4107603144480e5406d0804000c242c4440f240c903841d56000d41d005401c0c02022680c803481d1840303400d0000e116210041c1200d600b0b00071040080485001240d00f801d042d50360b201025940c1000c041000a11405140d0406640760700c005198003090014141c0000000612002801c0030071808810101c841680164052840010891181c00141e88180000105c4410060074014000603004003280711079108464407011514002e50303103e40c61051750441c0000100601c80c4c5661085407900d40c43c0c00006d41561240e0707091030105020107a540d078015880200e091013280c80f0448581518014402045449000704000074ae0304240d00070441d802000381c00031814101c0300c902c0354151310002404240211000988202d5060701a0050a151500502103c540010030314004114440c44104205c040c0c2103031001141e2294040200c5007203d4042e92030f003c0b840c06c054110b172001c0c0200c400b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 930122221 1250 930120971 930120977
    0xa050c150a1407020307031a0a0519051f180e0304030f0221010c080105121b01120902062d0f0f2203051b060f12091e0703030f02010903080412 63
    0x3000800607178040140c0720107580318040c03441e04d03c8000a048401448090507104416050104001040f20544069404ca6000c92804200303900d42d40004a006501d61440d004410005000840c5401e040da910400d00458800100700201140c19031036200d004502004141d607059000d90000740c684003003452903241c15100321441e450381d081001c60854100c010080f011600d010010000c915280300381040894000015001e1a08005540310b09900d900c1111810710031402880e0302d91110542c0000c8505078058905942c40b4000300c4d25050344500c000c040c1c4240f44007a4030100300f44113490103a03402008110792403400c1c0343d00f510b20042c0540110400c02c1c244202c500344280c40700703803600d8600000c50049000c0e1600503040c0751440c1080310864211802008c041010200c4542c40000311500001216106821515460203150810034803a081070310a21900c40c40c0c09031301c0400310b00003085a1003525040340d44085e03280260300781e400d40b85001d40803c11140014010464a80600241c14260700d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 930123471 1250 930122221 930122227
    0x2130801020319052202012f060109060b0f030c09040b0603130b01140102060610031d1b01080c1b1e010209120c0d14120c0a050c150a14 60
    0x4603003240c108480d41c2903c01c1c45655520825042d40c8071307080e04a48046481d26140203c00c10105000f17010b00c90007410820781b005031105613600d040001802a043e880d090000076180c40b4100d5170350000303001d4410a145071140c00103200041c003044a08040c0d84be0030035401e6548003150018140c20240c2c2041d0841d848070f131a44510ba23615001188104840c0e5100d42e04200d02e41007401250388140c000c040500a283c840c849283c0c1c000849550000b4110340c01610b500c054281180a41007440d040c0c15400000035448a9541c4080b92800902403e08800060546804011901082e054881d411140350401c4100c1d036003085001c07414203060341d0100f200c030b5800c1205485c814085159401120503580410414003171b2824004030042c8903020b40041146403038103400500546000d207802042c91034070180c040d031003d50600070740101004110510340c43e1101c0503030380da860700c0200708100e649008042071030340e8a2401503139440215409864403418051090741c1544c403240d204101628080080c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 930124721 1250 930123471 930123479
    0x6020409110304031229030123010e1605041202150a050c15040809121609020322200a030606120507080d2312040b100506040f0501030213 61
    0x34054600150145440982ea0b8a81410010010800800719580780d909100032504001030a0300d030484104c4107240080402d1a401000038010b02c55220550190110060032120307128201d40024102e0b4008940320000d5924cc0b2000c000c1024200f0303c59010030b1042c8004e01c111841c4808280d01c503407001e402c880701e00e40340040340d084540211101a0003c3c00010399203e05100502c400040d1040100d044915802c0983c0d41c90b03040d01a044440d07000d040ca0501101070344000300f0550b15480085004500850b03121001000a907204403402d90042c101d0241701000302c201e0302c0c0c00c03134100c0c1d0308095140e0600e0301c0607035980200031415010960012603c60040049070b0300d0b06c1030500800501c60a4004a581854051304025041e88850400d400c6015a01642500070601d5440059100c440c2c00d800c00c2e01021b11841805022101d00d1145010350820041000740d01e0210b005e47e0b242c103400303540c043c1e0750340420010307100300d0107040d0603400740e450208100c0d4040e070090b00c1e800700e448401c07896040d12 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 930125971 1250 930124721 930124739
    0x50904080f07050709050a0b060f0306040504050307060c0e010306060c02030a1205040509090a02011e0e1c0b07030605041b0909020a02011d06010504150b190e030a050a0b101a0304060204 82
    0x1194001a4985941d030060081f40320342c43c41001034403401034648504001c450780300004903000040c4810b000726140c0700000c040040503c111940756522030b4007000803880c0c01e41d00501041215031075030f0207e4900700020603024024000c010307249078001d00801d560006076848083c242c4000f00344e10284076050102080695810f0354041c4185280401401041c071039000040c03c0c081000e04030303500112110305130420301e94405e84d01020460184c0380e805824201103034000790180d468202a03c032908803002e1201c02c5034035402000448038112011700290341c1c1440d811081820384a40100402d80d40d5500f0025101c65030040c5c00d6a804500000401904003c005842c0e020804601d00d000e4102400601103480c00f4841e960841002d04140360300181080c2e0700c1756581c420740c00c120074948003840c40d0306200762040d090702d059040e025061f50403044032440e1685da22511174104440c0000508000f039000f0081c3d01c80c01081700c0e221001e5600070000203c278045141d1016005450f510740800010510400c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 930127221 1250 930125971 930125983
    0x16021509030a2003010c120f020903060c0a050f030f0a061410080411271302101209060e010c0e0d1e0f02040207030e0f0a0311010e040216030306031b050904080f0705 73
    0x1a560b2643e415600407d81440700301d91003071a2010030284140000b46041d200020304e291311070980c40066a558845400030340b90b5024030ba05071500b8040001c01c120820080030b8105000e07042c6103105110003071b103d1110141300c1001c0312100d50440b41d240d03642e50321284203101c03040e0400d01032855200c910a5005c04140741e2031000d50a440d0f9240c5014252240c0c09104003007590189481003a00035803085540010301008240500340c0800102c0b0400c210100a90f40c0303c486031952006042140c4044c2000d02c901a050f2561180003003502c091411460741020304684c0c403003a911061a140307100424103044901e5000c08029540f030780784c108900c0010384461000b04603203802034640719000d810000801c10813a03d080256409002200c4080001030001668520644401d00705069440c0f806000315000b8065034064180c17104070b03180000203068040d400401603a006103030030b0701102440561441c500045118081c0c00c07512000020300030600d50405090012048003004d880c1002c1e6403500c0349420703 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 930128471 1250 930127221 930127241
    0x1050910150503060903070308070c030c0b0a15030507080f0102120402061c020a0e10170a1d1603060c210b0f031b0108010f0e13021516021509030a200301 68
    0x30b1b20014440301455000f924095100d5080d01d070000018040c0d9170010000c130071400c0004d1402280700301050041003160003601f28100640071403441d841d40ca0a01d280d41c1c400d030384a49489801261141c021401060085590040c10582c5010480d12140d0a00c007159202101c01410340c1400d8241c09014141c41c001454101c0c4259a408c81c0805c2c2d0700104181150003004031004e00020000d80284603e01801c51640020f03110340c001103801d250f40081030f9280068500040320701500e041b4442940326900d241c3e0903240110010040d0311507110007540c0c03a030f102848203203d140020002e040e40b4a21504403144d01321000e80882c8103100f04501003882c01014400100c04480c116a02028a59100340d04900401414850503201c5160144101c41d181000c0d00700004950452100030654881c80b0085440551f0070704156503d100602d4111061840035200b03e129421000e942101124240d0650703c00000083c094290290350340e6803480c040041c000c201818454a04a0840d1540c081c0b160f56000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 930129721 1250 930128471 930128473
    0x2a0f030f0c0c01091d040201030b0a060201051501030c0212031005060f09151c0b0f2707021c08040f080c030408250b030a0e1902030f010509101505030609 68
    0xa5110407201820007042c021a40e0402541030130400c40000312144050201309020320701680380d1100e0004901400352035900c19000b501c40300000034459070540c0a1886010940e4590201a031042c00450680d12500c1e180340050340144a000c404240503c011a005a5840106640c65a480012440da130b00500d0206e441c000c03000c18404c4140c1010101e00c2c0c0450394120f0068a040120803004441042e208004004960780c0d60404000342c0f24004ae00f038001c000201191640881c1c400704c801d00075002402282c0404c0787c50f010450080c000242d01c7d008206600c1403100806080c034003207581c4800208151010603003d03044c500840c0703180300241386103010500615907032800c01130203628021080b100071005c40c11040c0100c401c031980320704000598001003400360b0fa0f91a007111270303400340007107044912031406000f001d41401501040302d1007016109405039445607011b100d0640c202c407012180e040717058100320666100d81c0711650105513040c3c015100703c0c2d80d00d902c0f40e01103481e02c40e04585c84051 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 930130971 1250 930129721 930129727
    0xf1701150f02010b010518010302040810051012021003050c1e040f120510050402132301060302070c090b04094407151d0601060908032a0f030f 63
    0x9a030300582126104455000138481d0300c00c4400002c04900c5030040c0d0503001421342d0b0900825a100750102e400903d507010480304034021154407040148000d8601c1c14100344190000944000d1a20160f007580390001c1c2165100c14100301c00ba40541070003405480b040404000100001524420200d110f1280180590300e5a041c043e0840102405801001c2c0c00e24040059400040f00040d0702c1420b00758060000c285c2e40c58a101090700c00a84400148020342440c1c0d2851100c00c0380f00c1c0c6a0310392447d4240c00c0c6c0c0243d07610341c0d05408034030079123070090507944d5161400c1c0300c004d0a64000c3e0b000d80303002820006031307421192540440840c0207120b030000d555103511901101144503261290050101e580d10390280415813400c00707140f081c11030080c90900d07a1100300c42030b80c1c6d4540c000c9841d510b00740c91641c000c0351851840c0361200424010303c0702040c03100401140c400c03000401e1b180e145002062080d24850401c201c009900340304203400c1203038451390407440103070101030001c1e01070485ca833100035031 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 930132221 1250 930130971 930131009
    0x7060612050708011116060c0903140309090f04031b080d0c030b03010b01090503280606080a03020f010b1c050709060b180f06120406060f17010f0e0a030f1701 70
    0x10179982499034190391541d05021940c03803c1707500d5221504a99010100180d840300004040d40d8602103640042e146c05050089009410b2020005101d41481285c000c082c55454000441251009560290002e884d29400d003c5645c807000888001c9802540801e042c030047e02c0d04c50f8240c890300c420550000380c68600226442c01c090042c101e00310024248000b900d03040c900401e0703440001c0c00740d60b100703403d0b0320181d401c2c00c04111110058090304014180041510768041560b6822074038000c40043c852200d4a44607001d042c40b41e40c1d4049030080550301214004c80e91060111122882640c4501485000193341c492f207103e000c0040600b849440d450310b103c1c903034010402000344501c1c0d0040203101801c40c295928142101c12a40c1442d40542294030307103007001700040c507850300011164142d206001c02c404a00381610096103a1240c02400740d0040c8440000079200c05400c0d0390910781c40502e0f0035000902401d83c049495201c1d1818041203400303007501080a280c2070f408000e4245419370b03414 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 930133471 1250 930132221 930132223
    0x40c0e060313031103310f030f0b070923061204060b130c0203250f080d0b19050609012d031118121504110406050a030b04020607060612050708 63
    0xba14000c1d03143c024500b801390140903441041c500702506c0c40b1540400c0e03203501802c03900c950700070050b0016400c2401d40d103450f490140d400402d200e20a441007a400343c002804a88140d80700390503945007a0081c00f201418840c2c2c103807106810090700d03910075001e0003181390411452380403521490145002141840c448800d0013a54548900e44880c8c03d8180310480826139000400c540490540c60542076200e400c8004880c0103000c41e0100800703440c80c4015400a000d00340000d40340d000d250b00b50820034001d0640c20040300c0442c0890039074240008001c100503d15144016210840c8181418032282c02000017180343d10f00039100c40f264000c80c40c0d400c40c0b4103c1d458443ea0800240185145141a24448a1a030f200c404400c1c0781d07100f03500c102d003c130035180d4040c00b0550f07048003070030489801c07410701d450040240e01001070360703074041d03854480001520f02d8074180c680100ea400121407030454940d0740921809602004003a500c0c030f0b44030317100064010b00f03040c0c00e6402d8601130000b829099007450b12003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 930134721 1250 930133471 930133487
    0x4050c0d11032e0806040506060a06030204180504080f0724050105030c0d17120a0c090e040602030438100b040504090606050909030406110d0c02040c0e06031303 71
    0x302040150034010803610301450983d442241d143c150002050441c00344000b03641c440c00e508044218010a401d010400c0000180180070314800c407880380307041e6110700b001c40403801584100c1200000c240c1c401e80e4a107040707a2041e90041e0003807031494501401d03c0340b1001c15500180040f904440a032000c44000104141008084610600f003032115500d05400242d40b403007608199403241004218074020440340d450b150b2880c0040410b505c0c3c0303c418142142d0b0310828111881c442503810003c94080d403601c102c890b00c003601c910b141e481880f911142c070740c0c2000303420007401260030800903c069204044e040b0208160702085a600c0c942c80b81c18101480301158028180ca00092404071051044041e00004c1e10706860040c0d070001450980341c01c01c58040d100340da001036008215a0140408400040024001d44d5100d4613040d9500c2111359000d503aa032498000040000d864040e05001880d203500829403049103442d004c1551189080003814075401507038246050b50f90030340301408041c0c00080b0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 930135971 1250 930134721 930134741
    0xa030803100e060d030f0c2f12060115020f01050f1e0c1b03040e01060507120219080f070506070513090b0607030e0d0c0f0f050d23010b04050c0d 64
    0x400aaa04000380030481a940952006052020070641c00b100c0600c20344031a140250230a0190003201187e484105a901103c01001200c680942e0303103080754148002d05014640b961801040d280e0328000350f46080841d220300b61402c60040402c60340c1000000d0007136070f00405150020191500b0001d00c102140000c200c40b80758a40340701020421101c070030006440c104914000034002ca041d603001c0540c01c5118a030000c021081000c000410f07c1540320b4041e241c52171007413810707071402e40816100741d07907491201d5040d10781c4c2c503c1034590b00001180c131800b402c0b104904c541c205040050756540c5a0411200b00d66500c00108080b80d41159841c0380030380e0100a0605080170004082208040b40c1c0c2c071f10680794080d00b4082400ac0e1042c0a44070542007440d80c9420003035928160307031904c0004014400c54402d08494074002100440c0781c5c9000c01c96105c07890760000748030086180708800c408802d198202540d056540c3c4420484c000e4890b0b010701807081200e00c940680d20b8844c2c1d480c2c0811981d442007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 930137221 1250 930135971 930135989
    0x11202031c02101b021b01050403080c0a050607020601121101030f0f09060c09050607260d090201351504020703180b031b0304020402160506043e0607020a03080310 72
    0xf041e00d034141c1c0125a01c8a040d28501c1c00d201c246190711b00680d030074400d6601c001c010420000e00035010304030126200003518410301c25242152140c041c202e940b44006e0044040700f014800e80980040e5010a83c0c2c1c29058041c1808a805400f04c01240e007100c004181d211092503c0b03200d4a02046118071401807280c0c16403c20aa543d81414042061401402001411001e4410345419140048011420502c46901440b0365400181c4031070005014020f008902040010480d0411010141c446a42d40045100c010325040c1da80708442c8841d0340060000ba401c649140e01c012aa40c484d80010302d0b03038034007030340760051840c50ba80792180e0406a1540800d02e080c00074002c1c08440e610840d08003582e00c440003a415100e031182c0c000a0000d00c580840343d801c9404815251080041c0444c2040c4118040c40004072261103d80c000806160007105108480206521040960407181c03408008814041c09503401c140c401c0d800328000315070681043c1ca076610301004001d910b450154446c0d028004801c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 930138471 1250 930137221 930137261
    0x7030c020309060d0f020310060909090f0b0a090507060c02011806092d090509210f1b030a0c0c0f05010e06030429010510080f011202031c0210 63
    0x10402074a03802031540843c0b19140c0003814822207120b540010710106401401195a4140660100303690200e912800020900c0d611000a2176a801e102d038296030303500046140c05008403951000c040c10401400c80d0400c0b40d0340c2c5010707008500c08011001c0500041c1c1c0312040c4a080a000140c2186940300e15445040c4019400344481d9901040a80468003d00c2c0801c03035904030007400c041044086d0b0284410346840200010380c0c005035400280c02009208140c1e8007044100b80c01c007012003c40500c0e80c9203000200020a20200d118000340141c40321000104100c203d02c410040c2942d00c00f0105400040c4220000d00c240303d180c01c080401400024030020780c0071710b0000007070301c212141d10180d881000044001000d10802d51508903521040904110508820080503020032000b80601070003880710354807500e01c480c014080c0d58050351384910100726076884c0c4209a880e07901c0b458401c17a0507020741c1c258103808071509008419001580e40142c0030340c0188200113003c9420310200400401211 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 930139721 1250 930138471 930138491
    0x6041514011416120203070b071d0f151309060b09010206061206010608070e0d030f0206100308030406050903040518010504051006050307300902280b070201020c180f0703 75
    0x241d40300c40c5a0540c4451003502603050401300b6403c0d40110a40503003120309030001c001c81030380c0c8404485841c8214001d030000204100007440464412400d004e604107014030284801340441202514500440a2403d0300d000d840720411419140c09521007004020007144d150200c0da0140443c0b507110700185c0707008400102c00c2202d5030f51880e041c455101404003902c04100341c24841d0f0b220148055000d000c41811116a2070020880320303400c1c21200041c0112008120407007900301c04030044a400041060841d00c80f61959001404048d1101d81c407407104100c000b03284e488224402d080c0481d00b40c0c10000c00c0d0314000c00d000560720000c0c9072a1690041c1181445400d030000d00343ea0308101c452501c92001400d84031112001f49030700310242c1038000400160301c00c141c0da075000a40a28426209112020800b4000c0c0720101202c40024100030100c0c00144481d90301500503203107260052040703c2815020a010904040307406010340e0945401c0000c20103080040d85007076400104515040000b8080 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 930140971 1250 930139721 930139747
    0x150903091507050106170d11032a0c040507080411030102120411030109140a1515120c0f03120305060312030610020c0301062405070515060415140114 66
    0xc0200d4810318010200d210014007100b544000040c21500f2181c1030001c04006825982d01500290308000a1006239075100c1000c020040c0e40459541110701d5a0785000c521800c260140716680b40c41403849100201c1d040d6942c0d500666000d06102e07100c200301c81c1040d081a2061030180d800b03080c040da004000d54400600c5004455600c190810090001440d00a000a000d0204a807018003c3c541035030307501c003201d1404106009c4c440d1251503900d5103501c84014030070969003c99a42d008a030342e456000c11158181c0072480007043e2094040346109a100c81401035024043d41050301d00d640c202401c503d4081d054403d49420003c00c600601030315510b00544103003840010802c1e80680110044010040d008201082d10000010000e0056940b0b44110080031210b084440c0690001d1122012130720780103104541c1d600341c00c000541140c040488440003090310182c00150040c1e52070203600d400030b6105440701c010b050112801c00742241154001007606440011280ba12902041000c0714010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 930142221 1250 930140971 930140989
    0x80f03091c0f03020303060f041a01110312010f0513092004060504180b01050a061715061804060f26031209210406021509010608070815090309 63
    0xc0125082001c140484032a00c040c0000007000030880c0006402110402d9008805140725541c10380d02400354004540800c020741e102c01c0c842c1407410300340d280b89101551040445d5801004040100c134a41200d0b11041500d01e6001d0344140d03104d12a0440c284198504810310b004100c014020500116421703071140003544803206000c0018038605c440c14080ca0300c43e038000d4001414014020004940701100f104100c0c00c08170021150544200d0002c9654504110004240c0711183c2d0344112180c40078007072051460010300010a554043d03151000c59982d048c0040044c0d10318466000380600380d071014031040c0c0d8247e40241c09030034186d45003403103245509040b405224280110f00711080020741c0d8090f00354455004101800e58800042204050000551001801c00d024030500c101d0f2a610141020b400b40380100310041e0041950080c885500d2140c060704407614800005101b507031001580c0c07425070715078002002034000e0342501082c10082c803581c40e408454200914a4010148005a100301c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 930143471 1250 930142221 930142237
    0xb01030c1a030c160326100b0c06070c06090213020a0206220609021504030f120c200a0e16030b150a080a1401090509060a151404091205040807080f03 66
    0x1400032035442c1c05146c030a00c0e00c0d02c07840c010702c10000780e906842d0460f02208101180d40702d00341c0700e00b844001104c440c41e078100c0341103100381e40240000d51100001143e5018080c0740545a054440100c03c0260b0b44854a089092924140041c3d64416400c006030801d00c0047c00502c980c1020401d811034000301d100ca08450a0b405107002503080107502c0001d80e1509511404002981d01250100421102c070049002070b84c0148a12690102c1c90007040303482c44409032005262100c8920621210501c40368101c07021038004158401103038803810f620b60214011210250361112280034016041c0d00342c41612015a010f1390303110b8204035180220303d02031213100c074001e0401900000140c01c0351040d500106000d0141d80380c80e901540c0d114100409008155400003544c0a100c001c07881d42c40e11445940d00420300c0d541c108422074600403007601c41104c10603826800070740b640c100c50009816452014280095a204e050b05c460401c10014504607464101c0300e01e942c05142e810b5124031000041e12614 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 930144721 1250 930143471 930143497
    0xf0e011413080615120309010504030f150c0201020301060f0c26040b0f03060a06030506030604081c0219020706020718020f251403070b011e030b01030c1a030c 70
    0x2880c901c0400c4989110103a201d850180100e01c148104207011140c00d280f060790031100860a00000109107481c4d22500c01a036000c94400c001c2040002c81f91480001024060612004404032100d800303030a5500030320203900140d41c00001070110755000402ca840013a924580710f081070016642d01030300786110885141002100241c85041403000c0c0c0c003100d0241031a994815101c8004580f203402d10303001525854072840e510303400410101c0c0b09214080c401c0780d0050050500361210b88500e009980110765522480544540c04451811a0700052622009071085044483c0301d02c903000303003000c0b42c54001da01150080301c000c000d01c3c0b03100c5ea452400002459801270352800c941100010340d10502c141c083c140c0c503014410107101c0380440d01c507040b524002c203407060052100011940e00c034401c80c8001400111780340e0060005624145694030300c5122000121100790f1617482c0c00f20146e100364030407500000030410034840c00002d0050f06d18201c01224070305040d81131070401641c007809441484100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 930145971 1250 930144721 930144727
    0x605040627060f110a090e13110f0303090a080a120305040206030a11040f0b0903250605090d02041d0f07231807110f0706091703070b070c030f0e0114 66
    0x3c01c1403a80b104480d100881400d40ea00e4003008405001200c51341300c0c03c0b40030181640090918842e4011100d0100d6000340440d0801d81c1040c100401c5d508100e1180e84c042c402400740500e140c44200002c0060869000100482d032a10b10b400f80e01c07044141030000c20981000248001a2110816179030480c400c030102203040050342c01216400c0c00350398001c1c0d140140c1c032040011059582401450340450940913a5035002d40c0c40c0e90901c00070b0920001e400940040401000300b81d101d80040c020302e0b04014214030404c0169000a010740d99106034080080c1c00740303103264809001c1049007100903907141c4080c1080300d140450b081a0340300340c041ca00e0740d441140b62030048242d0302c14a1442d42007510b58140ca1088c10030003030051142262001d00c2c0c4070382c41420018141100c0001d4481c0132030703801d940ca41a0782e900b0003004492118a448203c9964841441400009607034845001d03c04c0c0c10a1341c9280c294070f8181401402c0b43c4a400286d070910440781406440c03643d1040201400051150495603 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 930147221 1250 930145971 930145991
    0x1020a171312030504021915050901020106050301060f0608100e060906061201140f0405011a0a1407050102120c1306030203311406160c020402070609060504062706 72
    0x342000c402070700180340022074200601da40740c042c0e2109000324029103045402d40344081e412801d61142c5c1c01240c00d0f041982129041a81c41a0004c2203022010300c0007180d400c0d5600003103800d4600a801240c91908440400d018030ba80c415480c5900602c10070381403a00620b1304c4081d41404a016090030b02401f141c01c009803950701d5200131145210b40e01d1608040b0383da51410054104c1c0c80360405503209e41d114002c011581d00c0e0030302866050b6002c6501e181084e110203402c0400c03a503c40c0034110280003552aa02c08210822805480803c0c001d070000b41c2c0c4d5a012454041031880000c002c0145420b040c40441e010103202c00050781501c109041c0180d882c3c0758211410701100a62034602e0a03400940080c0d161003906064041400d48100744001e081d41044945e01e449103801c80344010381c4102c141160080c584162603407a4801d0018000520300091511b8201c242c4620410548501d605ca205000c100f00740c0c0c1c07240c0340c200e0b04040085031075501d401303122424003001e01ca40a420280c882c19100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 930148471 1250 930147221 930147241
    0x50604120206100b031b12060a0603110d0b15070804061404081f0e031b0c0f010c030c32210d05060303250b011a071401061e051201020a17 61
    0xc800b42105d80706c00c41d1102c0ca968a0f42151b01800c0302c1c0e050240e401940006851402400f5005104000c03000c15400c008804513608003c0c03003504882c90b0f10994100e505d0352900c107508001c000c168002d0300203507659418140e000e0003101001400c080300c5503040004000300a000300e411401e80d41c20040400c43c0d000c81c60260000f0b4001c1d540084990f0200182c0c0300452a4000d800c40c600112900946075440989820007091003104141c1501081c1901a030300c001074801c40c0d2503426944101d80c03842c42c840301c1e5203441d0740c03d020a01030a2070500207058154425041000420488031400c11007481d041823113501002e031401000c2400c49015201c80c00305100396010301c26548110b4014094030030a00c500e00e14280100000f0f001910000e072404008501b88150300c2d010b00c0000310849881c1c0c40c0c8100c13a03481c940081101c201006540d580d40202280034110320048020310034020f8090034120f414a81001004e442d46022098a0303031041118045503500580c101c0030007490404440445e603540e080c0c1c6 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 930149721 1250 930148471 930148501
    0xf0b16020402160203191110170a0501031b14061309020c010203041515140301021b0627062d040609110108041a22050604120206100b03 60
    0x2035001c1d0010a80d10340600180c804008014001c03001c07078440720424941c4c03100221a0729805010200b11400c514100c1c00d140f0303c01010100180351180c2c1140207a020510144810b40b040c080868a6400400900032080ca204c3e040841c00043c001300c1c0c51500500c03202c2c075103640c401140505008540380341a082801c0e8440e004100c0041d00b5580c48800203c058001c0d8801c45042b00c510004068506000310244103100084103400d100b40f02c064240940d0b02ca103168202042541507400300b06410500200103028114100c1900080441d410300641900381042c0080074206586829503180d400000d00048040c1c03c6070074a02d40c0d4090040c21461a061142540d1680012010210900042001301c1d071150380d0207400f84518034546d02106004441402045e038018040c03e54003c4040304030003049984075002002c48500d03001940303040c00428008003c1983c1524039070090010032051100c0c04440e0081c4494505c0500a1450446120a03207040c45014440311618044005506d0310000501e03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 930150971 1250 930149721 930149723
    0x12070206060d1e02030a11041d12070c0306140702011b170c190e0f010504051003110c0d0309050f07030807060507180305031306020d14070507051507060b010203040f0b16 75
    0x40c1e902e006c1160510481c520564001f4500481c43c04100410100212108207941c90a0102401481c02070312040f04d11070b00301039025115140d0b84100040010a244100c0c0c4000b80d030503020b0120344c03824410103403c441c2c10140002094500d011450080c03980201020a105514400f48555443e04505681d071800f401e2115035450f12400c4180d0801c42e00441c0034060b0a108450100030214444011100e50045210b00c0e5003104201d0141000c5030b00a40055822000341c0d5003d6040007040c0c00c000b8540800c802c0d40c00d010030fa64180240601009000c900c240d0a9000300030300085156a840260f2803040c194090701e03007641d5a004c40d940301c0c801c0e641c500c410914543c00703011440c1c9a0400e50b40700d9005c6d15081c1040c91048200080c031a0010031201d80041c2c40e074070b618504a50307e00a1615613480880c0c129014000c804001c01c183c2d03a49401e0000d401303103641e40c81d52111620f1038840125030a040c0d59a05640c0140300c00c01001843c01511800c0d2805051002c1e1204403d001c400e9041b220110 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 930152221 1250 930150971 930150973
    0x1805210c10110708130f0f03080412110402040b090108060a060e22060b121005030709020c0f010609050f010b07020d02360a1a06040e041a01030812070206060d1e0203 73
    0x80c41c40100c0e5903640308200386d6600c0a540181142c0d9a0149014000103200040c840380052108114184d41a0741d4a0043c44c054161700e164800b04800040803a030041d040170701a40404142c04050303503848150311340d10039000d0300d8403a0b1a5041c22409003c000d02002e2440c0704500b00034043d4030982d0341c65940d84511003000010b1040986810b0691819085060002c1403101d1200000d044841030454020440e01c014000d01207184c1456010b402075031040030400c440d44101203201002603024401c5000a040701180080c10f410030011001c940a0182e20101414605201b11000340c0d80b2545a90041e50303041350b079003005168000300803119030b44686040c4101c0d8503440b00c806440c2000e0104a01c00d10401500300049040c0015840b4130700090b81d03400360080c6050009000d080035600ba03050b085809032034611094601900c3c8030b04030100c03d0300111000074000c80c0c03124040280520300da400548c2e84c000740400d0b02c4c11101140010100c0c00c00907050070700440003055070f002007840495210f50094 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 930153471 1250 930152221 930152227
    0x1a340b0105040b04052406040b040f08070605071a100b070525030b060405070314040f0606140d0f030509030a140d020c030717011805210c10110708 65
    0x105020940490034032070700d4041c40c107011110015142510442e4407540500030600706200100b0030605c0d90400012603a40c02c004200b001240c0310400d000544002d01003e100d504a01c0e00300103045040546e55800b030b0003481028000a40040c003c4039107820000b2011900b07040a0b600d40208000c500816032100a619100042003130070300801041a80400c0202d0088582e4580090001d1040404901c005010440c4800c042550f0b8540340d00300d01e0300400d00e0701d404268a00003500384017100605850441e80e1520308108401008203a0041c10018844900b000c0c0c8a5010700d0003007915840c00c0c01004041c014040c203802c00700341c090020703640c00320009002ca4168589030303e4503070603061b032000f0b51240c14450350381d04812940c80000c02131800c1c14040c0240058a20307205d04a0300410300c5800c054015500d41004100b0007842c505400c150354060401801c0700d00300e00b10030513030700d14048041d28003800040059401d03040700000c800b035030102c0f84903000401081803030703102c00c1d1070040703540040c4031003800 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 930154721 1250 930153471 930153473
    0x21303030e01080609010f09090c2c1605180d050610030c09050108150702010b10050403030305100302210c0603040506071706210c10020d091a34 64
    0x1010006003030311400c2c3c039141c2c0f0390b4464078204032443e1000d1140510544a000d41801052111780100f444140306144a01c030858940300c0310400c5d590b1503004040507043d500c0750080313500b55061410341c008203017005080605021120060140c07244c0d03900c1440002010441c461140c031103011480c030150b04841560041e042c020241040c4918511055601e804090004155100300c0e1090f64102c40f660402040250454101200c59180c020309600644d565225480407980f41c412148400c003c044e030316075a03504e080d1700d00602250005002c2c03e210658040381400140c17191151281080e800e850140500d0300b1410b6800d180c44140d400035500200007109000c00c015002a0040c01030340c484e284d02c400d01c0318201010302904012280c055001d1002400f40c0f0342c0c0c0c094440301d0039580c4503000550303100c01090004100614001101a40164412120b40003156400840710010340080d11000e0369112000703484112074007680c0d10046208281902552030f000b4000003404805c050307000c048070411a1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 930155971 1250 930154721 930154727
    0x60c1e010f0c03051003020d0c030804030b100e04020109171e0c010e09070507080915211f0b160210050a0206250807030e0a0b19090c06050d02130303 66
    0x940c408405441c101422884050701901449102c5c56101144441d0545181c081081c0f400240380259448440d060003c00031801c08801080658000c1070840450300b401415a440380d51954020002c080e191000d00c00181ea1041c00c00d0200d80c40420042014070380b40414034140b01241a0748400c8080c014480c8407900b10118045041580036220120760381150313020300800035400c480103400070b0400c029610000b0010006040242005070060720b00829075001064158400c00110200d100c5840d010003a0790560b0268030b92207010340301c40014011003004600003504142c0034071200440302140300c04100050040c0c5805080d0001c007a036404080f5030390080c00c154444042e40c4010f005241c00194140d904800700340340501414503074611150340b203c048400c03210140004040503161140582e00240c03c100e1001540c1c050101031049041980781440004011046d14030845d00f00b081e400c0c0440d100c442c180702102c886041c00f0f80d40e80c03a0003007803000900c02c4000c3e1a0003d21042001300625034 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 930157221 1250 930155971 930155981
    0x120f0b0603010b190f27110d09150c03020a0c0f0501090f120e0f0a03080a140408070f0e0c07031b0b0703020903010518060601050901030204090c11100204030f02060c1e01 75
    0x1039008042810546c032070740301c6030b5012030900c03d4100007000b40c2044240365185074454841d101055003c2e50510280c0400c540c207503a000102520030100c02d1280b143c00010900c5000c1a1000504003140b4080b03030844003070100e540e540c0d009014060b1114140040c0300c4207410140708140c0c4507400305004c03c030074980128000d449640b1200043c0d0700c0401c0040c5070034801d6000800c0c07500104100400e038519502c03000076902035440c0004108a014000c036030034074101e000c0e00c0a01200000341c90010301303043c00701c008035509500500703488400d40280103525401000315480701e900b42c40c060100d2204900685040b081003038008004010310f60400c0b40e496415400750010880487c000d01842e2510701000c003001504152111003a01b0480106640350301407001818142d00605004d41000c0c1e6403d506c0088421001e084070101301807601128400009100f4104102c0c000e001c00c50809003503443d0340d0034010710180028040c000015003600d28002c200040340402c80480c0d04000f081e04902d403e24081c1c1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 930158471 1250 930157221 930157229
    0x213020d0c0206090c0a0b0304050102090a0303091502030319050711061e07020c01021c0c0c0b0703080c041a0a030f0e0708060745080d0801120f0b0603010b19 70
    0x101a18002c90500c2c2400b05d910118800d005200022160030f100c02c481d02640080c008864941d820400c0702c0381a250055010000e5019480d10400303a864138080e215a1244440030504540007081080f05010b80103000b4803426000100c0081c19030381e41d09069400e820703a1a5950040e2081004105100005c4071120707203c500124505007580e00c4402d41a60b0700c1d00111318031030240e0414408999004c08105851106410b1352a00000044071622205450140e5812040c140140021000249604000710b1600446071414603490036141110207958040460361040d0254000034600181c0f910a4204180d07207001140304011000180c480d00d40d82d40d02030b02c2162100e01035113001030041405440b11a511800840901920040d1072030b00c41305814402410580c0252801000114640c40c3c1c2204c1d0041c0c800036009001281c8445000380213448160700440c0019100c8000d6000159280381034041c56501405080180e102ca100082c0940007000c09150000c201101120303090349410801d504030b03 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 930159721 1250 930158471 930158473
    0x506040f0513050402030a03180b0c010f05090706020a06090303021c05090c03030307122309070807090c05090105090f0301110d150608071407050136020901120213020d0c02 76
    0xc0042d2400b00c206030380c0100c1c4d000e07625400c0150140080b90040031400c00201003100b1b0b0060003a100e01e140011900000318070f811aa42d10003100116402c03511400350842540340040843c01d00e4011300943c1c6001d802001006141c980441d41e040500a80507500c80100790078a54150040a040d2100200401c40b03200c201d52090010040c4c0c0323410040112400345031280d0f2010300382c0c0d4070b580780e500103055010384115881ca4092a10030381e0303001690b2124054082ca80161028501d011482c41c502020b40d04a141820b00d4090f980030007980040440303041c20070030b00385140c650744c40350b00003400b055098043c2038040d4201459800c0c1740d02004010540c4403c841c100304500e880c0c0003c0c3c101a25510300a50001c9140320000c5220180140d18204214036400704440c9003134410f42d01c0b0ba080d41d400708402d05843c488284841c0294814801030a4003d11a8810800b000c00307175000244001d00c1882505059209400010155101e20008406a60b01480195680c5000b404e40b40c0c01040000c0c488001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 930160971 1250 930159721 930159739
    0xd1121030d1e09020105091507020d2910230301060305060109110f1827070f050c150603030c01060f06091d0f06060405031e0d0e03060c090a0506040f05 67
    0x1265003500c40c480f021034042c0c0d921400c1102c184148000054914450030000038103110000060303071007a401100e910703c10303290310081c00d0b224030740700050000710300ca500a0581e0034010803200c60800d01205007200d0520f01a50b00380c10940b0251a151042c1000e070035019401c01070044240100003c425048801510b030402c90708540d0002e180f0344e80500903000000d1442007000300d13503651201e440320210a40041200c002c40300c0744280159007241c40d055001d0001d10107020801020380109812402e0300c000d0030120701c1d0003a45051103480350250440402000c40510100da02500e0400c161898040d125008011041e244c0c502034450a010b4800ca000060300c110010451010301c941c1c0781002d4014140c003100c65194052091b4001c2d10080c41981c100301d00388800180c03a901003250309400c6000f00c203407114a401004c00e5030309114040464409122207806a6052601c0c001506640311050020198035030740c00a0008508111691010f541b11102003000301d0103410000761b800440c0c90840b20505 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 930162221 1250 930160971 930161021
    0xd030c02070b0c0a0f1e0f0c091a0909030c160e0c0c0604060b0114030106081501030b0d0f080708040605040920070308060f03010c0e0306060d1121030d 67
    0xb060340314042c0c068400380c000e20548800104d40340500002244100c2038a908580c00300361400003001c0f070303000a5440d0b405a034104800d12180f0300815010301500031090022468a4540740c122008200240d4040e6613000300090424805000b40c443c40b542000130794594111004603003c071207010b03020709500c0c4800031001c1360400281c0b000b1281d82e0210300340a800c50790344588900e0010484160701506000e0299041d80c90b1086181c02180a01569261204c2c2810101c103401c0d070040707004c45442c0c145031600c80c1a070080c0d80ca0b01018071080303900c06100f82c5403417007078030b046200d6020b5264000c100311404600816200d03005030141083e102c180c00304200e400f13180d20454201c440300810082c0e1201c2c04000300c00120380b1662aa96210170045d142c2c01420483c0d1010908442b80c90b15113100185030007071300c04090310b0b05206007500300394211500d100307000c0161203406465400760181031040798484410804c00c84001c50064080d0301d00c1d81600d0b200d030104075515001c1c0165100030700c21010001841d80f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 930163471 1250 930162221 930162239
    0x2030a0204030516260f07060332061311030403020c010f020105040c090504110a0f05040f0b10052d0913181b0915051002060c0a030f0e0d030c0207 65
    0x4031520300031854a06594240b4189080e80c0c80c1740c80da900b0380121155603407000d1081210b4002006907580015046403032044100c952403040d5490352403410004003d5540494400645400a000326040c1d00100c06031207150004042e00c02e034aa0000c00c0110410080c590046960400514281c03036201a02040300300803070032242e08590003130100c50444010f10002015500c00c1d68082d05c0b600140b84107030b2900c40003901414a42d0300042130b0691428080c851400c1c903010700101901c12034000d1200c803218000054142c2b162810941c20003001040424088000d45010880c450402200721704450554000c266650302c03140c003050044241d98025200800d0030311828106104103910060365540c81e82d510300a010010b400350580201e00c3e0000700707541c0824803454209404c04041d00250300e10345414841c03051031190440d01590003403403c20035404035102c00c4860050003494000b070010707403400000d0000c11300c15441c18030303130b2141446070001c264065105c021000ca20b80c00b200c0800f41e4981e000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 930164721 1250 930163471 930163513
    0x151e060806090334020409060c0908164a070804030804030e0a0f06050403050c060301030f0807080f071a010510090315060e041b12031e090902030a02040305 69
    0x113403c860000000400342500c01002080345001000219000c1245034001900f600c4480409403102c90399800b50348400c4d41c000c503021000f1b10602010f0b25015a010070307651310710750441c4210034001085040d91a0403c3c0850319210008284522420103001c2403640c0300e03034030030044075418600205000480c0f0798a01a80d01180b041c2d03130607912906a1381d07851f5000c44268054000342e50308402000000b0070b005400200d24400752006c3d83d20140c48c0d61030b5007010b0303180106455945004017810001400881c0c9044601e403145608080c450381d443c0c1c580d00c0e0000e110300ca081c0041d0540640030400b07504000c20514580086101c0c0d00d060205662100100700160070f03d04008008207002a82c100002042c6110315165040c00031000070355a0303a90b00340c800820300115011902000009840e400d00f8216a800c03002400343d008a01844141c1c5940c0034084101540004c03907103c010700d20081815200350aa880900140d210a54030b0b4103244610310080d4005000450b40c600501d0200391840880001d4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 930165971 1250 930164721 930164737
    0x16080a060c03050f06300109030e0414070f020c3007050907030e0102090a030804030201020706080c040b091c0c0f0902090d0b100807030f110105070201020a151e0608060903 76
    0x641620388602040010702046c1d94030b105c00c40e11b00c103a103030250142031420b6040307101c442400120303040130345113002402428000d0f00c0b148503600d424403c1c012003a07010f0400f0360041c004d0a12040b03000c3eaa2a060b40f03080c40d00941e41c3c1d17000880c1c041c1750300070200d8201c07400c181c503c103803a00b002040186003289480f001076000c1c003900b094070200003942d2280b00c0c2c3c0141c40800301d01e1000518017602000421640c400f1074200751101d0320006010811943d04028000c02400685820250b5003040040c180c0180709603c07030000711030310118094801da611030807802100b64403001382d00700c030300280d01d0403e091140f20f104807401d028000030001114000c2e802111011a03000703041c1803080c5600e07078a6409000d0041c0404000c82140d85000c510500b0802610010b035004000c0c0e082180389070b16181a1107001c1034011030401c80140504401070b6000900b4070b901d5039014100358000f101541c1c100e00100040f28002c440c184171100050800d045e941e111000343d8035000141c0301507070740b1600f42c540d5038410048 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 930167221 1250 930165971 930165991
    0x203060a0506041104091b0c030c15020d051009110a091e080607031a10120c030e03161e020a0905040507030f11100e010f080916080a060c0305 63
    0x2410400941d12169002000600c00544c00610002c09105500240c00006405907141040c65800c40c5521510b000440300b49840108102155402002600c145000030300c00445000c0100d418415030701a03c42c00c16400c0c8040046244c105c0003000805010f1040e510010701c1c005442c4000601c44041307030b00305078041d100d03500d800e480d05030710300818500000d1020311070702c20100c0031440350400d1081c0f0380280200c2e03a0100c0c1407042c0d0700c180c64900c2404e4100c3c1c0d20860401d00071001003a000403d60000d0411414001510454208242d0140c50040e000b003003180400a102c042180c0c40c4030000382c0650042001d42c54212080200061148600c20042d5000c1e000940402c1142d0f2641c01c150303445441a0305540c90706549a980007559810740030111449a502c0d4407440c86400e041c00c0c61a0303450000d02c0c0c1943c404040f4000a00400394101454081044d030100160200d0820420903030048413441221294554420342d06840311040070048030030b1410100390b90301c0c1d9440380c05098010a0210 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 930168471 1250 930167221 930167233
    0x1b0c041a010e040501230301110f0a03060506130506033d090203100b0f04032907093005150714030105010219020d0b0c042d06031e050a02120604090203 67
    0x45841c42954440f06e00855056480350741c031909910301c02001d4a02114080b2031542c5a41080c44080c003a120140c00c514040c050601541100524a00001d030456000b43c44032075998540482c000d0108280c0304010078141c0000d500c4c035894010f1000441000c1d50100900401da0b07031500070300c0003a4401035031100d00454a04009104000b510001041103c910f0311807203152540ea81d03605003c40e484280b1800e0702c10b5041c25041980c0800d0042e00c1d61000c079034070705400072608210000c0105480070b441c181d582d001008803804001440c21201080c0c0390010115180e0703010320741030303e01001400c96001e0001103000e0070940403003202c00140c81c180e81058007d03203024a40c00944a00081c41c42d074040e41c0c012a8485c080001c00c0b03480b030041e03001e03141c0c031091a035a45052516252030000c0c28402100e500c48955610f907031204031040300c0703410341e07540d40b0b804548034645040c26000d800800300383c00030242c070b04003c3c0584c03001140c0c003c0c050304c17505020285180e981c1008010403100c0003034020b50542c00c42 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 930169721 1250 930168471 930168509
    0xe040513030e010507060609021b010c0206191508061005030f0a0f0303060b070f0210020c0f06030601110d02100b151804270b13081b0c041a010e040501 67
    0x4400b414801003040c501241001c8003919050165000b56012565550303000030242c00b4484419810301040c803c0e40002e00c0091400d0342c000303669610050608a000400c0c6401c060028044d8010004000848a10161381c2d0340310700f500c58135800140c0f034511062161100000309824080307024101101c103000940706801030754440301c0c103e4849075001c408066680d84041203555807a40a081800c1c0030700b148015640040c41804a03085140c5e10103425548080c02c3d0030b40c9a502d03004025800c11050756055103907110800143c40c000380080005110303018000540046681c0001c0050084010103c107100001ca6071040c8540e070281400c8000c4107100401c6020200071030300d03226081407140030384001503215482c60b0b80d10b24448000341207690501900505014000045019a0400030341d0b0612404000c4555803212688151701c1e0f801501084aa410789140b0340c103228800c142140540203000e0301200c020110704040000c00490b01140c3d080e0314240725420a0301c07486041e07030305100c80382a80d07183c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 930170971 1250 930169721 930169727
    0x9210303150604170c0127120c0509040f05011407050f0a0903080406022b0e0d0c0b0f0d0e0a030e2b05011e0b0a0938010e04051303 58
    0xd07054210741044007000006442200b42541075041a103c201516604410000060600b41700c3c0c1c140c2020542103a05901405412008203000c03620000c0ca201003007120752030070307403500720044d0f011592201c88482040b091040f681c80c04003a591242c0020089649415500e0b800c190301520f411001840501041c440c10301c150008202030b801909100c0d034950356a941e02041540301d40c2181e40140c01c0310f121151007a10f0300b05840360100300c100da1800300c100603401c018480e0080c100e1051043ca000082e071804c0c4070060100c04054a464040e141e51103e03d1030044076243c0c08859058010341c50410b096840c6400441ea150303c980e0f05030740380803030302c190b0004001d01c4900c0521900c091290308607803030050410f011740f02c003421446500040b401d00d6100c06d004600c01c13000c10000421303a007804041103080d525140e14405403100700d040010040400e0b101c2410403504001403001c42e0906410265140446600100c4018801d80e24611018420004d110542d50300755900c0c03a000700e04209076030001c1c1c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 930172221 1250 930170971 930171001
    0x130515070806062101150306050d0203120307051306050a1707120509010b040f0c080903030f1609030812040209010f0e0a090311100507020d0c080a121b0509210303 72
    0x3040380280040e400c01390f440c07083c2c50002a405004040890701c4034030040e84d054002d40e00104406c452504d015095900440d4131741085145880c00e90000100244400c0d00900a89120203081040c0341d42041d00d849020b40550300c404502c0b80031178401e0b8109004030341c00d615000d1141e00d81d1783c0d8495005694072080d8000c0e0001611060b4103540b540c80c1100961035510a40601050000c0d000c6030041c284038000d00240784c09000300540382c10030070030400921210403000707800c944007a00e0300c0e0700b401910314111414082c540008180400009194003050600e50125010318001c8906050a99070f40c400c01b0b0507030b0140c0c8101407044040130b00098400c070342644400041030290a28070311700c0c0400300c0401d00345940c3c2400032040300d81e40c00500400690400010403800b9090916464172a902e0311100ca0502844117603a003080a81c400381080c40079a40c0109000950810110210018141001c3c1003070f0004c030005801070303003510030b030314039201c1101c90590540d42c20f14007951841d201c42030600c440b42 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 930173471 1250 930172221 930172237
    0x303021c0e0409052107020901050301380d05160602013c1e0f0504030503011511030a112a1513150e0306071d030106080613051507080606 61
    0x2016210107000700f4003d0705e40301c1e030f03002200141d0903a40304080d104000c3e0040c0c041e000709000344e1400a2208070b550503404845d84020215001c00b90907400703075515080080c1080000c035002a004a000410020005022501d00c000720b40d8501c1d41b03940711101242200c0ea49041096400510340c101320792620040c3d280d000800d49445942500c0b650f41c40060181c52140101c0c2094480ac0d074800b8001000a2294131001c0490f04014800c60605407401461400306000d448007000084884090460244040c80a07030680c2406980e1a00c0303500e48050801002c1840203105802140482403500c03204106502030403500340c1400b82014290300038041a460110b00382e8036001410000500303040c0c003010104004100f01ea0504415116448005040c801c14141380c41c0281d004005005040740c114095140c094000044201503600c140d000a024048550101c10b20340a00030602c01c0500101001c07410742400354040b41c0041500c0c13040100341d000e003181d0b6200081c4c10319020881030f01e0204001c21202c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 930174721 1250 930173471 930173473
    0x1060c050304170c03070603020708030105040c1205040605061009050a090b060c07030f1703100302100507020603010f0512060c04152120040803030615040e0108070303021c0e040905 80
    0xc07644a400c0c3c0042070303441a80715000c542c01961050990700e4200300b4a000781c446443c0640c1080700541c2d445040340410700416200700e8560302807000076407080080070141c1c07401c00c8041c081d03030500b402c08030000e060507501d41c2c0c0500001001d05082a0141c04004211070024240c0e44040e403030240031070010070001b6015a0302c20303010408411840010001da00295000f20f90340f510b07040c490310701030381964003d140c2420f4019040c01004a110700c0c2181030700489805480343d000c0d0000b0850704403428891004002d41c4a00003000201d082c03054010a24182c0701c041d20202d44000c0d044005a649090899030381410100801c410310101146501d00d140119060810295046072401c800d8040d8900e02d01980b080c9070355161a021000c80c2c14611424448003820b01c0f4605401c00405e070f0b03180d1000414140c001c402c0002004201c00c10001210010185640d10549070358580c051543c03525014031040c0c0c01032290600518410b051205200c03103008491321a0909003200d141880003510030544240c8071 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 930175971 1250 930174721 930174727
    0x180301090f050f0c09040f150f020d0504060501050d150e030f04091a060c2a060a08071e080f040f080c160b0307050a050f040513140603011401060c0503 67
    0x112900c0d001d40001d445400a02032000d0b24150091411084042881c82240c0c524103010104001081d0200b800d60480e41585c0d901482c4801c0741e029060104116a002c1c3c80010040d10b01c0d803d07070b80054012840fa40d028030690760780e003082050325891004054135580c1400e400b80c0c12840c05900080100500100792410709600c00340440a5070481e40c03213201c10b0b6464404203010303990013040440d1100c204890030ba00300304104007061384c0e9000003100c2c2e14a11080310311000703401c642d001451500c1c201c01000f456881c0b16420004294030003c3d40d40c1c0021a1400c12442030600204242511a0581d0350381d004195640c1c0c0115040701001502c1907030515010405000440d140100901549a4800003400c0106605181140d1040c0562280014910902c140501607600500719480c1900c1031400c10f40702d26807600089014812980f04070340c05000450b1491050206401a2a840000c44010f404640d03031101410300f0b0b240840340c0144015007000040c800e0500505103c15141c0c010002c0385d007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 930177221 1250 930175971 930175973
    0xa0507050313061410031103060c040915090603032606060a1b1b0f17030a030b011101050106031a04020315041503051b031219051e1809090705010518030109 69
    0x3015800642e0340078001845e088052041c4051030a418107002d000f540205441e15000540710024000c0e40104400c60707480320050380c0c3d03c0c0817002d90741c4050401d16004000865603450060314401d90b42d056103134112440845003164038104c000d10391048001404181c9481c1c400d540071999869516004000d0345608640080030172002110396581260326013900c622603003441c0e070091800e0819400900507002000300e0386040080032041d1a02006c1508011910213098030060710500004d1158011a41c40d01d00005841685034005000c5d540c0402c030380999841c45041440300364441280e100c610940514451090b60910342c0c402c0346249081d14000c000d980e140d55426041c100e600020304071b181b40b9154400254603003030117250b2400500c1103041d0f141407048000030311003014890a01c0d0902034003142070500030f00c03400780055110200c0e1301100d903107000214564000c4c184801c43c1d50301405050f400035a095038005446c40c1a100161107481c00c10f0704031108488221720310314105030195241d4a020b0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 930178471 1250 930177221 930177251
    0x1505040506040209240405061c06061a0702091b0c0a06060302090601020c150d020403120305090d030203060d02091f150206070c0b0402010503090c060f070204050a050705031306 78
    0x680694800c0c00a040c1506080c0100113400002a110540320400b030050380d1040400d100c0070010111081d20041503941d0f9a1300091a400e005000e42d5501c400c0403001181044001d520000644d003403500145251010108540928040c00ca0000c0d04641c4a10114240080011003042e520032201415490041b003c44010f060020500007100c0c040d4490009000318508007085a5000800303100500324a5511400101d03900445159582c003a04c00084079400e00c4540e804590165802c088070300d00d9507080c014020000e085c100c40d00e090b64003076400d08005503846802164001d50000b0a0382400741d540350200103440714054400c480018017654110617550801c07581070010105049d101c2042910782e075019092035030042440c8204001c1c110804000740310300d005140c0040c0c080c60080d80300e64803807501500e000015900c19601510106091142d64a01c500909c0181e109035028040c5440d540c110700113440007901d407807000c00c40c14000111070211510510b0b00c2c244c02180c01040301c4080703201d00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 930179721 1250 930178471 930178481
    0xe1003050d0f02010506090c0717070819111b01050c07050315010614031b0714070305060604061d0117150c120c0a0807030c0c02130c02190309030f15 66
    0x80c002c00c0c0c0344040761030090b0302032041c264088802c2c3c0384608107240581c2e040f03075944a1030320001e0400691412201d008110356040e070b002164008000f65848181c0b1358261400e201051404000550000e610160100b0115a4882c440c0000e94282c0c40c0c10044001034499400c414440d00b43c91142c08000200b5590401030302d1261a21910304002550400302c0c01440300502c100c01c1c01075081d003002803000042603028031495100f0231120b1180c0703d0469280944521000d000c0800b102d10071170300e0101c00d104002c0f42c000c0c041c580032502040303140e0b6140700c400801c2005210700030742007804a0042101409050b850040c19803075000b070b00c118201d48592003050407410740d903c001326140814050503400d1401904c64001a0045041d8104448a07500a240200003090300080580f560307114820203002d046285280d0b0390042221842098041c40607005001c0f1090000c014890090040c482080c0d9044500245415170313900540d950031a290504203445122080320724090301d01d1141890b011502c20 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 930180971 1250 930179721 930179743
    0x10e153a060e061b030f13081c0c090f121415060a090b030c010e120a060b0f15071205280809010203130204090204021902030a090b040e010e100305 65
    0x80029500d140d080ea8510384540202690b8040001d00c4081d016020b00b5816a6840090715000c03102603078952400141087c440c0d6002400c0749030109880420078207813100040c10b102c00b890100300111034840101c900700b046114642a11481d0b48041c00f500b0305940040f4a61805180440d0540c09840780311840e104e0b480c104002e03803156480c02d110742480d00e91000341c000c10b240041030200c1d007100c4002035101c0141140c01410711403501d1540219449412481c4007001c2d07480c0c00e4812011603400e11902030840d0044c0c0034820928001c1191071480e00e4008000140e8164040c00e0520a0554a0180c03440f48041c0d400240325051145001c907101840d0741c08070410070840c4000080820400140404001800e4440385034010b1040010310b800c1d0a441d451103e0701110041241c04050010400a1188060b800d07a10a80009443c078142d07000001004c1c044034583e05c8482059840e00342d00307054010383c02400b0106100d0801040a01000d008581d005100782c00e0404c89680d80303582e407601d88078180701 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 930182221 1250 930180971 930180983
    0x60702030d020f06280b010e0301050a0603030305060a0305030f0d06050a0b0403060f111c021207030608060a0501050607020409020117090f12031e071202040e010e153a 74
    0x10724400c480310500420b50800109075011744c0344201010603490b00d46000c0301012455030b81c0d43c0a0a1981e11600107030903480c2c4068004c00c0300c0e0804411440c054a52400150003290411021030654108000d400c0304994003c4043e6080051001061599a0241d03110410180d2980008581079a0f0841024020310301305d10301c0340e82d40d4a50b02d000c50a680410100740e201e680f4161841031480007140c02ca074070b040601c500003d401014909410001e002d83c50711505032003036150030054115050360141c3c050b0b6190200b1102207580f0080058190ac009001d0b8a40050082c0300c0d1000600b00ba4000040d080d00c141040c04074030400704600e0785440d400721203600e030381c0e840100c9442d6800317414000c469000074101d00361840d6240c0b0010382c803205030090010034295091500000d50301449800e603001c10350200c00f815596141d55420602c14070000307000d07014410384060046220125520411018108007408504070a2298040825211108031400c40c114400b41868046840304400c05031120780b15203 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 930183471 1250 930182221 930182233
    0x90c09180201200601150926070503030a0c030e040204210309060e0d080d0b0a030f2f1e1c051510030641060a1211060702030d02 57
    0x30000604681100c0c1c2102e2401402c42c4004503c01404100981580c084005409885145001c200d6190f20180d2002151121300d09080b442c0d0300300308015a41c408440d5045515031600e4004040e03c0e40f140c1410540450506440e03100001d0040c45038070b5080700d00600c0181448c0e500c074948250480d440a01da1400741da6000800109500030302c00101600705440d08002c2c5100300000301b10301400103000a00140e03400b0036000091002c0c0c1d000080640c10162042a503a0b80d40d01d0124599941e007a41142d0301503181c0e40000d102d50344001d490303060b01c1e814500148010522070610804041d680c2c0c0441140800141d17182c400d4603421045030000905100311001d440d064241213062074092513100074603603681010b00c450100c400f0b003280207a9411200000300c044024003000e8101e10714440316440380030810401c819007848200000c290f0710300c0300800a0301da07450030108000c0503544c2c0074100f0504800303801a004201d042c40c40d01c4a03c0c1011f40010314002885d000070340303041004118800142d1010f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 930184721 1250 930183471 930183473
    0x60507030501080304080c011b02030114100617060f0d050105280905120c070812030906100b250c08060105120f070306181b0f051909090c0918 63
    0x1881442d0040c910301c00a1800d05041c01c002c551035a0780e100406040181001d140d14180e4040d007028480660300400800100005090300c05a0300411900e00100e21f401c41c40001e09103019032008944144c00403514200b03542e45408110001d910903960a81140e10860320400081091165500410301d2244071124440d0320302e590f40003281103502c01110903040655140010300c0004203680c0c00b0f65852502c54854403c2141e29180c11050743c441d640c148100039003c0d159440800003140164040c40664050307680d58414441101761030300c10348462000800488428415101c0503c0c10401d00601c04030f02d07030381d03e41c80d0b40c5280583d6800142d51a007251004101d145006001c41c4141704000d0b0203800342086504986880e81e903548405880d441c0c0f20000c120501c0c4a455a040d5400d92254a465003036400c01181c1c00c010145002d50450202480c001241c28500364000e00c2c0300a450304440340b030082c14881600c1c06404010310071515512080380100e01f800031030280b4040b21482c1c01404083c0c07011 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 930185971 1250 930184721 930184727
    0x415080928141617031c0216120806042f0a050408010615080603060c0702090c0906070302010c140c0a080904110a02010504150e1e030c10050603120a020601091e09060507 75
    0x5002c0c3c41e9040d640c02003020501000c2d115240e006c09280c4690f0041e240c0f01c3d5110b400780c40340a41c60b8001e141e0004010144801c07030f008158140290802d9a08001c1e03040f480c02c80b00303201c0c0100d120303800d003010340c1480c0f54020074056001420500641e1030f18500b130a5845120701d0030f40d000f0b50400c0116081d01d0541401c03059208800fa544040c0480007425242403c015207000d610900300060b0042c0c0c4070b50b001819640016045810b6603c018180d160b07901420b050007402000c441d2102c100240740d07800016014030003907068400000c02040034000100e0036960300300541d4045c1000c0c3d600b05459081903030784400414003400f000c6600c3d40001c103d5107414034001c101c440385d81c54502e80b01442c0c002c0d03116014400140f1120083c00c85815401c00751000d04c00c2500d0342c042c050004d0810301c0f0b04055800e048640b40c100070b003d020107404403042510000e203903601d603004030700703005006030700c1803004100340c0c06260012140d0285805031003108141459082d8140c80342c61909958050300e40c5c043c03219042e8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 930187221 1250 930185971 930185999
    0x21314190c0504060c030e06030a020c01050106081b030912040308040f050105190e0a05210f340503030d020301050906040e03090105070c0b04150809281416 69
    0x2195030820000c140311001e029045010f0b40c00307035400b0040e00701d54800c2010701944801c414010018406502d9281c10800c040281d031006102910319401d007000022411b0091038560b000d00e06040b602d014103119140d0600f85900020f042003110b1152940c024040c0c20242c000700041c7d400355040761707035941c101724041104102d81d41c01181085010050032029154a07815101a0045440d0294140349617200040c1c038034680d5000707941e0088200314800d046200a090064024294a080e500c0c038080220030281c50300340040341c6c07882c95031405070001d1044a048401c56034109120004d0003c1d29128000b180c5140c001469207891180c1c00801440f0605c3c08240700d43c1d00000803101400180c60803a51283c03030b0b01519640703c3c1844000b241c00010040104501d10281c4a0440340d0b507101c55480021109066003a07000c40007168007000441c80401004c50302081c111000e0b43c3c0d040ca4402180c4440b0f44d01300c0092001d0b200300988810b002150300c0107010004400b4000325071151418200740507030711412 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 930188471 1250 930187221 930187261
    0x706020d06080616180e09010b150405010f0302070816050f0a0f0309050316030605130203010905030a03061e0e190914070f03051504020105073327021314 68
    0x17100c040c92842e4000709801c803510645080030748600c00c9403640c20f480d40c003400300500f03021b601515041a1542da0541600500b04842d400d90755050104410241034089103d042c2d805052f0b500308002c682c00c0340d50b81c0c0c0c0300365485911031030889000302402c941807400c0c030300c00c0e0a080360b00581c4c0b15228070600d9482607100c800b0300821400360440c07500d014150914003407a4440203101c15101d400081c10407050500750110141c025000b4010705906290040e00c0b58030103081100400d140040c0854440c4082011089004071008003820903400c000c1041d881840081c42c00c0d8001c80301011110341040c09008110176640300d1180300614540c8102e40c80d0a1aa0a8100d070780350b114401020000700e900020761900c201e4501000c200071b0f8989000403105841440740180c401c80c0d81000e00b403588e11010b000304c80346094042e5850241c0c010031303040f5015140d41c0e030b840700703442e00d481c554042c0c00c00c0400041d004070501c018031140c1900b85002e00c41050765a401c1180d400c07810b00a0400480100c1402804800c2c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 930189721 1250 930188471 930188477
    0x302030721030806010e03070b070510110a1d04021603171618030c0b0408060a060b04030b06041b020f01051503120c071e170a170706020d06080616 65
    0x90300e900750600503405031060003804202458001c10400d034060b80c03248400201c09026074810a8482c2c103520380b1030b40402e02c11200b40c07180c0510f540765182c0d50b20400b8410042048803e00c1c012b2800c00460341101005280c0300e020481a8074a007041d6500d100805078207500303100c800b5031603a15060280018010200340342040502204000031400760141c822480f1042b0b04220300e01840c440b54510100c0780e1500001d203040b0b290140403e07604040006041260f1050701240c00c59511184080c2c1540e02e60720501d2165041408140002244582402c1e03000c0000b800000e90424803010b568120700f0350307045040140c0c00014a90f00b4610082c05503c0e0303c202019408242c000728000400da0354a240381c40b511701c0c060302007010240c22900340034039030041c10400300d485070a101045d5003464500052190749080010211080356081001c1980d40340c0d0b9030005098400c810700d81404a01a620035102101c500c4e03402c10444002040382d03c140300281c03c00100a140303034a00f0500c00c0119100c560b10704828 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 930190971 1250 930189721 930189749
    0xb0402041202120604110d1104050906010819050d140706090b06031006050d032f1507030c140c010e06100302180f07030908070209132105190905100302030103020307 73
    0x3c20b51040440c0006e9406071401d094141c124201031100040c091480355006040c2803d011500c0c20011340c0d03d06039408101a40c0d01020701401c051140071f150000145203400202d586036881d400751102e01c0c8076002142d055440c0801d10398400c411110f185100b26407a540d0380d01480714505080203014040c1070079003010400542401c0003e1905803400000904100d500b0f0b51049400c21513108260303580d200e21030440d18a240e100c1c0c102da01c503440d61542002d240314440c00501c85031301c20b014502e1a0075454440814003030641c03030f40039001d520603921101c5540d00c07910140c40c83c100c01c0150910810040c1c60700031005085204000e014010b07840c9040074440791209102c80059021051074103c0550308000580407102d140031440c42c0030700d42011354020001410048182205201e40d82264880c0c445030f04020010320100148101508200001400900190041000020030a00f015205007010020035a407007001170300e010703034280382c010000360003100400c11410704100e102d0141c40b2071001010 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 930192221 1250 930190971 930190973
    0x7090b12010807170309040c03110301080c042016081303051e030a09380901030c0320070f080c0a0311030a0807050d0b04053606190b0402041202120604 67
    0x11742c80c043c8401241c03180340d803184a0710503180280e0010b844d5518584040d900c1c1d607519140651100745220321240200d082c0110b58001d00602e4a9190307901c464104110309000d9140054001260103840840d9490310400071124010400d905041c01940308034000d0642c4040c0d210b0342c01c11000641020303d590351041c42010000c0d900000d0b100c040d100000b00b1030000c013294014192410701ca110a0342050f104a19114251807031b194001c05152400f038800340000702002401b101111480800c1803054031760f08243c0c1040040c0740008000c482d004d410030b00040703001c2e40c0310014203900c510b00c0380785190b100e91011000c06070803807030541004005401075400d14610020107824100000e0000c401c0101c0083e1030f25034180385030f00465012001030010002403615610002c0440030409001c1c0043e0700c4a291083c040c071000b94641540c0c450107000d8011500d440220504012668450481c2a529130059072810340b180d1020380001c0c00246040c1c2c440102d140140808050346940c030500740c0d0041d0f000c00c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 930193471 1250 930192221 930192223
    0x90f0501141806130303020d08250c020402030108072d05040e0f0f0106210f0204020f0412030c060c0e0a0b0d060306060306051605040e0a0507090b1201080717 70
    0x9001031407040d41c02507451072214145441c03210020100b5900050100b4180181303100a80440d0a8a100e6000c841014518a805451507602100d803c4800c48a01e045070411000040c25000c05a01300c1c145410841d0b4151700180c00e03a0000d8107c07074110351200780108003855052400713074614210100c1100004140721549207100c100b60080c0c0b030089881d6002c81038040020000d4010070f00c00e05054440101c4d429048078080c283ca0320072920341d010802020a280e002010189007003035884a4800310010107542480040c1d04160201210305400307000c0041c511140307100c100c00d030f18070a50b2001c00c1c8505a1415038100e03858074041e4000c1106100e102c0c0d6031520381246403010b94a401100681f0b03003e01c406510090000c1d038000402080c10101c0001c100310030350304124042c400d1041072a1001810000886050040e0310401d43d2040312a0b000c140103600350b91009400445524294203541d03114600c40c0207a51055a43c00040340c4603c004102c4010244006c90107003c03020886100e060000e0051 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 930194721 1250 930193471 930193487
    0x30c1917070c030c06050a0f0f0b0108010339060f0309030c152903102d090b04030203070605060a050d03030213120c081908120901090501021603090f0501 68
    0x8071040c40300145508041c18020544901c80c80d900581c140064a0841c3c18a00501100030400f00d150341402c0112010303003002e0003a01304002040c0d42d060541e03071964490082c9490304140c1030910701211445450716048050506500042e0170b0142c40c4000c0c40c0050003403150f40c07141480d1041514125403040003a03440b4243c3e50205401401c10301d510420a603101005190310032a070603034804803142404180310448880c034030b00c2c03008500350369040700c0d04031005092712502d60b0f584d1a041410708402c04140c402d032112008000324044002801d2180d0f640b070004a6400f07642c15009a8000708041003040b019001d01d40e400724098440310280780c07074600402e018001504004081c0340c0c010500e00300b1412560301e4100203003480b806801e203050f0075050840a178546805180324502075030780b0408010300e103000300303059080e07010700c095241c02e501c5408038003501009044241c65548684425001c2003090014101c2c00d0010010061040f4003441c002e00b80d031015500402082c08100c504028580c0c025003d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 930195971 1250 930194721 930194731
    0x1d090103060b130608160f03030f050c120409051f0602100b13151a040e070e0102190623040809040c20030310063908030c1917 56
    0x10204140c090b8000203460003d002010b020400d15040c3c1c0000c5141001580c280c0c0c0181544400b18025101c680020600c91180000341c00704442a600d0701810b889030009202d0200c1d05010781d1400110228001201e902941c4061a010780b01e00a00ca0040520900300d03200215802c681080203160080c0070b034641d2600d07282c011502c2d541d110700700d81c0da4907464440103034044211400c008a8901207034400c0520081c1c0102220424003000303c0f0059404901210150b5820030568540c0350380f040c078104c80000401d89454118014001c008241c200c4a90039400040c0c40381078049140d524096030420343c03900b905e1000a4440700302d0700348004110b01104840340320509690100d1095500d050546d0348901d041d205484100911414080c40440400554044c180200e4110410366484030f080383c9140030f03e0700c3d141006242040910600020300300c005480030481145d041540944e8a84c02e220303400445030f103410000005050701c1450780750814640362080c1e600b0481f403060082d00c81c2003010203000b03107 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 930197221 1250 930195971 930195983
    0xc2709111504030c09020717070f170c0105070903031d0d0b040f020a08030703180605220f030f050706020d0c11030a0b090d1701060203181c050a031d090103 69
    0x30707407015100340d182118007454100d000701200968030440140254007010003500c01c0e8001c2c03910484102d11080c1200c041503003110001d00403101588511800108080049510100130420405d0a00080c0500b52003290682c60f000440340c51070402600511010030103141c0301c00f1400810b08655200a03a60707440c550001d4940c0c0c010fa680b481c0414045110800195100078094130004513010000014040e80740b0a564808401c010800d00c40303921909806000c000c00d00c144a0610788030705148040e410004462942d20080342d8450300c1ea542150280c009542551807004404180001004584c00412075440103285034000c6034001441c951000200416884c8280f411604541c1e04020188005802150b80c051500b03041c41d030f4660b1a8004e415542c08245080c1103980f007210380d520440d040b511660041c52400d6040901214003503907005015500ca022075000d04003641e88002c44940c12841000240b140101d142809000c0b0740c0740c52011b034840b50880140d85065110f4900150440b50300c50 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 930198471 1250 930197221 930197239
    0x6040f0915030b04200901032409061503020405011a0304150e010507050316020c10030c09080f15010e06060702090a200406090e0c030f040206070c270911 68
    0x1896401d1041040c0c0c40605078961100901c07040c00752242c00005c811654104031150310180c2401e211410f4000d20010304400703042700603880c0b00d41a0320507501c040c2e40c2140c0c0015108082d959803804403014142e000c140c0300c040b84824405c40c1031034415180500001840900f03901f0720185090001c0c44001d000602d06811070b00c1c107408071030164000e4031148030448001d0040e8030f0302400041203508100d42c0780010102c0d20036503a060b2030020072281c50140d40034207030075848401c50320280e014121120201c81040342d0300e40d00141c0c02c9414404c189000038200c005e010b010740070720960140c090068104c081104d0b410b40c180051552110100e402c90380c2d040d1409000c0d6a12001100300800851040c1d0b14614807244007820781c205030400038015a074594441c2d180103034560403171222030b0700c0032114010784041c200007207200d062403003041507440b03440207040d289410b190350b445500840096004084905401a505900c1011042d00416810016a0400c24000c45885440c002100b000004c1d000303200503 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 930199721 1250 930198471 930198491
    0x13080906190c150903090e19020d09030e0306161809050a0b0a1a030109021b100c020d05190e01020f030417120f0d1a0d050a0203070506040f09 63
    0x1a609665a14008000c1010368841d0440090001841c0c51011500d000a8001d00c001c2e10300144a089075243d010f60311510801c0c1001004000d2240141c001d1700c03410303810900c1840a140e5400280051076610720003052081b4245000392640010a41c054800e80101c0108010030460000e031080d16081840c0034010300c0240b007004034501c4030035005204510f003000200142000d01c1d41025110100c03c1d500b8552a0ba50f030b00041c0d60f904045001d0742d2010030100700410081100d40c01600c400101141c3d401c3c00c00d10004541d610b8026046900350005480c3c55040102e0b540602c80d642e4029020f052203481c007000450034604095000181609020600c20703c014142d00c01c0110030141d400c02000c8036641c640315a5030f00542114410050403030310030703410a003a01d0b40130441610000c5424000050808001003248000307405c250b114003c021006140c256459912441505070090046000d80043c41d0703503005145c240314054011501415003080108400c003400d00c2101d04030b4100c0403000400d0144 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 930200971 1250 930199721 930199729
    0x10605191701140909030313081e13030c0602030f09040203040311030d2a4103010602010f0c0e010e060409060f1707180c0e030a06050105030d0305130809 68
    0x2040d1040c01c0c440c00003061a00000c010764410000c122400c030000ea0712040d0706a500d02c4210b511b02c07400701070001e492000130540d2010303110f01c603003034898484503940322050b20000d03811a08004000e0711019a0820902803162043e1018064074806107140c4182121030407050b1141e80c1d040c4d4090b40d40000041e00781407040e401d5114601c0480103407640c3d2240050091301601c25044000591220301c466095407240e51f0041070100d200a456104c100c1001c901150b541c40106980103031080b06245c54101d4400381c420394009940540c8669540b2075041000080c21503000c110040c0c03215141414a06040e40c2041001803100400d107440f00d41e01c1c10b24004a0000e0107141c0c03000c1090750401001007480d02c00d5600100a079141110344445002c0c0b0510601d81d0780115109454401440320504900340905421040700350b401410705540703c08035000481e16041410340c0582d2103a56800050000d40b03414808003a8a50003880d0030700860810703818052100841120041019030b00043d03103800c070b4803 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 930202221 1250 930200971 930200987
    0x40203030328110c07090504050d110f01090c0e07021f0f2316020a1220030a090303120614121c0314060a140f15070c050909030301060519 61
    0x100111092241010020700030103c0e0300095400005802030b942c02041024451240038822070304180180101e001c45a0b0503140c2508100390010303240038803100a01005070901503010802d2040b44010000da01d800000e1581e500040e00d01411500004980b814050f100c00c00d0003000741c0c02a10000341c0c80400f450840007482c00310282550001d0150001c40345401e40e501c164841e50070810a142803801039001281c0b0343c0e180c000c0c01002c90275602498200c3c0d51080308861b402400d0ba1441000710060454824a0750300050f01500c00649040760500c00c260b4807101c0c081141c407039000d050100e241811741f80201407550155140c02000480c005001440c0104084038004007922111401c0342013280d0024040c0caa07900300c0000c0041c0100111f815400d00507691011510302c6032008032132000d0001040b10403020001c0c0507034030181c401d52410340b03814001d0040c11403a10a4844900c0303286480140800100001d144082942050004000b001d070030000324ed6100c40381e100205140c0c0030340755055400c85 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 930203471 1250 930202221 930202291
    0x51806040504060e04050f0a05120c070f030b10080c0105040302060906041208070c081603120e0918070504020c030f0a051c0c111606050d06090c260402030303 70
    0x103402c0c15000034140c02a4010729014038060700603201e0911f01514407a96445ca40c840081c155842001e46191040c5590060050a40041d069403a2603503100c10115041038107400940c0d20920304001e101000b008880058000c003020f1010300904c41215001800314001c900c0060700580d000a5040b1003966442e08450103005850044d03e0760118a08008400d50011603085802042d5404042520700e0001039000e445840a00c1070742d107082c2941d40e1142008484451003050042c0d6200b945a030755140103035248a00d0540e070070413944541c6100014541030780e5038049801503104000070701030228040104c45007540e800f41c03216036560092038119024818000410b15500c411061445d5034483d40c0c0000c40c1c60000d40c0c1d600c0c0000c4209464842e200c2c1c1d114425070003907880ca10010882c040c01900a0402c000307040a000412969910051047c1c80c400302140000440c9801540080d0300e020b0881c0a85841244032080e0520309607001c60343e40d10016140c6002c2e00e041b610b52120750340703544101c40114 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 930204721 1250 930203471 930203479
    0xc1c1206030521131706011d15060c151014211f020a1202210c0c060f061807021906092a1e120c0f0b09090c0a0518060405 54
    0xba03039582403a410321017a81000300180d030040e0000010030402c580420451a88081e851041d2038840e54a14101c00d4001004d160308400284030901240f00c05011016049140c03a00d281031034901340203081280f50503030700204490000101501800d48030404801c00d0308540404081c004030200f851646458201c540201500c4500e14000c8070301803080e00507054400340f0b6180e0290200d00080c0b05070580c02071640b20b8110b4480000300c85d80c2c920081c441650011001c214039403070400900d00041c14458100e404008100c01002400780030b05143c005521130101040300308100d0300744800700a454019070a20158072841e016808410300c1625441005000d5205820b045a8420015032020045076484140041d01d000394001818802c5170030800111181400c407510218280a1040e024410403141078a81d1060040c0100350303103080c200c90320003a10300704010b02c0d00d913540c0e0000c005114000600880040e2421301080710f0554001c01070710064a00c41c08a42800441d110228181c0d000d1913004641c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 930205971 1250 930204721 930204757
    0x90615080d021b01110d021f06060c061116140706020105100603050411040c12050a0c020a0308040f0b01030503030f0903120115031413060615170c0c1c1206030521 72
    0x6d0142c00180442d80c03282d040b080c0304142c035180c24aa408a850034400c0402248480c50b2101c0050311552050582008512581e070414103080034202540b480d20100b00d50128812a12284121041020400410040c4001d00080c9803a0320460385246142c440c0d041890788079030125003080f480e1212019051000b41040003c0300c00240000d00c0380010024001141d46880c0c041242c001039401803241006c90760700103010300c001d981e5084844000050040d11440c00f40304081c0001846032800303e0085015100840d26403c10402e0756840100260030742e0300d254001c10903440910860207050381100d198800302c032141901c2840940c007030804903400d4001842d000d401c001007003003d11400c0f981c80340100030402216858007aa000c17150740090322800130030b031031041c030801d51103103003101a41c8944c240c0216030074030200f00f0301a49089005d9020b201416124040710f0906980722541c4103034135032941c40a0040360f00c0c40e00c07030588880b5842d401c0300018049a0f0040398040c8441c0885500b80301190004032 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 930207221 1250 930205971 930205993
    0x1110f0a12020703050d18170a09090c05031b0c0604080d0902090f010f0801020f030612211c0516030c02030903070b1216090621090615080d021b0111 66
    0x7a40804001c02807580b41540a40444480047d00c1882c1c41d4032005801100b81260120071a6070088602c80c0100a083d5001003a20340d9140a0141c4408094407001d88a0504130031001d42c1200158011203218000d1001e07540391900080c100350455041304100c0da42c0d580d5803442001410801030003035040b0346184207002c0102d0803c50b100341200c1c804039281b018192516121400d070700c540d0340790f000280030510111315945040c02410550401e100202c40b69014016902004103500700c808070118078000c2592014100c203020300040110415908014034074000c240082c14201c0b44002404041d50703100184e0170913000f0001c807a00501d00070102c9050710364400b0070300c200354405001c05071150b1082011811405211000303060314001d0382ca65109250030a0011150340200d0410b82e01850442c101e000c010055a00c12882d401d07010f044081000d00840c003084030200f00540c004481c9610405610803034a5000c101c450841815207400540c0e8502100104c4c0c00000380e1a01c1d003070034080e10320036403 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 930208471 1250 930207221 930207227
    0x306050703181b090b03030d0b1f020c0301061a0304260c0c030d0201180803090304031a1e060a0302010806040e030313030f0806010906271502010e01110f0a12020703 73
    0x200402c00a82c0d0204003c0343c0b11900f203802c1d58164101c03560594418003003000542c039175030800407400c0c40c040c04c0503845514889444140900101d1082e0245e009009010300c00d06080c0140c0b0054448034255400c201d1594800a0403440001e0018280b46162410072002d0400701c0302e001c600340f01000300182c8540d092744d00d20b500e4500c8280014070a01c901d0103105041070041c01445902c0641e412050081d6001c1d03155052294001016456607000030000400007400d85000d0860201d1045200c4c006807404940001c46808509807038400c000a920402c8440d595880070742d030aa90342881c001c0a40c3c0c0724000417401500c801c85a04515010100400a820011404809620b402640c82030401c0407824803d40d03400c04259800750004800700340074030500d03000d070b102c0e004614040040d4001e030340c5116188103402852904903820450203801a60f000d15424003544401085107402003000305145aa02c40003445810b103c11244040840c80d0468540141d00380262504018401d6589042c945802 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 930209721 1250 930208471 930208493
    0x711031305011b020a0e1f09050403081021020d021003020307170403021c050d1505030d0806130c09090627020a080601030e01060512060f0108030304030207030605070318 75
    0x2260015103c00705043c03141d9600c0041100700394010341211402030a1680d244661003009240701008181e8018003441d1190042e0701c0c10080039070480c00101350810340350040110030054075803012081800401c4c06076000d1981c0980e20011540c81d250000f0b102031011824506040d41301940c84103502000c40030858060300210301c10485030760f50200c020300c010702044041409031030260050b8001040d0061300383c00b02e00000a9103245092080c10400a44039940550300304c411407003440b1800460400c098102003220840c0402c0368100550726280c1003000c518807101c0c80691044254503100c211128601424401014040c600c3c03051000ca5104c0d04000781c0100c1d01804070400441c3c014a680c40403400b4800e0f0340c226615503541007280c1e1150300c011000b034110071040d49090756a40400040d107039195445c0d04003440320000949001d103484440c410b42c031201640301024640080041000003a804907965059a900000015103074444481c22802003554610f02052507026854400910155502c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 930210971 1250 930209721 930209729
    0xe0301060b030612030703081605040b07120201050709080c0f0a03170720011d13060305150615042d0902091e06300f1e01051807110313 60
    0x28400031344188074200b507940c0c41603070000b80028a503400811041340039881d4070144071801340b03040f45c1480e4594044440e280c1c0078883c1103c41e01d031031501e0b0844098081c01580d902401906181d0841031401c0d0000da2100e1684529a101c3c040c240703030340c9080c1da841044503400340d60841c0c03035a0840b40006108402c2540414001d49411603003552200c000101c070b010300140d40c00103a4030742c440034580b0381d034440c5039181303094069611008807154800324042c1882070740000c60046005180803001c10750340345600702014207401d019161003500e55110701c0c00e8900f1207084502a40c8114001a843c0240c1780e104603e0b94110300707400140c0038000460400c00e80142400100488850300c019070360901d2002c421807800c0c1105c0d0000028403501007100441c4140e42c5440d2121918030f000000148216420008101c50040800c1e0b40c02040c0300c03002d006503100a00071100200b9444581d414880090042109108001c1500413904001088070f84600030502010810b50101d070380b1480c01c1403e2902e41001401 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 930212221 1250 930210971 930210979
    0xf09051c080109090c15032a110604050601050d05010b030d0f030c2a0303091e120309020105120402030a020a0b0a02151603020f0f0706020d0b060711040c0e0301060b0306 75
    0x7001040c989514402d0400040d032110000c4091864004200c3c88010100080c07424035030350350009640d48810300451131080707041c20403100b180ca14048015046103400c0340c000400354424003c01001074000201a41503030012503807481c5035455446c0560244c40b10241c02c0da01401000c0340c088583e600420070720011780240d10300384210740910104540c55000303e03082c10350050a022442c507074a60420003586145029190120720701c8440d844840c83e501070441c420000480c651001020701c01c04c0400b40340804030754a0203028000d00c0d500001c216020b03181c0600301550321500801c045680c00c2101c080031950180ca0821899624001d000303a54110800000260142e0320121100d08200c5004511650404681c035402c00203403c0118001e402203509600a82d1040000c03446040011010304000c1d40309410140e030b5040700030307820019601801c425a010702018404040040c0c0d040d8440608401705442c00541e001a9150484032007200300c2895815520707000c000300f4070342000b8004506c1004103072 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 930213471 1250 930212221 930212237
    0x9090c0911210405060c1c0608061006080106020705090a0b0d03080f1803040312030e07092a17091c02070312090b030406020a090512100f0509030901030f09051c 71
    0xb1410b0740068011030b00189241c100b4000130350985442c0d806042d580da840884500c0c0c81d0f0301d030004607085a01039000b112155019004100007821805c9070403001c2c1c40c851a015031203524043d0040e41e01c41c10780c056640315003218400200d040303d26501009000300003c1207591000d80a0401810710358050704e00c01085111000000c01c3d5407032900000c441e0080342d00041d4a014075645856541c10503558400040549801c03a108800e00100500005045413080001d402c0c501c55519020300c001c0d100c414400010780c44003400301c140d000905905090304590360007519070b90748854141010b101c05500b800d100202c07549041140c1e400030b00d99058038421030401c0142040e651090f070310304c400362043d410805c2081000400154060300a050107024a0404100880d00c130000a80321041c4001c201e005941709825684003c02103004170b0361490f4005104110508102c42c2d20b42d100c2c82445940f50625440e284040d130740000f107078062400c003038008055030f1b000001c00c03c0c00d21503008400c601c100003a01003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 930214721 1250 930213471 930213517
    0x1e09052e1d100b040b0d052b0503070c05070f0902131a0901180e04080a120506060a0c020f0a0801020901140a05070204111e0327060109090c0911 64
    0x18031881c48a010070100904603414074a040402405804682c15001a00c540c4110100d031582107100107003510400150143c80c41c00d400c108030358800014048128402101044004c540000860780c01255a18202c550307031549081061405a09520a10340040f03044000a84130034154041d04011542c0031151111940d203038003000c0f407203034000501c2c11031450030400381181d1360098806c4843d03102c2c114407041449648440500900300100c0b030958240c840000c135191004c2d030141072140c0c5010300240c20003060424401040c40350013100c4d10101448060003600055588484074804042c20060178008043c1d1903800950107908070508041c08a10b0112200750325200c24011f442e0008041d03a0303403904011722502080090155200c681504034410010314100482100218040d00d010008450362424806801200068900c0f061140000c08401c00424100045400c0b030465002403008a00035420781031060040c0d10b594011500b09140091083d0200c11080152000c0102e041d8610140510 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 930215827 1106 930214721 930214751
    0xe060a09050f030a081e0412030e030d0f0f0501081f02030709081921020304140f060d050f0708060906040f0f0204030c0302090a1e09052e 61
    0x10001c116160740c40e0340d800d1b600105c01d80415000b600d016110308401000c800c0c5402c04040e2076101400017070b1000c0045c2c4890007403540f01000360070003070412003005080401800b0905400d042c000600c080c000b20b00403503031078400b000404007128500c1c421002548020140400d100e40428041607031706081001c68580c40c0303022050780b18101c0700d0030049070b80c04040c0380c031020201d04a001105066804010b580c12111750b043c00d21fa08001d50000aa031b2004500d03601c540056020807032545d212050b41005018028140f0b80d442ea545a0b240e0485080c00122400380e0055040b00c007080349428294807821010244040000e4664151034050050340c2c4554001d40c2d5510700c04c101481503150010030b464100080100420072512000021807115107c09040703100b071940c1c0d04403541031281c1400f80300b0f800c00c41028100305401900d942207a200e0704c11911400740c6440c000c3d060b96458a = true := by decide +kernel

theorem cover : BRFrame.Cov 930035971 930215827 := by
  have h0 := BRFrame.cov_init 930035971
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930035971 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 930035971 ≤ n) (h2 : n < 930215827) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
