-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2416
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:39:11.696011+00:00
-- url     : https://prove2.me/submissions/1cf77b0c-a9db-4a73-ac32-3dab31ca663d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 434352517 ≤ n < 434532374 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 434353767 1250 434352517 434352547
    0x21212090d024e0c010e010c08040b04030606090e060f060319060f060509130206030a0609020304140d020f0a0f05070807080d0305131a071806090905090109030c1502 73
    0x4440c0900040704100705074458401048042c5400f442c2891024040c0b20885002c1d44070410107010b41d041180303c00d19495a87c0c802c1092617007054100518690782c07a25090440c0f00c0e540103002c02d83e11a420410002240403852203060380c4a000b6001030409a2203a40307800303c82180c05170000340d1600c44ca411305c050030304a01580c031200e030340b0824001940b04c1940549400340c03602a400203101c1c0302c0640c10008040c20110052095590482d001035582c2d8843c0030080c01418182c02c00c04a5a00c044204010040303a070703003240d40f90341da01d400b21041300880b848100d070781d011511400b2826402500c41000024180350728100010300c55016142544d44170014180f03810103c0d40400240d0b8441c0444054181e054812160403c40000104010070444e46440c0c45886041800010a00c00b000003d0103d45c810800c80001c80d0344200b06008031540d400d0010494001c1e030052482c650b00d0940854554081449801c900f80d50640b16918401400d44980b0f202c09040d884074414150200301c0003403c1c60060b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 434355017 1250 434353767 434353819
    0x503060f09100e030309070f0602030a0f090b0f181e0f06070206070302070e15090705030604060b16050c0603130b04080c01090f1a040822050d050604021212090d02 72
    0x754004644a280c4546c070039142660a42c000c25002150031401e106181d808002c4400d41c0540e81065500310b11400012504105158001000c8400105400402e101d000000303061210301c0440102c200e000030f404104040e0380c0001010305850703c1804080007070806020a101229008203100c1c2002500e80108541c0d901c001e50482c0160000c2c9010f01011020a5403030750046001c85404109844030008101004030107001d03102480000700c00602c083d0341c1c0d0703007104015040303070409180c540080300e1802c0303609031405404480c03901442e104070442d800c000040d0380c8941c04a109500e084d42c0c00e44c60342555510007a2050320061010008481006000d0182c00c0c90180b243c64003922564041c2050b141400741b4002198802c0320200501001c181c1002c02d07650202c4070f4180d11103480890f410700903804030480d401310760814400002403043c0180480c0f41c511aa000759500740034601d1654070503032140c020494941c00c000d000d00003910709042060b200441a0300c0606440c65030440e00c40342807146008 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 434356267 1250 434355017 434355041
    0x4030203030d1e0603080a0309110a03050f070806100605160c0308070618020a0504050c0d0f0501090c140315061b010e0d020f060c090a21020411040503060f0910 71
    0x2507600d0661407108082040c2e4162440e240108401c904507906e40480380301d00150101015140c02d4001d06000714860f4400380000c0c000c0904812603a00d2a12540710144c1c2e800000042c01109000111030802040b07891003208103003511849241000c1c400e4400d5001400d04a800311a04403055000401051200002d5030140e045207072107151b40d10302002564010100110103050540c103040040c0c0301e0000306403d855007190301203070070f9a44480c400c10350f01880c06004651070401890310260b078600c0d4001816254401014006c00048007800c1d05c80711000710919004110810002d070168140c400203104000c0001e041fa4680b6084548644840c4d07400640a269a550b138140040142001c0128241151842c0003030092151000c40450301d40100421003e0030b0701c0d00141010031562001c0452001c4c0800d07520218043c840c10030030400e021464441280501c1c0352092000a40749c5040940c2d040b503100400918040d991803141051007030000c0c1501c070880c425110040002da429004210300f08c02 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 434357517 1250 434356267 434356271
    0xc050a03050319141b031608031005090709210602040611060a06050d0f1406070f0e0d080d0e0a0b01090c08010f05031c0203040f240201050603030a0e040204030203030d 74
    0x1000f84040750720490062110040c03101000101c0044031540095511041c03403034000060800c42c0d0414603045200f0748602111000103464010100700f8070320061030003040e10000a0220680301c500303022803644203031001008590310480820410643c01c6c08001400580222018aa80c1507070f00d44c8240e0300039802040210b034203c0078840c1b201c2010840c450f4088441300051007200d00c2e1201244040d00810405041c140c4514060024440403a0342c42008031030480c1110024500b0310401424800864407040c000307003070800340e01400d19150900c0e812207500304090502d4150320014582c0244045941e643e581d0040407004408511103103009070003030130b1448000c102c0d0a42c0103001010304005030454059400c0382e0600340025180058a4803c601c045200020041d0441c0780c10f03440d41c003c65214604500ca000c80102d8240c500c40c0707103451145080e402201114074051002d81c00d07200c085501603016441440b01c160b816220b00642e0f1b5806401a0005181c41d0b1a0b802190855014a0140304459 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 434358767 1250 434357517 434357527
    0xc01180f06150b0f0a0c0f060c1d010f082203120f020705061303050708180103051e0412110609010218030d02071404180302100c02010605010e09040c050a030503 71
    0x40094012142403501c8400703620402c1e03007401d040b06aa40198050500500008120122805e0107450000e080b9600050902c0350700c00245015409000d803c03503c08000390101c800030724401010040c06503001016110070451a4074003c003165400b100511105854502c4000c001042c1420020b10480c18001c3c3d450310031082080300b01c00306036002d81c1d00807210300e84100104004510003149490700a11404140440c001a41c142141d0382c3c09142e00c0a00200e0340000d4400b68402c01412076480f000003a28244019960b20361032468141e41c007000c00c0d21804200c3d0009000499101151903d01c0b0a4241842071144001c0040d180031002c4603859120383d80003429086241c980294001d890701c0403002041031010f0b001c1c0080d11408544102d14007146411070700c151030355403500300070320414a005c100e000400711410000c0d43e0b10b100c0c42c1080e1605181030040d001ca144103014050a0341c1741078540303030351510301340f070030312008190040090720016507800d80802c00e03546070075170b43c0015409140256160 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 434360017 1250 434358767 434358773
    0x8241c0606080d050f0318030a0302070b010e0114040c180e06120703120c0302010921090e010501090e091006081c020304060e01110708010f0207050111041a0c01180f 73
    0x207503226044600aa07201440003084a40d0180442d019056044156a12a01d54030344600300e401e481c0d1002a80c2e8040414848240e6a155014045c018020700d04031480c0d0340e035403108112481080c000e0381114004025110030030f091a822000f49031200b0f02e04046002c410351441c510030030329038100c400c2c4200f0340b505118007840c0260a1450141340b00002c0c0001c07900c2c41c1e49595041806504100074040560f244005140c000e5020031903840d00b14100315402c2011000002c80310404810f084003244828074040340700907503220f41e18141c0d54183c4480c0304050402440c60460303007009000036500d200301194400302a501c0e0056400400200d001400c282e00070421200e680d0354075030301d40c50456000f030004000c03141e401000c0c602226403e080503101c404034881542c0c1803040c2a04014902c1d801d04100c84201c40c4140d008102007400b80000b0803406510240214089c81588580101c0100503101c40c0100b0fa00769004161584200000080c0c3c540c00125042c0c00c0306104800395480c210f490440c03c00c0c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 434361267 1250 434360017 434360021
    0x120d1b080d021303020a090f0f0c081b0c010903080609070311090112061e061101020c060402211f0609020c0d08090a05060c030f090c03060103030305100504020d0b030d0f08241c06 79
    0x2800d902094144001c150968002f000c4550003070003a4810030126440d1035602c10a00c0841b503211101c44000e004842030b500b40900411000e0b2081c5010303003003040000308614070a20a00000246c2e50000600d080c1d0a0001150035683d54101145040d40da040c0002c1c440091000240c2d5051080c40b00d0380c0d40c28500304010348121000d07001400d090f4010040e03981c00100109926500560403910782410049400504c040081501c00d0f03699144140305441d820080c03030a400c013006982d1203100380b220f29103805103401a07015941c010000707a440308d1400c00b0494042d2800c698000850400c585d1280e036941c4980c1d180800035a101580350b40000103210309020703402e1070650f101d00002c3c0201104500f103c0800d9503414144006410141e0350008125440c40314000d01c0001e040043c000d548446a196030040104000c0c03900c0d9100744070f1700b046c8025050288102c968210402d84848843d0b545443c5450921480010710341b03050422820b900d503884c2c0c1d0b43c040c4142520b115043c14280101545804e1017 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 434362517 1250 434361267 434361281
    0xc0501080f130b0c09060310030b13201c0803070e04050f0a0903031b0801180b060d0b0a03020904080903060f091b03010605120d1b080d021303020a090f 67
    0x1d00d1824001c2009002d030340e445004a07806500c000210070954600341413103031034010f80507019486000003040c00700c520b07070700700032002500d02904040318140c03200b0000c24524018094002d00a8180c0e85009101569003540b8840d44600503141c01011b08021070440101c0003800c1c000c07111014084288001107a1115401000c0c0d8019a4204000c1c180045d01143e03981e4010030300d1401c01e45401c4130400b0103200b030700001d500d0040049441c0d40000300510107000100d090040c0c40c0c0d40c189540c0c00074520100c50190321302102e005001e00307282101e415810405460b0f8036100b036410135441940040180c5078011117505c95809100003e45801038141090708211000d04818529240c0c1c505100b99800081801c0320740381e0341c41141d000d4092540001c0303030143c1181d0344039952004102c01951030815002c900e4110041082da50704480054103542c0051500100d1000f4058080a01c00c241c02c1c8142cac2c1d0f008007540484200304100440e034a0340040c1c0f445940e60000400da5031940728034900e4240398010b6030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 434363767 1250 434362517 434362531
    0x810080328020123060d02060c01090b13020d08030403051c1b0c020a06110f01050108012a09060c11030a1412070b060d151802010807020a05060c22030c050108 70
    0x84a00348881c44e0500240c8030105500d2980315994021070b0b69030f030310110095203459010f07098513154464429014000c0c280d4030800d642c3d110f404c6000880d1007107c80c41005485500810042c14410340f40c8031039245030002801107003445010070501c016601441136052000540280c042421090080c1e25050f038000000c0070000d1143c3c0c900360a0050361000c1140313060b81c2c00d500c3c005000600905800e0320700071202c0014211546044000701d1041410740051514440c004007102240c51410702a0f4000814102070078002011f05a043c049288145241c94a40d03001d5084807020001e8200080c0c141299031200b140c4085007400b800164185c1409100350816107220f12608101c5681c0310880018801482035120340d041e80003040800a10306c0a072002c1c540e0580e41001a412510408036a10300602e80a9000c40d10240001d5007a61002900f80c400c182e001d405003607075480d06600c04060750000c3d16a440d128804462a500c0d4400c0440341000540c02401d880300441e1401001410201c00a4000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 434365017 1250 434363767 434363771
    0x61a04061110141501030e062406070503040302041514040903030e0d08060909280c0f1e05040228090b130905070309050a03080601030b060c0307030306170c0108100803280201 77
    0x402d5207e4070120307100e83d020421107104000e07035a42c0d99003a035040080c060303a070382d000401041003402d00c07100002038002d99109803010400d440820342c1040c0c401c00300d8450307506d1030144140b4103545814640c202c0343c4510f2003400c0108003014600d40007400c286854001c14002031040b4104249071415200c0650407a200c1000340c18015003000b000d1850050046000c244036051b1008101000072f03903480040146400c0400d50861602c6580303040c082c8051041100844200785008a1545082d20840e4550085c541845005642d0204991a00310100100d1014032408a50000b1b45211041c01405d54154182202071528100506803048480c05403680042520304203420000810000340707a03441030740600b88812030341d81d41c0b001280a0002c204681e50045008203280345008800400303801010701c0385d241800040d448441204010320b0326015201e940e03100c0c88203518954040c103405a0840801b4062089198541840b50b144d03511591318081c0101d5002c81d80800380d400d10548000b8030041d803000b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 434366267 1250 434365017 434365031
    0xf140708071403040206040305120403051005010509010909060f050c090a08012025061b081005040b010c0611030108060c0c03031602010f0603080d061a0406111014150103 75
    0x1400842000d82800b8424400004202135542c0c03070050b07400441d8000100c43c1d0781100b1540345202504544011902e505c6000d5508102c2105405402e0588401a00f4980940c0c81d1280351409000038030401da40c104e03504d04000d80000740d0390007101d200c1c201c56031400d84c2c1d940c56134003801000c940a0f403180c5542e03494103201076200c05615140341503a02c407140d640c0d51502503800510500540c02c0d200c0c98681d00c0c9440c520000c0110035003000d501c1000c84210f10300d41c54005482510301540440d854134807895114414481407500354050480694189460881021030780d458004440200d4000134031a80f01200401000c1c000700030301c42d40002d081920a003051100d040007a074134000542603610900d00d840380d20050b0f03813007540680d02c910b0034144240400c41d43ca0510b00d00700e070322100a07004080e00780340d8041020180602140743d0000c4900109180525061040303540201000501e1454040c071012401450355500400b0400300b855503801441d81002896491104414100385040c1030520070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 434367517 1250 434366267 434366281
    0x1202030609040303091401090c0911130306110c0313031110020a0b07030b19060806010e01020705040507090f031118070c0f020102031603020f07050307030b01090b060d0f140708 78
    0x11045401c030307505050119017044e8520301000403205184150145618201d10581400194003148044a288000c10010100c3c7d002d0255000c0c414001814621403085404100160385ea50141a00003000c0b0b03449401e0080d031031030913400c41c0e101c5080c54160b010251801d000380315601e61420f0342e0540860348000061403003040030352140035820b40036000210100004031042c0c06508003100101d00140305400a0498425940600c0d0840c0a600002091280002c0b01940940c442c06510641600140341c01c601e4031040002414004110340c04025844000041c02c490800303a800144d4441d40050f00501000c3e001c1c84078011182250610203060f0300184124030344c207d0222022507800880c3c17580640a00d0006034070354407582c01e501c01c4e03090321914660149580810b082d0f1383d1640c4203003550141c580da041090b9881040d8000a0890040c09004215901e6558403142c00c21002130b004904102000f0040c0d41250a254004605542c940c42c503c041d200d205140d0700e034800c4150405106901303200b0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 434368767 1250 434367517 434367529
    0x81b131509030c030b0406091203021908011d0a020c060403050a030e0c0609041a100207030519022101060b121608160e031e0106030b0a02030c09150c0f0c0112020306 73
    0x80b1002c5e1050542002003010710101e41c001041c095004a00d03e02c0481c00c082c001002580400d5148520040100c13117500d04501c110100ba040300c0100c0d0340710341001c0b900d550701104000040c02d0403d40e6603080103010b8000c0410710002c0d12981c025141d8070340b9130100c1c00c40030f001d5900b035051281007500070070403e45603641c4010684200410940d000540d1220042c01505203c40120055a00c0f004401000041c0c2da400a225410380f803140d0207481c0001030f80003505801002107003000b50b1010040380b1b4254441061301c05905641e03003036400418000e903542140305003a404030344a205d140c2908010410412440842d541121040749084101e52508840ca000c1c40d45402d0140c0b01009805d034610b999035542004014003940c05803a9100f400800991011300070000e034441143e000e070742c0c00c002401c40701c40351003601d2207040b24421031844c05038250308004030704d0505038120426807030620201902d00b070100459000c03201500c0040201704804400507260075215030903004c03c1d5004204020f101d031600 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 434370017 1250 434368767 434368769
    0xc120405061902100603060e07121106090d0b0901020d0e0318120304030b0c0a020c0102160e07170f0907150c0b040206090d2001090501080601081b131509030c 70
    0x30311004001900b442000304c0c20441c0c03804030704011504004012052040302d0784030200d00850720089070401a654010300c6100004890040d084403200c00b03006030759003032040090001500041011407991031039034170728401c94001d8601c80c3ca140c4d400306900751080d60900c9040e4505082100850500c05015040901c2d0b21b4500d1900d030140740c22031401090ce4000f007040c0c8000d150701103091544c07490680b80180081d00034203081c0707005104002e0f0880c4a5400804c0009103000349494802255042040d14810703150007425403804c104013146003004120059800e64012004c01c52956458209528400c0c6030400c00e0b084404840041d04c0090034164000446114065111400d20302680d15400029118003035400b420b80c02c151900b078101304100e00d09440405c81c1c800415074004030030707140d0011100c0740300030b004081c045644d200c0401c0c070f02d6020310b0110f42c0c000744407904001030385407030400c0e64031542000075030f0500790b28102e40900001c4101510140208070615110329401d10b107449004c40c00c0da007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 434371267 1250 434370017 434370037
    0xc0902070b061e151c0b0316120605040302100513110109050a1a130e010614070b040816080d0c08061f180801110405010e030c01020d0e01050c060c0c12040506 70
    0x200c009002d40300312880170f58000d40300800c902c6503a01041030060700a410b510700400d04c640180c3d520103c0380210702074403406817100703083d4044040c1d410360341e80001018064020742c19807051010034644400715025142c410310312400d50310050444e80c504103420302e402d00c90041c18041400c03c20b200980364008008121003203045110101c0000c0d40492016201d8004d000e14010703440c800c003080603110940e040f41290159a20b41d409110154642020741c055040c00800e106440b9003c980414043c50223082c038640c40481560340c8403a15039454031143e10540356481915125520810140d0700b000c0b40d0703544074006440d001c820707903515500c890060f01840e500030305010021040888249209041c000a402034500070015044045690b0071030780c010f0711481c1e000645032001344202d410f02081a403180503042c0c008196050117a20709452041d00808035504025040c05006280142004000e0040c4c80c0c42412076901c111100c0c81c5402d1001e00c0c10740c111492000c000030400c0b070b01c03580100c581c9800 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 434372517 1250 434371267 434371279
    0x1f0e04090f050601030308010e07020102071a06010e09152103071205040f082d1f0f02040b0d050609150f0d051516020f0604060908070c0902070b061e 66
    0x1058500790914031500003020703205102d40c0703001000f0181c0190b07079107042e508011b803d862266200c5a04900f81e100300d5000030849d01e150913000140f40340010409810100c14149903020072188400300d054124202c030160b040700c0041000c5c040b1420810501f014445040219402000d0a103ca5651300e203d1084010704441e21004d01641140c428000d403005050302441d010b828580e1010030350307900d542c2c80030708202407408010800030320340c1400414903009400c0006400c0b107100d404000c120412401c0c02c0c40103040c0e221101d551143ca5103200130006010050040e41d25604c100b5009011203270000c10843c05000320b1024001c0c42050041c00d100796000c1100e078010001c1c28007001c50307560f00c403110000341035204000c0d5072101d14101504541c468014184019806551442c04907030702d070b006840030015a00a1000b00303010032041d822102100d0b024850b002d1410004c0c2d0344200f09040c00e680300100c039645c0812740e0400c01141c3c0c03040310380003039040b9400b010500c43d0302c2020103142c3c0300d049600d1240c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 434373767 1250 434372517 434372531
    0x3060e0a030e130b060d06030317131704120c1404140c0a0216121203020307050d05060f09010602070311041514030106030b01060e121506150d18021f0e04 68
    0x50141c2c00ca8984c400300070f0700440e00d035280005100060219800b0450225110074500b411003000000c0e158410543c24510f55103038245a19124041a8070240003103842504102c0481c1e00807026529074001d0b441145a007503154581186d03580305102641079244168101100c03207500940600364150000100f820b000e50ba40700c0c400040c0d240080c0101c40551400318070100060b0061180020700e0000c0c000d016582c0b246028031030403812844201c0e04400482c02c18441341030401d0301c1d07178480e07540320f640500141d107818102d0f0002401e92034244d00c0b200050b801180e0030b1003040f009210280201c6001d032014030542110000b1382010b103800c1d00400b100700c0b0101c45034402903030303094004400468001c48001c080b961035410003807070404007d05460280c1d000d82c40502c8158030001d8040e40500c4001601e003400d0304d541d4200f2600d03981c40544001c80000503c00703402c0400c0703d4402c0b1405100224016803035102c182c41486900c0585910f0196460a5044280d20258005450501d42001260002450 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 434375017 1250 434373767 434373799
    0x204060e060a12050c0a0f0f020304140102030d1407110304050901030b061f020f120c0d08090f0d08010f1403060403051318090b01080d0e0103022b0603060e0a030e 72
    0x8030403c48003040030a04080900001c1d00070b200017041e078040c0756518500034014158064a041101c0d84140c00164000c201c208041202c03440b81210b04481481520b02d04410300307a0007804d4491085445007600500e50a01441c0380d00b001c0b0401c54820354801a500b0a071902c00080d003110b04c144006880c950101001501130f0341c40c82610121110340201c0784560248081c0c000b581d4421011a214540c41401e81044c4505020020f94a0b1080c0c030318000d012034040c0c8a802c58110001420820f090b10401d840110400b40c1805640e0443d18242e540d1009907140145c00c1003050540c0c0e000f2080c0b12170103100b9060907180803d00301e5015406040880c4d45260010907050029259400001c10f442d206055004501c0c141c0c00118255005a444a00998848000135290b92220207520003082c1a5515816954000c1e006490782a0601120103001280315540c030486100c030901c1105400e0307030380d2030a108121180c420318500702940c200500d0202c64554014100082d40d4001a104104105508001c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 434376267 1250 434375017 434375027
    0x60f07080a0204180e010c090806061212120726070e0a18140c030c04091109120d110102040b091905060a0503090601080a0218060d021207090e010204060e060a 70
    0x801c010513500d8a00a0b07004a082c000385200b07000030380c4950811014000c458482e0b0060801d40e80100d02821441d10354208122504840f01f030b641e02540a413000542c6d00407608400741154003e210441101c0d80342c85003004040f0958105a0503c1c40200311280720a0201000d1040c0c0c848098102200c64070044e40c0000c401b22125440400c01030307a1404800284050341c1c0140364003081007048010192104041002180011a0201e81145041c00100303c4141c3c0e0350084451036416219182c5002041c6000c2084601c075280d01c102070b0352004203031740c40c101d42c00000710021068481c000c50a00d401d000a00b18031b0312501c644244258141039480b0103607080d8000e0a802000000d0115590300c5a241e000307006500111400c90f0305018050000550000c0424a00e0030309500500d202c210300c0c4a01040e103d246030103001290419100751441d001a100c02900220300d0403207100501d040c0b4544084030f0306803203611031201516401403004000c903c0d0050200001c10070102d800c00c0d11503505001c201c035 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 434377517 1250 434376267 434376269
    0x5070e03030309031b0d02060f1509010e0f090705090105120313120203210409270809030c0a08030409110d0504060903270e13050a0c17060f07080a0204 67
    0x3905010020510640d03680000c003c00c0d052000303449115407440380182103034490722902034071405600403c0024800f00301928026500c840c0b0400b070261050082004202c280500360041b60742d9600c3c000a002c2c1d4512001c0d01a584511460004d090340e41c00d25002c940d03002e0043c81410b0094070620004880540180241c410b4040c0400e030781030300140d40d50714000c10b0307160140069000303004940c039402074809504464500f804820b1200380c40c140c0740c10844002899203c9881003070810740405468040403044400070000d020707100e41510b8580d0402054140551501c1a6201c0c2a140d0010482403070b0101c02d88d0100c4004600000d5600c3c003400e000d035054801d41c6200200030f45844208810030442e80c4c40340030701500a540300f404401004030398100034400a42c041ca4000c0c4140130801c2054507504040ea480080e000e920703840d41d00301369556854103d1096040701c49140c2a43c0501c20002d5454a04d00c9601403400100705505144518000f01a0090811420801c1340da0002e092504960100c40c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 434378767 1250 434377517 434377519
    0x100e01020a0503180901060203040311100504051206011802040501080109050709030f0803010e100e0a0b01050c010f0e011b0f030b011b200405060a0504020d0b150c010509030304031205070e 83
    0x25501e003041404e4285091110342c0c8075118207100c41c00403032120310010541d0141c81c4d04c01ea8081115141d90200b00e410b08040c900c000400000b088003007403548039584444a66412000101110350508190f0090300349580700200e142d07481404200179603a0b0040390181140c0c4607800001e425118148101d485c000240c0011701051001f110390410441054001c0d4109c0e00e41c0d2000702100d4950114201e00c80f2818843e822100701c0343c10106518191580c0300c80c41d40d1005060461821480d480421301391060203030b0f0354120315500d0015403c250b5080c09040000c81c0e81c2d094014203140349500150001007000350395010156900f407e02101d0340555282d2003018012840d0540211345480c2c220301041c03258810704d80c42e04890350701c00310900301030061074010100180081039190401d402d00009401c003912040e4000e44840d1058801d4503000151014450f03403140155440b5011540c2c50b094800240c0101a158410030030440401c0c3d005814100ea80050360303010482c0c0d00d40d03480072a1101440b051385 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 434380017 1250 434378767 434378773
    0xa060b03040f050d03090b180708010f060f0512031b03070501021b0d02062203120207030216210605070c050d0f14090a150c050a0b060a090902100e01020a05 69
    0x100042c401d610600c50b842c90711680840303c1e102200401241680c1120070300802014203640410031900000c549802d84e502500101c032070f925035a1a0017401d445104840341d065680c3e484050058024202130780c130181000f0b88410300115151349450359644a40501ca0880c1103442500946503903007442161070782c079080402951110703030510f541c0782d400035203000204041c480c140211062038001b04126102e5030400100ba07003c1c040c480d06a589000756807404030100145800e0007034001001d48060401c2c00e0103a4000d10324496070030003404842c42c19820400e270700310503c400c4880003040413060703c0d4055800394002c2101c0d1168102a183c0651055000b042ca018078000701c45a690300c0500750104100e565200d2a1210000041e14803600c10003038400d41088005406008506290002c121401c14a1424029280d41e41d2070301400d00d0b82801044422064400600c51985400181d2802411200b14100640109540092144069140c1210a000c104000d2210710381c0280860030031141c100040d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 434381267 1250 434380017 434380021
    0x90909030e010306081b0f030304050d1a090f1914011d01051e16020c03030a080406110a0203070605150d0530030a0506031e010f061502150a060b03 65
    0x80903202011041c0c100d40000e103020300000f4201c100007145610070a640c681703080919140e206210101111500d900e0301803100300000141c58485c4002c10614038000c1000028090741002c002c000300c1c5000c0c00321304050b0320108e006010101c011444288038071b103004605c0203110f002d10b46184008615040c2615030351916402c184082110702c5600f007080403100081280d0b036594164104542201140e0700d801240e0200080c0c042c003950404c440c004030300c1340100c1c0c0b14040c06a00003491640303c90302001c0000d402500784400c2102c00e0094140111056001c2810325041c400700956a0241c3d00c0d028003426212030200b02000318010100d0b003001005840354603500d0840c04c0c180d503944035402e0b06640b520a10122058200740002540000c50b030001d0a880c0ba44e00c8410303002d405000090001030b4103000b0a00190840180b04c40c0290f01c194a000000c01e00c56030081c103480884065500c0410031854400341600c80329800b203201c800101d0284110009512a180100e005100c1074020810081c00041 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 434382517 1250 434381267 434381273
    0x207171606020414100503070f0309020406030204110a0908010c0c1b050a06030905060604050103030c020d030e100c031d0a090c03110a0201360b040201030207020a03200103020c10090201090909 85
    0xd00305440341d0054543d030685e03c10740c1034221800d100840b607200c0019065140040c65500c02e400c00008640010000300719035440b0f40000b030807035000140c03d4a03103c10000b204041103801800250041c0b600704003c000e801d55161014054075601d0400410080300039032a511740d40895030495014000c058101c0076210349580002d0001c0062180039503840c490900028030724501800703554140d075815074500b40d80440503824400343d510020021818816440031924036500e82440b15110310403655a090030155003420080e000b0780f26060314007500d116017000756149803603451880085405181c4002105884004210b000340203400389114454030000d4401145907054018080c82c03041303a6560500201c0c007001e031030f4840d640074031041070681c0e50500c00d10115145200d4281d01a0046c1400f61070600d030760f80040e02c03190303030fa801c21144141e650000c07840801d030101100300c0918080c00c04501d8150351400da5507899500080b8002d14640318401c820441e4401d9151100825280b076043c00141d034946 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 434383767 1250 434382517 434382539
    0x131208040203240615090d02040c09030807030c1e051e070503030f0304050606100f0302030a0f0905100c140301170f0a060507020105130305031303030608120702030f0102071716060204 81
    0x2441301880f030040c1c031010032622040241101c003d80c42c0144400c204501d40d07824000078101022510040c09003042000020900c0310340180700e200e21036507450042c00007074034194020000c1d0a8100c011007500403440c000040b80000d003031100c68515075943d070540d200e0f10801413800c50310360003194250101207511420040340c40040c5019a10a4090b41e14179901d500601626090341c4103c1d9001036408040d40c0030490180d4001d54000c40d8001001c00c02c010842200010303608c004400715460303845040c085001c4962441096403481180c50616101804d0200c00030b12400306001d040000c1503842c1200807414010006006a580e0800035180009040e040002c01440102d581d000594208400501d0200b20070882502265154640c1419500c40002c01e000d00c10740280c046052553f240c4010507051001c110100101c0c0610710020f550328114810705040519803100500c0c0781e80103000c03c800085000c00740360441801000c0d660380740e1002a91010f658821000058141d9100190208c0c48076150 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 434385017 1250 434383767 434383771
    0x80a0e0d031401090c14030405150c0a0905010801060509090c0c0a05060714040f09020c010e0f010b1314010e0c130f05100903030206070f0e0a150813120804020324 72
    0x2c028042c1d42d03a0303039a0341c03031001e50320710070a90b600240c2425014540c000d444000745030031a001e80102c5500c950302e94008101e414040c1c1e20401c1050000c20129009980421414041c0100386080c6900e549484070182560040704078107031042d80340c10300048071031741e5182c240c4600340c64013401c84520200c1c50070165140c0c1020b4401100050f524400004100003a80441e81110811820f0000f05494000e40000a420000c0c03401e40554940740c46042034001000012142c50f8147c000042d0204114100500b40700044503d10707020f800c00d0304101185241445c00d07411102e0704030321641d0903a11400041341d24450803d0306980d242c07540c503011400c040440f00c01c1c82030f61390507500070800329550030094a402d0201c1c44000d0040c0e0090300010b00880c8180c440d02e582c0c078101c0c00e044610300911780c00100401916008480c0c4c8410080d1001000c40c3e1280c82640c10103080400ca8604110319100d80084480c040341d41c000780082040410215102002200740441a1312014800d40d8211542004000c4003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 434386267 1250 434385017 434385041
    0xd0b0408040510020303040b0c070f0b16090f03170705070e0c0403060608010510060f0504030c0b0a02010c17011a0f0310080c0111190812070203220510080a0e0d03 72
    0xc0000000d610f41e00010444c2e0085410000828107907496150020107944186003c40d0040c0f442564503000030548403906009a00f01030419020682d00d8200912082140d84200c104c500072080c20000b05070005641d01c100b101400c54a81e440c81c0609201e4a059400c0d0f01940a1005500402c40301c114900080c0c415a4070441c41403004565613540d1500380c640c19911144601c207040340400056005445a100781c150f07500381141025a6500d940e00f41c0c603140e0f480581000000a1000040303039082c401c080c0c0f0340c076440c1821009090008140c0300640c60502a6208140e81e56003141150120402941d01040142000035500d20b0006452800d82d8074a10900001e403040101040b02e03036004000041070349854800519003420340301c903010f04409000e1b906503000303502005100070082c0100100c0388101a99002036640d1040422890b4902113140c0480b01c0030b0b4903010050040790b50300940002140d04900e4000c441e5220401c3c090020682000059400d1060b20302140b40c00360103421561010320 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 434387517 1250 434386267 434386279
    0x30f060203071b210e061209010f0c031b1107060513151d0a05130902040e0307051605010305070e04050912040f1a0307021f0e0703031215180b0d0b04080405 69
    0x1581c3d500030703030b03049880003011740c4d1008090046000210030901c080380c6c030074110000800c40c42044d058000448540e00d2890000a071102000c8030140680c0c128407502c0b000c1c5280c801000d80503c0840c540300d101900030032081160004c3c0c4c0800000704150703090050244400000c1c4035891050300508010360200c0d1900598069800a102c00e107840e032840c030101e0310040c201c006000c420f6103c0c400103010b0320204aa005664409080a1070010006441058464001804034120010b2074003485101c651010b4101030401c0104016a68405110b220241050310080b40c25207071100d80504001c4115007189080b040407800060107004c001410041354600c034007000c00102c42c0241802148011a21800945d04c645102d40300030080b4075062941c014130710400505260446049400c0000c01d41c8143c002809404200c1104240380c825503841603400c44410a100b840c080f961a982c00c202c070038440f011680c540c071142c031342d071508203080b8107190344809184d1140c43c1916100c039141c0c01500a84d40596 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 434388767 1250 434387517 434387573
    0x901120b0f071d0627090f060a15111002030601090602010605030304051009232b02060c0102071e03030e03041d04060204030203010903080609060a030f060203071b 72
    0xca86007001e6000b040c255440000f04400042e51601d20800e030501d068012104016601380310040c03124029203207040510070030815070420100211044080d24280c0383d0b00000051041c180d88031020381c4200c0f051705c810340c010000740c2d10007910240a00e4920b41c13410301031103c40d5495140c42d580158410b007400d807600b005c056102c00c001c07822645940141501a0f000700005d01480c90300e140e01008000303036890404141a00c44007860781c89106105905903520034420246070394540312100c0704808103441100700c0d100d024070a00445041d01c121000e40104400500d2613210f48003901210308507504088461001002c59445041c0740c0844142039000905c2c10364603410703a02d404000c450455903000d031080819903450302a00b03202e00000d002211115030812000006881c00c0c0208801140652140e0820786040414001c0c402002454039104000d2990248001180c81c0d003c1341b075081e000305005849940c2c18205540e41c18186205502200145207044100140525184204000709480007152 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 434390017 1250 434388767 434388781
    0x50903040303020307111207030f020a0501051801120b03010903021c140d0b01030605090f06040b03030c07060e0303090301060b07030f080114040911043b06060d110901120b 76
    0x900031800000c0c0180c008001d00c40c045407201501556404c0c005216981d12085522141c0c5040152390086440c80c41c0c00f20f9000540c908031541d48000d050a0034440d00c0c128200c3e00d11110011065503a5060150a9003103043e00000c0b68080114028040c0c02080068406e0501a43c0d0744005801c10f940040d032541c0110340c5a2144002084e002c070050710745810202c203100d80700090045241403c0c10103030f54182c0050940c1c2c07250307561070042c0c40300411013074507050050501c000e45180a906a0203540708204840b840e44c400508501120078a282641d00083d0040009056115143c02c13594950b09281c40480d84958131001061f08030310a484000c6481d04401c070544000500f4406c694101042142c40e2400d402c00f034020211051041ca50424500503c10000e0200c5900499034141c5100e0403440d00551032840018081c0298054854403044081601444d075808002700014001c1000042c100d080008100301c06400e458000e0441501e0741e1240c1400340074101e101021344040164102145407 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 434391267 1250 434390017 434390023
    0x6080d020601150e030106030b270c010318080c010e1c0903150906050f06030d140304080705070b0403050c0a0603090b0406150b0d0e010c020d0923030d02010f0509 72
    0x10140658000d40740580c6402c00919611808050303002c140310128640c1691075400b840f40002840c8501c0b002161400d0409a0200c030704440c80c1d000103005403885c4c021440000010300d11245000c240380110390b2004440c20144c6030824120000d2008101090200c10000f041d013003007004114201c119500e140320b6500c158103800c00084200c01140d0051800d00101d421045003a400b80120389001c01d410b800c03580c80070100e030000c80e0031210b00003002041c0523181c07070107100340ca030042d0b628a0000c6242c400c200e0030302818130000d040104080c2000807a041001410710000c07004010050160740c9990303607030403c55191022080028031401d01007901295080c081d01c45e034150144c0121107451181e80d40e9403002c0081c1107440c43c0510b100c4c62502c1c0000c850301000c00918810400d24004504214021450350035203485a01c0700007507400284114440326072110590f0200c4e886004800c0d000071030b2000b141c8801c0b8214603629014003408a004c00c8054054004003035600d0b0180c010403c0da6203800c11651 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 434392517 1250 434391267 434391283
    0xe0a020d0f0218090c0f21041a070201063008041404140c0d0e01063308130f1703073f0203090115150201180804030f0303060504021c0608 61
    0x401d11170074840c0780c2c0c81c6098640503101c05d5001024480080341d9044809601082c2110300312440304c2c04000d20400d51500e8080680c00600364002071010038100154081c01d40714008509190358201d10138104210b504035031500318682c00c5400b4940da103459001e078810f612020b40105005070704000300340545d0b144100d0101d200d14a0712210781d04142c0302d08181c50260000326101001e643d00e482010440120b50a85039010580c0c0721450fa905a030102030082c07042b004505100144100103040001d6180310a5000550a40c0708805514a40c241d14041d0486580c51815281e4a04007104004005420992040c02c0c140010403061003d4014650594010907102c40d1245420400b180e20325043d006401543d0814000400407902c41d0342c40140545030060b03544003044106100100c0b0402c3c0c4d40a1144ea0b0134174119400c0384004944a80710315041c1d114500c002440542200180c800b03051107548070318040c010081055684150b4490000036107001034018103101c070700d88000002c540000161481c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 434393767 1250 434392517 434392531
    0x3010608010b090d03200d0c2001141b0613020102101e110405091e1003020609060a030f0626061902070c0810020a17060a0e0a020d0f021809 62
    0x200d050080340d941124001c0844190903030302210806c8074400900144014000c119a5036a050041c2d50b183c10714004003803c503d800c003000c17144d0440106440c1da11850700d800002554103000c3d500c0c1d41c0a15040405c1c9100c0603841c0b014091003050080d40081c0f4020200d00038000d908803581081242d0150302210700b0f400f241c81d194044000a41c00803105500301c2e05150702d103000d2090a03d0340c1d0b0300110700d5400e81210b821102034594181c038807030748002500441d08204200703070060041d0308503400f0410038803400b01114840c2c040415551380b0035119400603c100e85482500f4003155a45800c00c007801d0100400e4200540440e5201c1c1160b604001021b40c07081c1c0540c65007420404441c4040c2009500c10841594800706200c80450320390b00400050440c803543e0b00300160f0701e42e41001c0084c01e076481e0b51503ca01c0e40700c10300c003403145554035400c590342a01c5d400305a40c0c005440d000d581200a11402105026141c11720511200603212036000e0301400c1c19405403c000800b58104000d030315441145c80d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 434395017 1250 434393767 434393779
    0x120a06050111030339070c06080f0405030a0302090d12020c031e03030402060c010920030106050a05010815040e0d0305040b090a020303160c0504050109021e030c04120507050406060503010608010b09 87
    0x103584072040c22041d4040c69404510b8008201005c8204c00c50260300800701580d030207462000070400380d0f51206025a004e0038000865091342420356a550b124410044104101038002c1141c21141c0c1d10f142140540c0c80e44840079051080d400c1d08007030744502010303505500ca030154030759a0a40a00c040614a5840514400b440c51907545508201d504d811800107071940f596a404504002894600c0c1c41c10541504c444004141c40781404060a441041e000140520040e400400c01030740c21284194200e0904500841501085000b01d0010925100d518115205154000090741d0301540640d0141d4000c0400035029594041c90b641e03212500000250143d0040015128150070f0000500d042c038441c1040c40a120b98500004040d94001e0700030b01080d640c009002d907180c070303400b10f11f1054403e05800058154901501200c0e40c80c001c41c421302101c0c1042c440070700708110061090340c01400f40100200303c10707a15601c00070510f8209004e0031003c1600c0800200b01500e502042d100c000000901c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 434396267 1250 434395017 434395051
    0x70e03070509100305030a0908071202091503100501090b0f101707030213091a220f110a030b010807050306030304092a0f090605091014120a060501110303 68
    0x6102e40b119006007480c1d800d00d6000d0340840000c100b4401050800400c0c2e44000280d801e240c00f860500c1041c0d48410b004189020854005840e80c40046511003400c4d0325075000c4000400100c3e00f0a0300405403041c0f4249060000b00b0b06030110383c05503420783e2054601c40f410540d404140301d50418182080c5001c96086000068160550740700f05510011a1a000d420b011a2002444400c8459084040020303102c40c01450482552200b0300c1044804640c01d402c3c0f114011809a02c2100500146481c192101000c074000b455503000f1045003124002c40036038520030080c00030024520790f00316500042e140d10120386440e1080081d03a00914008016500c0e00d454841ca4400410822034003a0b43da400f008405e058410032601060b42d07901007511045050020060001c0c00c6d070700303250000014000d003405050f800d9110a24101c0303c091a60608401903001580c000f10240500a1000c002482c40e000704441224950800d03021287c00f80c9429542000c81008103851340000c0700ea01c03603c1d6503604030b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 434397517 1250 434396267 434396269
    0x6040207020109090905100f0c0e01050903071215050f0408030c1602091f05031b040f060b0f0405031507360305010506091f06030906060f06020d0305070e030705 71
    0x4000c0250030700c141031010285503075054081c10388940c503074241c1e03081d0410010102e200c15180600350182d0030142d0b041220321011000942a80050000c560400001184850207a00c00300b2109014100014030000c40500e5032400c900c003103100c2c1d601040c1450038200071991040400f041140500d5200d031219003190740b5108242416005402c01c0d8048412220954000d6190f070711900d03000d11144113811400c903194041118243c011603104500070f601c002c09914141c41c641c2e20700b2240e0181120049090803503150881e000c1c00243e00100b0742804005090300404e8105001082110016070903211407a00484e541c00901000f01e4407039000c079824800944208900c0c6d4021280445003500c4141c4d0303009020340301c02035400c0c1c80d0002c84482e951035050290602d0700c0065140c0c811070017610703908a00b002140d9214101d20138803034601455161740c0781e54208580ba40068002c0c10b030004414403a16500d20009655602844880021034036080105003100d10500000000c2e10018000b4000e03107140030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 434398767 1250 434397517 434397521
    0x801050a030323030403020a2001170a150b040906051905040207050f060c04060e062d040510050703120e071a25030809010e070905060409020414011802030402090604 73
    0xb00f4200d4090191068000b040c51180083e500450196005103a01001031401310400f90035280114140390b0704002c00807842c0c0e0702ca00c03083c10f010040240030041d40c80e0984884060f04910401d2202000319010110304454000c0c082c4c0101c0700c0c2a1000d1110a40d12010b000080c0084500e00400c0c0d880300c2000c0c02030382000d8005001241c8a00100c50410017044242800c102098034940008400060308003c81940103020386004207044071868513000801c1d548508001c107070000020710710242013210595003492810303500102805042840c0c0010b0420f40100039600482c01100820380c40b4880d40c038403900c503210392011b400f01c880050071141d08004115035088004c01c403407081c4520400548130b1002d00700c140c0030b9000100182c025900d152038540504828001004800c690307240001183c006200051140100c4031400c1c00040c4540f900c2010a000d0081e154010f50081d040148844200b460030004604903041a1030703144241c56440d0b040000d0f0b103c02d44000c5c2d4090120008950285810b0b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 434400017 1250 434398767 434398787
    0x114031207050313180f020c0303040b04020a03050a0b0a050a09050705010e0307050607050c0f100815060403121805030a0f0b070c05100b1f0c230129010801050a0303 73
    0x40c4100ea06142c81c4c1071284100944a400080c55908001c1c156045200c0a000c0e0001640381c16405604140400c02d4031a40c2e40001000a888012810042001c1d500c0341030074034010b903400405890b0103101c0740c01c0c03540501e0810385600400c0e40c5803038001995a845403207640241940800940708091500c401191030014000310140d05000c0c1000004090303a84070020300842e032088000d480c9c07a1020104208e142c010802c09140a1500368040146460b032182503181c1c05003007800c51481c50f00050000c215940115003008280c40540d04040d10415003054000f00c180040404050a0a80f44c00600d038403042600b01c010322a1a2a002100011340141011a400050b6180c40c1c031401a99854091420810602e002d0b04681c0d11a0813041c2e0b410320416142105032001c510070608240010014216078803280b010344000300d80150748200210304d81c00c00700f40c0181e1400a100584104502c2141402510362040040d030807a14590b620b5406249a24104c1318002e180c004c290303295803426240310200d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 434401267 1250 434400017 434400023
    0xc040c05191101180c0902031e0c040339050102030a0e030c060403080a020c061309050403030902120d0e03010c05030c0d090804030308010315051605090103020912150114031207 78
    0x1960003a910100070034031910310000700c400511501c050035070401405c43c54154200343c415038010001c100c0540580d19101c1c012070003282d900b852990302c281851445001d01d400c010444004003240000c02050981050705200b810707900c810820046071200087e4880a01c2142d026170028401134070024080c2846c01c4940704040c06507800201c08200007445644642c100b241e0b80c00c004075040044650401048284038401e58003d40713040d8035000031204402c0706101e00000d0546400000e01050f101e6008981110740c040c000390092104d040180e83c660440c07038001c00014155a03e031200b180b80500070f10358502216107896240d911640c146c541d85038050034417001099151548540014500d4004000640c0240c2d40c10610754190b2030210500b0034014040d0b652030f800c10084c4810b20482e82c840e90a8400181403c0c0d41c0c0390805801a0041d004030540c8640c05109170400041084000c2150b0b60354020207000b1580c0ca03030b01c600041040044102101c2c1c0c0681c0401461645d52250000901110340 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 434402517 1250 434401267 434401277
    0x80136030306180c0212030103020f04020c010906090b09121213031b0302010b1c03120c171302041d120306060d0f061e0b0d180506010b070201020c040c0519 69
    0x34551408290103550000803005903a80c645032403100d03030345c14804041c800c1020790120f8519495034000076400c8a0742c4a0040c0b1a0b81d00240c0c0c154080030940c8007820190b4007201c1071200805c03502b001c0400110071914080c1c98003031026180b41000d000b904072040c2d02c02c001c10710091500e45109044900712842e800701d052142c144001011105070b9428118568400e5002050f481d007030b0303006c0c000034000d240144c00740384002c5825040002e030040d07084002070034210400940f0444e050012160f14001d5014a00d1003000f007000d204002410b80c5000d04454006d540a214460b0081ca200f61441aa6205000780303411480d85500035003009002541c0200c40184802e06000043c14200c0480d200c00fa41c8900590761281c0407c40c0810480c0c0b41107500400d400034404080c034000300343c40399120f15050034002c00e40e244070360910b0a000d40040b006203600041103994540c6c440000a1169008260a074051f100d075400e11060752600780100b0001350480d03540ea03400c00d0204c04030303401c52028446001040c0700b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 434403767 1250 434402517 434402519
    0x3090c0303131d040201051c0209060c2409070320061914210a18080403142404020f09070905011e050f07030504030506040b01080136030306 62
    0x19900304040d018107425512003010080c07a06902616141c1440703c1c80026021070380401000d42c0e040025200c1d42c0007250240d0005519605c13001c002480b80013141075001c100807e021000c80000640c4030240c0d66801c18101d65030041004007803800c44115956041d0307600c105018000204ca0310318895040c0d141c4010303464419201e0000500d05c0c0c00090b544602c802c440c0c40b48091542e4400b01c1d1201c2e0243d4070f4106490442070b0180c207000c1035410b0000f001c842c1d01c04408509002c43c0b952210f00d21084990346050b01d0102451300841c2075103d840103860242400e0040e5680071008620240020100d0310000040c2d07002669550703407010b0080003a640207032480003113030217a101c180d4017510450107981d400390b010b03090000240c072544c00310040d81100c01190110882ca41d4202c01114400d41513642c1d42500c41e12140780480c0e003446240c100030098021201800b00b0000200d00d81c0d0706035881e1000a00010b0001d06800b200702c07106507074480b5000440c1c0000a20540908002d4450600130301d404a515 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 434405017 1250 434403767 434403769
    0x30706020d050f07030519090212010e010605090a0c05030417070b0709090e01021809180d0e010908010209090c1b0303180c0d11060a121803030c05160803090c 70
    0x1e030440844001d100c1c1e101d200b0031186506110314164020854101044241000b250440c8246403824040480b642da0303080601c01d65680c0c4c2c0c000e606580c0341000034810515540b0803180648260f1049500603440759002c40e40050b15800b0b58284a1107d03540c0b2421661180c580c0d03001e224848092a10441040000b0000308508002c41407058009071a0000320a24102e4944112441000c6401d0540d1041c401094800c0f17001c80400e0b0506030841d0f42030400d88540c0c00f4540d904c2402981010284107000c4018030355500100c4030070080f002600d0b001c07207480e964441030742030748100c00a080c2d01c980a00005490903c6150250400200c4903802404100c2c1140c0f409103141d0041d00e0102481800c1c014905809104001c08070403090262032420000c0c0050742c070009034420030035101e4031440b000703d03c84141c640318520040c590303551315600b4000e0290008006940a481d100150006810010070111660191045402c245103608001000c1441030b11303000b003140c001411003000d034081d038030343c81c04a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 434406267 1250 434405017 434405021
    0x60f19020a031a040b0303040e04051603050a02090606071101110309060703020c040f02130303030c0302070c0b0a03051008070302120a0b010f080f0a0209060d1b120c05031207020111030706 83
    0x1022015440000380100f240c421100c0c01c1078828141c80c4120300304459031986407400310a850442e943d140b1420740c5600c880c41e0650401403250000e03c070307000300101c0010a014000844400103402503420703000036240d0205002041c4988040542000c0d14205081302ca5446a201d0002d082c1108003924100028000011041d034007003a03041c1c0040e0b0001210802d0361074540700b008a1903001f124214904104400354042c0c032051032201800340b5603038411aa0075680240c0444003003952000da0411081e89413220300000390441030384000024940301c0019030008034021703010180c4140c0401005200d1655080182d0380280c0c9542e0f4406010b001a540e0015404880c140c4c00303442144050480e40d0300703120a244c5061002070020240c1c1d07000740804030140c2c4401038042d40200341542d408084030441d06000041a0300800440e100d042050f80009a400e1450fa0f2a42114498015028003e40d40d500b05992140c00c010140440c210030820f4000542c000c0055081d5428200300356802c01e005500c80c030702 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 434407517 1250 434406267 434406277
    0x2040507110f0c01081f051c060e2b091503090302150105060301030b1302090901021801030626071a0403020103240306020315060c010e010c050c060f1902 68
    0x7160031a000d16059080510086401c8884000144910041440000c00c259070180c111698058046a40c180f02403003c18540c3c0545005024a5146400781038081e00d0503006801c1030b10f03d43d02c0c04400105582c40419460800910341d003540c0e102410440c001001104032841c0c4106100044d02c2c001920640b01145030543c14039501e00160106203400d000e0f04001410307071400d04001480c0010300c4141c0c2e03081e05031b0341034a82203951403009aa9041a00d081a120481e0281d80200c50b2010002c40d1030054009080e4000c4600311040d08030001c000540030746815004480f400c2e0f029449000c40101c0c01c90200610500042c201d54080d03944507010b841d4071945030300c0c19200c0180001d043c01956010b005020034003614055241191400140011690300b640c0001000c0540000204110700f0015038580e41110340109642d96403000e40e002180201411135030030000b5428110100390701802038048d661101401000303041c2c13780e0392441d0a020024006c103410060100c0d1000c15485000030303c0980 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 434408767 1250 434407517 434407531
    0xd0b090907030b1e01090f1404061a1509060307091703040503120f0313060605030d03050109060f060f08040203070e0a020c162304020f03130c06080403051b0a020405 73
    0x10810a00350704001601c003c0c000c1500f041d4000c01219900550310320081241152504a8005400003190030640058101c500c10410321224120500041c00000e90001152402403180c84194601c0c0c1828060580c414880c90484901e05008420300c070b0401d00d00035a0301814a01e0207000c404d4072940e80c403100702850307051550603600c0400d0921503800c0800c601c044400210842508004011400c42d015120041c00204607803001d4801c1020480c1a81083c030117008000c0c00d8407801e48404034000c0040a007442641491401d003e00000c100c2700499000c030544a940c2d403044450006801c040d51083d0000d0030417601071084940014801190500580c01240e880c440540e6420030a219280307800c6032901501c03503840d0010401c01c080c0021000c1800c80081c0d0310a94110031a09900090090040c801c0c007144000000040181c41103c400048601030f100c0c00c60394000071f031a90f10031074920b00b0880700100400c80030495142e4201c001107145540307486581c01c0b42c0100b4419400708084d02e81c261006 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 434410017 1250 434408767 434408773
    0x30409090f050a0f0b0906040209040f031403010b070302010b040e0a17040806161e020c01031d031b1605130b060705120a0207050d12110a0501110a260703020d0b0909 73
    0x440030000b40e6442184c004e1a0301c03000784441d0500c1e2700010824040680012b111403c80d1003500205401a0313100a00445120020b030b840c2c0da900c55510001d9400309504400551a140601845140c50b21405d068858440014019080d0300d07540c1c0c5070080c503041b040d10500c0c0c1003071000107030250003000340728841d03000c01c4502400b60b0310351b0101410106018902c104030000300008032040b2980028602ea0407034003440c000c80c1919403115507582c14401d00700700507018000051680003950710a05240160500b800803600b00c60f07842d41000c450702c10580142170340311402700000c00e0003461940140c02c80800040007903162012070381c1d81c0c51a01411a410046914020036226507c3c1c2e014800d10000300f01c00d486510040c0d18913602c54030980c2880c0321410078003000a4a40c031204c207041158030400390b8854000c1101d02ca13a8940407405030054201d03d0f00140751448039042c000c580d180401001c001e40d500c600529150b540c42a006900101c4096100030354030300d182950359403000d18860140c83c1c110b001d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 434411267 1250 434410017 434410043
    0x1101050106180806070e0613030c0b0703020f0607050f1c0f0b19030201020a151b0915030903051e09270601030e060718030b0106030c0806030f030409090f050a 70
    0x101c40752203840c2e50203e6241e802082c10408455085183c00c5141001201d034955290300042070072100711095040501840340b00b40d404184254820004c141e514040c2d022200c3e40b05038070381600d40d1984102c684400180050240b9140048203102804109c6200c1282e8070361419000d40c1ca0b402c503940358a10b8425180c8900e810075003410402c000102d0080400400f034501d90550700081c2d92001c5000c03000b40442881d0210700045410340d80a0703400031030008240c040303020a40784000c1c260700b8107028001481000c4041034800600900c81d0b12a91540741e110182011031001281d103d000e80b005220303400003000c10814055940d401d81110014807024618031f60f06425070381c0741a401c14018101d9041c54540a140b680c916000211140d0108081c0350004002540005a01040b2507d0388024a2004003000105a940d01604030f040c1821880d9620300c3c0070350310704041554801c3c0b003500006503504204014000104140c02011034140120b541009260b41580c95502d040040c80c000c1c0d8040b004044 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 434412517 1250 434411267 434411297
    0xa0b070804060b0603010510050315061909060215010314010e010204080124060e0603040c03060f020c1c080114010302070f0803061003050603032b0c1d09010f151101050106 76
    0xb280f0700c2c2412080c0e030b00c01d00f558105000b240c8180410101e42060110100000741450004c0c0348107603107a0800703041540c41301410100f44901c0d5900c0702410021481310f8038085800e501c0090b90010042c020502c2d076125928640364009443c1d02600c443e00c5954803068110020203090009000410484d0300000b07a100307031020400c40c0740c42d00c1c0455102e0b034805c06d0000c0009640c8005a200b01405c11151150b5980b19440c0c4070480110340e070b20040c001030811040500120385603014211030780750482514164255138224401401102e5414070118103841300520550711072074103903a503d6030103040040c6018420344940c1d81030b200c099002c80fa40d00001042106a050118101b65120381c1c5050600c594100000040e0f02d90140c1846082f5407010b04000d00c06040d54003401d000c031103140030410484510003041c0104144506000c5c01040da205c1e6000740385905201a401d412a40c0d20300428220a00300740710101800000c051007410064801d00300d03030340902e0038031916000b441c1d00d072225026112204 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 434413767 1250 434412517 434412521
    0x607060212011415130317070c03030e100201050f1602190b01060915020d0e06120a0b010207120c03110102120a031e23060a1701060503010b04062102030a0b07080406 73
    0xb05102403541802d100003044170b226100075405490780329000045020080040641d503024140c0081c10310404010700005164000500c044842d030b0035182011110010074087c0d023030305c5d401e5441d007962102400005000040081d20700901e06500d1054511070281c9240c0c80b00000001c00d410364980c1e030f01c00f0040148a03004500b0800031311417074407007000030580c00c08003a480707078443c002c01e400344904001c040100e070740c8001c11102140240303000f003101030401d402c0c0b8100030050f818985015204003800411780d0030707025226201c0e0b10350000c01c048a6500b50380d80c03417400f00f681003152410751140280101008280401520310340d2038560300002c090003a0340200040c0091800c500501d2032038000d100f50050b50b2030071140d800644a0080e00c0a5413142404103814030344c170383e0010302d404000c841071800304001034215030102c0317408a0003170001c004403004000480d4100e1044240000b980459115412100407454401c5c0c3d0008040d203043c04003503120441482c60494034900000c801c4000c2208005680c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 434415017 1250 434413767 434413789
    0x406021b0108061815060f0904111e0c010e0604050303070201110403021f020a0512090906040501050d030f020a050d081608090d0c05070306020a05040e01080312010506070602120114 80
    0x246001042424541c3c040341c056090b14001c0e09044c10008005803a8645078884c0c1161820094030a039aa00141544000160014250035104500709154041d18039a01c0081c2c52104540c400d00149180e020719406a0a030320100018110703540351a000180480c013802080d01ca54000e4010b1681c92418101c001d08503465102140401d440031300050001d602c0d03008010712400c942158000703400300c42c850107909d406107219001b8407a101d16179118918070303446070240683e418207a8401e030440c1c4400007008280d40c000d02415402401e00000314002c40d201c0c1c0340381108800c090041c0c172107160041d2202c0b400c0901100380b940c08202c00e4400d0008080e580304084000098500c0d141c0d915051a44605484500c0011a1130030812454030490178010181b002d40700660b03105804540c4c501b06c038140500316410034030540701858840000011280c50200c00c40d0741e006004044800c5030307802c100400c1120341103400159401507007800044120300100c030b403030383c080d2081c10740e0380407070003003210070050310f0004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 434416267 1250 434415017 434415019
    0x1b030c090312110d0305161b050f0d020d0e0d0f020a0b180112151707081e06010501230f040306090c090c090321031b031506050c06071809020406021b 66
    0x5406c00f044070301307403000000e44508074851030280d04902005840611404c0201c4018115014498035103849840015500d03104030300580980e41c050140c880d0030340c0d01c03810005d0000c0d08020200140e40001d0b03201c85c80d00010520050008030201d884a85c1d041c0c5940000303082d0617407491030407107034100c1d0342e0410751010070201280402e108400001c4600c078088120f82c0700d80f1650218043c01080c14440600c6104040d005880c1150850200b041c1c1d814100000e04c1d4290b00640240000881c941d48100b1021f00035842c0070820905954410400c0c0d03c040d4001e811003100c0c0d0200340b20100c0096114090011107a0081c21988001414000110201c83c0c0440211080c8440244100001145048424800d0f0380c2c0c90780c005030300781881d5410303400b420305080a1100200f4048840e6000c3d46c2603031000d550b10b410640d01c0140785132206003d482d03902c148100e042d03070b90f44241300082c811071140300180f070102d0801558285440e5034141d04030076a085a0001030158200700251005043c282000d100032002c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 434417517 1250 434416267 434416271
    0x8032d070f02040b0616050a0b0106020309031203102402060c19080a1b080115020d09090b1f02100b06120402010c0f02180703050a1b030c090312110d03 67
    0x69075551030100c8400c480090090b41c03142d007068200c0d9a803c0179912880b0060940045411076468440c1c1c4035020100b08403100e5810794004100148000140d55030398402070001d08520b00005400102600010301c0766483c841c1e02d03140810078201901c1160038070302c911080350801342c070300c908064100080144804034090701840b01c00c8000040001e0920398211a00380080b42e900e455030b802000d006d90740e00c01070103844c00302e0ac0006990381c08081c0d24104e40301ea2520042e07041200b04100e031109001e401c25000100e42e82e008ec4002c2d00c05600050003480c009002078180d540c8203081200741d0540080e400050303005444090190051401240001e0b04220349a92903c030614116110f0031030040e002904012007102c42004100010350501d588640080031010000048c0c0c2d40006040c5044980d0f0340000c0c21720340407400004490054411005004c20b0160a01c000303040114010308102c1c40c0c4104020440100001043c40981e10308440c40715641e9000d046000846e10a180c84006500c00013014 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 434418767 1250 434417517 434417527
    0x20d0828050f0a14040e06090702030702011e12060803130602011e020a1101090c060e1c110a0e0a15080304060507030e04020c1005160309020303071b08032d 69
    0x5074808110b89612520598458032520302d1101210341c0f40001c5080c0b00c031102d0000e4007241d07155456055603c0b90004441510071a501c05400f2a100d01800070000d020600d80791130b99a64a40d1301001d40141d05291422201101008a64800b40c031050391100c40c00750800070b40503042c461540404009440d83d40002c1c0492a107c18101c004c00c0700190400105942c0840d1601d0710b50710030300c8104040040d0030002d2003000d0a504121203166006e2240d900428040354002c0d0003402c1c0402081c82000186900110008194590343c080130b804a45090384581c1072103000c1000610311760950b02070210082c001652041040212842e00d825810040c03a50b030040c001008602d502400b02c810141e49854001c03c4d4031103e0300441d01034003d442d41c104a5010700c00020390309904503809a0f00c00d50b00c15100351240124440151b00b240c02a95010307402d9001040b1000208000401c02804000c1d080c00600c01c0c10355549032141150410800070b003007907180c036054802c0e00f0100707221650240c0d154003c4034030300 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 434420017 1250 434418767 434418847
    0x910030e0f12030406020c1f0615080103050613051c030e060901050c040b1804051303030f06060903170c061f1a04150e041505030115060c0f050109020d08 68
    0x50000130401402e594001a400100442c240300880c0b035107240c01ca060391f070321141d2500c0c8400342803507000310804030700f82103c24060a44240501d42c12a500a801f420260f180c80d0b1a07008140000300040e00c0c10320558442590440d240c1c1005003101500c2c0c0e80c001102150300e111181000ca029201d001c0c6030707040c0303001c2c0712080b0005022a0101c0703000d0400140d54107680d401b0001204409034000e603201e49072a0810681c41c9805a40007810b0b486980e0802200402c90041001c45400d4002c242c0041e80e20315003070002500015003040c001042c140e02d14200322a03442400d140c80004c8580c1c103d030070002c0c4d04520040781c1f0500000054009140745800f80012280c1d414001e004900c280c1d951609201c5540145500801d555010160003410034003902e9090303100e001c0003840d2481064007a41c80d0010700001d400c03111004a055034030355030790180c00e0301060316015401102c0050035540d556854055500503928600307101c903494807440038252107141ea08080007488000305600f1404072303414036030001320f = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 434421267 1250 434420017 434420053
    0x1b0105090a211e03020a080901060e06100c0c09060303080907080a0b0a0e06070908120c0604020409081917152206050307030c0e060d1a0601050910030e0f 68
    0x1850064008541d00c031041801d0890340001112400d03d04004070740c1d40d445540303a143e002404c01150540300c030802c54403180364031030072101140308603848040d41d1000b040b150710300314000f50b102102501c1c03d02402c2401c1d032a184101410790f032000c852165204000c000700343d001207413968040e2004000d0040c041ca04401c9503211b241d2440000d08040039400052109581503020241c10740c0200104e840c0342c0352500b40a081e5000e0b9019030500c5101d0003a0640080c0010b004030f881c2c08950a001d07141c40d850741e07824000501f55112040340c0d012414000c0c100b82002a020032a0305080664950390030200c040c22080001f80e0151803801042c00c1b550890009440303941c00c09444440c41001e081c0100151108071000707100380d40209616001e4100004107203d41608a001501e081100d0203115455105c1000803551100c0c40092080d03040021701c040c000c0d1007040d0164014010f0418626004c480303c001610100d040c944240400d9440032070b0171040404102c0d201e107081c140001045084609080060 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 434422517 1250 434421267 434421293
    0x403050304050d14011d060a0e0c0f04110d02030a0f05060306041b0504091b140307090f1b050c0c100c0816020901080a0b0a06050f241b0105090a 64
    0x10046040241d080d0412072000c51003030301d04e0b9000f03000300300b1420304541c943c41e0148460304421040c895000030403c502c0d040e104100c0c84044800003131a04811000a01041e41d1103a0303009540310ba42d91006003c3c580e074420080070580000390b030041e07030f030b00d449140702046030800340700f51104501e4401002001d4800103900754100e03401841e029811130b91452a404281190340007550494100b289010800003c0031058007114850040003108a41301c0e60800c0c050601128000e42c15400481d0812291440d540b00b0b0740001c0ca44180801e813190f0b0004030041e0740f40c01d51010070000e100081c1120342e070042440342c5c0c402c10000711003410f990801c2e40d800800d04101c02c080500300300b100080ca2060321030683c1c00210180e6000e8542122581c1d100811611000038140541e982c00300c2d000002d9111a11348a14401d8440040403603004d14800c40074082140010a201019400f60200b040c3c10f05c0c1c2400c001d400508569042c640c1c007082102c07945401e50710050107c1d041c550106032034200154412001c12 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 434423767 1250 434422517 434422519
    0x91509031e0f02032a060304020114031902040f151d060c070512010219110703030c0602090d06060f0906050918190803150d0f060b0411040f031205040305030405 71
    0x2031000880da0502c0502540040002503041c0b29080d900300b0303080e49500c51030b00140c280349224402c07030380c0403000e04c205440203c030028000351103c0b06020503016200051900036400b030060b5000340aa8182c041c040340c1c0300d42c00408400f04450360030008130401d0304c01002094150f00c1e1042140d011400740e00510413010001e644a0303540405c12044840040082000034000241545000320020711540d000790b001c1d44031120704908280340e22440781d000e080e0f00d41401008400900f201e6156031411110302c80400d2040f907000390200050b800d1940d0700c001c2080c0b101d005030748c002002460001c0c82c0c1840c007159031105062a0410301c00708240c1c0d0303920030625132002e40100d000d1000500360003902d00340035002000110030180402d1103001e02021402551041588604d0194280710960800c070b0b0032041003000070703c40704005000c034001840f10b0304960345013200680081154a010036241030a6000354010903141c054010f010002d1103140461480c406000b4100b841c03515003036071142c5459109074001c107 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 434425017 1250 434423767 434423813
    0x40c0905100c2a0b0403030207090506040603020918010507020c06030112020607020603150906010302160f0302190605090c1504090b010513120308011401020309220c09150903 77
    0x180c14060241808000765a0710090004800d8180c40c40c8018580d01a006510120f8002c54040b44151142007280d095a4143e0005c103000c6103006032050107020002c00c0684c000b034a9050020044c0c48071024980214241e0308440682c86032412518215000206980c0c01c40d403184c51480c0243e01d506045905550010b0725400fa07040c03c60010403024403840301e009410072800802c1181182d60720619071900c0341c046400b41040d441c0c2d90011001e9000362109440716840384040600056140104000d40a10900544403050f2610f5030b005a4250460010b6500f141c80d1002c01c030301040f00b032250450184003100d041181d07249450741007246000358012085403540d0b803510a95507038000c01c1035a180849104600640d207032200c070002c6810301486011008500e04a0000c111131800720840c0181d03e206034001c5080100315400c00903090003030082d401d50f110502c041e103030080c0818042c8010b49000c45e150f189580740781003045500c5199200060041044032207051000a60100c00310b01482c1d500100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 434426267 1250 434425017 434425039
    0x905010c020a0308030705041505030106120519050705090109120503040506071407090c020c09040206030c090d0f05031b0d140a051b0d0201110903060f0c070b0406050f06040c0905 79
    0x1c1601c2c0c0e0401c1e040901544ca0100c00c0148450b07000c2d0050065881741c403104040c8000c0001c05840c00d000031b0180e000420015040046028869132000391700c07014601503104091000b40307210741120803c0c0e48000020302d0024120306156003201d8240000d00d0021040f08c254042511080c1d00c2e4042d9004692240c0400aa0002840055552180024985010b861170644e0f5020040b004040450600016014800310100c4600e45400c480d44620b4014000c1480e540d188246005c1c0ca601404560380e0080b88025040e02050075542110712a42c4620011503940c1806120250344502c4010000c846500c2104240001a8041820b103401c0241008254882d51600e80640701e6011b14030080700030344540c080c500c1a030540000c03021107004480d0000c00030480605d200407040c1c806c0380800c03a00342d44040040f8141c040128002640300e000d07014030031300344003003075840541c0c00310252000d40fa17154560003800413000c074851010ba045a021901080741421003140036200b4030003849524415120303050 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 434427517 1250 434426267 434426269
    0x1b07080d05070908012a0f020d0e0102010905010203010b0c1501120f020f030a050703060606232a010902040b040504020f01180b0705151302090c0319060602010506031b010905010c02 80
    0x400340c003800c4c00c0b000a001640d41c1c0380c1c00030b40d907095243c08548005000da0140900600034a1040a2803019034060f24020070b000f1015200110a056040d04640d49c400d107900100d0f900f0b20266010b811a0403089960b070004100161800311135a00c005880610302004000a820b10300c0080f403825030080f48809008918000140017490350340300c2c6a0580104860141000408107142050f40d104030707420090f96032106001c440f64903c0840c890405001c48074034001203204c4002400441c40710089210300065014440b940381c080c00c4602584a079110b6103200c0171850180140300f20800259020056441c0c260002414420508045070501c05004040002d1806841c000b4001d0030590180aa03291280d01d02542e40b6040403421440004100c400b00c0c0b02d00404c402e51a4040d9001480310015865000300e650590b40044c1c5400c030b038613004104100c4c6205990003000002c204c183c000040c540b40c12000d01d414009401d07104003090120901e03500031070b83c1001c45c60054071000c0c40c04850341a0303284 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 434428767 1250 434427517 434427527
    0x30c0607030b031023010f080c0409111f08060118050d0614090a030305010503060103050703030807110712020415051309050c060408010c020f010e1519090b1b07080d0507 75
    0x1d8841508a81001c4159041e9001454003100c04c0340e520b105d03100030360ba0741c1e00da500034404180120750468211009140c0c052900f80c00011810380900c01d941c828180e1000040d446580188181e11108003e030a0049015017214129600c0340080c00c000c4c602048103110185c0c8900b03180589840303001c07041e07204418054aa40320441180c0155070540b80340c10001d14403507850031100001c40000e17080200114540c203000c1000c5040743d611400400282e4210798041d19145030080c080c0003000408129440000381c03c001c050001e10701c64130341e03045114960041c0700c103842e10194992030407403801c0c0c42001320792904450410090482c00001a440600c0d04e050340c01c0c02c1140b65100d502000100b00071a8001040d0701861800310b0301e800300c8129003a05c1c0e000c1803d90301c2d9100d02500d0360300015546d11001c06e580700ca055000d02440d01407114950548061703412100780e10010749128840f002000350500c0200c2a00381c0d048105d58003103090a485503500c440d14030400e4006503403e912103020851450045e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 434430017 1250 434428767 434428783
    0x3080f0c1e1608120a1707030f1109130510090212010503060f07081311090412081503100c05040e0114040b01030603031b1b080618030c0607030b03 65
    0x34800762586892001d840480c141c8905a580d60365004102c040c080b0406114021000c49181c031010b04440c070f16850760031000c0d4208850341c50522281040801c4443e4603201c019124102c291000141c504d510706c0040300f00c46210448104520301044540040d988004180f110f19201c2000402c15584150f44040d030801194000c46140b400404c2d82e088102c45e0a083d203042e1041030f01150b0041d5561309104c611000300781c0e02c0034046405000030580f040304035203103c10780318010440100700461150103d407007004205c07025560080501c0ca01c010003507100000c1e9030400d03101280640e040d040398002a456180e403418074003504d5a2a20003002030b5001d042901c0040c050028584401e40c0c0d120b5540084201d610481c6c0d2140d4640400d4a03c198000d2243d58242c0717405994035880075a0b25820036000148030384054402a04040320840024290000d8001600740c2c8005441c9504110380710810805203014448401d81050000b403086c5180081c0443c0d0001d180d14022414a603584040f0f4102910 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 434431267 1250 434430017 434430037
    0xd060c120204031a060a050604030b1012120207150207090216020d030906080a06030b0403080613020a110601170c1c02031212090a1104020d06050d0308100b09060403080f 75
    0xb0030b0003c00d000d150100102007100d040304000569889400308400a0070600a05620100c20700c4140007003100c05414035801034401c481c0507210f42d103500652190650598044a50041080d101514550b040c0300c008000c103e8101421110b0440070350283d12001b50f401030b035404550105082c040c1c04544400000000d4014242c0785107882c4031704005003848041c1c0070388408511030358040f0b0303051021807048a003101d03000074a860042e1160754080b5800c100181c56150b20107081500c000c2c401d8542d2008140980080d101e940201e548075042c2410000141c0c01010003074403100d00b801810f580400c0442c000c80088805015402e03503c03c2d09500c00d08a420041e4040c4110100d00e036002d02c1e690020100c0801510304400181d441030441692101c0d201c40017803c209414485550a003060340140079000c079440000725410b500c41c800316044030011001a000280c8a400384003131803860100241c007a00d101d030b0318207240c1880c15011450503c03661000030302c5024001988807103050a41c00b60f52888030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 434432517 1250 434431267 434431271
    0x11e0e060a051b0f0c010c0516080106091116030c08070803010b0310090e102d02070303110310060804020d050d0c05163008040608041e020d060c12 65
    0x1c410030091450304100030080b00c0282440701001c0303200c1d0029840c10740d0305041d8001c288462908004582d103034a61042218184500600106134850340c100300c1c0060040000000707641c81c81c244182d03040e1140c08038245c1c074002040001c40e024117802c21820314182c1e050b0074103203d42817183c5007a404900c0f40ca440076140d0b1101200203d1002044401140154010010304451644803001d2800300c480d12869800c50303a1040ea80e0301080013007071b008001c4c404102c0c599032a00500080401d8034940d0201008284a580000e144040641510621b11100c5021184c9821407412401441d1401d010303014107800c0c0031412001030119901c00240308a09507014050724001682600b025002800c0500c0c100d4407800351254125020402ca0031f500c084070a4100120310103008045205d038400f580d054006c003542134801e0706c03501040c12180203000402c20396030381c90450f05c1e00e81490740140305504002403168419110306e0b009a03951105202d2099080f40c4d000070801d020b90750603626a44081d55001c5458 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 434433767 1250 434432517 434432527
    0x4060524091507051b060a030b060f0705030304050706080105030304030303090807080706090203060619120206130308031b0306010507021201150b0702090c0301050a2913081506011e0e06 82
    0x80b1088020f011042e109104640d02c0040092210150b212481129508801d003403000b19101803282e0844244201c025210030300d000c8030003908034005c0e03000540c1611182d1000041c84100801040030000504840c5001238865040000113900d031300c5244006010552500e03400c60500c60150100d8010541c003449803565000c1c00d15105c4081c0120001c1680b0074095000020202e092084400300c080c40c40712001c511740c41c24151082600349800005a80050741801844010307001044070030051400344690307a81300d00e4211b15140060515011184410b5003e02c280846039030403d0507120b00d42d6040302c94045900300f0344403190040200da00c070303101e00d00a50b40001840c80070b044010030b1041e00940e0303103200d1903845500000a911007885070603044668001e007049480e1020a55500c104d0380d200c01d003069004da80d20080d01d60303044401c98505140c0010802c0003110020024801d15420011a0100d03e16040740041e0000361000700e5150308c00d950b8010f180c1403500c01c0c0340c04a88100000c2c00c00b038581c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 434435017 1250 434433767 434433799
    0x905270a0612060b041b0503130f0f030503060a06030207030f0302070204200c0c0f1c020111010c0504050a08010b010807030e0f011a04050f04080406031e0c110105060406052409 78
    0x80d20420744034a004616048506c84030780c050a0400903102c107a619001c0c82d548440844540408200209440500a500303500000410101540e0001d0f8060703511035890b03042400810480800c50742c00841410310410025001a404c0068000d482e4114100103032940010700125002d13000d99800041c90411500111812035140f502a0480c0180c040880d84424050410302004560b00c8211960280c2e0581d04400c104141403020702c5014418509400301441c2c0b405502d0070b40d8921002540401c2d4041810300c840e09000f100e4070001d0000d000280200303080100040c00784400a00100c08264441d8602e543c8040304100c980040b4800304020040305440f603204101e5014112861407169051002060102c1d48139070f0a507006031b4200d001c071840c0900d0444150024246080d001c0c004d1000a000070501c580c0c684508010700b92207882d01001c02200c80741050171034400500341c0384a01c0c5001028840f503241d03000c0c0f89001950484031002420840c0d010190300c0c0c05050034607640108401700000071 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 434436267 1250 434435017 434435021
    0xc170108060412030e100c02010f06050f0904080903031318052406130b0403060f05240a090e0610091107060b0a09090f14060105180a06080706020304060905270a061206 74
    0x4112907002b000303200c08045850081e1a0140305295001c00507490708401450165111030308248540d013030783e142044500110f42141c21480e007045014924001c100801e21031100c00588a298842c01045149012042084201d24121001801002068a07000740d030b10b401c0c0494180403510061030003c0d43d41c885030015540c0c828001244e1107030a240c16848801803501880e03025400481c002100b00d82d060844008001e040c2c80761661001a0500000364503a480c4500c0241d0b80c490005090f0034a0150b1045601456950100700c0d40c5292030742900c0400c41030401d94110701c0d4022004500c1c040100c002917000c903101e801c12500c96140c205560b0800900f210001110b0f4030504401521462411882d44c0f61402441010b41111003403900d070307002000029003aa8040354021000500741c0e00d8013902031620000307800c403802581c000202800b03040c0c0c0051015000385030848080300c0440a100c081a100040542a80c0d04203c044020800b1504241c00c5803010b00b184100c200c0c0705100034180140 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 434437517 1250 434436267 434436281
    0xf0c0c08010f0b0310020403030c1e0606240f020705060f1b0f070801090b01050904060f0504030e13050c070f05032209050a0207020a052b060c170108060412030e10 72
    0x4c0301e407082c0d4100210102c010700a41c7c049a0301501c0b52882e40070103888001540320410541c074900411a242440001c02500c80c00019040d0400001c07020004c1c03810b6102c80003440100041480101c0e9002a10242d0001c0e521054031010b84826890b40f15054a50106008241d64802d1450350065503250007a07000640c0c03030355480428221103100e50b40c0c2c2c40450884da02404040c0010388a030380144218189040c0c84e81d04a4481d00e00000e030280c0d11b40740794046034015601180000c20381211002e0a1401c2c20340440c281c10520401c010034244015907404500c1400300c02061210100200380a1003130900984101c100c151400c101d0405151812188018071402040e80003407408021075849600b6109883c0560340c06488018064140410807034a00c02c14038103400c202d200d6180c08204402c00c01940610903100c0e000c00324941c2d98104029256181c0c00c664000c0400481c0010407500c00300080d0a6000707900010501c8140c107119200701c2c054110124038101c1445400c007220340c2691640d0002c8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 434438767 1250 434437517 434437519
    0x120c03070509070512071707020705010e100c0b040521090a24030908191205010b0702150304030c0f050a060b03070b0a03020f040f08060106020c030d0f0c0c08010f0b 73
    0x4240c0c5441e0010020281c0b07040d035103100043c3d41401001c0c4440d03400d011164010b2000d0802240300480340d54903255141003201c0700301c0140c100d038a0810042d40c0284504452070700c12188040302a004010040c00a285070801500c1561008080340c04c2c00014404004641030b07000f04003003110310040560b9165407003840c0c076602400400c1c20014203108445000c24544201c80c032940c0b2402100542200035110131202580c90100411030040d10f28418501d016113100d543d10303128a0210006064021508160302c0106028020401c50b40180c1d1945511000800031480568072a02c49041c1191155002080102a02c200c41e6070402446000180210030a1180c3c0c401c2c050034100400f415280c04032481284082801800311400083c041c1e009000c101414191081c00d190380c480c1c015800011627409040585c002c0001882140d44c18040b058484800707400130000814144402014481c4100c1d480080003691503000c0104810700340900c000f000140024000c0c500142d081500810805d0155 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 434440017 1250 434438767 434438773
    0x30703080702060f04111504060207060201150e0c0309070e0708160c0809040e010b130603151a0d020f12060709061404061815120606110a020f040b120c03 68
    0x50300340d880010f82600c00c203855402c00f6029161136450030704071021202c14581c80001e242201c031070820a50044c10080034075038000c03c5140c0c940341010342110100c5a50200702000d4100601030308174409581c070307088100c100c440382d980ea44000d4401d040c004143c002d0514240944103200c1e030641d100c0e0000e4000c0c091480502c19003443c0d44025520360b4081e80e001450090700303104a52070b07482c0641c00a5400905603001103629115000051000588180c102c00b011740c1d80c9805000b801003c1b00c01209649100d4020800c10641c04a18040820350040140c40707500e08016207021512a40e4031a20641c1c000b900035071148050710a1161900421a28400050300c241c8000603103c1c85003030924a040c071803002030b5281c64104101140e81c0050030303560144003c11031400003003070108030b41a107408205c0c640d80d0003110511580b0b00801e44206501179801c02c0310040c044410b141004c1500440541e048444281d940310309004a400345c11900042940704145480032510b9002c086606c0480c0c1c070b0201d040d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 434441267 1250 434440017 434440021
    0x10e061c0c0323151c08030a0c08010e04060b0d0b0703060e0702150a0b030f1006060f0804020f0f0f040e100c0c0506010306050c0f180a0b16020d14060903070308 71
    0xd58083c44415580e15018180c0d00804c2951110694400f81d42c90068011403040c0d0502001140290000c10120b802d803e00004111200c80c052040e128249014500000d15508d860280920b00e038028101030042640e521550b0000d40c2c49a0711100d54642c02010140350780383c4418003500170715462040c0e89448901c0c000246a41e4400320380214120600d61100321151074a41c444030081c100446902c0e010300c5510031010071091b0030400703010552000100030880740d0800200a20a581001d80e4000b07100d803078028080143d403401688490180c050360260004905a800034030542401000c490300149894100c1840c2c00010074080f40c45554942c0a204008441e48101c8400e6400d0802030056005500140001580c2d41c0085801c92036042c2090300700100012076150030b5201122281031000540c002e10102e0608040040041103010314440c2044c0b458011030142000851000340306006480b00001007082c1c2030814549600e01004a030818036254141c130781c1c4c0b94042c50043d40402c0c0b0b01c0380 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 434442517 1250 434441267 434441291
    0x2040e01061a07023c0f0a060f02070b0a0c0c0b0a0512090703021e010206090a031e03020415080106080c0c07090c0e090f01052409010e061c0c03 64
    0x50030045607014240104601141021418150850f40040f030740003034644c1e5081561115200140ba81c0302010b04d120814090420084658203056440300f0702440500080751402c1d030703500c0190f208958244c1061105d08001100c1241020401e4105401d00d640101c3c5003007500d540f0200c07064203903124001c0002060388a01c5000241d0050b90901c10014004201c54040c0c4102c4180c0143c00c400550111612a916580010309028030300240d901c01156203001d808280d80d04000b8a50011080760280c60f4040c602d845c01003101ca00c2e61481a880d000040348072031058880d60445004000c00c11f12001c15041901000741034602c00e100303c1c4005030070700021a05000b0319500b207030b50094130040200784e854907107a001c60141000903628006e00800114200f559201c0c1c1d079080d0b02c261090918140c5640c100010000040c1c900c0c80c1003a2102a9014800c0030550203608a50b00840b090074a50740b030f011198001482d41c800e0075843c0704601780c00710380303200301c80403e400014424180d80c80a005107070100b4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 434443767 1250 434442517 434442521
    0x509011b050c1005120402061309020d0228020a06050601090305060108070611060108030d1e0222300c080a05010501061d100f12020a0503010806060a0503070e190e060402040e01 78
    0x100c059424650740c0e80110700146040d50040c81050349c4401d182081c10b50352104041260000b890707041969400140117080040b420050705600c01d070401c21041018100d0900079998034002c01c004003515958804100e150f0300510421000315030100494025603103c0c20303050344882581c8207a07404515520940d0414a00119409059501300c00c0114104035003088a24080c00400c49210340d43c0e032410700101c291000b1400107000148a00c0d0b6400d421030310003601400014040d5201010094400c1c0300b920070400300000b850701010b100c04e071060384115107080c5000702020070351102d4441c1c0300760f210410820006400090494240d41c8030351620a0002060b11240c03c411025550300a0f498040503003094001c40000905031400d2400c4043d124981540383d0032039000c0071035200818004001007180c01410007000341d0040c010f860588a8a182801280d41c0300b0050184124080f582c0000500100392002d15000e0145482c0060141c000010125601c55134252000d901650030b0100f081d442002c14 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 434445017 1250 434443767 434443777
    0xe01020c0c0906090705180a080114010e130b040507050405180c090f040311160902090a051206012108121806010b090409020105090a0801060e24010509011b050c1005 73
    0x14002013200ea41d48041128594010254926580c0f01d115145207e070300c403d4803c1001d0001d1000003d00124200c401d050780c000142d01510080c51a48100031500d8851500130b2190303540080b482116850354600241048426000960007501d05001c101c80300c0801001c010402c484201660024030b800d1060085902d811070f0344064882c407840100300064440c24007940540010402e0380c0718000e0036081100b01120a038030680c3d5841e00070451b4045881d0102035000140070841e451030000301e0000005072640c00510805450345001c82030003104550081280301038560000078281e442011100c03024080303c050314591401c16418071040640c07440041c1ea20305942030b0200702d40c28140f03101c0411010b080145402c0f8100801407106000e2916030140c824007804980c80049011070420032149003e5a00425200010860000303000e0002880e50102e00c05c0602841d260741da4954800041c0c40300402c6d0035140074141c0580e60f85200303021000c2440c01c03503010304603507944030b114841c0400c50f010b0040b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 434446267 1250 434445017 434445019
    0x10051c0b01020c122d0c01020105041203020c07030803010801020a080f060102061f081617031204030e0105091c0210020106260f0708060a0c0518010c02040b03010e01020c0c0906 78
    0x86009010054a408510002401160000c490b104190054a5005c002d00d004c01030521143c0d03095035501e070b01c400b03000403100c001d0284000c01c840e203401c0e216000b40c154000c1c20102450340c00624440018030500002c0c002c0d41c0c00409480e66940c0d0740003203134001e50000100c0340001d4030345000324084800c0516064000c200c140d000f06296221165101c000c0c4005603050046554803403000510780c401800508099001100210300d260b141000300031031440302c080d000300c858008102460030403030700b000c10640090301490914500807128006030f5461203030400c01c551204001c00307565525140c000e215100c80c0d1080d901e400304044282c0e402d03401c0c0c0d2100c6c05403c03c000d1002220907151040700d00d800c0064981d16089411110407804107500b410856082400b041d0009030410040380424014440402590719041d880c008014501030780070503403805440d0401980340b00407001d550b00ca0300711900015000b002004100c01c5100c0d070314000d51052510010074010065003a01d50720344031071002e100c1d40c4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 434447517 1250 434446267 434446273
    0x91e0c07150507020106091a040e0601051005030a090804030b04060606050946030c0501080f0115020708010c0c150902090615130e060103050a0c02210910051c0b0102 73
    0x701082251000e407030014519800c644d42d52000203100c4500d070041000d40c0c0f89072802500c0004211040c007050f40d074403403007400d80e540c410070040103a43c403815002c22100c4141d08c3c045d612a102c0c1041e15004d000041c40151540e080451701100b4001300b102c50700d010700c2c07181d0030400005130f85101c15a80c900032050000c0c1d1000702c100b00307440c070031500441d02405440403030450541d49040c1261200350841c1c00a410700300461000060082042075214500a8002402d000006141c148212000c030b610501410300c0700c6940040c82e00600b4000c004800c0a00f1400c1d00a2100002813400203110040d006400d640070a000d030060032100f4001d2040e8118690003412212040d52181e00340200400440d40c0c103803148000704840d0105100c900710b1326015203150b03040458242002c0000605403180a080d40c05000c1c90502c90030606a0000303075100c103124000d088040e541c52040c584046a00502c9007164200d40e00100c00803c06501200800841c0494010700407070900c07030320b81c50089444100d025409a8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 434448767 1250 434447517 434447543
    0x110f040e1302102105101a0f0702010c05100c0503060a060c050d0c0f12030603120203090306060f0312030109050601030606020d0503040204110403061d07081204030807050705091e0c07 81
    0x340c41629113108400b141d0242c0e40d031030601e29602e402200c038100d40610103000034141c00c0c45031000241c106101c0c0420052000d0408500e034000102c40d200d2504000e040c400e00f8a0703540d0400c0024081841140801041004122a0084041c219034800c4840e82c2c450143c210010030b80501895100152580080080c131408481c6d0300141e401a0342c0301416510b1003683d04e050000207003c0c10300c014000207070b5a000b1455910358901100388a113003081480540d0400e00000502d070300c0009115038055000c860310584140c0010100703041143e08544202d9a180c008004130b04031043d9003025020f13840c01c0e80c0c00c00c002a41d0307101c100d880705401021a00024803c00129000d80342503044030281c4045d46140340d02c3c1035540c2d91104111f4881d0280041030b40c2c2c40391000c2800c000284080d40041224402814102c483e207441d82c401da120350300008001c1c88021400c4c03424850104030301c0300581009030658082d410031501904460a851a140c001c2c8440c205c0011450f01404007612150340e170000c9411448 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 434450017 1250 434448767 434448799
    0x90c04080a061107020a0f030303050109020f03040f021c03020106050a080114071d220e0708070b0c0307050a051f0b0109060f03090b0a0b031506010f12110f040e1302 73
    0x28080100d86080d10700410f101d15009a40c0300d11b180380041840c14200320314549140740103001d99405038400320380b0b9403042c4040c400e14104407080302c1d4495402200701400140d45c0c4001440984034905001c8101548080c90b410103805602590548a040311183c00c1c01381d8614030f5a081c2c1e50440701214040516070b0208031418000d40841c1c60109100310310074403002c01c44003c81e028000420b5059074643c0d841110b901d4400c0c3c0d51007500300c5070100c0d0300030b00f041c54100720215507920418803480501c0c402c006956000c803101842500c8846900c0829121006940d0074055691041d01101b00c50a4030301100d1440200f050344698003540c80306842c0c000035503282c09015542c140108074030f00285504d89074441c1c0028500b103240d600c91150391074001512094042410324040020300000106100481440016a080203005a45884515240a50b40d40100e00b08024200b00c5064400c44403010950303201c80764800c8090410703a0001200c045142c0d5a02500044107080400301a4200811304050404 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 434451267 1250 434450017 434450021
    0x40206120912070b1f0305060c0d02071703091e0703020f01030e0d0f091703070204150b12060f030a11060309121803010b0105120a05060f1c02090c04080a06 69
    0x70190a500a03503070a0401004010344960000303000700e0b03016159004214071051612400c1c0101000c405c15a680c42d07041d9503800740e4450014044d54811a0046201c4030868113a8040710161903016200180c000072014031410990000d55141c075140c0140c001304140d0100c2e0040060207080002c0c0241049441c513002c1c050090281c040990405031910802e1018900030040341c070900805036140319096620b164000c0c259007580d0030120316850760704032085400d040082035032400781e0119400100da0300344400032908041c03d80d0080b05002c1c804281c44415035600480f8500c07a550030b07154a0480400081010b8841c410f007a8010008510310341c2440040c2072010296074000c200400300c41180d401260385680c0358015111038500000b0000d400546814203000d466402e140a09243c0d0a042c1400104030055400030000c8000b00e03030351400110b096a03841c9400c1c50841000d02103c40c416150283c20140124071401a8000e1030640c022446411200f0200d504450310030019000c013010755511800 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 434452517 1250 434451267 434451271
    0x160807120504050a02100906080a020a02190302010f0b0405010b0d0b010504050415050a0617040f15060608060405070906050a0e0a0506130311010309030f03020901031e1e0504020612 80
    0x8100200c2084000d0400a50300c6998040ca000b007004100c0c5111620421260305040815072003000b6400b98100405500444019000440c1490140e1240369699089140c2000d2200080400c8200e00074042416010350010a40c00901682070050031010005e020030f40e079003845001e01c0c4603400c019140d0f111034180d120f40800b00c414075140d403606540710005410b5510464903004140200d0008000e5844c6c801c080f60020052400c00600c100002d05185007140c0b00188041c220104154180b01001031a072000d101c54080b48070300f004441d4448100911030350007210418029441e24000c108070b0fa018008031000c849469a88030b14204018100300c95402d481001c490700161a0f450100d05a900e0701d001e4408004904000c1c103a00c0d1841c1465001031003001c0002d41814544030003500031961152100000120508002d0b070740b0704180004034014007144544402c5003a01402d0000c85800381e40084118a00310300701c80410101e80f4003518110782007030350001d5112000b042500043d9480e440703080e0b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 434453767 1250 434452517 434452531
    0x906030c09011403090d0e0f0f011404090f06150c050c30030304020112091a0910060303020c030d14030a0b21010510140102060c0f040909080717031608 67
    0xb1600101c12128181140c005540440a540006c050350700c0c01503020f0a04910600125400765100e120a0003291403076500c1c01e0b0290400030700410b9500008801003c580003440901403c00c40c01c0c1c90a04000c0c0140654003e40c907003050444a9061641e01c582808600306420101504440c1c58400810403403940c2011800f0300f0954100341003814601445402c1d20908030300c401b961f80da00e054400101102c009140c540600ca261228500208080c06003804040e004c2d40c025000c80e0b112403281502e088481064800fa00d81841e0010041541c01300e001d890340c580c160119120381041e00c205032801138250709441046070051001070303100741c440d420130000742c034003e010f07071003500c82d81619510041080d808400d41c40c1c0d10756050004102a0200000c002c080030181e0000e0341070304000007500c0784d0002e4004000d101000c5400c00c151103201080714001d02c2610000c101502d0b4524000e0b005801c030030420b41e403000b5008081c03825803800340105d038441c481e1114822150303000d444040e5018580070b4052 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 434455017 1250 434453767 434453777
    0x50f0108160e07090e1006110f0304060813060c0210061703070f03051608190e061210080f0f0106050301020a021002220b070c080d022e050f010801110906030c0901 72
    0x24a800c0207024079406180b0886c020800b4509141c0040c06440c807281c103005003540300d041c441070380c00d0002c02078509840403403a00c032419071683c1840c000c00381e008200140c0007910313040100e021680c00164103410301000c0382052044690341e80704201e041034491041c000c0c45d00200040c000182d22500030318440c521a0402c0707814801000c1d8005079030900560b0803105000c0004120880d0395540112408260052400403459040c0101040050040210341e04d20007200401048003013040ca43c244028203809070844410340c01d07002c9180c4d1380d241c00c1d40d084564ac0d440e103d00882d143c10b041c000c58080039a2030f0000d0194544030004d604c004d42c0030400131010711015088801c41141315003a040e004001e00c0811540b100c0f40d07400c064540011641c80048030760301071058020440d40115116211b440c01c094210404283d46104c015424032200e100d942c01441e1008104600c9c0b0381014280c103803042d207030080100c010202e8140a0501c40c000550b6840881880010900300840c0c00601421106140c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 434456267 1250 434455017 434455019
    0x5030c0706121104050d020d140d050d180314030a0b06042c10170a08130806010f1d070203220617190b190801050f0108160e0709 57
    0x129908186640d080400041c040702c84914400910f03018201d03454450880d142e00e024540710004003801d602c0400203001d01c05494401c020700504191800d5407592078401e03a14400514640103142d40e10810780910410f2030091640b50300310311015425002d0f0360540310110f0308080c000d0944901d0300000d083d4010140c85400070840d50311400041c0008052901014a5024111084848801181c49510315a401c40c0b820046180c21000100e0210b90a00c0c400324100f11301c010710f81e0b0420000c0c4030050a04a0009401c178040310324201c19038104d0f0410025601c440c1d8960344003c1001c600392180d02e59107240d20310b4441861100702071490304000d05004403031611108189140b4011b4222003a014241d0444404008264104c94494900603c06403840b000e07107444160b1613410714520f180750b2100c4d9038070410194103403191400700c5c62994034000744030101d95403100b41c0740c064031080710045d201014076400001c1903100000c0102d107a64010200c40882070403c0504210040000c100c14100103003450 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 434457517 1250 434456267 434456287
    0x90218040c09090b040204050f0702060a0b1810031407030b0a0b01030617100b0f0d0f0303200711060304050604020f0a09020a092408010905060d121d0306060d0308040503 75
    0x71400c580244900d513500250703d4180100710440c2d000070640c0348074003010001c0100480d40030074010340c020301c151000220982c10601040c02d0481811002000145c0c81d070501c0709504030b0420000c22039110f800171071100001d0051262701c2d030381503210052003843c1c40d8010800229054004182d411410302d000110a80d48040300b90710085031040100950300894a00940d010b001d0040006000041e40c0c14403030401c158021542103044100301070030800808074007004051094100060324003504641000141000c158203003194441038045070408801101d1080a041460039030707220369005006852a552207800348134040e030007094115804070700076034089810303a1541301400241040b42d50301003440d81410080c8402c0402c114140c0360041e2008501010030b9480711005065880e0124041000d0300d42d0070110740b10910400d0300038500d40e140076040c10981d6100000d240c070f0314404a40704404c0720002c1e0606441e020240c2c1c602d500104580980c0c404207000d5a255a000391042044904c0c0004503d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 434458767 1250 434457517 434457521
    0x50a0209040809190501020c090a2012010515040b09150c07080606180c0c0f0703060c0f140f160501050103030e0a0b0a02031c0212010305031b01090218040c09 70
    0x12000c0b54034480c00f28503099141408070700c2865014501810310a4075040c880040d61ba80c10b803001c0700f48150101d6000a11180d195000700c0f00466500c3c22000d012580d002c01000c140c0c000321f041c4542000030320000280340c50021500d03284854800801813605081c0210301182d51721041101d6046802d02c03c40f102100b284500410b1001d000c0740203418660701304800b00d810440301404592040800b40d55450207040000107998018045c502c00560b070300380c15070803141080c01209000f956405288400000c5c013200e50400c500f144210f640e084103180da04081a03801451b0220080003005040c411590351030719600082400c1c1c1c0b500303240d6031080e99840d9a500e0a442c1c1c260000c6000400c800c4142c445410000e00000151038039000d124206074607084025130b01d015514055003c00101e444441d5041c80581c100d038848424400c80c41015a101c0c1001642d03a44016498112182c0407010741000400600c504016140e00600006141902c10811021250302602c1550500b400d1500010409494 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 434460017 1250 434458767 434458771
    0x110301030609020d2307090509100203071b030f030b040207030c020114040e01080c030f1c08071103070c1802090a090218060c0622030813030908010e030315010315030f050a0209 78
    0x1481c41710702e124480507001ca04100346903108048a609080510200c040045050000c1d909219001600c941c0c07044d078126101e0500c07611083c107180d1030305604400e0580c08940c8120ba072180c2d88092005615500c180801c034810b0001c041d0009240f220003000540c42641605020005482d40901f0f141e1140c4c80724100361000e80c01840140d01000382c520081c2828003400824000306d07405030030041007040c0a2404884840311090400c005200040c00003401548201e006d032010300100d903290340079842c04030600f01c0c481c054499040154445044158128000c94040391409080c00d0595440c1129a402075004880000650303480d111000d0140d40307031340001d0f28007045400e00429040c14a20380841c03195a011491041c00c903814100e040101e070300710403003a400c9010800101d11007800c0d406e00f10b41d10305013030b00120803550034292600100e41c0000003450040d150901007060b6504000e00644c11101076900c120200c0003c0032042010a60702200e100c51300380150242c4840042e1503001841d04002 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 434461267 1250 434460017 434460053
    0x16110d12120612020306192d06080c0a42090e16030f0608011107030f030203010b040512010b04020a0f02070b040f0e0405010207050d0f08061206310f03080901110301030609020d 78
    0x545400c00d28108140c9c01008000c00c040030160040d43d44420120380300c23003e41e00585228584541080e02a4a40c2411007952103c80514040c054500061640d1803800700444410018000c5a07002c00c0c5440c000d901c4034010031011100070402c90040800350003410519403100c3c01c0554a100c001180e0718280603056203412030b4941d842d50340050785005043c10188003c80000c052051005211104221b0125415540704491500c503c00da0003017100d015041440362181c00c2400800c0070424030740c1100c10203c1c03803120368094500311a200c00440d01d09010300c2c0f048400f418041e800810058188003145c0c6c0e00640150001f500e000d4598079030603d001d194a030114002035221038412800c070340c03103000d064101d58121100c10070406440130306a50366070098806c1c0903c1240a58a4910712844900c202d1030b4021300c541540081103500b0003114070307130180d0400c0d0003103190b240015800c200184208801101d92142003030540e400d6841f440010701a0b83c1003260003c0156903039402003804200710340302e5102 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 434462517 1250 434461267 434461331
    0x6010e0109031a010e0703050c0403110301020d090507060306060201020712140c01060f2c0103170405090c03150d0b070e061c0501050a0b16110d1212061202030619 72
    0x49000351705221218020507400c1010328010500c8166001d001c200c40859070040c16a003074107018980042c1c0207208640d201610503180802003010040301055440848030395490800803103039250426404c1c0e20407440000c00821100c5c08200155000349070010b01481108102c604003044400ba190031250f40742c100c0340001d442a030042100341031700000f00306031500c050301c0c2c0492030419203070300a0f80c007106020003424040f04c41c1801138a80d81c0d08003070b00c0007428001c01c0c01d07401d400c0688030948240c0c800e403881a010b44074251101414104a584030004540c480080c0b80b403035850407411107003000210380b4268085c008202e0680d61118007000700d001c407001c0090004803945010200300d90000c0c903504c0000941800d1206001a07160901e507040e115410200c524003144c0207000080009059a00c000d01e0322030140301f44010b00b90700034111001121000010012161500080700e40d501940100030341c035074010000100c0591058080501200701c1d1400425003100303c4410310007819850b111031010321 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 434463767 1250 434462517 434462519
    0x5090d03025a03041212050f0a030c1404090b091008120d0e1f060e1312030b041e110a0504050634050d0807020606010e0109031a01 58
    0x8015a00da5003010304148010030b8401141a41941c8220705241d001881401d82c808650840310301c2d03850010303030002c0c00040c3c0341d440380c69130400205412400c01c1501c2020707031402c91024050292044800c1036407050350144c141043c0720012005408443c0e412410812460b03410b9941c0c0c4850b20180010301400b0718089400c10b139400500660b507a004249607120000c4280c10818080c0103d0305000302e08110194558426460501c40e0151082e0441e441a07442039a5010101e950003403410070001082640a001c515a45d0724810001d04050300d501045910140b1503000060000c012400c812202d0300f030200d02c4d0840f000003c0d04460040170b032005000010340c082c1c0c9505085200d000321200803004014240010540018130502070350080c24022400002c0b9030400040300c03200000341c504030410703c2030401030b001c00410005078484070403116440f0b2250500c0d0450f0041611a01c20308550f402040e10360350b0100110380314880c40320014140b00a038007000c0b000c0385002c1c034602c1e500d12641580701159 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 434465017 1250 434463767 434463793
    0x17092803020f12030a0b150f0a021204050a0b160f0302030c10020c0c0f01021006090614060a21140109020a08060a030b0714190c0605090718050705090d0302 69
    0xd44103540300c0c0d500360403070450440303e031041d10f09590700240e6a020001c3c0303061101003c645a4081c0d030b49924005000480e0306a2000d8400700103100e141c880e94244ca031420300b11914850076000d54007800da403181e540c64050180200c40d0000e00b001040740142020f17101c04544501c54140e2411100781c005800c00913510440150401c100b0748980d508900c210f103030440707552600c1d0b01c802903068810700c5401e0440d2400161ba00c02c10130920700b55840c4004128040e070320180e8500400092141040d501241030f010b0b800c610b082d02c01d58061200700e484410810050f0700c14803070301c006460320800400e65500a604403001c41811554007820141100603130340d503240d50b8050605031004042503c1102c031b03810b06000281066180c280c002d21035003401c0c10211101e02c0000d030140510202c3c0725941401c06840000c0651000e441d09e0b0742400340f6000c0240d903e80310b02c400d4880e00075000c1c1550715200d10070700390134a00c043d030b1209070310029516019040000d100001040c0d030303d0b801000d60042c0c1c4080240144 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 434466267 1250 434465017 434465023
    0x8090f04020a0305220b040212030c060106030902132f040b040602030304020f04060506040329070e0909062e0806040c0f06050a080a020702120f0313090603031709280302 75
    0x341d02c5c901c0c40320003c2030354503a66035808405c001d0009019040481601d50900020001d540703600c0c40b09400c0d148550b0315003100030010811349005910442805401d640404014443c4180d1139070b0700380401d407a40c2e500c62005080525091500103020384100800942d01044001a001070703c13071a800b0395034a05141c01005280105100440d12643c0381103800c0140340d4440044601b100d502c540c00d002400e02c00440c2c0000303014484072207120b240590017040f007050340c450342240e40188101c07808031094460003201313039552900303c41c40c40d840c0c00301c95118900745040d1040c00804980c078580810041e1384403000103013810b03c1039070100c0f003483c60000103011200b41e00c900ea60160000b450810700707142c814400144861b0002e00784404d034036800030b05102952940c070b00c8540c0c2c0c48210b404490884405455441d542e0340001135890348038540b0800403c0c10342080c080c1e6401c0300d4050f6100d484902c4204503852110b08042d1880c0214411002852f408480e41003c60203142c800c2d4401490b548082c0c113020342 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 434467517 1250 434466267 434466301
    0x50a022d0a050a05091008010f0605030f01060e0c0903012c0d0203070c0504020d02070b250905030a081317210901080103080f1209070302011b0308010308090f04020a0305 75
    0x840789240180502864884074100402c8a00171600b140003616860412000c88036640c1208905500300000607107910000d81000c01100d03c1541282d070400800d807101e42c2220700fa03014032400f9180c0800440c07815010440030b000c00c542c0081c0002001d400300c1485298a48a0355068075884015402440115a081c421028401e100b030014628103400c1d41d41d094070282c2c0a000e00383c800e603804114a803240400da4180d55032207070702c43c618071580c1c20500045c00b1070150700c0040544146501e4142521030344101d0070a802c5402c00b40052180000d0741e0744a4416412102c243c000a0b000c410f00018003400d02c007055019210204050303c0194005a88a41c1038100c800020440c907000b00080800c59901c40d9800c3d0440344c0120000b03841c1c00c1c072080d0b20012841250304c1c06480380d00280610000f05c0c80800c007407007200c0c804d07215406081c415500e0052141c10346c0c04050f012550701c00c010800303e6420030080210307032801400300c1000c0300da5800040c03c0385c00414600c07000170ba9940130041454041c1c08040c3e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 434468767 1250 434467517 434467519
    0x3031a030304031a090307080307050d2d05010902090102030405041a0a150f0503012706080706080f0105010e03030708030402041409100f2d0b1503070306091b0c050a022d 75
    0x145440070348c1e00c42209510014100000f00a0000b035060340c0103819502c0b120745040c031152003c001d641ca5803100d0594220503c0080003040c178005c000034800f9170a00c2281c0ca680c0068001c4c505191404003000020601c0041142e036400c00c14000d91202c5e0340300001100501002c104017003400403d11002080500d00c0c0240e0b0741030110400c01405510f2030506190a41c00c22040da00e410710340300124501c00343c42150700050032442400d40200d40d45030410f00c0d55101c0c07480800b00300d005a0341c078401103640340f5940060903090b4001300980c40100780100011540140068004240400d0341c5102481038041280d000307070b1031b8000700300075100064180101200c404a903c42031001e6405c104541c85258140a1140003291600140210076a296007040b546400001c20302504001e03a5000b0210551040701c0741e0303002902d4098045406841403017007080b502055420400d2511150f1400d54a581207100706540c24816401c000c0300681c2c82d81050030f0100c01051151180d000054030080a41104000072 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 434470017 1250 434468767 434468773
    0x3051006061d031e07050102161203050f09030601090902030607020109020919140114090a090b0a11430b07050922140c03040f03031a030304031a09 65
    0x200300c040e03031107001841c000c800b01c40b45152598842c00002d00d002c0001d10140c25107020049408816000455802e003103c1080c0c007998240300701e0202458a59590b0300812a811000da4440c0b00820305c1000945114035590f500c240c601502c1c0360011746002005d034014181e080c0c440c0003413421420184032141d013000d0340740000e01110806500041c44035400800901ca1f2000300c8540043c41412030f004401800e00f10410070140356150f60b0580d2030459801170050040700d01c01c0120741007000900c00c0c83d54140d0019184081600c64100000180010f150a008441c80c207011000b0f6448a81030748454580344081442008079002401040303030341c8081c402581102c001a420300c00305820514182e803004440c81e02d0f5a0b07481125000511040445003e594414016503029450a80c16800000d80071000001100903a9403800d0004061200321401002c001c80411581d0000b4020340010003103040c0c4014030b4020b18100000300e480c50700f09500030f65800c00c070361036100701c40034101c45016041480000a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 434471267 1250 434470017 434470019
    0x1b0d061e0b04090c060e010504050405040507060908031813060e10030c05011704080a0201141e0a020316080c0409020f03150103020a05181309030806040501060e0d02010c141603051006 81
    0x1440c03400c590305205d082c0601c024500400a540c0c82131080700c0107044010f00421250505051043d40e034801d6010352000b2842815001c111840004280d882c040c030b5120001040e441c2c0b90007484904c25803240c40310780c00d54a4009c0415250020940030380f02d91b01e0780301440070443c81c60424400c140780a620042c14062420b03480100e0000100c0c0030344d440ba4000350342c1543c840100c4001c900502000c084815024242c01c00c0c0040b169036982d42002c010551489040030351100c1809004a11060b00e80a030210340c148000406d0a00800210394005450a1600c0c24141d50f0341201d01a0303403180d90b00c110b00850001c10000c4070380c0c8040c07015550090a290071400c3c03421200018015111380d495841050810240300300081c0d84000000e1131b0f22a01c05002e220321045031402034184802568010720580c10f00c0004030781c0d103224922051540500070325808003220107400649401325a250107481c40c2003202007414603100200860002c41120303c121540712451820294140055604005046410214 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 434472517 1250 434471267 434471273
    0x80903040302041e060b1b0601050d02120106170a020312040e04020603040c0305100203010302180c0d0e01091b26031b1e0c0f09091b0d061e0b0409 65
    0x10603542580e07416500051960840b500400001a00322a00031030380d401c20f0008030f0424161006441c41d401040d00000140c41310442c0b0b15250b0070b0034056550003c16400c51304000d450b0460300280c000700b01c040000380103501d96081c054207511352441c00341c6a038040c1000c1011400c0030000c0e442440711844405003081e00380381d04010480c4002e03001038490170f80440410240300c0c200c0500c20003560f110049403100c05074110160302a4100344400c1c1d200f50425406d424040e404d103280d4520409900350007900e09078030115410024160701f030400c0c2c0c1d80c0d0360310035460700000c0700700980d0185140d544001d401c0503403800d60015000401000d4039043c8496916014815400000551b42e604031034208911200f040300134110b1400950341d00c210710040c1c3c1841c0961b14075001080f0b042100000f540c070b40b880707900e19a09000d0303d07050980707511940751301010f00d0f104c5d60b48103080c0300381030070000600e0300510b043e07a5181c030400d45505040084c1e1070251401a54140300340c5200d0b1070140070302030701c00388442c022540b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 434473767 1250 434472517 434472523
    0x20304230f040915050a050402040b040903080610030e151605070507140d06230c1c05041a04060506010f030b090406051f141002011407180f0b190809 66
    0x81800d078040c984583c0c40e0000c02000b1600c0c0d5449801080e010011031518400940c00340034184e43c26802189043d081c920036003014001c107030300150561903038410f035160031081c0b12080c0655480b0604240e80e890803000001c5081c041c5c202c0c080c41c120289007240c00c2c4924905140c00e61101d802050004c200060000288007081200071618040c5014070b82d4000310b4041505040042c0c0c009102c0740c90300404010840540d01d03000341100c0854014a62942d44440c0501c01c0c1c86103100c00c120840c03501807000e00d21000345d00003d07400392040482102e0048006642c40441000741c504650380e0740c44000300704455030b1011100da400d16840c9410300c85e2000341c0021640814000d0708c0901456202d400082c110b011f403460302650300360402d01400d07000d07940e42d0341d030f03c100000c1e000164420148900042c00c40c1780b050081545582c00356801038456140c11000760740c44200c1441c000d50030324103e400010507204580e0005c0041150004070703690382482074108401269800301d401e09000d010400d005180e0400 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 434475017 1250 434473767 434473789
    0x70c0303020c1608031803010c1704020f030f0a060506060f0706020c011104150210020c070b0a0201090c030b071b11150403020406090c1d01020307080a050d060602030423 75
    0x1030400594800d14444580d04000c8803201c5aa10f02608000024104500000800386c5101080c41d24142c413040c401018262000200c5200025801480c584c5070458154002d5401c94070041c5940027948280700440d0800c0e0100d107580c1e5250308418041806c2c05024001d40da80803004a03007062500415201c5410342c0e01862901030003056020403081c1d13000e40e09503c050404110035482c251603d9460901c22021049254510010b0040d44100c5001c0407450080e48c149450380400307450303414184565200150004620b18046641713a880a5021401200300c16000d140030b40840305c818500480003030403042d400c0580c144811f0740f1100010105050781c070400c0c82c15000f201d80d148018065040030307499004580010f50b115150030301c0000c0740c0700c441e802100c1c07041d91500c603251141900c0d220840191469441c080c050313042000201e0000381184002c2210b42128107090b420500301c607407150121541c540041c0b0269000050500c02810503000c6448400e003003207007684141c114070005c40d07060505 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 434476267 1250 434475017 434475023
    0x6031602010905100615050301380c010c08150108061903080d050612070f031b12030201051503070f0b0307091e14010309020105030612100207050105041a070c 70
    0x808108048a030300c00c0d000050501c2d000303421100c0d04c9043c0c45042000b000c180c41400c0f80700a61200d80c810480c06075003640d04a03030450100e0544540480d803012525420303040300040114031014aa00074244210203400044220702c0009407020444202a142100181101c00c80d0404500700003401e80e881000241d000b601520150031894660410322440102d42e08000d01e074500114240b04a04004da004601c141002c07126602100010811582c540c0164040d1811070900e1407400d00209029038621a03120440c00c03002444107a5030320412002d91001002140182d450398184403803c491008038a4030072908070082c1c246680780c03120143c82041c4070301c00c030004182d01000040466000c0c40c03002000b4a1103809000d071402565007020400010382c05001e0718032001d2000b21070381f540f1912650002c154180c5400d455074540808006102c494184545031520030300c010400c4105060002e814214030074000840c0078200362900401201000d840d044c56450020100b00303840754080448150150 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 434477517 1250 434476267 434476291
    0xb0904110f0f1509090f1009020c12070b070905040b0604051201021902160e011a1c112805031b120c0a0807090602100e100f02031e04020603 62
    0x40d10404954803826944640d54450104890108400d020f000200710300e9400300e85650341c030380c1c2d12050460790003401d60320303003d410040f80401c0c80b21050550081c0009000781c402c55492070403544041b005c07548500c504035040020501440401900040e17004007500f0122010b1090400c40c10200e9000e001da48180e0780304800e8980c40800d1800b00398120349240c01400848601c041106030046d559071320340d0a8400c11340700504000201205502c081d64141d4004c0c01850440c009081c900c55000c0e00400525600050f5040107290683c001d44640c01c04610301131034083e291411642d031155840c1c440040e01070307000480742d000130349554031004403580f1a21a01081c61200b4003411808094003c1e00b1141c06c42804d00d0007031203c4400740c10f0181c04610511b65a0314034039607d10108450100440c801c4a0141e400a00f00c1500b2101d41e80014000641e500b040b941d4401c40b41480d403064030000c954612030250f000061049290071100c1c0404800600a000d01c0c55007000d80c04950584001071054100e04 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 434478767 1250 434477517 434477539
    0x30f0b0f040b130905010507120905101e1d010606030b13111c140c0c0c01120e06010f080d0f020a200d0b09060615070219050306100501030b090411 65
    0x9924110307a03c80141001c041080400c00f60301d491802400d007604c075140850100d62100300c5003030042c015400d40341d80c0607015080c5002c408203094007818030400d188856420313007514011061401d115104020591400901a666005010f18219805030300140704150800b20408660385605010102001c4404400200e8409071008407001d0b005802d0100181d031105000d200b0030040c25080704004000d8180700c42c40548801c02c54804070302c5102d40003101a04200082c034140d601400f0042c5000310060350116001420b44005c0b03050403026040300c210f080a4940c2408a0007082040740f081e00c9090801c14a41802840301958440c1c9244009040b45940c11511040e00e100012400c80040040d0200c038503680c09280c08007409204840094540c4a8140081c403d071500c1c0941c9110300170703149201440c0c01110340070301180312558030318110450300c00e031000126900c00700302c3c5038400d415407403d081e001c0742410001004e85001c0c846541c403e8581606202c003007150110b02c6400140c003142c41b04450 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 434480017 1250 434478767 434478769
    0x50d110406170102030f0601030608100c03021b0708190b010b0307120c02010f15060c08160c030b04060e060f0a02180603130c050306070f050a0c0503030115030f0b0f040b 75
    0xa00695004440001550345000b40c070810305401441c0595040010000a55a084011011111310b4483d4180c40c0d48251000c05105005500c80c011a400350310b40549018101200d200c4846480240368403540d208041c20400440c0030301461500352402c494101c940070158031840075206c01070042c001e144800102194045001e045166442141030205101321800310402078001c0c11302d0109a2816424030010340c883e2500d0104030b0094500d2900e4816402041b40c4a104036904000f44010402110b448103401189034800144021031140708054039500d004e141103815034200a411503541d03030018041c0114030510140c86540400340d01001622201c083c02044180042c007022136030081000410f020b0b45c0829500c5a00243e4004e100c80020b4640d2541455650300c4200c61000c00150700c40b5900f80981e1140703005294450182ca401c203111003ca488480c199482a030042c14080740b03219040c04030742d405000702c2c5059900700004005400d44100401c04512010000300c0c451a40d031400040703a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 434481267 1250 434480017 434480021
    0x702010f1b0203060103060506030118030f0c0201030209090a020915032418070306060221040e040f0512090906010206070c03140c0f0c01030e070609050402070602090907080402010801080304050d1104 88
    0x70190014100c94595a407424018000c01041c1c4070f80d80a9428540c20004060643d4291590240c2c183d0701c4200c08040203070b08540003400d0f540100c0c10140c080007a01c5e210740d1444003441c002d41013074000580c0c0740d01180030840d20344515070f101c5485075401c1c41007207030b518864442003140725501c0d5035030000300c01c00364005175184515404d9106405812014403086950540c0701e07e084d12400d4088440044140c0500c1580446100b400c152545040200340716000d04401c100e500b2510400d1008000340b45e540c0c5050034441c6031010011a00408920241989414404941c01c0002800680107500784240000c1c180d40c03940c41d003c0c050201c40c0c0950040100044100c40c03c80380094141c88070f48488106054a0700ea80000d214000390400b44400720345500401c808045804c0ca40b91881c9003807030001800069000008241c070819820322180d03078151a11281e040c4a0002652960b04514051002400002060304440c07450341c41071009001644880c6800540c0e207810000201d6045200000100 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 434482517 1250 434481267 434481317
    0x150b0405060a1101050411010f0c11060c0321101502060a0902030f01060e0f0703020a0516030903081c050f06031f060f122a140a0b041413020702010f 66
    0x52a136107408208018080e05100751003907128240e0b100c0581e16640d0608641000105001906504240d044001c031898018000c08040c4030120a40e4100705400b107007242c0c40d0003a01082000203d00600304040360507150305040c06001141641051800d4901c070095985200030301e00485242d48108140079580c0801c81c0c0310003540070174001e01801c0d17140d882c000c0501000b80e800318030400024010456240c0640280c0740403c1082c0e8403542800c210745504070716540c1c041303026401e02070600360220100384814010401c41d18540301800d411500300c0007120403039600400c0082005c0c24030701448803503503002c2001035a000020045a038105045002e9078010101d03580445580e10030702d40b00041e403102e00310040d405a4092080900c1c08454850f25200364424640302d0040c0c60010700040c00b040e80c5400e94001e0021016001d00005030f29522040131303a91181d0040007403003404144001d190302c0c01201111700302071078410070741c1810103550000e8041400340807640d0610010440b141c14403140d5614003d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 434483767 1250 434482517 434482547
    0x1080304241205040606054902060d0603121e02060601020d030b0f0301090b2e0501031d0607050c0729071a070807031d060c030a0b0301090c09150b0405060a 69
    0x140c20240c00d40308040d42d41ca10b4015000e4000a40b240d110384c040d158560b4071900198072342203030702c08090076820081190f210900700c40040d60340d06804004100320211600022015403200102200e01030928103880c50341107034035800c544c00031041015a9030701080d5840c4519242c01d01051200ca07001c000780c403800403c001c00d600340d03107000192014000c00e00070b4103010f1415001c4c51251911196110084007449901303004010300c0084003001954860f6014807040e01006580d20802030000c403d090401c40c0984400000800c0892281401c0d0000d000d002c1c002c117011021226201c2c00d01c0c1030095401403207144031107d0040440d40c1c0003401206807441c0c0003000d40b241000b000e0b01d085003001d407091405039094400a4030301441d884021120174015145c5c08a0b400047c141c0366690300349a00c0035480202065801c0e0380b5400c40e000f25440900512030036038032a88207108140e04040b4040d048038250044c180f2001c00d174060410a00302d12900321000e940301500d06540d540303908402500e40b40f01c080020 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 434485017 1250 434483767 434483779
    0x150908060f060a120b0103080706020c15040201020f0c0a170304120609060b09090a0f0516090501030b1f170118150e0f070e040c09050108030424120504060605 70
    0x401c541100403514030070345085660314000b9480d010b036098140c841481c0180907803000300c01070001c5812100500980c520402c0050b00c0c09202d880c105003013941d954034681b140c2e03013004240002c56070184161050341d00d00300024203441529400040b881c12003031054007207644400c1c0000310114401c0c0200c6d00605a0713480d9200b00510345103005402014040000d0300c840f803520078180518034018950500440c0d03408020010a0b656031903018401046680071507441c426616860500891b8681e03d0008110a60000407a58558104041703451001000c500030560700082c0440000b0100052906450b09015101e0300c0317001d8424030b075004042600081c080d0140c460000820040150110241c1301c2c8801000e20801090902c030542d588401a00315003660407000043c45289500c400c2541d009020b4943c0741d02d0743d992491008122242030b000807419400014060000c1701480b05070075031802da2410468841e44140c0c900808034000018850b16240d00c030004502072010799080200504401400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 434486267 1250 434485017 434485021
    0x92d0d0206070908060f220c1401020613020130050c0a030b040506130c031b02070828031202190e01021e030301050105071a13020108091615090806 65
    0x2940c0d9400442e540c00000303102c41030100e041c3d040030403400d0084603c8248178203a512500f00720502c040601000032005a0300b5404000070407403503070000d4010b105007610f015142203000002400e2030401001200038081060744100140d0780180c0a03a040f2100c9440340d1005414408003000c110041e240380e4800030b00308402d028030364054900138149548039440402c41010510144015100126181907114091001d000680c0c66181c0001e201014149000038140342003001104440780d240b41500010b9105103401d00000000304030a1078541c10451150488003580440600c9001c038503500241001003502400d0300707108181d010303100300800c80e18101c0c041c1c007200c0c01d0081101c0c91400410380140b14640c480d07403101c42124218141c130f8411002851540e802c000041d034085d440720404039002010344c02c103d090103881040e030302d00a1045814038440d100c6640001055500c001d40180e0302600464101010814810f400c101114481c2482c0841c64100c1c08043d21010300310350140d9560702480d01 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 434487517 1250 434486267 434486293
    0xf06070503061c0c051002010e120d06050a0e01080d0903111908061f0609060207170a02090a020c0d050c0d03050712020a0203190c0206030c0d0f0e0307140303092d 72
    0x1990054071070640704940d201c5e5560008030300742d0b03c200340b500000350800c5030303509507101c3d0039001480bd0b01c11070540443c0303041c0d030342010a4595115501c20b400c2c502c001c500600c403010090207942803c111502d00000300ca800d41d203c40700740800075003071103118501500764009080c20745002240107084607001c2da403143c6864012040780d009043c00c2d20011400000004c2102e900450001c002d60f40583c1c014640d0170300b09065049002ea07400010101d070f1150028940044e51035600f01c070b1084002c9a070150b11440c08859843c44d10380705071002410700c40240b100d007015003c0003c00080b0143c0500e40801ca580314800f09a6082c00b07644040300c4c203980000303480104c0c2a0008002c0450048280700ca504c0c14078403c4c1c040300ca00d0340070f00d0000d6000341c04001161a440114004c2c10180d00e014170001600c00490001c141110300b028003458554002040c140140f01c07420b54180c10b50301c4610003031031840c54401e0b00741d0f03140c030244180705582d42424982c0d1000c0118002802c2040d0f90490100d03012072007224 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 434488767 1250 434487517 434487533
    0x7170705160f06050a0302030a15080703171c0c110129030609070e07050408070f0518010f0605070f050709141014010507030315030308180f06070503061c 68
    0x1c010705410031241c800040c002c040c1c40c07515046a10710790310181000c05d525402c5010b5031024050001340ca07126107115812003924541e400c0148111001000107a14610701740011f50300a0034181d040c20005d000c0c3e03030480300c1021840d03120103090210010b81c0c041c10300c10580b01c5d9031008101074410761174030307421242c2c822020071024420925400201c40b681c0d030f51710405a461400b104c50804580100350208017207401c811003036400a00c40d040041c20552908038462a01c0003991100c010401020010030803418000300d0300c0041d010040c00d611943d81440f030b20039019040f40c8203002c100000000e025041c0901c6448480780c0603030190031703201c443c0d030b4174040e61015100741004100012040780c00310381a03d07908038240c400c80350f0030195940340000e51001035450ba082140e0940078140c0300d5410300f172002020484074015520031780b00c407400e81c00c0034502d03401900405061002541d110102031020544000703251540a2428a4500c1d41c03035032400d000c910707404040c100c0c7e0440c1c42c0101c00d080d420000b0071 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 434490017 1250 434488767 434488783
    0x50604080c07050d0213020307090308070b0a06080109020a06270e0a050105010f0e01081b030f0a0e030c07050f0109050603010806251d061912200a0507170705 70
    0x121040351401600e903404c0200766005010300039400b101d01d062420070f08025401455110343d140c10041c44080e629140d00003d40e1203048104d0352001d4074001c000c03103c2464425180501040802045400b6455000c5844034515014884c00c1c042d510700103c202045141d0620450320a000c2010b040f00d68580e48101038800590300c10070100d080000104465220700000c9100c0b2415565000b1a00c0c0c100c40103488601e0017500c0f021001c465204081040300c9030302d0045029250150341c4110034a86600058100c074840304403a82503070010041d00045a40010740c1400b42c6108a8180307085074088001641d01c07403c0c981c002c1d6000070300480000380424021499074801d400640520880314282c911a2a0700c40c0515000f001044d8441e031040d00d48102c482c150003400a02501451070500340060034038100d00c0665001d40007800e243e0341c4094070070751400f0310b481200c0c02c0e03c008141c0e9101d07105006502c2c052118000704200002c2541404e012000326004c902c103981c004110350f60b01c440c7c240300703480d0940c0c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 434491267 1250 434490017 434490037
    0x20301050603010903080114011e170606040b0f09060403020d050607030f0b09041211031801020709050903040b0c030f0304031d2209080d0e03040e070206150d0f05060408 75
    0x38090000d811410107029007060242d155440c03401130703070924000118035491400c03a9810070009c085840051038000108480444160f1102c1c0c140c0036040300ca401d0b0f17000c0010103030340c01510140405c02c5501170090a441554207105007940c1c4a50084010032418012580081d51004410400c1401d000c0c003c141c06000f81403903907040c400d03000583d10301c81c161251400c2d419042020400010086817188456001c4450300d4a4035016028010a00a1075500a00240880460300c00c030310840941e010080000248020001480240b030321130700f00e81d140e00551041c5503c080e000182c04070251402d2080798160620141c01c15143d0800303040040840500402e07840c0a01801e000c03a1500340350010074080c820582c44480c036018000c034140c07407014002c0d4a0049074800d505216003080c0d42e10600400480f40381460040d0b403194034000aa035000e1202400c604c0564001405009582074942c0c01c50f1000c400035100805207410503d413028242c0b078542e034007500c0360103910144000c01c8030b240014081a40 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 434492517 1250 434491267 434491271
    0xa08070516050307030b0a0b0d060b010314060d031b0b091614030a0201120204090f020703030b0d20150a08010501090b0c07030209060423040c090603081b121303020301 74
    0x4200640c041d2042035502446505500400c400c000198104510f5036001c1040c080224040c0b040304041014506001d80889000c0e4480411034915645842800807a2100710602102418418041001103104a501604100e4211400b000c1062071030f800e803c1e819404041c0a4140c54820070040e29114088032505010180f0100055008907030700207898015001409070210400da68015190182a20068083c103902400002080f5030203115100350141540e03000360f13136280c0d107150017021100002c0c80c8500c5920840641070100d9802c0780c03090403520b0181c1003000141d0b8110001a010f4080b4484114000c800007850346180b80e100342182d040364020b80ba0805400d440c3d1101e8a003074020341d200510b15500054042001d8a014403926401103409480000c041c104084451440f403107424103210102d60200500c8100107030b4010590050041c1e020030800c0038103580d20f8081ca4403031840c00880c6003800e00500c886106041c07001594000c66400c0c055030325002041a40000c4803a4030080c0c3c4254 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 434493767 1250 434492517 434492533
    0x302060a110702031b0f03030d02090315040f060b130e011b050c0316080c0105090303040b0115050f0c070f080c15160f141009110103060303080a1802030a080705 71
    0x7948010540e03148550003409404512003040301042175110041d840d41c0c0c00f0641c400111402c1c0c4041c001006050344c402d5002d42d8a00c25a410300d031800807a028080ca01003c408200300128124000700031525a00103c040f420b11450ad001a43c4000550310501d03009142405000050405501c121182214007515450103c3d115006a80703a018241d076184183e001088908400400b915640d44c640c1c0c841c0c5070b514108240c4e00301c01821a036085405050f168400428001400032005005004190f000021014100a07050081160050b080030250490011500300300c64402440200702901d5581c0416202958551621f680c484441044600401600c882000009151400c0310503a11090509410303580695407075403d0a510000240c540034141d4000d000c01c0c000506c90660860f40100c400301d640b1085007024560070045402d0740d814146480c2080000903008848160b0014035034900044441c086035880c1e011451000c40250b040c0202ca4280e0104140140076010b03150169041703a4900d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 434495017 1250 434493767 434493791
    0x21e030f060904110d1403070501051b280e031c0e01110d11071502030702010912110f190305030a0e010207031a04060e16180b0a0e15030a0302060a 65
    0x41c101910f003e0b01000050b260700282e0300300303072207100d113034038483c4851415040160807441c2c2160004501202c40d41d4456090000360040e01545042c041c0c1c81c100721500d02001440d180b1000c40c040d10bc0880124031250303107810524081d00162003010000317130940306c51110b41c205003442d4050360800030010070b040e01d0030302c1480c0d44030f445215a03030018107000b0300010b00050026214400d80d00940c0e566485900d00108035207121744054000090503400850f15400288005000d010307468000071408002c0c40804808a5030000c00106000341c103454420070752500f440071803054210441d0a1052a02030030340041084170000040c02801507598030381041e009400d0049881d4401884050503141c0340440240c5070680011410341c10a108480000b050300200907014140310202c1801803c2032801041000440300300c1044089084404400f003000340d64000005110003d00c0c0603514403051440002075602c608000d0940c100e07040202180d2800c51180b5009503940812104001403504007043c405007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 434496267 1250 434495017 434495029
    0x6080a02070f060f0e1504020f1e010309030e0a0b070204050604050c031f030b0405100507080907140307050301020412110618040b010201110a032013050d0501021e030f06 75
    0x105544204103501c40030594983c00081c241c03600c1c40b2605295240d0161946910401c01303104070008180c046407032031900d4010007204c913550065460080c469203101000d0348024140100e09004242000a103003809402c0c102c4298141c480f1a43c0c0001d440c1902144012010020b00340d450b1080701d0a01031540d4000c2030100740d400542c1c00440a80d02400464881401804010a80e54441c003806440c1552601e41c2c01e0703052000e64040c0d4141e00840c1c4074181c0c3c0360740340c000c0c10380c464620f0030101c80904003021800e94400079481076101d00f0b5200701d20005241e60900040c8000c080040003951910b032100300032071415000c0311084a4084850180c2e8000e820014240c1e075005c1c81c0d01f10091400341e643d00038000a0008940300d64115561507014409a4590380040c0c00d804e1015a00081c0048804922550039007502140e01c0c0d02400500c840c040100200c81007105588003039842840c42c3e1068601180a8024404442c4e40b40d4080440080c0940b0400091449140310740e83d151410707240c090903c80 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 434497517 1250 434496267 434496277
    0x9090705210c0616020409060b10080f01050f210606030f0a030504090209061c0c030606080402061605101b0f0302030402011709030d020d0906060e010b0403061a031606080a02 77
    0x746900204840c0758140303403078006042c446800c13050103152459107a002070201c0740c440b54100c0f1100d40c5d40c4c555043c1401c04000c0315140e0456810501d86030b007400c0840200001d414410740340705415080f0700c15070302d4840503180607610124180714070741c401c240b610b0310b5250001241c50902030302c1109009801a50000741aa20341178154031004d240c6424200304a010354003e41c010383c0c00c00410030420b80890f0b441102c10303811034a114070010710501032040c000e0958549031721140421480ca020311000d659105c08407120940c82d02d405180440d0b461402c14103010a00c204c4103a014034080700c0e0a540c0c1440c0ca0b1303810103010f8541e1652288220b401042e0203d000c15a000f90001d40041c92103483c81c00d0b0401c43d550001a02401c503400c01c600c0340802b20680e417183c000003500d21389070f21484c0204109400341c0c0001d040c400e2503e05141d81043d944130031a000300d11014000c0c50b2038420341040d8192114880300e030340310058155143c00029098042c3e040e041840f4003000604041c000030b8100b5a00d1007514 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 434498767 1250 434497517 434497579
    0xb01141801030203061216091104050105090607020103060305071403100e0a060b220605090906042d08030708070905040608030703030e2401080c030c010e10090509090705 75
    0xe150402440114025000105403d03000307200c44400c0d20b1407160410121022841030b40702810380c0307400c0011480603a04100d2100205801c00d200920403680c002043e90001c050568000d41c880c0204e00040b4003030001e50740054450300806a01050341c0441c00405030450000f44c0407143c440030b000c01781c20126410401c801c03016400200c0d21500048258200360000d03100104080000340f101e0007000c509a081600303c14610744e44070410061030408041c0710f94012175110242641d4034241c1c0380c00f9074103844a66804030352502e1107080d52105440d852002c5040e500501440e80f00d180812020b010076070103a41d40000310300b0042c4005094586401024181c814200145040000c40d5800ba40504410f081501090282c801c245074a18a11002d14100845d0301d02d15900039458041d103d07040c1141d04989070b0207504508004481039030042c0c52102c501c20165080035014004a00032210103105400099004008500317100d082d840020f00502a50b008562402d1100280701c507400091040070202 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 434500017 1250 434498767 434498797
    0x30a0e03090f1002011410140306010617040609080d1d010e07060f02010f02030a0209090702070f03080c030c0a050601170a1208100306060e01090506190302151b010b0114 75
    0x801003e040c400c010981c83c920500010407203050703041407061465411071f01125071000040717040154000020740c1000c0c0303c0d02a0041c108a50609030000c0102440707609000c16507409001003010070101d170340003214140c5c001c440d654a40c12103610081c003806000c83c00e0030980c442119a014982c07818441c060702181d110b002001c51915240c1c1c00c2d035004003d00403900542d5030f601c00c11004103645000441c442c0304038100040e1307211015410040191030203041001150b006440034001903008100007800c0e40e8014880a803213144441c100c07440c1d4400d00d11140c1d50741c05400328960800000048187c180d41e80e00e4008060f0100c0ea104d195940c01680001404040d408107441c64441e0103180036036000340800040c4c080079034a945424040c2d40c5158000b1a20310744980040000981c2d911405810600466440c82003030201d6100002152050001902c50380c01c0e00d20f6404100300e45000c8600d030701204540000214460f000303060007041c0e00d54946010480e51201e82c054065034200b2034240c0c4203d01e0f01 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 434501267 1250 434500017 434500039
    0x1080412050c010501080a0c0b0c030a030f06120308160507030e091305060108030c0709060602211b0a0614070915020a0b04200402041404230c030a0e0309 68
    0x422803040000d1a9050910008205018241c4000e0040ca406094468010600030b402443d00a01090031980401e203c00c00c10300c00e19101a10120071107080070309510b00400e6840902c000f0000426060b807102c1002c2103041d40c0001050340104000f40324885c003410301003028190940988284c46a40c1c00140000e0620410708410300c7e2500710399410018602409a04102a0f901c0905e440c0c000e030416039182e40301050100ca440c204004100203080414014000549001006036807401800b20f0803c208440006410101040e00150751200314a10454002103a00c200d040e9100e5075250b0040d52003e00302035548403844c5002469501450340341c0d607403980043c9010011500200b030401d10340300f1070041d001c2d04400306a04000746030156001c3d161f83c1000056503d12008810742412140c0d015500501040000a081c2010180695000d0300c022500c00c02103040301400d5103104070394400c00c685440900101d0010200654858104401c3c100a4004050352503942d1b03009421055038461400d0030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 434502517 1250 434501267 434501273
    0x105091302030924040b130f0b070e03030a0302040501020115050a1206020c0a060203070e0312180303040f0303020106050102100204150302070501021c0506030d0507080414010c050102030106081014010804 90
    0x801180e0107001c1e2003d4403000c100c120400c0b07014540840403100718581c013405000611a020b240c450f004000b810b1000c40c05540313030341c9442c2ca00c41e50345400b400e1000903000140407180586050100404010f059075a900c0c181e942c0a4020b40060154600661078180e03001d5803000e1031b81c4958162039008001030303495458100b44408064448038200d1324540c0a004c9072a120400b00303d000d2100d0f110b207401586900d05284c00030a51240c40000500ca03030302423407404c102c0d01d60820807104401031b01220102c4900007280841c0c030314403c580c810004444407000006c00c0c50341c1076200034191282642600c0208030b81c6c11518080c0d0103940200d201c1900541241103005000c4c1e802011402d10a10001d42402e44030150f008070134445425882d0301589650130004989424000401100d15504065040c12100e450303820b05070042d80281c04050102e01d08142550f80524500020694050b0095591b503031076200c010241d00080d02c101002c45503040000ca800f0351000c4070340c03880c8441a5155143c80c1d607162 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 434503767 1250 434502517 434502521
    0x40f0203011401061701052103070b01140f0436080301080102070506130c06031e050405010912031103040f021216241d1207061e0201020309150910051602010b01050913 74
    0x841c12303880c034801046103c0c0014800c014903402018800488021a440e02041c88107014031884041c2c400c03407030a41d41100c1441185007100d108400d081c1e010360702059200c603403400e00c02c0c56040500743d04404000000d9a0320150004c0030f4030740c480d1081e142142c48a4075400300081a10800810200510f1424000c0601c0395000c0c0003842c28094085a14442d2482040200c4805880984941e515107154005006243c0542c0345d68101a280400425043e6020305c401c0d4080600000c1c40946490011010b5548a00f034100352030017201d042c0d5540d1980061010000340291048140d15051480d0481c04074110140c9a46015825141c0d40245c41d80b409445000d03a01040403141e010f0003074000122252802c001000c060300c05600c03408024081d08014084103e03200c1407075802c583c0104104442c050010610125a16503881c01541e6500d4942909007001c0d80007a40060791481c01040069007840120141801491340d0001c004000810340111401e1192000d10b54000c800d2501c0307007000380300c0e0b9 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 434505017 1250 434503767 434503819
    0x80f0709020f16140f0d050f070503040e070203040e10051003021e0c10050a0207021c0302010e01051623030c1e0c07030c0e0405060708040f020301140106170105 71
    0x2c0c03040c6518184668201205400107a4070690b000c0021181001260404102c0700d40c5440790340d401030030300c5240041c0062080c0b140202140c4c0c3c807a004070b81c3c041007001c20020340300580300301032a8400030310301407200a5482c0c02c144924403030801e882002c58820200680c28100b640d001505656541c0400716040c0c0203540701c078040150400707075120054032098a11000d020710481d02d80c007402d88500c04100c01c5060341e03000340c09560484c0c4100805801a40c0d007501c000350300702080b0380c0c1c0551403459050a07801003182d80c9140c006035081904202240d540a0260b5000070400c2d12040240317155010542c0c0c4090400200102c228810008a540400308030b01400052060310654180b65501c2c513828030827500401c14581a0358809002032041203001d081c604060070042e24000010700c0c1c280ca80310307031b5400040e0954060000c80d00129080c000c08078070170030509401400034040f6803040354020501035000d2182500042c0004803818811308207002c507074100c4c0c20041c81444000c44414860b20300e8803503 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 434506267 1250 434505017 434505037
    0x11406070b0402030a0c170f07050d03080c120c0304020901080607080109110f0c0c090105060f030c13091506030c0c0c031101050c060a09060c08010b2706180307080f070902 76
    0x703103c6a0100191406e440c0c000582a0b0391924102c412644400510303009000300d101d4003e800c40b4405001c242c94030482c0050a40c0c0510380200c20751070b5800b1507040c0c0d105000f50881c4640501c030800200d03207403400095008038400d49a00600b42e0381e44100703030b8486205696010001e1401801007080300500d800c1802100c5d241c081d95403074002901c000f10305507481408420502d0700041e42405480c0f03013000c01e540c01040d05440003858280c0304681d034112840003c1c0034000055000c208062084a404002c8007d0042d10b41e04000e906400c0540004c4c2500350b12520000a00f4540744070f030351501c0381c0c1e41c01008036405003040c4102400c540c0c50310501e820103119541040800e004801c5074030810455240111690400000d440c002c134281501914003002e45401800f400c1001080450124030858100f8021001141034034031f00d80401d00340d896075114859a20240105015400003084032511140003812822100c889a80c4c041d01a00d4009000815020380c111a070104201443c540040c4070707960b6 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 434507517 1250 434506267 434506273
    0x1e0302010b030d1205071b060e011514130b0d0602071a010e01030b01050a060806010305070201110a051803010e0a080307030b10121d030318070e130506011406070b040203 75
    0x1c003000100389002003140c41c802c0000c1c64032012403c1034421340f182a0b080728080c0b4200c0344510080081c01c49051286100400c107d43c7d50700d424185c5a020b500c07401e00c4003000c0070314400160b40c60040c00c95243c80e07a20500e2180000720002c8414008501c12441c05142c0540380d035489407200c0c0c4a110094000003c1582c00d0000080120700d0b9103540d4400b5800303401c0607403071001c00354118104001042d005802c40b50080d003001800703002103504010030a43c0f0990910740860540e076130b84c1040f0f0240070f4102d0504402d400104005402603003200143c502c4002c0701400e14500102101014240c40040e01c841880d90004011074020410007001140d012120382000325041d19804003065240700312074194000a003200445400e1070f4040d01840c80d00d0140c100015004040d11581145c0b2840007405080c00e4840c3ca2041e04c0b203555052244c60b0003410f20803400c442d580b5248a010172081d19844040380d407030103500004a80c081c20100d81111102010700307140e041500c280d40d4010802000b400681e4944 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 434508767 1250 434507517 434507531
    0xf0c2c03071a0a09061106041e0c03030f12090210141201080109020f0d12050307090b0f0405100801080a0b040f0203010c030c03060542041401090506071e030201 71
    0x80035446000103003002050600c1d640e804401d00100000885c0d085802080b824002207008072800240a54205070050591328022404c0005103d04001d0400c1c011306409a0b09000014180c200b820400030000ea07480344c80d01e94410071032410850b10b605c9002988141f821034031465151040b0300180c42c0401106030b4626008480e08000501f83e8241c1c043c105d1030303444020440071418017403445211030f1400e0780c0020140050340d65071604120100c10030400c02c000400000c440303510642e00c44000b40340e055182c80c0d40e900c0030305a13022182c2c070030700886000701018035000640c1449000c0c100d040b01c1e01000a46014440e40da5041002c0388050003c5e01d01104440052015960a22801440c00151707200001c40700044c50700a001e60b0744a600c1144207010703050000641160751582e44081008500405401c13200d038184861000010f28940c00412030040760100b00884580c6043c1c3e50321909072600d840c2d60350b4510070071807a8850360b5801000c1c0340928284c100c4a49245915100c011300c6070001003219 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 434510017 1250 434508767 434508779
    0xb0a050408100c0207060804230c040c030608160305100f02040e0c030a050606090f0603060d05070b0705100c0903020d0f1b030b0c0f0f16020307090f0c2c0307 70
    0x400b55890104201d15650302e20301c5221a010498803006000c40d007401c6d03980d40307005c0e20340d45101c2500e5450300c030b0980c3e0f0310443d00c90700b140b042c4240c01a0800082081221090028005008180900595059209200343c0c0100ca014072008501104d40c071000400c525500d81842c10701030407184d645045515020b000c08030b0030303070701c034107800d600c1b070415204c1c4581c07203150101e01d00042d82c0b0302074040b9024507010044500749446003100e078040b8030410f0350044d5507034865a0102d04013000d4510f02620600400c00049003c00701500108180ea0050048905801440602d0b104440f0403488030004100748443c01c10040c1070844645541c5130081e0141051401e16458051503581400f828083c0c0a0318144107008000554040740e0700869540042d608010040c030030f5044612038204039a10702407007c1280003058036100007080a143e40503007681c462030f58030019400070b012284482c1e00c026051140e898005c51140c0350080391000040c1030388100541840c24120400725035004075805002d40000803901c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 434511267 1250 434510017 434510023
    0xc2d04050a1401200607031a030a0804032f010c03030f1a010906020303160c3017040302060a0f020c0a050d0e240d06090911010f0f090b0a050408 64
    0x2d0111642604a0758114800106a2507100720404190480403200d01940c0c640050600e40c8401a4100002c100c0c1c40030078030808038051721002c01c2c0c0c10300c03407240000204050500038208491003081d42c0d294030303000c09000110400d0000310890610a0707001042c1c00f190320544d41915080c3c0203007800035420340340d00d15110a85080dd83c1d1442d588141e10a01815568402140d00c001c1165101841c158240071852100c100a44282682001350304108003040c03050529410340d0415071400880e04800d850300c1c046a100d400c40c41e01401090424140c0908007002d2104103100e103a145d40030b0304980e901c1140030030040c1380340c50144000700c0e03090100c0112540304100512609000d00014a5510340300b50300204400c5082ca00d1602034010314200745e5414000c002070406052600c42281e40711ba0b0107a0512000307002035030103d10154145102042485422a40480c03800400e0760350311541200c1007800e81c0d80c0c4081e1403e081c00905e001c20f0401c49d03070451001a101100003480c04501d4143c1c0c8131140c902d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 434512517 1250 434511267 434511269
    0x90402120607020a02030f0703030503010e093d0207110108100f0608010503060709080604110301110414030705120c1201060b12010801060f0614070302010906110705060c2d04050a 79
    0xd43d000141180c15860208101c44102c1f80860081c09150709555008003d400188a1020044c4140d800710300101400d1002880d164041100100041c8079455405800d843c21352550400103045505c0601085d00d2b402100c0c1440d81003030700711803c0100755004450f440b000410105d411000220049a5038542c001420000d103529070f034489440d41410101410000d0103450702091080c0c40804001c0148042100e9a1042e007084030000c50329416004a0b024010340c0d007040720070840015003c40c52441c1e0070002c50aa0000f40c003124081c944542c14050661501d000d090280e80c031007984031802d46000c60081c0c200d00241400400c040341c1c1c0d4290540c058120500403202c0c0351940006000000c400d10070540100b41128541c0e5600c1e140910103065500c03203c00e0341200141c00503200c02070500075000544050f07448401001038003900d01c040c1c416600f22a904896900511002c200d50043d01800d559406110201002c55880b4401d44003a100109a1140d00c60388000d000c001529510303410408 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 434513767 1250 434512517 434512531
    0x130b0108030405040b030309030d050d020f0409051e071d060409021204031b1509030e0a0306150b0418020a0c050105070e18190b120106081501050a0b090904021206 72
    0x16807203030300f06800c01050300e0300010f482d40aa801841036a03074550300003450401c0c10429040c4140e503a400703599803401a1240c81000245810000f9000a000e11030f603000c98410100b00d000c40d0003120000c1811000c5030010355000c00061200214603d03041c3c010014405d00d200c0003002c091500d95510a00380580c0c00441240d01c40c0341c2000c040005045e002180d40c4024002d00e074400f40000b015a40307207465200408001c102866039414400b003018010306c40c410034000002c1c901240143d81e0b00e488009480c01c050341507501651410300090110141003520150786411004050020a5141e101e0094120b4070341c01e0204540c404510010820030700c1030600400c059039a040c0314103c0e8006001c087c450082004803412404c00411010345400143e606004402c1d4201045002841000803011894603042c2c00080d4a0003000207682007000400400310901c0340f0f0249826a80c0f4420803601e444a40319516549204008c0303503045240c03010003d9801407004010350500c82c1d0500c0750078600f200890350b01c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 434515017 1250 434513767 434513773
    0xa23061210020315100903060b0d050a0c06021204050303030c0a0207031e060506090108030706150b04080312060a05130903020a15050a050f190e030f0a0801090e0106051008130b0108 80
    0x700210750a4124a180c0c1c01c6426541284045d1400b80020920841880040c1101c0e68036071010b00d96a582100f0807244139041011244000c0c401c0c1080b006e0390729907106100140c840d0701100c04034241c600050324112032004014508550341c0c50360404180d030180d40404110b002d451400300c0001c03404185400341d824038980121b402e216628000003281c01c082e210622404501e00104408803000003140c5d130080d8816008501c2040f64000c0010015841c0c01101c8024400300b004900148000042d16003011416100711060b15002c0074402c103c4a40d00800d82c1012282410909608685e0000110389111384115608100c442c0c03204a20385c40d4681c50350020b00d85440c20310500401318010320b5001010410164914200101c410001c08403241c0e4013003a05480e8502c000b400e01d400d1003520606c010b04040702d0381e584424000104002030074012401d4507032824900300c1c48603030140328603000c2e168050b0159420400410050305c0a81d03008220f000000c00b100420320000b9281031131b0500800b410401 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 434516267 1250 434515017 434515021
    0xf140c011803090b12010b0c07170a050105060d021008100b0316030e150604110d0203040605010f06110d050f070203010608010203060418020607020603180102130e0a230612100203 79
    0x8018000001c5a04c00a20444244194a400c800507503456044400040569030b41c2c5184c41c03880340c20012184d100e0a0344181d40640ca06041c00d02084181e01c2c2071054000f00000e0740c0f140200a1a2840e141000e9048008210270741c1d41e460250107a40d0308040078103d07039010b03170303907941104001c561044a07449000d410a85c11818029003500880c07181c203400c60058060307140c503841ca10352601350051015100b592200340c40680c12849500f1190085082c80003507650746041e0510201a0400b031140b445401c0343c226000810a201d0741c9141708010a10003e410310000469045880c2d802c4025110603000c82045040e0040e9424854a4020300c84c0200150300d034a8644204001c0f200303500010000925400b80c040010794442049076500b907070417140641c4039198240100001d11064402c0d1647c0d40c400108007086440d0510160304550000318014081d41d04d811240c02039403a40c000100305900c020105d20104081500f480c1c0e400903003c1c000595a422003924286001c100d01c2c190382d0b2081d80002 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 434517517 1250 434516267 434516273
    0x105040e15040503120106050313080904140a02070c060f1706040e060a20180909010207020901090b040c26070e0409110306090706080705031f1401031b0f140c0118 72
    0x2c0b85e038010503980c06d0440c254600900190003406a00d1001445802d0019501040d581c03107500484599140c00c00c00c0b1007500e03100d070845000b540442070079100340d080048001100d6129403000b40c80001a9920051502c3d1009070b0300e0400b0f0406408a0750182d210381071a50050340400c61584070f48529140403130b888902d034420a00070481140102c2550004000896402002ca100e40228940c141e414110903915044864020b000b01000290310046803000014032401682100e060030343d0854040240c4042c5241c01e40e90348100010301f0202030b1542a021480c00002c2c000940e04c00418100b01080600a1000808803a010441207170b000c40c1141941a05090400286a0220074030000b00803041c2032420250800300c00400c8403080000001c000303880c00e900350301c03000300c1d101c00c038958844550340319202c205044070080840d60009240240340b030000075890036a28810a410385481300703551484d8400b1a1498060052504520800c0201e9264540f00b48616090001c40e462000e0040074249 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 434518767 1250 434517517 434517547
    0x81b0a030b0708060a140a050d0c090203040f031209020d0b0601110f0a06060e0103260408011a041a131d0a060c090b0310210c0602010c090b04030b0105040e15040503 73
    0x41c010045a030a00002000300d40c0326a01f0b8042940c02c1150360203001011482c050000310310326000f29a0b41e0340003100380030801007000610101c2c28480d8403080c115002c040d91a0b4200c1300003044c080d41c042008614000071071260b20b1350680040040c503108261802240308540703454140c0540362601c0c0c0c0501e516205001103446080d0141820b04070142d85540345440350300ea1f41102815034400e4550340600e1034480e0703a109003110010001c0d07400a0081c0000450303030084010200c52030901460401c0d0b031118a0069003d08008121802040c1d82040303643c0d01078000003001c20b011101c50601001c103902e42c81c030b04100010850b06108660220b4076000034600107007684603c1e405500848428030510010410039070701c1c1c01c00c0c1c4803410380300404170b6003a240351110f0380c1405a000c8c240e0010100c0104140340d06410203480d042840e01e881c07181c076580350000756191041d841301800c0e100d001c0005002910f4141c0110601c228001c04807803003200b030445a0803000794180d800b100c441c3c3c400100301200303800e40 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 434520017 1250 434518767 434518769
    0x3050c1501051503180f070e0f0439030c0302030d1b020f0f121006051c1e0b01080a03020c0108010e070819180615081b0a030b0708060a 60
    0x846591a039a501d031101190014442d00e82d002c440c0030003c030001d5007021100840b05140d004d8082160040807444401d1a00c3c0c2545000d0405441803440c00039107000103036181c1c0d600440c1c1c8805590008030b0380e1101110400c2691840701c45c507119034400200e000296a0601001e10b00854414a4052440c8101443c08581d182c01d0010300c2300f40803100000b5005c81c0c001101a98040d240c0010744910b00d4002003030102442c0c1030540c042c01e6030405e1250220001078441030000010420008280c8840401c00703c244400400000030340c44088401c001010004e800058900404010842711040d503550302000c503090304a02c4040d4061034035401419410811004c41035800e003006100b550422950f82c41d0301c000240480240b2070300c40041004020100c0700000014060390040291780001100b81c43c800c00d04417025a002030610504d002c1e1300c900744034904107c1d20700200800b0703140f4085090904020055410590003101440008046561005014403400b0b5540c0c44100500e0301800300b00c142405 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 434521267 1250 434520017 434520043
    0x30f1b180905062b060207060506040c11120d0207052506031e020a0c140a11310e06010308040e090a02100c141204060f020d23070f03050c 61
    0x1440280002520755052040d200c2e880c401c0741c0030400946404d802801208a540104410301c0012040c090004950025000b00404c03038041c00740007a401000c1f245161010f601c3d02d20354005102954991008800074210340c2280440503041c403000c2c0c1c60315401c00720201c0c0c51402034080c2c0d50036042d0403032045070144007804039400c04015a6980055242040003400e605054a543c00100d0040f8140100c854090b4660302c5500c3c1844c542d9410182d6454440700b11084650722854040c492891600d0071460f040d01c841101da40f1001e03402c6c070852a40200d8081c007040c0000e80d413000e4180503003805200d814080e60065844a554515018414054680c0181100559007000c1c1548005039524105c014501c02d06241c1500e060441f82443d50a1002c0a00d040c0e180344503500a501e0f502404034050b0048903120f494144200072440000da803541c403240303a40700c0081c00300b415820b441005059003010b4025220012420403840c1e64520204180301c0348283c010071400318001103000c03410440c00b242411 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 434522517 1250 434521267 434521271
    0x1e030e0a0503130f12080f0706051005040c08060d0f02120709050708010b09010c11010302090603040c030212070e07080705070501050f0105030f030405030307060b0301021e0304060c030902010206040201030f1b1809 94
    0x41740c400003440421a5001c014484800020b074440d03800f149901703680340325410400410050030000c0d0b889910142900c18107008900300300d2050181802442018402d8102401c11104484665284c44a0094241040360f1000d0000300307441c4190001c03c8104050113510900045505206d03001038034480d0141c1c0110f0a108082003100641e0740c2c820141e841c09680032080e0480c0139411001600a400b0300320b446908080301008101c1800a440c1c541c01c1102d00a0781c1c00900c00c404452410749890040c003c2d080040e242d48042481144540000c5a0082651900f14102100c590381c140c2910804d8500c1c0703072943c24500043c000380c0703014010b4450710201c21000b103181034502000720303842c0c0c081c0010140c00035607220b0f070442c030303030303202034040302c0000407810301c00e8a01e0303002000601100d800c00c0d9015105d11345020a01d6415a00a2203400721840d016001008a940c60381e00450113400f07020100b81c0b290751138502c1c80032101d034031000780410302d0160b4030394aa910400d6808181404401c4e0700076038030700d8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 434523767 1250 434522517 434522519
    0x903010506100f141603030506040b090103080406080603030706020a02060906010e0709170307050106230301020310090f060e07020d020105090c0a0303051605060103030306140307061e030e0a0503130f 88
    0x140d008080648000c0090410b105801c0f5840c0c4994094001d5445c1070000f0400d01c08031204040d07142e0712603031080d40122020805140c1c100e040c82440007090000611808041000380842409410415801180101143e26000707656440e02c0907a0003450407a409a403261050040510007800600d000d01002060203645140c2048000c141c0314051040c22a40114004040c811000510440c0c180c0d50b04039000f07011465480403007400d09440c1c800300c100d10004e0b942c1c0c5426145018001c4034044d256101c0e82c40d040a040c8001d00c401892100280240d0700d0742ca010025906505804c1d06200c0c0007260094100e0350816180a800c0d078200801c481b065070050081c40c4141d82d5034140c00815250181b401c0c1d0b89801905040e1305641c00c10701e1015180f0301c1500000810140c1c15000a41915074a00b10b4100140300082030542d50b9040d0302407035000c20b411082502451820704002400b44c0301c140340100c0c00881c000501c0f400d099000030142c5441c0c1000401448580d1040000c10050054100410704d80b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 434525017 1250 434523767 434523799
    0x30f0c02031e0909070809070f060503070806040207060515011416230303090309041d0d11120d1407080403092310030c08010f03020d151b050903010506 67
    0xc0d00c01e140d01c008030140b0480032006545110815151407010103480989039050075a40500803100840780401984568000854000756030300701203048407201c1d01d50500b1519410f20581d4052002842036400c25424081c4001003149130288074042e480c444420003203c03182c800010198812504c041000e01c00c1008200c110010040d042076003290050031200100d030650112096400605a440845100c04801d00820840c04801003070b040c001150104842e480302282280401c40c00301a5103015000000b864007033901607260700707003502e42d0301080e0348800020036601e00081d0040412085501c0c1c1d10a22010700c2103400c3d4406410000a007052010361070540e5004000401d18000c0000d5409581c00c282d60074100d5000e0f403a40100700620640d144d01510000a00922100e42d401001450500001070508011003404040e070b42c0180030541c42c8652600c9601110907014078102c07626a03130304c3c0644021031252401801d01140c90741c5590741c07080d03904201402d441e0050300322803181c0d071143d421100b4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 434526267 1250 434525017 434525023
    0x30a0801181503080f0c07031a10080c0405150a0b0d05010e04051207030909050f09060a02130308090f0a0b0403110103110a0c14030a12060e04020609151e0406030f0c02 74
    0xf00c0b98042c81d05955400c540861076043d00402103400901c1c811408080204034074103140c030310014030300b03030f0540d030b850f91a000c001900c0c117143c1c880c614194000c0340e800196030812b504102d900c0f5400c9241c0d62003d1011070003142c200c403c00d1740020300a140100d81c2c00d080117445e024050050049000b070302d0103030420381c41c1e5a4a455100402e140440030010321242014001d0000308020305001a04200503c1c05075113100b0803040071540d031035880c060b6070006120b4802c01d109942d148049244480c100d036040d980c074415607602003e20719510502c0c110004015039211000f16000d804640c4006444030710b1450404500e00d80169070506240c10a01001042e89101082e82c4103840140f40503403500301d1a0600502d1040030481020490100180801180360004606805c00600740c0c0100099543e078401c040c60300005a8009502403001c2014040b24a8850b458420004014040f980b410402095000d000c0f41d24469207509148080303010021705406104040000c0300003481800414040b07400291 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 434527517 1250 434526267 434526269
    0x40602030a211406040510142404141c02010e09060607050d0818150c0304140a050a02040c0f090e1504050a020309250b030612030a08011815 62
    0x8008901c030381044445102c02c6421901c00050204002c3d0f030012601c52080300301c044546500a03030034100803454130031011400100300d0314000710340a0309040450800c1404500703a00640400a010241c881010100d14020f000501222800d9030f109005c20080c0107502454503140c0c0d403810012140100981d0708848007151101d001c880940c8143d9455000130124010b10f40c2c00792281c460090b000291070b4000684a005041c42c1c08183c400c0c03425009081e903929170300039182590f41c1804000c141c10002500113075810030301c9112a910104400021245003510101c0241c4003640032080450650070984540c101c0301000d442c1068840d291010060030004091088000ca005010b000859a0010705900829541c0041c000c2c402418640402c10203500b0554a0100c07901400a01404a51000c00c0307280403040c81042c6c100301145802420b4050782c00080c03005802180c115145400000c0510040564125503240c21a05504003005652107400c1280600003440c40d0485501e0002603182c8600 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 434528767 1250 434527517 434527537
    0xa0b040e0c0f2704030507050a1109130c09020c010902100c031805300a11090f040f1b030c0315141b03150a15020c01020c010519020724080c04060203 66
    0x9042c60b20781e0705e002c640604c50600c015009018501d014410040302d07600311141d04000b21040c00117522081000c481401241d40010b0900381401400c000d5842141c001c3c0c110000042c0c00010041806e40220b502e514524000390b00040c041c280d13a004054112020b10326401510b00010300b5581080045031541c812209200c810020400c1e0654500210034800403400c9420010340f44003002e01d04d40b034041c0c4958240b44501c0740403c0400248410b4050134894401e0b40c02032840ca14564050f10350381ca2403400300584185501c0c81c54004404100c18204050007103120380e0b10940c03c0010b085840b021103c0c42c80415442d40000c200380b0004901180c454030030a607a40002c550390b80c80300100c2203a03001014241c25048280d40100040820a0074504d64240f000c83e000c4d260088040b1004a8442c2d110a00da98003090090104010141002c1e054152055043c011554440d0311400c9281c0c0c6800d00940300d0700d000101e0700c45070a220342e11441403034106aa0450550410b803c2c410041d4403401303046035907 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 434530017 1250 434528767 434528839
    0x20a0f0620030a180b072001060f030203190201230d0216110406060905060a020c03011506090e0c190c05060405100c020c060301090507180b0301030221060a050a0b040e0c0f 76
    0x41024086c080c7c40380010100b80c8001c10000b503a130512146030301da091205a2090180c2c664201c0c035115000c0c588055194140d40b00300092820b902400b0900088051120700c0400c24000341810604520080c000381110708000b5200c071030795140098050000c800c0c00d5014a0400c9403c1201d140c000c58080155803044885603100c091401c02280381890410000d581b5600f4604081100c0b81505480c50540701c0e0f659601402d19110402e54260ba48161451090b4200411510018054680c01402102d41e41e203044d0800202d9070310341e2071828100761020340b1a074000361052552003103070f8811804242001e00181c00d180c000000010904d010501c0750003401c0742c032403001800311441120b004c194010b10142e00c0071040e84402c207180c4581c00901080f4090055078080d0b0700358000d61041c12104094401c01410656254081403001c1c1002a2040700482e03181e00c0c209030b1655580c0200c80949001e51b009245074141c0504110b01240303480c92843c00b44450100242c2c00210800100e84421081000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 434531267 1250 434530017 434530037
    0xf0b09150a022e151206091502031806240405090a0807080301060237020a09022d130909150c0f020f010c020a0f0620030a180b07 57
    0x603418503402280b1041540c06260790a5440041021020709074445500f003044458072074070000f120001c0710f000b20f000804100c417665000441c2a0400c02429100703100c010071504000b5490020398000f0350700c121001c0002520072088540400c03046901c06625200240041088205404e400301011035842c05203407070b440000c485100400c0828060396010100d03d580d0b4401303041c8203000350801c0c0a60030060041c003403403030440b01814600f0300112604caa400c00120515905c00c10036000300346001ca80185620b8400100c0c100d4038405800c0110030f07401d85c400001103031019607080d490300c4100201a40c00900c0304200004140d48580181d03000702500240540150a00020500411200354145d50914002604255216070360300300d44101030f002c440002480f4030300c082c2030b2640d0807010b01c010b034441507001011035500c00441087d240640310002e88011440092914104a621100034085c000018031203645020b1041c544600340092140d080214240e64507943c80c40c0241449041280ea140 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 434532374 1107 434531267 434531287
    0x121206060905060313050c06040909021207030309051306080d0c1e0803360d02101e05040305130303020d0f030e031b03070c030303060f0b0915 63
    0x10100b9003580d035240d40d00d01702c0400d100b005850a120b81802850561640c0c002440a40342c070480110b41d140c01d130b0050015015805202c0007a56101810030404290701c10440300555004480b03038407412140340c000320068940b0341c07c2052035000c1d000811203441d401c1032a04d40380c0391141c074410380e000d1100c081da00341d040190480030b000d0050410000e01c0380d0940400240a02501d0001d00140240904490b00d42c017034156940303103aa40c0085032108815804100c11045002c0710f18041c0280829403020b004e01c00b01203040d09018a858801080070180103c0c00e0721302c001d02c0c03418656905541c1e410300030b40d500060400c034404a076550160022652090080070711401d00000114600808403990703410881d101c0c0d400081d14003061101c0c100040c0c025074807000840c0250360208205085c4986c18140220507444500344060401a01001e03131543c04030440c0303600c154600b00b40c90b403c0c408 = true := by decide +kernel

theorem cover : BRFrame.Cov 434352517 434532374 := by
  have h0 := BRFrame.cov_init 434352517
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434352517 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 434352517 ≤ n) (h2 : n < 434532374) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
