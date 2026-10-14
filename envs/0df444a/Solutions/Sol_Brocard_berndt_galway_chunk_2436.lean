-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2436
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:42:58.982821+00:00
-- url     : https://prove2.me/submissions/e1ae7a2e-670e-4ef9-896c-ab980d604852

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 437949640 ≤ n < 438129496 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 437950890 1250 437949640 437949643
    0x30c060b0a030b0901050f0103030f050901030f0e010501081912140c07060816090308090103020c03040e0910060b1810020f0a060509060106080c190903081c1a0a0b0c 73
    0x46000d41580918404008010031207000744250107440810000c0050381c1d1581c107091024007003800041d0224110481c04022184a040100601c090615001c50030104502c5c81c1e0302911000e6488a1441c1d4441c001800441c030200283d013841c81d05401e03505000e01d5141c80d007018400000b5101400c0040c1100071510000f50a01140c1c0000c0c90982200c028075560b400040648400391000922044001303106104503115020900a9a03044020540780010740c400540c003c0d4891005c0e502d290005200004100c25a0018144504400ba004d8040c0b1a080c0b00110120f800b10b80004048240600002c01c8885503990900c0068034151600c2c104440c003020140e107080b01803208034205109200f022820061341e41c200c103009064620403a002031349c03255001e44c1c802c1c40449850059407401d0000d8019401c2511b0880e0601110342007001d84d054407525643c0d842c2d8400c2c121503010303070450f100c43d04100119116044200d00d1080d42a4020002d10b8000344080300d1078811004603031008a0301d00f010364030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 437952140 1250 437950890 437950901
    0x110907090510032703120905101d240a060b091e04060f0504050901020f0a27030506150312040303050c030f031009050106030902010c02040515220b0d0c03030c06 71
    0xd074840c40403012418800010000c61044d4086000941740c40c11000806128010b0780d130110f40c0003001c0c0c076000510100b054024080c4020b0702c810800d10f4100c45102031828000e044e0f0341c82101000701c81e48400d4040d40514010090110000140b5001003003103103030f807034005942d00740d0b000302e0380036034400e0300d80c106960303000c810154940d80241b41200002e42444100300210480348250342c01c0c4a51390341c0190080c202e002e0401410b060384000c1084a01d0b661141c0505100f201d44100c1003d0072007014100c0c1584903070650000c40710f0381d00600600c0941e041c4c5148800422500310000c2030102c1401d9104280d5000e81d22005050250104803044020307821700c290340008440203201c5489140c00d0115026449040c42402c5250f40f810303002296440c8280525542e041c1c06854a142c180d81c180e003070000601e0000d000c42a0441100a103552036031382d540c01201500b21000c0034034100780500e940d44044030718407144940b00d40407801984001420901c0b100003240d03014205041d0200b000d0400102421 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 437953390 1250 437952140 437952161
    0x703090605070513090b2b0501090821100501200f0a0213050c0f09040e010912020f060108070b16050f06070807111f0e0106090911090709051003 64
    0x3814407042001a5910602808028914103100404169903882c0542120007001007a90070408810300c0c903400182510050f0190b0803010418001d00c2c080744c80742030171100b0881c01219041c600180e0750300503c0300d02c1c010495002411003c901e0504041202c403212110901c592410700c02e40000001480c3c459600300c40c2540540c0c0c06031035038105441c61594079038801034400c030300c10403a140c0c0c000101c404a1242910400544d80c1c401c0c0b9004452004e0318803a00700c0c400c100e40c400e4a81c0c0d12103104807000e01548201c0d0b40b1404100c0340c0e2000d03468011b4100840100540d000b603102c0130040050311400141c0308210354407240001d50741ca03200320604680710540040600580300e0310810313401d00c143c0020218850b0445940b0a09039854400d03044030941d0040107080040e0340048100f40e00041c002144425a40c2c5a2100055868041106500303441c0c040d401801034954604844043c4a01d10302110500307030b02101c00d01e0301d0349040c9401400d0328066000c3d060180e041c429080ca1894000e40c44811101c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 437954640 1250 437953390 437953403
    0x105040b01031703100306200a12060b180402280801080d0306081b030c180406050604090515190204080d0e0301020901050f03101d1e040308040b070309 67
    0x146054103004160a1081c80101c803050100700116940840700000e80c2d006440000c09080640c1c5903880e17980140000c0010a11b03444642041121541603406c000d08003004280c0302c0038034004e0074150b01421076003141d005001703260081101d661041d030400406221602e00701c0c0c0040c1c0300d0a21884116900d503510354410800b800400d0703603e80403078100d103a960484d102e0804480311455510001c4068132900d114254a50f801480e210842a2450078652078a1202404644190f407070200004c1d407155081700e02505400984e401d21041c00392318000c2c164402010b0343c040c419000325070f50b03040e61884502c100000e0009120081040406040b80503421603480346810754690b5141d04801c1c2c0c6402c442a2140c0105841c0c40007503290b41010700a413000010140c44190504c00c2031030340140580d10041084120300f08101c0c010031a40303a0300b104050403444070750300d4042034502000078009400648800c5c01700001d40c0000c110010741d2050655521590000400400b9120707a4410b9000d46613800005052 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 437955890 1250 437954640 437954651
    0x40302150706050601031404020d03110d0302070c09020a050313030203041503020c01140108030d0e0f190b100803070609062a0f0315140a0b0304060b121b040b0102030c01 75
    0x3003909030018254060240c0781c100120340310900150211051516660014440f1400080c00b51a0034048400390901a041c45001d503580720b125a81032440503108000030a07804201581840400c40b5031401606070f06104501d8052a80344c0035055000007001c0c0741418088603034030030402d8824805e54000705403143c4020340d01c000c8104090040e40050750704400940c6401e220742c032803840d4111914100c40d10600514a1b02410340000b401400c9002604480352207903201000c1c080c0d40c2003040d503421401d00c0310041c021603030034681001c030328401a01981071402d00360424000e090000c4210f91075203502c07200000b54042103140c040003500c00d010010f4142800c1911908104a00741041003400b08250303152813040c02550700680c101e801480c100541c80c0c40d07150080c0161030344581c1804018200602842c01c83d030342d90703184c1031203940104c034200c0711540c03102d071902003600340148031000351680c2201601e00f50644802d4105010400b50341240f041b52070b011087c071a44d00a20884001e042d005000344503 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 437957140 1250 437955890 437955919
    0x5010906061719030f02010605030a0c0f050d03050427090507090e0115051002070f0306270308060405040206040f0b07172b11030906040c06020c100305040503040302 73
    0x281568824514000b40c07081d0b151400a0001c60000802100d07440081c1e0722221548017124155100f25001c003e40d940e8140104580c2c0c0c00f0041181e459219003480c1c00d0b2207090680c8081440340da40d00140c064804201050000b0b83c005055909440f403404518040c0001903051044d2013500c04000071130076150200e0301e0306100000c942d0b80150f41c8104014094642c42c103c070076003281d000040008001c0a03001040c002854844002c0d40b40150510403100c6468036019100ca02c0e0b0340c680d00480c0c8661b030780c0c9c019062060008103080c5010b83e445103c1c040c2040039440c040e0492900520080c8038075a110002011552013500ba1005495605814020580c07500c5d072252880e4040141641d9510041d400c4240801c511411982d4020341d054403071003101ea07102c0e8000c54200002d2405852952100360f50f060368a015000303503116600c40390083c412402c1034242039102201c12740040c0e0854000c03541da980c45407903c1c03843e2640d0055528001482d6519800c003030b411405140c2000b03512101784c002c0f40e40c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 437958390 1250 437957140 437957153
    0x3080708090a03390b03190c02211201091d100603020f0d080901080a020c1903081003030801050f0f1203120907030201020a0b0406020910120e01020915090a03050109 73
    0x51144601100d821319000611010054403030304100500d4510400503014040300410202031b54100c4d2032202022144120880d1903000c0d43c034030010001c0180d00c8000b03055000c100c9172540c00e81c000e0381c00c94514030f8071050004030564264140961081140c48656052240c20b1045000030000780910640f803c0c64920507201c00908a1032005034455515030615000034500f002d040315074598020720715850603032039400555401e10001c0c1a140100c1d800d210140b0100000c0c04241e54008114844014411061030007401414000e004000c50000f03694091000940155081e815500d040b01c900c1200c0c1060000240e1841e420380105800c800c1031545060134400010142205044c00c0c481b115290350340c00e01e419034640152201a0041c0e100d50203034030100d040c22407440d0300140200c801600e000d072024042078603405100380850001c4e09409440d0364000742ea104178110100c4c41c0340258030b4400301c10b0002e4510052003600c4180d40b4400640078003190764100e1103400071a0703c04003c0c06144290700f0040f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 437959640 1250 437958390 437958413
    0x13051203010f08030301050d0201080921040303090e1014120708030301150f020303040b0a0f09380103020609121603020a06050f0d05100530150103080708090a03 71
    0x120310801d08071202050b01100403042e20f041e108068030445400c1045d0300111424540983390401c0e43c0503561001c0d0385101407141c0035407080c480d118016503842c03443c580104000983d0b4000c2140072803074400d014a49804420329012a0429540c0003600452a80000e5400c2c00c0308840700f0451045900004031242c01202640c121000c070401880034084001080e00e18509561030a0b0043e001000024001020600500e800c05440b0340001411491504244119000c11106503034051003040b0031602c0031503420854103400a1440b0710805200045500c1d07d00d00c1043c0070003449050040b0b50500c258031030301001444440756808403040181e00080d5030841d00494041039000704148100810040c2c007900c1115000001a4040c2c0e01d4030b0301151440c00107001c0581000d14405191000180c583d6400001c00f042c0c0c1650404003014070410241d0055442c814134100a10350004030380004500b02c000002411280c12400703990740e035070302440d00c0d031110b00c5010f00203030b4031822515010061004c801d805 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 437960890 1250 437959640 437959649
    0xe07050d0309140102030c060c0d061706060307060e0a0b0c030c0601033f03050a0f05151e10050705070f0e16020c0307140d050703080705120306181305120301 70
    0x610f0001045001241c4030712500d00e02080c1a8440d0303010580100e10900203005005203404005203203901d0f015910114000004e07040a207a100d6010300516140a01000b001003a40e420103c404c107220602240b40700039240300d04102d60700e01040e440118141401110a0040008181c8a0355a1203140c90340c058003600d00218280403070a48402001c2c0f070410314603c002800c1c03282c012840304080c482100a8138000780800000c58807001804000205402481d00403d10081500319100d000414402403485501c05010074006002481409484029012128419614207607607102140d0605502e04011a0b00244001c41e030954001181c50080c0b29442c010301d00b402944140d06100542203076900b07030040401e68150030240f01007028042c04245640105030291100184400d00d440d003604001c2d05902c144c0741c0103000100708040000c00e100c407080d9414038030881070940c00e02c0d001003462419619500c2c51565118408141c642c1d002c82074406002754040d013100d40c030700361110701a0401d400c213104 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 437962140 1250 437960890 437960909
    0x9120503160c031a0c070b06010c0605040303050a0c0302090a09021b0a03020304170327150d0507022503020d060f1a01030b1507080f0910020102250f060e07050d0309 73
    0x80380b0880e42c0030130224020540307042e0032800c20031036840e01030b0421409007031241030006512034a00040c0980c0207552046002c0e0318002002d01e07196110800f610b80c0036103a5810184100100840799645001d0402620841900143c80c0d1800e0040b540c2e00c0d5024140d1200d4501c9549038880401d03a001004009a80e01803485c0a0919000c02607981d480c015003c10644804c0c044102c4144003500140703060040d42c00800705d4100110f520440300c0c0740c4c0d00034562400389030b4480042020040e010408400822131071082030303200709200a807205444916000003445024002c4080d0b061014a82084d41d4041d104c0c070040010783d0002014100341b54100c07900a0102c1e042c2440010b180c6054010100c600040c14030182c50710005a58181c10b641c4074001540c8500310511441600d0f880d03482103455200e240d41c000503503070300043c80700c42110f04200400da01c041015005800015032840040e0503c00c1e41302c0300104c0d003800007040b558280040b03a002542c0043c122883c4a0030305611807250402c88400340d2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 437963390 1250 437962140 437962163
    0x3061211040612020f12011b1d0306040812040609080408010c030e0d0207030807021819061e23130b040b040209060f03040311030d0c08070f09120503160c03 69
    0x403400c3c500b04526007400307907201c52046403d0803d0b007000320100e0190401c9000000301c180d80381c4040495510407104540001c2d80406000c0011481d21400302c400d48000c0300145041e03d020390311850303036204400203214010141070208080083d1030700f000f0352070303035100940c1390700c3e5601c41c5a50740c000c1c0604400100041d0820440007001d12011502c144200308036409018010300b90b07210000c65a2203030b1000c0340c010080a00309580d41106404140c015000501c00c0d07840c2da014241d508060781c0603500042d031580300840c0d00071518526180b090b000c13100d070f814440d0907400042105000c0350a011180a030040183c424040108003160b10201f04900300f203600300700001c0300c841840100d00440b03245e5900024200043d1102e8410000590303403081c0b00e403819070104a08940d02c141190041954040d41035224075103104001d03007100802c1e51051491030468040f48044074010010400d07442000c45c5100700340c0c420b00a00c0001e0044030740740e10440d80d00c401124001c2c03901c28020740003803000b41c51460202 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 437964640 1250 437963390 437963399
    0x1d190c0914071d03030307140d05010b030108060a020c060f0a0e07060806030f15130f060c0c11010e09011802040e011701110f030f07033b0c0916030612110406 70
    0x3000c00b403e40000140003582135540721b1a0076504032914002143d070041c42400400c0021415006140c0a0b0441070211074032545000c07030540c500f9001404014019005210007440004000b82c560350154100792020010340381c5400190043c400d4400180c02402418008140c1a4000041a004032015411500040c00c07404220f6264403450007040903a19800d000304900154100c9041403483c00380c91601301b2038004e0785e269000c07510425590008140700c41d56290070b00068841440c000c580c2824103480512002d80000c082c010140189124110110840c540480d81c55051f02c014202d030800320b04a550711000c28490248014251880a60820403c1000b10440070b05a40c46160340050260542d1541020020103100003807255040540c0d5010500005150400c4030407240c1e01d070f81c440307510075170031400600c42049803c011078a01c0c0c0c082050340046031128100d040c1d104400356100610034904020480180145502ca84888103c0c2c031035900c28490881d800680c100b00c00c0b1b80401001e681c9 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 437965890 1250 437964640 437964677
    0x307090606050f0304080f03090604020406050405060f040e010f230114010c12050d1802090903030105010f200708070801060503060606070609020a051908011d190c091407 75
    0x18007800002903028031a181080c2c241d100a10380051103401c14506204040103012201e400440c0d0080941c2c0c810030a00096060500c00c0c0405070106039000c5c40a450034501140c2012240212240216680c08030030051503402e5200c94801c80b0a2101030014041c101c4240b91002e039016810900890980c0000500102c22101c0c0c00e40e045c0c042e1a41c2012040039110106056030894a28080c00700400801001500500c2100341c1200500103185403c600750040c81348204000344130081560042006008513038116604180c1c480d101e03d0840540002d1908041841004006c59000b82c850104c01103039094001c40c011054420b480f0082080756a01c204040d52000c047c0c413402e4120500b00407840104035503800c01502c0d6800680780c030105c250b44402048000d035007001114000e501922040c4000c140a01610811101e200e80612074500342c4c5100d15110034a514074206440d041c0c241d007004100319403985100506003e0000c009048200031100c41e1240c049607010005011490a071599241 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 437967140 1250 437965890 437965901
    0x61302090f01080c060f0d061710060303050f0c070302030a1103060a1a060d02121017010b15070c080f0303040b0106050304030f031107141b060415120e1605030709 72
    0x50402044d4030000e05052260603031040c1c25903000140c04001c0421410007a000b914002c0191040955040b480c580d4420304021520000800050410008001181d84082034070300303071280700a00580e0b56070050381151a08403940c0c4000c0d00b5008200380003040c0510302e1115a005a810fa043da01d072039481c411500c0440340e050018600360040d258081c0e055042c1300000c0c260708902c1c81c0005203841110183d00d03090403011071b5403000803400c540703040c8100c0c0c1d010780746101f54401c0c410092041054400c0010b464812251500c0c02108000c2906024442c45112038001840c2a009a0316203050204049407280d10842e004e917044084140000382c80c500c110120307441150190303180311944502600880140842000c020101403040c0039000100300ca010513007001d09140300052403440a0b0044401a248483d00454401c0900b40000c00404080040190b40442c00b440c0003405821020784d030b0760052440000782c18a40c403404d641c05540314003200d0070b4030070780b013044040301c54083e59140d0b14016140d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 437968390 1250 437967140 437967149
    0x6110a1107080d03050606040e0f19020909010b09060f030c040f0605121503070f12050f1603140a0f08120c03091914030307080a052d0a060503061302090f01 69
    0xf845036500c49a914441c1e44466082030f0010400361815031f42d100010b54110050324aa2000d40405051102c0d00441903010704140c100c1e10010340c1080140c40014111100501c5800b413a041c0004000c209650b40904441c498914101c1c1282c0300d0030300181da83c000360400e00075150304811100c00820000e000303005440c90001c420810105a82c0c44403142900e10300c0340c1e40f01540500c25400d003c68004134030071221001d043c0c400203e510044950030301500d002600b03071520403603400500f0003001c0c010000340603105903508454528081d0542d03c04080c5007450103000904581803403035000c0204002c0c480142b1900c4500791345000030340c440b010b492216102c02c2d01c2244c1c41d5840542520102010f4440302c2c139029000f103480e8080803010510340703801d5030300407100d0000040842041259822191040b150000714003100d965181c0c0c0b0903213245140c2000c0a800c0c0001005000c002400014a600003a025140103816540c12b0708008515018210046000728492251903001034802c113114400f2034120f9 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 437969640 1250 437968390 437968393
    0x307020114060a0b07050a05010f0b0f3f030d0b0f040c080109090201050c03031006080903031303050f271c050703060c050c010c081806191806110a110708 68
    0x38544001d50000303912544040760180112034028001c1113003072180f6100070a12407400b06412f00c005003048400300c8c40314a1729114040b910380034a9001003c072400b8044407550089110545214030651560818620103040310703204c00180040d40e200c0c0c54008072501001515822500c4004000300010b8800c400502c40c0000c140c9001005007201c15001042d8080c01030500d41c8c40c094503001c1355400c6501c100e842d2041d41415a070100012540540c00e50b520181e110055419820b0482c0791240c0080c4440c00501049400303d50814903c03c1441191603000c00300c1e11780b440100c4219801d41009003050074240c460358040080404000044070900c2e92a64800044c00c8210f00716038800004001c1d0f40000000c21a0034015207161090034400c00c295501d5585544102e460144d4410320b003285401d200c40c0f0030703401c05002e0244c01542d810090404000359000400c9440c1c1c64448011141000c01001d0481400c1c2000d0302c0c1944602002001c00d5101903441680e1400a1444242d88428601c1090a01e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 437970890 1250 437969640 437969659
    0x90c020d020c1003060824070801030515070e0306090f1e0718060302060408060901051303020607031a130f0b0415060e04200a0f082e0317030702011406 67
    0x1280f402107403810200c849400d00249186d111190302d0b1802d001c0107081102d401c282e501c210b90b5900e8000e40107038045002c0c50066640c0d819a900c49490b00d00f00800c4c1c07000032140001041d40c2900559040710080005000c8074211f16268664550b03030a0740c0d500c0b22943e03005807440142c0032446680f140d120031084000500d5410701e045103401c0a030107041c500d0640d2a0b41c80001200584e0703a04010402031000400420403801c108a216003110806801c00709516842c00d004400641c022520b81e07401406810001400c684580c0c0343c46a00752140041c031781c081c2000344198168074055004409015010300c041003200f2085090100f21020302001e8040000d00c2e0f04204501d920828904580010192022643c61101032010300c00c40511a582003400320086a0b001d0102e6020514048041b5076250090840c03d22032a4009140e260f1a403480402403e080240140d010900c1804000c41d4071000f5110886020403c1040980040c1c1c0c6042c01542084034000a410180c004c1600400380109210708 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 437972140 1250 437970890 437970913
    0x110106060507032003040305150c070f061e0509031b060f0f2805041101030b06030106030c0c0812071107180f14070503060f0a0e04020603040312090507090c020d02 72
    0x400c211505113480508200000405a060060015100452181c0000d11990b0f0300105d01c01d440c030702c0080000c415030078280000d102107a0300c0e100340490503401c96130025070011a4070503c5440d411032080100c0709810072040c0102d06100200400c1d5020350494004094103202003110380700c810a07101e40e200490064003140326005044496608101d40d0038003a40001028105c04040c00d04007110550065654020003060000c03048180c168094240b82c02c01218a000000502c14001030161200b0160741e0a814400e180c090127002454a82001c4d905443c0d400b074482844000d241240c07424005014550306036034000c00051410241c440b24450449d003000b00510078030007840340100c409080b80d00d45248440e448424543c0300d000302e90503544d259491508006128010890545040c00b40d0f407114010800d00081c039845581003541183d40f0366403a03d07181800c54200c014400c4d08a0524174040e140b0b4200100050810f00b168800e41040c0070007000000182c1e2030b00141d19102c1c01682050300b1440 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 437973390 1250 437972140 437972147
    0x601031109280f0b030303040f08090d170d0b18072d020106090b0d0203030f0901090305070b0309060a060501021506061b031305120d0305090109021003050711010606050703 76
    0x10380c000c000c03040c1404500d80c1c60101d80e408481e00300195018943d6085102410141d03405013403403030a030550003146541081c0e0f468903082801c804000d4a0b144c00030481142640e10903500d00b5501743c100040840503a420407400d15198400502c008a0b00e19151203450541001c184003a282e0030550341d904115a503210007504c0741d4900380680c00b00e5840b13010740e0a4440d032584c020b008440d6210b03800010710740d0800c00100d086490001413144600c855003000f00050703400004072803000180400440e00c5444980040e00c00f407800c0c2e0030003090740c0103481c40030903031040319809107101d6036822041311140d484207665402103403c54020140103800001001851214003040c0da1341020010b00308a29140c1340c4001071300d04002c6842420170079040000c0c2c00d80000ca4440c90580507141c00c23240c1051366800810490b0b80d81000b0038841007415250800540428000e5005880c00e0703030060324440030052064802001003608036200d00c0401c7d0900355181c001081480740030241d03a2161211854480a5107058 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 437974640 1250 437973390 437973409
    0x20105040311040b0402030f0f1b07080d09020406030f0501060b04120807110913050f2e0f1802091014010c0c090e150708130f0f0516080c010206010311 67
    0xf03800039103039a210059500c60707200440c440c0303441c8034905526040c139030000880c0002c058000c2c00c01076400c00c2550300d00c00b210011603044aa1100c41243e6440d2454825400b505e0608400b82d4805c1c6440c400006100300e03040302ca03250b14417680c000c00070651501c02d0040769001354080c04160050205501001402c1c00c0001c004450242c0502d0b2404132035240090062002100c0c8001c6d0750140341074010030400304001000c88584c540b0060700d60106150308040b9001800035030450764090784005040548650b60005a5013502c15070244084a8903002e00054110380010490150003400c0000d00c0c0945001c42c6582603a0b40d40b2000e100c500c1d02c0c0c000440d610081c20700140c601c58040d01000600c03909a00c1a0b80186c0340e00c0020340300d44100081045540c0000500300004c0c4620f050401411001140f11807150b540d20004684c00c00e2100d0a03c0c907c80c03401020006d200d0710841c0f80040f41c921403d6003d4049074048012516030002c0c14004903201c220a2100400140c0f0300700e0a4010382c589111003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 437975890 1250 437974640 437974673
    0x14070c030f1409120106080c0609060711061e040e070c030c02040c1713060b09151504180504050f07030201080c031e01090c08100e0610030213081501050406030201050403 75
    0x141820041810f0000384a40b13560f0001d80c49907952008204030056003849081c210385003c0307440d91b0a10403e000030507103038410070200604008d1550384102591303a405003512135079641001400115007903058046030302c0d40076000d28283e801400d0000380203940b03c0c032003455001d40c0c0b5580d41c4100b44007d50038040034240302c1f00c0c850140010300c0980c1400c502d415054600c54260140354602160040c1441801c41d9055100c803802242d002e410002041402a46003022003016629880108a600030b0b0f0280c5004507004020804c9000f000c5081c01c0328140c00940c007540c0118161080704051425603592090b89200082c0401c4042c00041c0210240202450380a0081100591b68171030410b2204507040d0300341c2005034041c1e0b45a48280205a000250b1030b800050f004041580600b407000710b00c00003000500c80d61040700400c236040820740c4681c065608503100c00d010040550b4450442e42e0b00c070361100c204403801c88000b100005151030240545c0d411203030107031542850305041d1b4450702c0541190071031 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 437977140 1250 437975890 437975927
    0xc050f0d03030c140a17150a0612180b0f010e100b0d1d03071403120a02181c170f160303020c06010303050705060f04020f1207120614070c030f 63
    0x513080c6403000740c1c0d0000c0c80c8880040d03580304c250410400d90800600380c0540700c000b402030300c0311003040b40b502c4917081d02c025500c0c0313403d0160b810340a140d0352501502524010520750110ba011520400001c500c000d40508405102c90f00755a8a912000103030010448490041c0d0307032408070400c0401c0701c04c8020480c0010b00940495464540d00380301394102010011001203034800200c940c240321174034005804c907007200c0001d549440444102c10315144c202500303075942d5690010310004c1100c80e118002d11481405044c0c110181c80481e0342c0601002d115409442510038032520f540c070302071050125490b410081c44110b04200d0030800c014607400e04c0d00d000710281070f804c02c111001c00d03c04201041c0258480d6440b00d540d071055103091410f082000c3e03c0c02070500c001c0028040103039981804504074240966640d1a200c0a030b0f0482890042603502400d12056040801001d00c0184d4008240d076500c4801181c0468540d031004680d6407211180140c0002c25003200c0e041001c2c8602e4510030103800d5000b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 437978390 1250 437977140 437977157
    0x61503030403020d0b0f011409040b15040536121b10050610030c081923100f0b0405060706020903010e0f070801060e0a050703020c0a0c030c050f0d03030c 68
    0x50108131142182d90041d500144040d0810044603400c0c041b1034050075910070413500c90304101020504804007d04024041800900040c2072040c690340130b075007160340c020010300060506226000c1c550400c072201000c0044840c0000191041210084058988283c014846102070403100a120f40004150b80d00006440e1203500a001d410004407612a0030000c0020303a50400d80b040247d01c0004402803420f041c2400d486d02d100c550442c11881d44040c0d8404c07080100b9000c00000320081101c1f81810487c1c000b6508108241e2403280c1c005d6101d603a02050001007151a001174200300c4c00903104410200348100800d00c07007030410034082c10030f45100b18005803c2c1603441d00040c8c03d40359044c3d400c000c50303481103407006094102002588020051b190080002d1030400d02d018441e41401844a40c00a8136100404c81b0544280e04489540c14070340c00b51003001100d86041008a022440700b541c01800c400d001050914000a0204103030318010400b030741c1107210369015009030402c1c0c01070500740071406 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 437979640 1250 437978390 437978393
    0x302010813080d0b12160e07110d0c06020f0c07090b150a0309060207060e0f0105010609080c1c020907081e0c070312140106020307051b151e04030c03120c05061503030403 75
    0x420071b2480340c8003c01c510a00c1c9030300306000000000c4c80100900104105961540d102140202c0d505840745558a482400d0342c0c1e07036041c018080d2249441c00c9541c60070000c0c42e0140408042203000c01e0324034001c42404880044010070210411844448059110421880040e24081e5000c000c915101c0c041c09400e068072616103004480541041c00da50742c00281c00642c03110001e12400d4007429607801c4c0030300c4150500360a00d40e5503d8650155001d180c241141610705900e04109014055008204580e9440c0c0004024140c0c18180c500400010b1203802d0911504202d004480c42880760008240c1410303c0c4d600c3c1101d60340c01d5080c0d201801c88d91902041c17407801513107290b14081c000720b0300111b5451200340f40542ca00010701404d112001c200402d48001580d5400c0032406489032190140c9d07c465429043c4281c040c0090940749000000040000410011101c458202d0b030251103030354500d80d0200703000d8860f000a1400104250440c100044034000038044002c02003034050110307400c00f92039 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 437980890 1250 437979640 437979643
    0x306160e030304142706060a03024005010530040b16030912080c0409050420060922060b1b060615071113020a090302010813080d0b12 59
    0x1c0c2c004483c081c6012a1210090034011241e0703020701c5c0900250000c004003003810b40d0010710080c1c1824485c0ea0001074590b074052090b01903550700e100082d15410300442e2000201300303070081110080300741644252041e00c04110401d101044542c180c440c28548095542410340d12221442d8a100b0701404545040f180b0781901c100030703c2036104e408168510f081452400b001d5661a0640307a0415003000301003000983e00c6028942d50a0071400c001800d0307103e0800184480c0200d03044100c00b10f18100400081c459803541100c21028200741c44030031030320820305200c0c480c40748886054004104a03801c01903550300c210700340c1104501010004000d40c5458090f20154020080d440030b203140071841a203801e006100d50364005008644040410010440d20b00040c050004042c2c050160f005800800d52a00014040034100e50350046640310344800002d000501a4042a03002480a500084102c10000694600c568100d908581003002c4094807038003804a10324400c3e08245240354034440b4110 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 437982140 1250 437980890 437980897
    0xc060705030d0f020c1b0112150b160f0f0c170604030c03090801020f03010503070608091b03010b2107080304050114071e0c090e010b010512040c1e080609030403020306160e0303 78
    0xe81207600d0000d46c80c2000408031480301040f60000d43c0341c2114030004035441e10418007100c20000c80c05482d915142050060043e0311040908a42030883d004003c10002c07203003250074580300d1030783e0242c0340d91620318480c41004104940d0a540d8040f0b004100070034090042f0b62800c074402c1c0350420b0707250b45400401e407da03048500509501100480148440d140600c42880988001e203014159484d051010581e1688040b424094803880445510550f0f1401e42040e04012405408207425a0b2910845101020f40c4500000180519a0042840c4c1d802008903401c50b2030507581c18000c5510060f1002280d0f0104c0030844100d144415000305500389800a501e496000d010040713000c6141c0502d8405442c2c5544203104940d14010301003a55a812905950341c1110403000042c0b6661940791040000c000794203c015a4802841001081454850b2440650300c001e400d66480343c072612400c560341d0081e0701009500d900708800080c280b01104950044440e881c3c81c1c10b024213950300340030038110750 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 437983390 1250 437982140 437982163
    0xf0c0c1a0c0708030705070e0405030405100c03020c030a020306071d130606020601081218010c02040908090f090408040918061a010e010e0d0b0604020f031003050c060705030d0f020c 80
    0x40c020038803012464090000500078107500014519216045e901c4d030361105090302850280f406000d0100302440800c00540d0007a20015007030005001c90100f01403e0141f107000100c0040c402c41d40580c0f22420046803007501c6503405401040701d40c4404c0015070f502c181003003003c0b0500140810f0b414182c3d8071400000301c0c29540c1c10740020a90b00f0030700e009040c00c10582180005900500224681d03608205c112521038040381c0400011280410049403070b1000708001941c000e0900b02084d0138441403000401c2d9000d402c4440032200e4203018180002414110b50142202d01d051108010340d480d40e4100b1041d00c1c0c00001285400c01c215921001124122074006041a0702e072880ca848a58001100e031000f000c0908207100c0a6842800241c984100080c0040501000380c020551684841e011381e600440098601078803840c181510080c661a1031005442503c240701900d2401c0c10590129201540c0040140d071a101044d115103028210000212400075400c1059892080c000e02c0055141c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 437984640 1250 437983390 437983439
    0x18030b0108011506050304030f0323150d0503090f0a050901080102120109020723030412061e0e0d0e030715050901020c03071211040b0909060103030f02030a0f0c0c 72
    0x1541011601c5084a154020008248031240c8060020a03000400e07030ba800399040ca41030365140a0401f08602501d044410031900d040f1590006d14280030f0304046510502c006003048040d00f034400b0410111002000025055802c00c10003154203003045004041c042c4030181a900800e0340c2d480105210076070913840a80c00307035404288054450211102031b40100249181541014029100c20245046000b6008a0759220300c01405d1004c2040c4281d8005210186110f80c03840d40760308100020b04480c03010b000403500b0211026991103094443e03207019840181c0101500c0c480d806055942d01441d01040d03616110720200080c0300c0521403429013100559544080d10b4084220029182074a04018107200e41c03c03000782441405c1c0345003503e0340102d0f00a014104d01c503900030042001050380400094224104200f080030703440c800204581200d100742d8441005460b004800c90b141e0003a07610080c0041e80e4600c003a00c10a1150400c502100c0c01100340185455580c0380340e5540180c903805800b440f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 437985890 1250 437984640 437984663
    0x20f0d0b040819090312260108030405090f0c04050d03050c0a06060905100302130209040e120306090a0b031b130c0e0307090e030919080303070201020306131401060f1803 75
    0x303a2483e650312000000d414254210360850744c0745a090780c081e94501003088040c3e000d1019082c00c00100481110070f9130020b00342da50310380b103580f0b850f68828014203015600c0000810b40800b0204e0032188141e40c03820005040509000c200409004c1e0b0031000d80c2000814424510003030418000707049524884c1c0400580c0701d00d4085094240c0d240209949054100d0f104200090703100d1403200007100c11703801e000507174403000140080e00501140103240d50728499000180e8298060000031405150304640c4c4142c2d5a03202004241910a4000d2494154106040c1c2d42041202480c2da0048034000510040c440740124000804039505c15071550005142c2400e8801c04d0f003420b00c044800b60041b8102403100050403802c4c4d40c0d882c070402940c58040e41c0b05c0d0b500c0d20301c42c4036907191020107002d507101680c0c0d40781814280240030b900b060f1505271241d07901280402c110b034110300c15500d4110300b11020821582c6440015640c00f140100130600f407007169001c1890040d452081d04000d1403182d001c03880d5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 437987140 1250 437985890 437985907
    0x3020a08120a0b010305090a1203150b030f010e0408120604020409090b040c170c12030c0d09060e040605010e0d14010c091a0a090b0307020a0c060e0111061003020f0d0b0408 76
    0x2a80c00890f001414545820b090020448000c600030280c03030740084822010126040e4100c004000304401100b804004050100c1e081051500550081c44810b9840c50035903210b2a018900080558000317015102c00c209041c264489440c0760f6501100041005040c01e42e100076440689400090880d4040700e40d03400c0204200b5150007200c05000e07003103428107202c0641081140c0e00c2e0300c400407070381c0718040c00001e038540400200102d0340c10080900555898400580010b0f00310250381c06140c0c0441e541b42640034141c00c1a1150b2001c07120705a41d40745c0c0c400310150503ca9801c0104805942c140125103425808400c2400303101241030300c0355038201c074141c030300344500b01c40c0311042c0c00203040755008100609000d5400805c0b00140d90450304d00070707a40c0d21501c0040c2e2420071442c2c401010b00c82c0c1840e0019440d908103c241c40888020389500180d0b280e65003000b80c481000310b0b207007090101c680f4014030140c00c05441c00c158013600542800702064035501d0f50350070f03035008446c01c86044100141030103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 437988390 1250 437987140 437987161
    0x1a09010c031a060d0e0c0d15110702060a080a060506040803070c0905131e0c06031d011518110c0102031801090b040201050d0b09010f05030d02030301050a1203020a0812 74
    0x8000c0c9040d82441841510101c000510300e04c2124844602c0645810414500640c00c1c054031002c41c50003012846000c0e0070340b405030500580307540010b81403442e000c00000c16074485022074081943c02030000d0700d0654605010f41350241d024003007113801ca40d6444003040031b0300c41e03100a0014000b880700464550703c071807030000c00300c161a8114440c0103041505002500c00354851600c5080d07800a4540c3c12508049204913400c1031030302000d0407081500c100050501c0c0c040e0310034100100000c21010244806a443c90f09130740c845104c4041c0c205008108206410310380c80155402d0102e4180850341012440d50300c42da80d080601040c807582d6000040c480c07820200068070b21803443c44002840000701580716090031080003000681440400914212100a81e40c0090407030b00000b0b0402d00696110f20104030085da0314041e0314020321591030142003c1e0300000989040b2a8010145120b407400c0080c0301400301481101141580320390140c580008003600050300801d00c4204110301c3c3c1e807400c001040c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 437989640 1250 437988390 437988401
    0x2104090e07030503090d080f0d0f05071803032109081206031603110a030b0f09060c121b04081b0a0617041b0b0c06060a0617131a09010c03 61
    0x344410381c451142040021008002c1d01c41c0401c003250106580305983c10400742600c514a03d0004004000500c00401c10007030340b0138030031201214020041e2b0390f54603500f9100100c020143c94007010b18164108002486a0100040140c1c440c010101c03024040d0b00c460161100c2d68030459501c0380124064101c0d49603400726640c0500218000d004900310350030140d40b102e41ca0701003d0815100103500025948030300507584d00450b442200c440043c500748100713800300601078580205074002c0502180c030341800d02043c0c490506032400307450600c0c0c075500e1103484100100450105070080900000411071402c1c40401144546040e024084101031420001c01c00c8050f00082e040c080c220f9230500009125501840d40243c0c850b02d0750301041309040400c0748044030b981c00382d600003000051100a000380401e031240101d6050320b00400e040c0d1620000e5609580900c50269038085a400003800d2000d40e103560700d1940e0003001264080005242c60b250210401c5610a8103a9102d4516071001607151055 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 437990890 1250 437989640 437989661
    0x3010b0108010e0c030a060b04030302060906010b0c070509130507030f050606030726120f12090a12050304030c050d0806031b0a060e030111070b16140906030405210409 74
    0x103032110360420b900e48200900244c80074018484c04800280d210486038404000307819600d2900740c0b0380d036407460300960390070080f11218114045c1c1c100015060080c00b00b038500031071883c000361075001d0510080c0003006038010515002c4400716010100031032010b00c1803001070b501901d07842481d009242072062600e480500f42600036031085e0030030001e0f40d16408042110021007200d03a01e00001ca840c030540f42c0b249103404921845000107002d128000c03904000e200c0180448800360450345e030b089a15232201140c6201400c2e480700000200103c0380b00f10011036109100c1e00b49003001d4442d80e1141450844001c00c51404101140d05000d024942044410042002030045484100c4401c01040342c40f1011304c0744c54180401c1d45080c143c2c2d65400e41012110a44402c020360306c400c0da5090071111008c003522100f04c0020404220a0014800c0c2003000d1100800c0c01114a000044010b000b0103900c000d0040c0d4141c010984014400c0b0f20780c400582c1035038001203015450702c2c01d04c0390a40c00c64501c42032 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 437992140 1250 437990890 437990897
    0x306110c15070e040c180605030105030c0d1203090f080403200f01020a0b06180c09040c09060503060d08070b13120e090f0702280b0a052202010509040903090503010b01 74
    0x80003030341d0354006541c0c150088140d401103580845ca00040e2400c5282d0380c2c01041d40204000c3c041001ca90101c051741c1201c104404441d145820502405215226544060000f83d0340500004041e80241c00006d9030b14800c07032040702c02040030385410580380c0194004407071182c2d5017411020b50401c207420825407480103c400020101c04880041e560b04200940107043e02019000074400359500c2441030a500c0030b11a03296854608100880500e50050004510991070b00d220646d03041d100d2180c650a44030681c6440e031441d01c643c003c011081d0200003085610a204101560002d00c031898218003510540064601060151802d07034520b801c0322450004020300e41c0c10210550f039415511035080140041c03c802c4176268404224140b041c0c0001080039549511030047c18286000d82d400c0072203001d000070020f103480d0204c00d4429030b84c090700e800300103500c00004868584402ea000c82583c501c1414010326200c04140030806a811301c200607804611081010000707400c0070b01032101042824038 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 437993390 1250 437992140 437992183
    0x206090d0314040b04080d06140312030108280c06020607120c0c17040e1f091a040c0c05070915090603030206040f170f1b1216020a0306110c 62
    0x424904115801032010708651004c1000c60140500501101e000080d91107050001607202c8221000c0c20000550041c000c1c41103e9290507280c07042800e89041c0e0703040300050184031248400c11035451003181500030021043d20901c800103401c182407800140340702e4020340b00c94501802c001d005681d001d034021031050f040540303040e54036901403807000380b003548152517004411508008000d140910341201105a05980911070482c01d0030046a03085e0382420b80e1003070300c2621070010f4000e542e10a400e281c1025031054868601d442c05403c00b840605540c030b000340046403581c40352880c000d02540202c0d0006d0713403490b110100c01c2a60406502500c442c4006010240c61070b50020b56552000b0406814103000b040340400b007112001104034034694241400da12140ca60b890070300031740d000b0038045140c0c101c24250744400b1040400c104505e508040c0d000c50500400490145d220308000307008030382c03010440001100041145c410003001c016800b001c02d0b20390300380c101e003a8036002000500d000303031943c0d81 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 437994640 1250 437993390 437993411
    0xa0c030519032f1c02090306100312020118080a030219090815090309091b040303050918060307230405040c05040b0a030b161202030925051311040b0a0206090d03 71
    0x10204c2d8002107802c1d1080340903524001400000f4040e1404444c1d05008440034407080c0c803143c1582d0403d03a40074504240b4042851107081e03080340c2925640400641c641c0c11400701041c42c078005000b01c01c0b0319040152600800001d0000c01240d600c050102103504050140445807081103c0480039070081c100d0300703603801c1004005903640601c00d0314a20810411001130b43c40900000300115244000b100d950f2181d0310b0f4540609540c000c1100c1c20300075101c20035051043d0640000090103200301030040c08003e4100417410954003501c81d00800020700b82c4003401180d0301c036031007100d2003070740a200101980c60a200070041a90b400c0301c2c5444c8180d1807083c00b0310104005900031900903c200d500e44215190103141540d030500b4202c0e030301400604c0802001b00900340840e111208601600c100c20310103050150380918600c890142582040c05120b04032170b0f58802d548120103e00344484201e0404d0380d00c0034038082c503910102d60344006800180900096400c03c0107103040302006c41c1005d00084030305 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 437995890 1250 437994640 437994731
    0x7030305180a0c050f04090f080901080f01030305120c090a06051c05010b0301062d050315060f070b100b130e10030f120c06050108071d0702030a0c03051903 69
    0x714000c2600c85c000e2603600500654aa41c03003c04000e0703005045080e074484504050003990046080e15010031078035400540c1141c5003680300c40c162513044d11102c2c01e0040910b102c1a00c03507001400705054820800c120960b95035411028030003003465a07179550399680009000c08031044940c131240541c50811005014045100c1c044d00c4c15201075241007091400f2900d0005071300b46848040ca03040c1c0c000b00414041080e408401540700d10b092807000007507440346605015140c80703403450481c1d8008083c0034160004494800c0365420810b11001e40c44660344529802000c1d03440028501c44c140d0741400c0801c030801d20443c1d1194054581c034400700d540361031a200ca108100e10302c81c0046c0f00744400300619804a010f010450817050700f06a0401c81c0d503868074000c81d502c01880c0a400396480743d0540d0f680844108610042c420b0301c05502450030001002c2c8182c4190309100e00032400c2c4007083c060110b541001c114020f40b083e032155400b00710300102150b0b05003800308483c03c0c0c1158900c0d00d044089803445 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 437997140 1250 437995890 437995913
    0x1b030f0902011b03121103010617040c090b06040f060224060d020d0816030f0311041202060c070306020f032401200f0a08070501050709030c03120c02040207030305180a 74
    0x300c6480680c4000f0040c5011202a403a00003001c00141c90300d400c00206160110166050320155120703144140000202012500011540200603040e12401031140521642001201400c060203250a15485000191540031983c10410059002d9103030b500010400203010720281c01c00800e159007908040b400304ea004010000c1c040c8c000c0318200e0306d61040019200880d00c0304144c0032030b04114002e00b890f00900a90714020300200003420700011101a10f04801203e04503010400c801146c0c403000c1d42844202d4002140d07128960041c610000701144841c001000f54414003a00103a4070300c1d21349010b00c95000f4405005800813404070b910b41d601c2c0d80103c4001c13440e480d40c2e00b079034904129903940140303019403c01d0381c0c11950140350841020000034202405180e8400c20080c0410b6441d43c7d011100c0268a00c00500b100c0314003107082000c070740000b003030010440302480c3c820f000e4180e58022505a90014400720002991542000b00d04505145890300d0400c048003d0072001c0c0907600c50054118 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 437998390 1250 437997140 437997167
    0x130c03150303020c0d0f1406010611030c03091306030b1302040c03020307020a140124140d0c030f0501090c0320010e060d0b0f1801170d09060e010e03011b030f090201 73
    0x216480d4294080c4000384004000840c0d205c0c80d1f50207540325203480075450710b0003071280e2008205110101c3d202c0307003404010f940603048000025800c00401408005407001c4100d02d03400e007160303079840110110301c1c11070503c2c0c41816081341c00300844615105200c110f950400014081500c140107010704258041800b02603e82c008111004c030003020160a801070480b10030080005501d404500d44290100b0b840008558190505101a50382c150500085010244005043c507203551030910005e0035405503044454014400024144500d5071034080790a06904213450349080d528070b80080069145840d80000f00030310348000c0d15106100461070720f000e15007005664039202c02203420300d44c0b10340510840081d00244011a1038650760a100000c0c0030070b003d02c0540e100c08850032092031000141120120005a5460b409540350060495201180e084414108900c54040303040a9a003402245110360b034002c80b00d10320707441c85d41c00902110146002c0d40309017404c060b2031201507a00400b103000e104 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 437999640 1250 437998390 437998399
    0x906090414030a031d010902060f03040c0e181009170d1e050103020102160602120f1e0d0605040905120714070807030b010501020307050714030c130c03150303020c 72
    0x180c4591400400080022489034100d11021075408005a8942c0103814450b480c40307403069070809400351482c00e031507001001039080307201001900c4069000303c004642c41400307041072948564542d800d01c48070510944054030030105078810100090414050446050700d40041000040031555464400460a540c507003213403d004030700c22004044580202ca00d1541e0a949134280c6501700f888140100760a0205900500c43c6903080308945500d042614256031031038000b4000c412202004012650046820080b0510180b0494420074849903100d00320000032a5501c2d113851400741c0d50b9048944175800700c1d07c0741c0d0a240c40c85010030300224003001490100c00c40c45513211603500340080d4004010b00340540078030600c8070010303002d00041110407c4d00d2003500ba0312000d90f070f00c1d030049941c0c0c042c84d000604a60008142041030000f4441010500140a4151400307400c80c0c00004102e005a00d95480183da2241080b08020354507200f084204140003c88048003429034500035030f544076040d4414003a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 438000890 1250 437999640 437999659
    0x30a1407091401020f060c0309060f070c080313080a020109050f010c05070b060d021c0b13081611041a030601050406150e18010b09011218031209051e07050607020906 73
    0x944d100303000c50070003050300300100c0741e80b410240f0790001c040d402100c02134a00d0062901241458441448090092980f40c0d20f01c00447d203540c4034054940d00181c02405030555203600d440c0040c9101020b0a00780120350000220201103090950034051000c1d1600c403140d251029014129401c18290340c541c0350030001003421a5074403c00f00d040b842d101d503030207540310001005060aa100006541000705e10481041d00d01d40c40f004041034038810b00c401c001340410801d0141151107901034205803440e5001d40501c0c240000824041004c99130540d40d0901c4017400c1103100f00c0e007400d04029860040c5000e036400c1041c00e2802c45800a008012880982044012118207480d581e034848008144201c2e03c601070b601d5691010328070b100358070001440e4013084030900d9401120b080f600c2217801d0010700c00440c00c007201207a982141c0a440380402c4c1c2200603901c110020100310308005e1546584009242040200c0020040c02c1c540b6045070300c03070f170f1084000b0411000103840b6245a11b400c44416038001c01c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 438002140 1250 438000890 438000929
    0x30c090602330108031b07060905040b01121508120c0d050f0c0316020306060a30080a020601051f020c040207050c0301050709091a060a0e24030a140709 67
    0x140100c90070003415484254600200b4130440100c000e00034090000703807035440b94075401034282e00c0319210300c0b5013004664803071010003240c20309401c030f01200c04051600c1d0000c01d8034080d0120449030340079503203599202520b8050000c1c0c42d02b00100c41026064075001403e1824080d056561060440d00e0786040103404144404001c4081e8240ca0888006105490b1901d150913500c0d8210b0342007100c2603109210b80404504a81000c40c0e000e02550720004062801800c000003502d0341d034003003071400806000c4ca0800c003804249031901400300058158003070310440d403400c4104210b1140d0a110b40c407445824240742150309400240d01c0404070070a841c0562105082d08006007080034a161464065090604210303002e40e20001a030140d8854840c01c003e21207910b803c03102d215040b070030240d070056010804c20710554010840c42d0305a0038014011080300910380400300b01030345064a681d501060100030300450210360f01076255501410780c42caa04a162105c0c0040640740326100350184a84600308090 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 438003390 1250 438002140 438002203
    0xe01090516170c060a2f032502030703020103020c0c060d020a09081902010807120212070201050106030e0705090a02090d03030603171908190204330203180604090e0607030c090602 79
    0x8002c40e046e606c400c034000101912a125440300c0f0380c42041e0980c00e04031510780e1094400d84000703144c02900810398070b070469006600941c00000b510322a8403038815801c0156036a0b400802040410000c0035032150007002d809026002d0a81101d0760702c0c0c01424040c10b0840550b2403188040c1d40900e8205950b032210341054441e482c0d860307a0400303414000914018040e0000040394010000c550081106a90b01c540c12403c80b80a20314500031078000c0c2000700800e2900421b9a40c000702c840b98010f280042d007900058000500850031008203454840070014000c01c000d484aa003410403200901d4114171204c00b403681074841d4a44820b011411003c40e01d05000d03019a0790110401e03900031542c4a442c3d040600c0d107404481e80b09038426030200c400c00802592604080c8603000e250f0011401e0100d00d070700740701000717040c0c00400e40c001c9000d2000041411041c0202003d180e140d4001d0680b40c104030500400350340d40e44c00340c0d806010704454200032959000480e02c00c02c16075000107040581a5a031a003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 438004640 1250 438003390 438003437
    0x80d0b0a05090c0c07060203210615070b07230307050a030e0106170c030102040303090b0a0c020406090212060306090309060d090f2f01020607030e01090516170c060a 73
    0x390b4001e00e6020401008000c0300b401480070348848402c440d015030341d81004998038400c00d122545910250b0701c944d10485812241c01d0342060b03000301180c04661a80c020900705070820f410a0b1042040381084c412400c1c0c0100c0054031040f45c1d000b012640d014511064038035480f010b0f112004100b8000b481050fa180710740d200704081d0040c84000e0000c035542d041d10000302200201014810b0203038542030625480c052085408495054540c0aa00c40c504000540d480e00042800e00510040b42900c0e401a603c0b8030407d00600805400140c480018450b107120040380244802d02070b038080c0b014030a0026001007500c8034180216015613480d040064850082d04140c88010b01d5409a40008810032810285501500c00f41c1e60341440c0c0744050400545114080c50010781c09a0040804100740501c03940140c500d14100c1000401d000c4000d40d0341e40c4ca000c1d501008400220f0440700c09014804107400c001c41d14004407401400795811810004940b44950300540052000720107001c07a00e500c012411 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 438005890 1250 438004640 438004649
    0xd050c0a0f050c01200703170403050607020601180b0f0928050a0e0304030b041b150903030e0406060215090c09010905040605060d030e01030c021f06030c05010804080d0b0a 76
    0x41550410070349041982c5015030746400780818815000f082800300c4500c0780724101c1c4201d0000706509440d648440d03070004000039915004503020040031010620401059000d1074095008018035031420005071060040c041e020707100c40d4141540d000c104e903580c0c00a041484c034210f4031040380780c8900e005854504050039181d1192100042000c440725a40e41c0042e200b280700e428103204411104c4202a120300c00c1d030000400c0c0c8440c107008100031504022041201e510320a10021a1035154188840070050130314003007001540c4144184105503100002840402059030203002c1a414072601a445580b918040320001e28244000f94150404008003010742801401030720165844803080030141200311426203049041002042d2241010300d188000980c26a03295043c004039480110003918803480c0c020110311491880f240401000341005c11007810f585400982a451460440c41c0c1030083d502c1141440544000c11011410b008121000a440c45800090b1565400001a01a80560171 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 438007140 1250 438005890 438005903
    0x61207050d0c051306030608030a03090609061d0c01050301060219020d290c03130201050c010608061305010e151b190305220206161a091c05040501020d050c0a 70
    0x28079403607160410010605504d4910104281c2c0c0e4035000180c05032281403080300c8103644100031078070601d4403035401151620710030031000c1404d800d591280c00540d205903074001c1c1148420360803102c0080d8100004c10388001c2c01c1c20403605540c58504d011351510842640d80f460740c000405500c0442d91540c40e500d203010380c007070300400b910002e6541e03404c43e11307581c5540503e86101c2100441c3e015030a1409403849040780b143c104106d03144980c01160305802003400d00e10f8a64840b9000b0688601c02e1045a109411100c19094043c1050905a00750b485203072034a0401c0e006011303048003484045550310303803103400b21858030f001c12600b0783c0786841d6101d81704480c03503410780d58039462450603410340105024640441001e518134003650f81c0c4c0346120700d00c000020742c0100100b051400300070010341a550124000d04100d800048080c10403500b030501207039400c500390041904491412000200100170000754035000d8145420200041d503149260711040041c0071004c00c40c5002c00c1030802400419551084 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 438008390 1250 438007140 438007151
    0x30204061d010f081c030b03100506030c01180b03040203150f010302131404260c1006081209010305180a200411120901110a0908060114061207050d 65
    0x80111084960341003954020442410000510040d0420003c0036181007001911012848900344941340c3c0310441c0c0e2200341515500041002e07602801407000c0c0c0c40f030251020843d49011005c0504020008641c0740c10b0040d10320000c10039010f81101b413801d0302c80314012907951703440381c2c00000d2a06042c50011030410000104000c0380179040d0300300344d040f40c0c825a11044609040503201050b101540c0302c04074600301c41e00000300030602404001241400060388091504481072045d9142d40c000c00841000740d02c42c03105000e401365070380310b818010403c04000e0624240000d8155665210301e5510b00e04046d100d0020909180d00281c0e11310402c00c0313800440d0a0354105240155840385040e241e10714141111001090070f04181c0600380c0d005507401e07075030761412a03080003010044001400c22600c543d0f0b154001e00c0c000300100300501c000041b98545404951030124440d19180050300029034810440c1880100d540b10318003503072880c62602d2621501659505421541c2d03002d1064010311031070030107 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 438009640 1250 438008390 438008399
    0x1f090b0109090819020f10020c060f060406090603060b090a0b0a090c180608090d03051317070614040501060b1207030c1e050a0905060a0c0803070e18090105090c060a03110403020406 80
    0x50003031b07400c032249054407007004c102c02c0140100d0041d10443d544c0380c0c1000c00000c40d00c03194201500d600c401e0081000801d2600c0d950080102c5d245504104c803100d51b55201c00000380f9000d8400c0364000985c003028041c103540100810122130040c45481081c80c1c80310581c144035401070000d00c4400388140c031065581591904000c10ba018183c1303400d24507004400340340007205e00c00d000d00c61043c20414124003a030f01d11a5102d41c001d21800c0c0108003044002e000d030000044003130003110b03441205021100c603c1c1c1428200607085442540c03000d600740308108401b4021829042d1116445030749800c0c0001d00056000d41038070345000c00400203009040c0a0100e10203590000d001d05000e4019a07240c3d000661603100784460b52240d04100b4000c42c80c110504400246000003c5a200d141d07840d082180b80782c08400701e043c0c009004188084650114200b01407843d0903c5065804015200186584c40380b14001c40d40070f00c140c0c90304500b01a2030301a010f04c50141c03281200d00541d40900108103080e0744 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 438010890 1250 438009640 438009643
    0x1018020702090603160b0a020703060515030d020a030c060b04180b0a0b09090c090702070801020304050d17060d14010b09090d1707141b0d021f090b010909081902 71
    0x8a000300e1203180000c0128091341800204d1082108008880380312140c2070400e5103440c3d4124411000840c442c1c200040006401c6005460085c0c40c0b000309644c45c0040d41042501782184172418108560154280c038011030b81c408000c526103900110006000c1d840f0030040307005000c101442001c006000c1201400b000542c080080c459062608100702c0640400104840b00b5026a076040ca950b00c041d015100b41e1400d5984507401c000a80100c0340025131391036016003640c10468090310260041c6d0744000761141c1254044c001030805224503401c5291243c00680703900755415020300014131004510303813607400951181c1409070008090008a24011071080c2d82d99400c00348100005555000c002c1c4071480c2c4010140c000d6009031100c24000303060340100c20f19030b0880301c00c0031507610484441c3c00440c00c05110540140c502580640701c0003118070760340c0e036895008038841e48985140109090200b10881030341419140d14050116240303409042ca4422405100a040040c045440622024a40 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 438012140 1250 438010890 438010897
    0x7030b09041209150e0402090301020c06181506060a12020906040f0807050303030906040b2815050f0a05010309050a290f100e07180602010c02010f091a101802 70
    0x1015a83d46010b01e0b1142c0030795000e55070031450140031814240309500b41e0319094024065030300c0301600050a1a80e80c17031f03209150010641c0d50aa040c0c81300070001c6d41d0b91200f030001c0610440104250182410700e0800b1030f185108140210301049007000030001d1039406a0111a0300007401030140b500c0d01d84601c0300d45a16182c601c120a401c5c0316420001400e03007404000c0d00d1146c000d060140106981703503101e119003a04002c0034080041c002c0c03d0641c80d2021400e04a500008a80c14002100641c0e140450a01c111070340080e44250002c8840304004d03503460356004103651080c40d010440b0b03032040c5480c524202c0b9030b20008050b034140030031a56009468820080c030800b980c0d0003c034a65110780c41c589000302425540c00300710925044041c006400c00184d800c0d08011a80b605040c402104040030345240000c0c0c1042005035100c1602c5e2890a609008444004003005c004015096507603440900500030003e0043c0340d500d00600017498428110404002001c5c1c55005441035641904007100070760 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 438013390 1250 438012140 438012173
    0x311040603062c01050d08040905040807050c150d110405060c0a031701030b01120515190c080f041101120903020a020a060c05070320060c010b01110d0f03020307030b0904 75
    0x6800034941e80d0000c03004404403501e070b038200c03030140703c0c3d03074200400c0c400700607490b044c140d441c030b80104070001e850340f118819188214050502152101010701e8a1401c1c20485900c2500c035001800c6103103041c04900046800301003a40000060035504502ea81d5528003840c1c2c410f6506c82c00214000e000b03110040344001229209540794444e1846544160000b60000e00001e030004074514014003400601e17101785030300c15000340112162142d0310421130001c80c0b01102c5041101688008100300d0f401140036035800e40d020750900440600d4034400107410741300700070006481800381c10111b00c07569015030b00c640003480390f403407061140d0000c50034080d6131400d44401c00c0340a11030308400080c28a00c12421341807100d03406800340c00114071b1130f11401c2401045640007804a401600c070042c0030f83c0c408008040084a402c0081550138640001404142c3c0f40e080a1030150015181c102c281c035440100c1000310b4034507080042e181e40f03615004400414140c0c40c0c5982007041d0f1000d110500410003403241020 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 438014640 1250 438013390 438013409
    0xb04050304170d0e1c020402130302040c0f0507021309080309070305070f03020d020f060f1c1a061204051c0203030a150503072d030308070806030a031e031104060306 73
    0x500410003c1c0d48080019104001406400c1e00890a19001d0509079002000c0e42c4d08120200640d00083d04a81c024603040019a401000070000c508060103618000402810400902051120b0182a034412100300034440c050b0460010a20900c0c0d5110014080e0402076298691621b04186a50307081079020035500c500c6184000a4000c1100851000743e036409002c012400721070b0381c24042d4105480070100d902c20000d10003c0c00c003074103a4026000681506c0c0c251100404000380d000308440d400c04084900e40c03103184c010445a1140011501c40d0345004000f10036950b01d0f406e086051000d00030400c00039a2200e50b10801c1d00f5130000c040d50241d440440d0400c043d005e5a001c802d10050144102901030300480010010b043c550112080a4440d6030460b402085007640d80504031405500124089044d03401840780065201c10041e40c488029001080301c1a02e94801a04003000c803203a1035145966540c0c0d0511a5120303400460302d40b8048000c40303407280e4a4442c068042d180e0f9000f40c0c07114 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 438015890 1250 438014640 438014669
    0xf0303010b12010e0c0412050705060c2113270c080403030e060702120f04051329090103140f0f06090c09010315050601180603200a0206070e0a030b04050304 69
    0x3542d114864150242880b45c00c8546000e1070412055144c800501c030039210b0340121540025581c0f0340038014002900184090206201e1241c405031a204003108140a410000d01c0400c03030714400e001100c0c0c00c3d20740c0800c90007074061240c095005088803040308a1070641c00c080d54040c10b15003040285025038402d44051100d80004600036680340d03011200c0c80b005900101600f03070408401d00040c4010203068481515041d10f803408900c03d1902c4401c580303040743d0340d0340008011450740d83c3d041011285041c8004000149100000d500c002c0600000c1d0980078881030510405800300b000320021503d00050f00c1c0d2000181d41c13106d44070901160001c40031700400c80488a5440d024644038180c80d070003403100803c0c4c035040041100a120091569040c0324484500a1a11744000800002003405641c0411001100304a02c2c0d0f006440c9014001880f81c01d104910282e0307004902194400445d02d003540d105500c01d400542140d549a10240c8011003d20a00c0b05100000c0000c000f66404000e45089 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 438017140 1250 438015890 438015899
    0xd08160c032117040b1027150807051e1f020606011b0f03050f070c052b020f01091a0c010b030307050d0806030a120206060102010605040b130e0f0303010b1201 70
    0x129003002d850f010300006403440c006400076032040c21054120038004055007030306417500340c10407020120134101c0200017008280c04100c40c40902801d41040e40c4100e245030308514007215a552603000380549449480c000d01c3c201d0701c08040d10f018080c2c0060040a00c402566008c10356414000b44002150042c010500014038650255600e0740c0d4940d01d651061803c9001a2220480c1b96848442241040801c22509041c0c0d40b040020748400360080c044c01030300501d000208002c40c1d6203400890740d101000111800415031490711500041c0e01507071820500c0c0032080040742c00c000c20380c02443c81040c41c0b1000c01d02c2015080701a1520a41c0c9030001c010414142d02015541d0081502c01071080e4012a200c40b0103e21070030205070404801340481d1055034560355402a415241c80d079140040c0d0118041000c19a82402090000d1005407010410b006d40d8801040f210007440b103103030b01d030342d80c45025a01c8041000c200307074219070300001c003500c0d1030356107900c5490f0840c1c2c020184005080301040003c81c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 438018390 1250 438017140 438017147
    0x90203060a05010605040b2812150b070311010b060d0608120405210a0f0303091112122a03041a030903041a0904060303050310080102090d08160c0321 66
    0x103040c3c03004d58a0f0582003600e07208802040e82e2105c0301807549114054850075000b10403e494007076283c102d444423150340c1918440181220087d2602851100c031151007040b070300100c04100c03140c154061414003809500d540c4100d0241403070082254010000159149400c0c2c4242c1c05041074034100b01c25500141c8502600040c2c0c1d0285029156002d0300e016003009080380c10080d427144003088030064403c170040c561503d880803404c220055000c031b5110754201040000324070040050020445280f03155803d1020a240d461004400260105400240e6440e10b82c6686a000581d1400f0441c040c030129075490505880c1c6c5c206100d4440b880d01c1c1c200841d40803040c2002a04d1158903c140114201450800c0f00404a160b215000f50546020082ca2681e80c485000c0d00c03010f0342c001c0d2602a0380c1e061010704050700450342c0c0c3c0310030300c80e92040c4040c00381d542e640c82c894541141c0046015480713206100800031004641c1034010071707140050100104001c4c0c0f5410b1040603042e94083c80c03441000e0480d094 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 438019640 1250 438018390 438018401
    0xe010e03090307062118111228020306101406120c0a030b04180b090a0f080304030203120907030204112521120b0411042d0603090203060a 61
    0x850341908004801c0c13042074412102c00c07965505010140240b1814060040c0c01c6130305000303c0d4640c01e4801070941c414090080d810b0b00c0104010b652501c2040c840b58003064650b4140418481000c12442e1801c00405812083d4401b69030010107555039410a1006651032505078031901f0368600269402c07584c81d15001c000c0d5452150b9180031a4003a0340c1c1c0c01c1e038403400d5500442540c000d142c2e4408403100301e51558880c00000350b8420300f0b2080d80580c50304040108800080c14603c8680c071042040b00011100344598103081d500c0b54541e500c03030300c0d680307020703425030150264000c540c11441c0108880100300188240440b4026141081201509802e9054900c00d10301403000125a401e60b041c002010064070684181c059003116002080d60100c1102d000043c1080c1c000141d0305ca451000e010041d071081c02c4914030102c80800030301d144103c020b01036008502c81c1070030540507402c42c951000440e5040c11201c4601c289034003031144c0c49030390240c001c242c80c0390141e019200d4040060012415840759 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 438020890 1250 438019640 438019657
    0x240102030d0f052d01062109060b031227120a051e03190f030e1b091014062203080a11011505040f142502010203160c02041e0e010e03 59
    0x1880c103036800d2003016900c0c00070701441d03e41901501d500087c10352102c0e00c94a101c1c00c0c41840003288a20001d42010b01c0c1c818150b80703000300800c081106a07108401c51981400404010901c03075590441800011001c0b00b85400a4102c2d0107400c045d0400c0010204180c0c480b0a0380da6601c12002034503107031040e230b240100b080d8150f071852844550300c8200d006141c0042c90f12680d19010903090f006803085800c00c042014240e1f2510030303184103a2814580342c40213540c400c03154120042001d01c1d10040c00109107400700303458011000012300300a0000e0f0494084074040b103400180c0d44096403072406e0304007544440940d03c00030300326005a15036070760107010b001401030450018141540c100310411004290003400d8099095070350007501800c0003a06079542c415881e80344103100d17043c9600c484000000081c0744501c21a4410000c00c0a00245c44182d6024001d56160000c401800d07403000c90300801800030901d485842607002d009100c030403500000709030764140e40280a081a165441c559a0050700c00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 438022140 1250 438020890 438020971
    0x41103040602070c0e22080705101a06130519241205060a170102041d060f0102340801020c010b0a0609030506041b0e0112020a0509240102030d0f05 65
    0x2503052040c2c07824081b030709076806038805501e01145a41c642e4604000301000c08059078603070020040110583c0a11181100103440da14603011044098491444141c01003a10883c006610440d249995075002d0001d000004282021004101203040d140500700305481d00086a444060110411030b0149600540001e01000362072410000031080000f0404984a2a507601703001c0090403074812840840c480c2e030000d10040700750404006001d10040020b89250542d0310101d581e00c40032028036000c420413031880034140345e100c4130800781c3d504c44920759010210f01e40c000300d43c0b803400042c103502c9500c5d1660121120301181e81d5880054031045654480a40542c02000c00580480e142d08115410761a00d06500005141c0b81c80040b04281d5081c2c00050009981c0802c0c40e0840c141500c01d13070060402100c803013141c2e00e000c5e40410350511a40c84d543c4000a1035040c00c62a40c0d0082081e5002c1d89401c210034803d2201d202c0c80207000304011910110803021600d920101805030034002000341c6081c11 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 438023390 1250 438022140 438022171
    0x9110702060306100311070b1603061a030c070c1e2114071509080106082109121e011109150c1f0c02010c09080c010e041103040602070c0e 61
    0x4100003442135290000410305807201d46c4000c1e0b070301c1c4010080c60828800d0b1108030b0a82004110840c00c81c0e04482001c040c5460910144102c841e0b00c90300d002104071822107543c0d00d076a0502418030b81d00400e02d004118141c40710300800d03c1003602c00716100100f41002c81e00b00065035a1740d184a09003900341e040c02e800d2800d4001c8000314140d1100c2030301c102070080c11100203a07a200c0000a548140301e00303010005240c20014040c60800380210802400d0f0b51004017486101c45040c82600c1252010710b4000a400084002040e158041b04540314404c4030199800550140c000c4096604150410800355117861400501204418241e61111170094441d5100784017440d09902c442d404100a0202031262071003111180c0441400300c0703001082c0d600c001c04c4403c000e003800303800e440c000e642c1c2100f441284002070211040000c0c000c80c55000900c0d00584201818010a0060401c4a1030041d00d240020800043c0001900241841b51040024a4069940b01c907103200401094800044000d07482d03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 438024640 1250 438023390 438023401
    0x50f0f09070e0a0302090405070602060a060332010e0303070207170c0933100206190507180f03020910060c0b0a020405120706030b01090b3c0301091107020603 70
    0x40d29600142c40700034068114813034407a0002294100100d0301103079581d0060b18240182e0398140025600081001024440c503801c540c4c501134503d8000085050798102c00901c41c82050300006820340340d421040080000800d8101420f4a95108640100c050702c10307c0c80010301150107816545c05402d81e0b5020b41688003620080200f41407001c0c1403040030001044464189100d9a458266208010400e01e007118100d00c05204541311800c4651003036400c660f0422040c18103002d028000406081c01c0000c0c155a2540203032212803254602c5503094000b0300c408540900e12907080d00c1540c2c021034ac0c000d01d80e564080fa40c520f05140d0300403840090244c45422002071394041240340c004034640340150030f0039114004540619a51916150650300c2803800304851509885043c440050a04c1d05c84101810000085902d101f900b60181481c500d028540080c962980816000400003042200e41ca0044185400c115082070282c0c1440900d400c020458030181d040c00c031010142c3c00ba041d541143d441 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 438025890 1250 438024640 438024647
    0x3020a0522020714160905130f0b180106030317010f060203071b03060c0e04111e0c0703080a1806020106120308070c0803016216050f0f0907 62
    0x340404c0f95900c203001c0440e40404d13002c0c00081d000001c001c01c0f00765402e140200784019541c002d007880441c3c41c0b2400a1074081070740c44080307440340398200c138003451700fa29209808503156414038420034107546407500101c20140c0c02481d51720748605c1d003124211280d8a401420101c8042c502c121400b5134410000e0360b0000303001c000311400050000c004c040032180d403611401c0c2030703031200c00e407074400243d020041909628181c424032a440c076200c1025401d02410106981e07400744040c100c1c03c0c0003800490b4a202d035200420070031000c0d5a0107004039884031218a0301070f1400702c007803501c0c00d401d001c0c04130041031040c41403081c8000c940d00c0c0f5014441c0114030340c03401e456010014105004200030003d10101040c6020000d50003019446c4504c100300c5482ca0a8070006d005c0140d2035030003484503122002a012101a2003030103854000204ca01070200650021594200c00101122600414020300b4607600c6880e1502c1c1200e00944034507688000b020104404800792451007507112103c20003180380e60b4032 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 438027140 1250 438025890 438025897
    0xc0b09041d19060f140702160b03061201020d0f0e101802010c0302011808090f04020405060d05070c320a0f12090b340c03060903140c010603020a052202 67
    0x10b83c6000074000a401201300c20b80e825040d0b90145501e040f03007404000c0d03074100300c2e00380103c0c02c0d5541c00b02c4035400d1a12104484c0700141c500d5116690441ca0741003446000c1d411145803514580003000300c440c01c441c00c5070140810814145c079600900004c1e04078241680147ca0001c8030411a0700080c00e00d903030056840118500c0203804541d80e0318000c20100c5082800400150300901d805920762162104105c0d044005090481c0180d0051004200d141c4031003054030903d04022038041001ea5034140304a070600d000c807001400041004080c040c00b4504040c00f8240c4010441050b8219045070302441d0f40c40242800c01440e0410a80783d4501080305550103c1146045250035800c5a0b40c0d03c1c0b091116800100170109155001c104540c000400b91840b042c50002851618040040d1519501e031140e25520024009644501d4680d0425100302000e00032603203035900c05500ca20705010454000c1200e4001203001d0402030b1000b10703252518032140d94241e4542c480345c0c0c482c11845040d5070003940 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 438028390 1250 438027140 438027143
    0x30207110913050706111e030c1b0405070903030503060d11060d05090f0727020706050c0901030b01082a07021206220f0609030c0c0b09041d19 63
    0x88003800028180d40e858510358000e42559004501c84011410302ca41421115440300e018011103400400c003240003c0381c10003000603983d080003907040d42d4580c410f044d8410f144240d40c407030044a00e8018280c081c464104003540044c0c2d03042202e40e68120090380c0a038407a00014010036401c0c000a0301500d04601c034500c10303034444c010f60740c0ca110303010020031000d401030079551024075126400c000441c0300400264816215820041011500c2d1510350071000c02840e04000c902d0080c0101261500499011103030701c00c0d0300c021b00300094a00841042141e4210705084c2d40042d00702a80b600d889d6118450b124040c4445400c0b41c6140406804120307c0c1001c0203414401c0d50070140000405a56208010142502c0006c0a403580d07207090304050500c4902c1c03499107896803199004500104001c3c05245403c1c2d648400001204d1845050507903001c01d000000500b50b01c480703a00842d60007000405441c94003001c2c3c905110b01044240ca8503011b28448482e031910b548048a1543d6011001520180c440d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 438029640 1250 438028390 438028403
    0x60e07050d240915080303190e06041a0901020c1209030606030c0a0b07020a030203031206010809030a0206040b0c0c010c050405190503100917030106030c09091a01030203060604120c17060103050706030207 90
    0x41da1741e03001e9400d6400498000c0106c1e0001840a41e8540d141d00501440d000518098200d51805c0d43c0c500c81104030304034825412001d420009842c1340c5003581221900764401c02107500c0b032005003281c44815440783c6122406405034070301003030450600003091040c03883c00520300c0c110181810011001d50308080800d070b038010074100c800005a10b0600040c0307890500021100d19600e0b1003000540000005803804005034010458240050b07404950950002d07800740d03946003140c980221180560185060468041d481e01e00c40d00004c60300325008008035a130507501c103000c0c50001c413800300c289600c03445840d03016008402081849240781c1d0000c0d01081c460b25405884000305242841c00303404c01d07008140070a64400710004615008880b4a00074085d00c00180b0605001b03200c1140e039039036800b207181c0c189900440481c44a55039902543c019003000070016038100407605208400c06580d1096040c42c03245024040710700c0b1b40104050f4140d03500300b001401c001d4030706401103000f580a82401d85a8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 438030890 1250 438029640 438029681
    0x806032109090a020702090903030906060f0103140906010801060902090607061112040c06030f020324060408010e070906060e010c11010e0d2f0a0303050d060e07050d2409 75
    0x241d844100c2c15000f84121180107803201328900c14444091805071100d1040c0d4020b204100e80440005240c661003c820740f00c04d02004551001038000d0312400026802200d8214100030000d10b0015001e4100c54070301d8021b20902c1c1e40c801030341c0124030a541d001500300c4000c101850100f0125080b110385040f1021840d4903041d494800001d04050640c0c04844640b880e04d07080202c2e03507041c01000603564280c28114594205092001903c4c140c1c1030004c0c080b15415502020542d44c0c85054900500003e0000d100c0d60b00d00d1b00e4203d45442007400b07080301561500b0804180c45100b04c0404101943c10b1f1641881c5801310344425032104003140002d030400c40588201c454940ba184203800d211880381c480c0401600800344d9181c00075040c0946a285d0001d840300300125030b9920304c1c2040841e9050f080c41646ca04207047d081000d0311440d0001c84449031b0a00c140400194441c004140a8407050030401c2048c180100041940b603460703d00c1c00d001c1d004a001480280070b80c1c6c1c031680c002280742018520 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 438032140 1250 438030890 438030907
    0xf05012a050f06060a050117070c050d09050a0e060607031206030501150914090c0f030f1b0907050418051503060106091a030c0d090f05011e060608060321 68
    0x9524a02540c111410b030030811500ea801c000411145030015400c440301050706040800003041e5503859007805c84040c020f1004240e40e02e01032017540300480e40000603158601d4541da809003880020744101c6014208050000481c51144e511040c094a00104400c1c500212030718120380401c0c0046200300a150365640010000d1424461000c062a00d851401d54192902c07501d05c04603203240d440c02c9800f450540c20088054000304a60221403000c4611000c5805c148020034641464180c07007454034864a4541d0510403301d0500c0b040e8000d0446600101c1c0d613030424111b40c00d00561103518036020722120040c2d40c0c4180b0344c10180e0f00425140b609000340421200091a00d0800e1f4001800300d619001c042c8180d040600c242d403100002d1a45443c0346045c00b00a042492203000502c500c40e43d59080c1c000100440320140312607190b0044002e00030a144481c1d125800c034055081100b0051410400080740f501880210388100c00040141c06030142889840d5980e04042d002d040180700200304002 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 438033390 1250 438032140 438032207
    0x12091409190203061f170606031e0a060f03060207050c010f022a0409030906081b0706022505060a0b040e0a02090711191202010207080f0f040504050a0207030201050703060f0501 78
    0x888041a603a440c40034416145c15000000007e400140510303010000c20020024040314000c80070041d03520100550b8400340a50020522034102e00e100310040c1e18000b0510125070080c005490059081c5e8080306000c3c0011342e00288113442c2800960050000c06110308940110508140030f2041c000214189140018040f031300550800c402080c80b144d010300c42c041e0700040da20313807000f00110541005082c001c0110b481c2d020f0780c9030003040950009800304021182c03800340a9030014420190403040501e01c0c0543c1c8500044a0410940f8580040c18001d8981400b81e414a00170410281c102140aa0240700402030700404600500100035894603a4030800c01c281061518032b5044c48109030024a0036000701800c070721040c030841e0b005110f05004184044229082d540108030b00d55a50b4034200d01c0124a80155404554414070b000d040040410040c4c0040440501c2540208010b82c3d070650107500300c448a00840d08030741144041404654041c0e9950f01298201e44209030308170402c50142e0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 438034640 1250 438033390 438033439
    0x9210803090a140d121503020418060f11040b0901031e0c08060d081b0c03120405010e0405160f020c030105090c0310020a05251209140919020306 64
    0x1c01c1154080e030084801d01070030003107042401e40404050101c0041c441030091018400c3c007070302e1518642d289000b028250426150350001c0d54040e005208900e20038404403068541d1401c251551424110842c0c5403003840e1151810301c600c2c00031581e08080c24003003501342540000c8445418160303100360b49040c103283d03001c5071569040d032440701142008003040010241e05019100a024521f005111000a1030800c141d034000d0114505048041200710ba100d440c150340310202d160540510000030300c15004400c0140b054800c207880e4483d403110900f040c4004c9400440303041c000c0324040051002224821207102881c1e00b503e10417505401601d00000b0f003100d8068a0b034800603480403980d201c9604060210120845148504608050650300003400c1c52054086007105c44a8140843c80030071503e8900e10001034000844081d01414030131b02520108207030140b1b00c204040402d40103040d1600101c210300c07500542c00311110700b08480c00da0320042e400c06040b9650010112030680458180344011 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 438035890 1250 438034640 438034651
    0x5040302150711120102030726070809160914160801050112020d023103030801050d06091a07020f070803070209040c18140609041e0c0f03062a09210803 67
    0x1640da040103d0040e2245032000304444035150740030036102c40038900e440412b60080003810500282d640b84415641003203183c41040986d4884000c001c1040d807101d502c00f0300d02802d1148078014940b00c40c5120800c0c18418845038001a10b00d500510070381d4800c4030900d10710440d403c1c0140c00c0040e0741032100280d07001010740c9038051340f10f65603070f44d10340c03200a05d400651381c0000c0b420810f1b1415520003c0ca4a0300502443c0d0040765421107010802143e0b501c0800034a402a01c1000034200b4000b20580342c0c0010340d40c40d001407141c81d42e400c0c2c43d00c10104004017281e000c00300031850010f0039806d2088005000303105982440d2003110000305840b200001002070084d00c40005000b080d223020b0385240340405031007a40650104020880040c55417840e80d9030342c203c03500c0b6424646510f03240200c0e40d250150468800e00018010000130041250025009500c030054898102d074000010751710398190b00a0210000798018004010011109142d08112a942c00a81400c4440c1340c599038a2039005940d03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 438037140 1250 438035890 438035893
    0x30b030c06040315050a0902060f07030e0901060305040209060405010b1602060903070e040b011d010e0a091403270d021e0301090c14030703080f0a021906090506070504030215071112 80
    0x100384207100e10501c0b0b8251b2061b9030100401003410700781c0104100d8099400019131007900000e03091b0605001d4034018801c800c000f0a00443c660316002c0083c0a0003054400700d006060400201d034443c6014016241607642003000c0e07604052a01c94980c0a11801c00300907a0030400070002c054481d2018020709005e030403114180c4041d414503282400d00b524050b400301000d14207080003810b019031080355450442d150901e04411a8072004c280b08014225441d0040025400d880440b00c00880030001d0900342c0f210b4400e094401100c000050380031525041710303e9200030200180401840d040d00c1919200d601c1c0000d583d051844000403c0c21102095000d98111482860400409000c0340403c0c1d640741080e805071007030071714503a5002151700804842402400001c201c1c014002e1081001051158150032400c1c103422880c203102006000b491000c4c4c0e4240100d8000444050049003160300302d81e0302a210032051110100a51020f8008020403914405c0d601c0310340c44550380b0050b481c0e1135040e8900 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 438038390 1250 438037140 438037163
    0x801051017010c05030126061006030b18072102280f0c08090d02041d0114040f0b04061d070e060a1208070f21030b0105040e07030b030c060403 63
    0x1c8078441095415180e45415a04140b00140025400f20950381143d803d43c0c003c0c0030310580c000c0d0120900d00c0b141c0c10084940315880410400301912500b60301101c006407410050032003c00140400d00842560b42d8072030300502d10229600c075115910002c0c080c80018084003d43c10603092700b005980c02002c0030000c0c1d000c0524a000c440c1c0c440d01110b48010124280500c040c1c0c3e915401810307809001c00058201c81011500440c19122810300c010301a41c0240100550f480c40c003a0030040328951183c405075503107000c0c030f80c80f902100d48852034010b0303400444858a5050f80d56490140710001041203400f2500d80480d00c0da90b0300868012035160134550060031807103040c40c0e42023000c81c10043c0714521600144c082040560280c0d102d254113036812190fa29610340c12800d14094403c80a6402066244008140c103610b0f4205a504c1c81201203c1d90180807003d803800c0111424001c502035103402212801c0821411402030b07014000040000d000d44402491110000e40180c200ba88103030389490410 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 438039640 1250 438038390 438038399
    0x207080f3402090a05041212150303020a0c1d1605040e160f02060c040303030e010b18040b0609010b0d0504020a030209011d010e04030c0b1906121101030507120c0908010510 76
    0x1c0f0569201ca000c503130802c450300e00340d20b5044483d520051250140801c04c1650680200582c020943ca104961101100180d913850000d6a0349a400410380b29405140c034007240341d980c3e01c01100c0d20b01d00701c091411a983c031407070801405954459164401e01ca01040700244ccc0000a0b60703818400c50141e034407100500c1021001600005400c1c840c01c0464004c1c4017000348140d072400a46042d642c05140009104082075031080c0102407654110347d02c0311720104101500d20707030700a60b913100790300c541c0004406844103014000007a8080c001d21401d00e80610040b11022113580c080e542c043d000801d090240b41e5a5000b080d4805130070f0f000000301c031140c0b4200385081d03000c0c125000d0040120b182030201d03a2501d0b031002040405402c1c8000c1c940c80500c0081b4001d03800d001048000c0c0d02254204002c02d69880c4640c02c5030403c151400c40b2032001122004035150702a10030303588105803c0c2c0720505103d1160050800402c46c0c400e1603400e01c0305d0f81c0c0d00811005400d1284a118102e804080e02199092 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 438040890 1250 438039640 438039649
    0xf10030b0a0b040b09061f020f060108060106021207020109050f0f040501090b01091a070308101701020a0906020d0e0f060d090b0f010f0605180d140105190207080f3402 74
    0x1300d4003070f40245041400e100ea2512048101078180120710280100c130310f0000f00407030410070050010300d218440c2100100e905034008c52040c0c1268010b4084540006200076940058080d010b4041c1c0824103407581081a800c20000d03070154120300600c402e20900398400000c080f030b80c0a8000307000c0169140b84100c42c2d542c104055a000d80810b000407080304860303005113808d610a40d1170080030014014045012540d0004021007e480e080c0c0803c1920180c1031107060003074011201010000301c0c01c500c0000e1a40c00428000d040740110764882e80420300010070300c01545007050415400c054104194075820000d40f1030020120710a4242603564185025085e294002c1a088030b540303001c0040c3c2c20000340b60408112480703a040c986440f4000f150b0134000030500089050701800c0300381680040c1001510660010b881902040110411309403801b007080224003920100800760780c030402c010607005014070040e1080d140f03081054044002c000a030001c040b00d0121242000b901c40740c0c001c1e402c40c0350 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 438042140 1250 438040890 438040901
    0xa020a030e030a0f110d0f030f020709020903030a1d040c080405070504110d05040c21060507020d05040308070602040f0b04060e010503040b01120311120a0305100305060f10030b0a0b04 81
    0x700b1801450302281c01d882e00c10100c541224002c117440c02c80500503401d51500114100450f42211255580802e00d040140040c154440e0940050103000d501140c030580a00c01d4482200d005001142842100501651a802000320701d55403100c0f13000580f0b801e942d03103005941460406984000341130800b031800528000c0c1c0b64102c14499400e111002845244440079184110174010380030890386c4903410300c1080b41565410416401c0c2c40c1c204403d03908409030800121007880b9a004000303a6552410032030300d4000c500380c2c03039000420411003000800c3d26000035000c80b41c059a0014503007a43d5950821890b8419448000c1030f5001060411050350441c506000740c410a0806601c0c6103055580d900040c0d4050152922910301c8803200c4c0c06051080750394400d40780440742102e40311401500200c82c150003481c1c000000904100008030740700400011282120740c0b1000a00380d130b44030800105028000181403210484003103000001080741400e146010305403c000000c1d80c03016034020b2000750385 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 438043390 1250 438042140 438042167
    0x2a12021f0f12051506030c07120c0201180b030a11040f0f060f0c0f0206030703021608040519030c06050c10020f040509010605180105030702010207051501260601060e0f04020a020a03 80
    0x24903100030802c0041c1e81c44144c16290401303c40c284e0b560b540d25010903e060143c2500038003614084002c01e01080d401c4074101680030300076203a81010100032011b52049610310300410071242c03418000702d10000c5440e0828041e4181021115041585a4200310224100d90784186203001c0003280401c10075403c00b2840f41d006075203291185582e41c190301c40e411100154800240200c4c400000507000074402e90544600522406aa0060120f5404d201100f40c00c28002c6034454404104c45e0907c1460081a040c03c07a540010504000c40c0f03840026941d0303420410f0f14980b1400b640c0c006080c407018a10003000a18801004aa100d0b418001030040102c0160030103420b000040001d82c0002104800d07030103441009180080d529a10b00720101d0182c040d9410041c05841403800300d01d0811114080141070b02c0610015202402c82003840e0310380706504000301c003540c0c3c0101005001d124820b152010b02890040c00b6200144000030102d402c0741d10900d480d600503044020b5100030941c0c444481c60181c07 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 438044640 1250 438043390 438043427
    0x5060c10111b072c010605161b090f0b090a0b041d0607020705010c110d020f1e040f050403051803150115090501090612021806030103030c2a12021f0f 66
    0x600c042412184c01501c10300444080c4180410751503040340c0c0c0d039448110340b1075001c241e8252000804040c1540c0743c07900d01411081a04241428003203440310704c65002c5004004100202c05c1c0c5855111000400031300190710340258840ba5249441c003198048501e03400000001054503103400318009080840c181c0110741080740440c1803d02003902004424084c1c942160002844203151000a000c0003102c01d07280d8100500242e602a08244404008038080094400b40045500c0070345100c00c03070307504031001404100107102c0445200340c40c043c070000d81c0502804440415000c0800c51a199401341d002b0342c90741000318480c01c00c0ca80e015060304000c1400382009c002d054144071025100c0ba10703a840c04080c040e804074100b5190030300070001b40250754000c0d1003265256160b0070010302040f00414165051142462022404889840591401c0c4000c0240c200c0076070925a80350b1945c0145582030f40d01641c7c08800d0b44c2c191001a0a03400d000509850f0100001c10500019202000c0c556024200 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 438045890 1250 438044640 438044699
    0x60403020619141f080d030b0901120b0c0f160c360f060519080d0504080a030f0210050a05100603050903030c0702060c0607020706080105060c10111b07 67
    0x51040302032810390030429880b180c0c00c50440100f500d5113181e00d15170084442e803161580e140d480700e0305035015044504c000c0d600030000d0307a210310f0715807140b1655080c014503c100d030300002400d8036050005400ca101d210a00a072601151105081c6d010501d00426607030800841070030000b285580d015400e10944042c2c20300c2c0159011513608034a0054280b901402544aa41039156901594810070107810300525414240c1850482c040e09007455001e9900c041c42050b61100d440d034081d0341510111540b910083c100441c25039422104540c0f0489030206600c10700ca100507242c80c15000d103621940740002e0001d1280b400c16526000014203a2001041c540b0b85010f10010100120480707074441601c0b01500ea0781c51052000c10140d110311503484001c0c0c041c403c148481c1079400300301d1104075100c507a21403080c0c3c3d17214020411148100c26049a2070b074021882c15962840701e8100a0801003003a40c49810b06901309201003913114402d68207403403500100307014008a85a1014081000a00d0f1120f028 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 438047140 1250 438045890 438045911
    0x30215040c210b18070b12010e22030f1b050d0e0d0305090f1903060b0a090606120f0e070603050103021e1c020303070c08010e07060806010e06030405070305060403020619 75
    0x1103d11000d4050840c111841c20303140f940803400c0021100034401c1e442255900c024500d400c3c0103000003030142000314240400811403c1d002c0c8804c070040302100d5050112049103a950680720319500320100d00034042c00300025201a11883c13401c1d801c1e540218060210f00c410400c0090223041c040041078821200d1010704800700c2d500000392584000f003602c60004010045d000101400b0f2102070050600101c0c001c04010044a1707000200911015509001003036140e1180c40207a038030302d026076070008500800003265054590800d6003098801c410006a144000225a0420450741c00050102c0e480d0401001103041c0442564107050000780d040c4c80040da002c00107035107941840e10005803084041c990406658052044507038160b84076040402c640ea48420050180c0002c2d08044d6141c003070001e0000700e0600900000d0f210f164141d5408401e203900c3c00c00c000c00342e0800b4205544511805601000040d001c020840c0254000e030003c10703840c40e14a4445160301141c400b80c90b14141401c01c500c1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 438048390 1250 438047140 438047153
    0x3090a1502130e0a02070b0412090f1a03100f09020717040e04030507030e090403030b180f060112020d09060b0a080a0c0501030b01020102090916030c020606030a030c030215040c21 79
    0x81550000f0080c0d40c520f0700c800c403561020b4060010090244103180d0140305c100b2251000c5c81e14400b01c1c503282c04400d1a540d1403490302c0d583da28400c034004580300e03040e03207440300140030b000715800480c103840c94401d00d48070300843c200c1a495401039019160300060140901c0300c10023400010910006c100b03850541020840304244101034402024003d010a072039040600070207002c3e00782180034058170110710b4541401009084441c207100e005c0c90380d4050f640b0054103136040c041e1241c540300030130b01400c1d01c0b1000115852200c0112184509509000394912404103001d2041c0290061501082200c920005c00014501d981e11003021580325404c0c00300001c40c002c101c80202c50007402c0002d5001d1f007500040c3d001e44500546194045602010000400c0c8114010b02060300640c0d410006003038107035002d0ba40c607501030301c610394035501c03031100900044d10640540c901248a031040d52840005284221220001070701c044a145a51074400c1c0459000140e007207100200407492070711542c21f81d03191907 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 438049640 1250 438048390 438048427
    0xa062004080709090201020304031b050907180e13061e0b0102031c0908040503010f0501080f010b03210403050712030e0901050108270307050c0a120201050d0c090b03090a1502 77
    0x10850343d61a40181415a8001d00a0b580150740045003200c400c0a8026030381c40282030f80c00340310b12403211740001ca0f008600c50704400c0d003550310010306004001c0c24811010250381c1c0050007840400f81800c00100001c0c075502030301400ba501c3d070704000c032003240e4058100c0942d482030b102075046500c1805254005104503d080e08240c203551030008040013a41056111071250790421a010740c20801d040e5000d12990740814102c50350317442911072550101102900741d405507005e00703030300da88504e44411154013055111801001e200c4080352605a80f951150305125856100070350380c0c402c61184405043c2c1044019040d40e50454490b0010740c140341c0007034103c1002500300c103140311100342c2c001070484800d10100c40a451000880341c0f00c0c2d800d0300e0190742c0c03203599208c84c9000d4069904000351412011030303112100c940c141c444d503060403454507140d001000c0b000e001200b0409001800542e05900b400114018482c0102034141c540150504456105035241070100c2d1500c10005d840c07682c100d0034000c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 438050890 1250 438049640 438049649
    0x20c030c0d1e1d1c02031513170d06081c02011b0e010e1306061206030b070809070306090807032606190f09230105010e04020c0f0a0620040807 63
    0x24040c51407449551400502c07201601e5401c600380c03040c00461814020756075100144200c00b07d0340c3c0041003411b1607110074020788101000006450190700000c504401c0c04503041000070b00c1c00d00b090040403000c0c05030740f110341c4500d6840e0001c1800c500c8810011441100c06007c1c1d00081c004110b607a040750307420f0f089900032641007080da103036620580c1c0c0c850b0109030900c410041c000c0640b4805155280010f2a940c480c03000030400740361006a000e002405250f040701d4000238100b00b15a582402079030302c0ea03070080c4118110b0203111340101c0010000d100303404541d13004a03007040d101d20306440c002d42094102c90041514000010481d4051015408910b6001d04103440b58010052103900e202d8401c1c00307a4104002602c02d030b08012a42603c1980000c9510407010696880d80b81606910a45a42c081c00307058002000300e12400e1440c105600104040314504003200c01907034801003168200b02507110216203441e02e501907100c8c218017108080035000150081c1c81e150610705002245c4d42e4010340f05 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 438052140 1250 438050890 438050897
    0x207030207090b1807030f060518010302010c1a0406091104020304110114070606080a0c050109060f230307210b01020601090f1b030b0a090216020d050709020c030c0d1e 74
    0x40004607500c03112501d4045640c0503808004c3ca00301180f010b0094465951600c5030705182800024140c0b07400c600d050345c00f540302410890b080c0d0840c1c00444404a2070717a01a69299120b81102003c0040407050b28840d034000c80000a500b244d80c900400c0140c0d40140607403190340140203100115801d4848407580d003109090148070040310071a000064003400e200a401d00f80383c56000903580e40c02190703d0002a209100744a01a9100d60040d0b0349410070703001c0d02c03001070520355000c0d904901861481000c81c86401c150701d094021801c02000303541c8225560710018110141d1040803620a017510785007030848003001d211444640c80005d6032200305100f40c8ac1410348850b03000c06a88895880b03a814585403a400d688151319625001c0c0142092454070f40c0901c0c003021001421610314030070342d141c00d00d80002d0101c0341c44040d000c0107020110007001b9511401520800211224a4402408140440f00186454003c400461820044410100720511108041c1d05006130340c02104d00085035000e08 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 438053390 1250 438052140 438052151
    0x92102031519060e010f050105070b0c0a1e0e0109090204053601030b0f0a0204050a03082107031509050402012124181118030109150b0a0603020703020709 68
    0xd05004154402c04107020300324500701c00801c00c08564800b150603180107011221542d40d403071004561510404070041e2a0800d000e0100b0304019500c40105202c440900d0801c0d000c03041c03001c900043c5c7c51038003410004107010320041d1a855030446946401030aa40c2011414113250401242d070288030100d42480000030203081d880141c843e001d50a0214142c540c588501e580c4078501460300101c25035940142080000000d14406010b008640944101401000007a40b5650310100d05820143d0003044902660080b1070540e00c030701411521400e0b165070702140c0301040c1d080d5a40c008030680c01c0100e00c00d00f00030400c005130f600510014607400502c1c90070104581e645c9824402021152b41001c48085258090075070f51100440210569420b251480c0c180750010354000101c8030b80c0345a42c117114806000307410104407000b17034281c5426006000499144515910f00c8540c82c2032001e000542079442400e441c5038144502d0f601d010300b616040840c80c0944a0700c01941c0c40945100e038100068a58 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 438054640 1250 438053390 438053401
    0x30b0a1a07150c090317090109060e1201050a0c0e040203040f080f1c1406030a12080702030c07090c030b010224040c12050a060c0e13050c040305030a0921020315 71
    0x100820b4007030403400402085446054007009068107501c0c481a10071511181120b000c0720681c42c2150044141616518811032608500783d65240c001c0044ea9413015602c0c0180d80300107001c0c0030716445016980c0c00016081c084003000751404025490303460141d80305100304000512700040c48440355400c84100d50f128461542c1c403e005d840781e40160039910404850380c004100c0a50031a041c130b802e0440700d80320543c3e242d4050545d03ca05c007000181c034400031035800c010517500a84006401821505c15640740680c82e603e114034142040c0e2040c80c0c050381d10401d140c0b42640c18841c020802400344050320740c5008410544413050381300d00c8510354448280022808000b6035005c0c0b280144003020b03040110b04802d0074031a450714139004003500c40d14280300c07900d0482e83c490050519800f00080c90b41407160000403c1c45c000700700060805141c040c04002c0800070450800207005024a0780d92552807413800d000c3c620b106c4240d441d41c01c04c80c81c0c543d054090f005a40200b0780920030010784e07188201c1c135a200d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 438055890 1250 438054640 438054653
    0x91e06120307050f03040e0f070c200a0b0715050f0714090d0f02041401180207060b091006020d020106050a03030e1819060e0705032404020415030b0a1a07 68
    0x1010302c0140544161000d445601c00c4c0032018004403500380c40401100d644e590b4504030b801070115004c2e030014910202c00da001448200080101c00c2c400b04c508081c520084c3c012803107c1c1441e402c010f880d2031010442a080000e002d10844019520380818003180c01c217900d04180700c1c1d0300580704005020b81c06550750400b070021801d4403440d45c0002c4c40d02d4174102407404d000403c1403244405a02a600341010208000410680c20b412140e01091b640c0701e40089011440094108100c1201d502d516160386108540d5100b9555004480030b005e10a4004d280250107450159aa8940403c0d6410184200260340e07a44090340c0869415040c0b00b12411030120010b10042d620410000405440070107100b8800d806090600d01c049403080b0409c100c6807a41820702310b2242c00c85280700041c80c100700003440d0a01e44550134a0b01082c10303540e00030303402e25080060183d070066081003500c0c0300384401c18200140d240c00381d03505680701550380740221030030009800341106052824881001d00001c04c2e000304181d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 438057140 1250 438055890 438055897
    0x801110a020a0b1b0409051504060f091a0d0b0f010e04030906031a0909010c0906030515060a1b050606041d060103080a050702130e010c1103090d150c080402091e061203 74
    0x34021340a43d50b41e11004980d00403c000d56400400a00e00203000b242400e1620684040d1010310301000615442e04420501070051058071507442d03481a0b03400d9845495007401501103d01c038542d051401e282c007400309039008905038056000f8034140c6050201081d00300c4510000d890080c50b022450000c450030f01c0d640501840f00c000e80000400c400c000e035000c0f040d030004040482ca40d84840c20159100c0e01141038800a9444198400b0108a482180c0c90003d006050f04455420122111031820f40150041c041400d010741e21508800d0070480c0500d440d104406101c40f81d200b5450b120928004c0b515503400b0140401420b07075000040c1c01c20014002c0c400e55101036070040c010b94900340440c000c0701c041c1110b1280301d40e0319803c007181c885c46280103d5003508450105002141444540010441001d0300e00c442900c0343c0b55240913241d805043d501543d034010140d602c800c0001d0400b407050040d010002800054003100824000381c1905070440d80303e80200301200e04500c410300141486041d4403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 438058390 1250 438057140 438057181
    0x30605310803220c06030c11070b0c070806040c08240402010c02030f0304080f0f0105070c030c060f021902062503050c2101090e0109080d021e0408070801110a020a0b 73
    0xb4910304030b020005811394403000e8910340d43e0207004e04105248155000022200340d40c0281c3c0011006200206010010380300040c46c20303048a02555807103c91380d09040b02542c0070348104000d01c8051000800802c07d2001e26040721000703d405c10710804020200e40340c0604020704200b0016911400c0d0358041002d00c1880050300d0550780d5860b80e4404059a600708a6601d1403940a400451400d030700042c03040e039100b4103136620f8000807004a41d90848003081405070448050b6990000c5002c001034a2000c0d0135070002000200c40c0e28071b900c042c068607011b40246010040c00c403400403203004c1d58024051034104085400e002c1441c0d2100d00300e20400e030150312124544491500703c204030f0600c4281c1414101d8401010070080d01c0c182c0a50756007a41c0c016031000e81070329002c1028401c8410310750700501203400780c0d60987c1001006800d00c900a42e01542c8444055403181e03006016090f17003072180c4800715814524540c541207074008040c3d2655401c150107001c00c46000002140c3d0200e510080e41c448 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 438059640 1250 438058390 438058441
    0x622050402190201050604060b03161106010f05090921070302070b160c0618141f02030306040c111e12070302010606081f17011104030605310803 64
    0x218000d152060b00c02d000400004010760a04022400030700345486001c003a258800d210038556a142510079201007070400e1040104010400c6100c201c0000703120450280400c1d4101500462802d0200090600c4c0641002074503044003440c004c403d0003c810202e040c942d20000152140d0050500703034240759881e48101c125200c0000d012000b1031070740390140c40302e510034a42100c0054440c40b049036240c101502d6466081002d603c03e1001d805400345602c2620380040030000484150401c92034074042404103440540c0c008001e004142c9454007030341c41c12085500c2c2c00d004001c16503100c10b41e5821402d40b010301d00e0001c000c24100a0700c040c0020b804240c4001102d99a803803c0d454028003d0502c1d04c241400203130304002054056907100b010400c404c090b132600800150401c1107060101100305001c10b4250b41c2d40c24031003403240f1400054801107000d07600000b10b5141100000444903000310005090102c180032242c240b10b80520400d2103a5000b8520175242d075900c44075244210410712441845c0d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 438060890 1250 438059640 438059647
    0x60a0e0a150b240f25060903020c0111030706051506032a0702092404060906080d02150c031306050103050307030315050f090606040911070c060507020622050402 71
    0x10010960032042c84050181d80204468040c81c040303040303a402400d403074868403108000c500d480402c1c2e030707000c1e00616210880c105040aa4542031103003a101e501412560503460b4120308040c9501885442103081081c20881c2c1d00343c17103052005460b4030076041d00404440e41c403808501580d0300503800c1305030740e5009402a617680c103207a5000d014104065501072040500a00514907114221081e1201c0c06d5000d4500700c2240c844520046d040201e05911402815003080c100c0b0141e82d440c0141401054214800901c1d142410419030611047d13a462400395400040a145444030185440ea8000400c808050f182c0d04d031503813403071800040510301814150070b000010041c06004001450f5a80c07081c2c40c00c029030300480e00d113450390f015036100744c03580030480c01c0880c400350070400205584240000c00481c901074848139203900301c03514851007211860001c103804c0c0800220701c401d000030f40500d0620606004a81d80003c15500c0381031b5050b034404051480d21611000c49160172130241030010400e544 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 438062140 1250 438060890 438060923
    0x2030a05030a0b0a0815010b090a050d050a02090a09020307290c100c05030f240409020103150f0609080109170a02010e010615090e090604020103021b1606140a02060a0e0a 75
    0x58507401100e42062111b880f100025003216564225103541a002e880d50046a140404004d82002c0300340040c1d84c140074941d07000c00182e65244c955442040500c8002032a001c10340107251400107540c21000c07103480c0710081e403c1d002c000368440751541d51600d41010f40e1a243c1502d00360a0007480c400d080300150130154112000e0340c102024600c600a400e07260703540303035403902161550592240c20780d0050f41c44041081d40e0038103098003e904414018100400c9244108014840c04040350b404101f00007a40d40040c401150b0107940304000b0b22900b0000d02c030014403030b01c50380c101c000c108907011781141000480c140d07050300070b40241c0c004000c144000c011469540c400e0082500c035562610000a1031008042034140856080c280207030051070081001d542c459006400035070202c0f800c6c4400da841e00d00c2050003060200101c3ca07400007031035000820549008000703042c16902242481c4080010710480911560020345107a0110724004041a114820142a402c22050394009440d4840121001c1d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 438063390 1250 438062140 438062143
    0x190b070c0f030c170304110103050720060402090108060c09040504141b10090e15061209070806100e0f1009020c1b01030603020307030303240323070602030a05030a0b0a08 75
    0x103d080c003c5015100e024421502c1058501c02194000e108032045454500c0551096000c1395005403a410300d2030100c1c188420f00348140c000e6210400d49984104100300c114285480010300402c5140d00801c480d09185d030b1020707000c1c0160300505002d20f549800090500240080c0001c0d003440d5a026140502150a41e0003001c001d01c0900c507001d009801780d0529500c1c441c0d45040211241101d142c0034507154242201b0000003004041c0764000801c0c840501080c0d440500a805000300400074143d85140c80c48060034a403009145640000880d00c081060602e20381c0e40c0b42d0b201c022403481e00040d54680401d01f0000c4000c0e0050841c0500c0440e41081c1c24070300107107050b41c0c100c036034902c02c03040e040a10045003a1202400002d405812680041002a000b42c20401c0c80f20409940400c400050060700ca0b800f9103c0e5000351416040001012444d078441d5035004024502d900203001607604100c000381d640d1040041c3c400030000000000790b5044003c2d8403555083c00d00501e4500100e0743c800286 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 438064640 1250 438063390 438063407
    0x100302030403030b090601053106020d091a25050118030e1203040506070302031603030f1410120f020406060906020601090501081b030c0a26190b070c0f03 68
    0x440c0801c3c44c1c031401c0b10543c50680c2d07141d803003030740142d441b6440d101501c0c540554a180d007503070442801d244010b0008043d10000c0c5d0303c1c00030b402c00d80c1c002c01041d01000d10050689040d5402007a9030f100c08003048440c924540120340d10202d1503815154960f003440e4944042440109002d001546440144800c55803d81c0d0322080d164065611440b650a1000800110140c0b12095641d10780c010070080005003450300160080501a0068034108420212081d0040e44103034030850020350b80300301821aa413058456440241141d25220b402e920708140310700c1000046000b00329040b60403800342810401c18100c400f03100f0794060814803a055031244094421025405414094003600e8004240c0801d0b520600d4100c0f040e090003805000306a402444003c02c00190f042d825000707260500721507460b030881a00040101c14070000540304c0460f1500c1d014982c54500c81196000400307603122680f803800e104444540c0260003941c03191240708042d160440c07045002003107029204103480501d030304004030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 438065890 1250 438064640 438064643
    0x703200a03080c010b0f030a290708010e0a0e06060f0d0c1401270b0f0f0a020c03070b04060c060e030c07031208100620030c070314070911031807051003020304 70
    0x3801106080741c00c110300540a904010b402d41c0c4000420004503c0719404000c102d00c41c40d00409d1001c0d42c440c003c0761086003c80c1d15101040122004201910180c1202a80845a06405c000c0c3e903107140360050b11010301411291150b4120603100c00c0c203940b1380c0441d8000070362001d21020740b941d4414001e0a035440400e04c16021501403000c8a01200b440c4942da8124041043c00809050a002014140d81c2003080c0c89424124144941090f0001030380003040052101c0e002040c10001c05c82c1014601100e0f6004109101307030900042103225008400003544950000001c5444c030250b40403185580246102034456100f407510002c28030800402e90030400517240e03116441e640e98150291002802841102d00041c2c0200702d10760103030f4a5078160311201d10034100f83c9280004510300c580c5004595001542c0101e070450300c0014034030003003014000502000720140404496594680c0385070000418202107074088601c0222144414031010029000c001c086c16135051100c0750080c003e400c1201d0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 438067140 1250 438065890 438065893
    0x506040609090203100f1407020c03100606050d02070501110304151104030f12111605090f060a0317040918120815130b090405030309070b09030703200a03080c 70
    0xe011541e0000c40c0205400b032500a001081000d41c031100c02401005207040203a40a84e55001995200010100b000d01540316030b80104034540201c0c1c00c040c2840140300034409450700d010300c01c004258000003500c01065000800507180c1c2940d09202d405031442d81105038820340c00008010401c5441d20300d100502040c03907c10040e110011070308411a00c5103000c00b802010b0f95400301c000141d6650840482c0b85083d18040c2d240605600c0c410b40703495030000303090002012100c0c0030312031810841000396010444030004491030802c40c002c038100400501000d0503c0e101700ca44290780e0321415040b18000d10b49140c2c200407010200120f4001c0e0015440221820800200d0300b95450b031040d4141c50080a94072100710280141c40c0401a0076480700c40381a0001d5150070b48000240d6810203906c0c402c5002d540695500d2820360212820490349030841030b080102404501d8881d02e00065002c156688104c00d08a41000b9041d1190916003580000303511002406d804010002100081d0007070144550 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 438068390 1250 438067140 438067151
    0x3050a080406120207031209030e0301050103150e070e0f040206271005070309061110110307021e06010501080a0e0a030e040c0e0f0d111003050f0106093f06050604 72
    0x2040c00583c0300e02c50002c0c0000b06400202007c400d80360f480384283d64400d051240c081381c00c81d00440d081d11402d0740306441c0c1c1c0c1503044281401c110b0501507000702e0102c620180580300c3c140011055000c5010700f83d4403006000000040854544104640d4102c100399500403113140c44031359000c9000c820440c8580034501c02001c1c002507900910580d01c1c1c003030b07064071444829400c0c01c10894031035684200b0400c03c1d1061404c00b902030f4101e8440c45840036901c00c5640d90713a2034800780180c58094801040b008481c180601e03001d14200108481d41903275000d107031101540d1181035801029182118688400b409441c0d0f1a908054200c508112040401c0cbe4040c0724942040c5001d41e03001040c0b0091540022070304030300214602d011180d03111070b030380b0030300000780039400ca03002040c2142003080301180869504c2d001d0203802808901024014540b03442c02081060801d0601c6603a2003400201e4414051240074001c584002e00c001d0708900048601d01c9003540140d0704210b0302078541a61864003651401 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 438069640 1250 438068390 438068417
    0x9090a0f1d011b1d0919381c02010e100215180a03030b0d1e0b090316060903210c1e020706050f0d290d0b0105010c0c03050a080406 58
    0x3140482c1000040c0c0c40091004041c440901c55032200c02030891b40c13a007a00e0301806c6e201e40e825206803800c00c141c8000851808480c201e04ca140700c4081a00341c0901441d03170309100762664135a0341c0d00105004c10410804104243c0c40180d0b40614140c0c2200e40c44982038003014a03540d800a000c44807a201381d080d69059484054900a24a50800024000350001d4040e000801c1c000d4005006281016000c203582c140709490350003c5500484601c9010100031140c00300344000183c480e0342204915014502d04015000c1c00b81c100301d11038000414941d00c81d400c0c041414003c10600c1d0348408205400154030022100010041803600b0840010035a540d400c4800d008000e0188885540c480c2c0080110906003101500c442c2c0140c400603041950401603056a10107501400c00f9484046442c09850300184e11301c02c1840d840501254051030100c00007501088200440a0458400707003080500c43d03900d410081440c8401c2c1c0c00241052141c541c18000b00507014000303000f202c445030f4407018001c021 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 438070890 1250 438069640 438069647
    0x405130209031e0607032915040608160f09030f0f120203030a0e01050c091909020a0c0303050705030f0a0b0301060506030924131101120e0a030207090209090a0f1d011b 74
    0x894400e861640b1165005803031047c010000d810000307001445400c0c01440144140c404c1d51107500000b001410810501c403905d403200451401c04c0d50300c0d05150168540ba55001810391505200c06400d851a0040c94418010710440b0030000c150824003011811800e080040c0d500d0f0b0003a6408200c3c1e928200042d0340c0114180704942c0620311040c02c492401c0380030380400040d202049410044008456000205001540b009000051154440040781030702810060300b11078000301600709100d410820130020202001d041a031201c15950002200c1070901c011a005090300d030402d9420550000900c840e094000450a0079842410440f0620300840e001c0700213109025a5030040c8581d807072991800180ba85080d0313400811043c5400100300d1841c030402c0701030720b40d9002c100ca0140c20900000040c9541801100c1c06081da256081d0302e0300b60f09001045030200000c000104c516546c0f07100c03000500840d00704c1d1a22450f107820114017455615403841c02403c640e0061000d00341d4080c0f820703820501 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 438072140 1250 438070890 438070901
    0xf05030c090c0c010e0a050607261f1a0c06070201020901050318160914180a02040b0d2a050f0604030219030507062a080405130209031e060703 63
    0xd03214010707a454000102e201038024a081203410f5403030f003079010111042005152800c601510081115040c0807401030650441c920124440042c4484d040e50401c3c1c0a0084540000352050003009803070448996054042d82604043d1101c2042d01104400044080c00341905280400035a6240d0715556826400c0784600100280400d5090001800703640104032121705401310300080d14445442c0301d4045150b1030030f9412104886031364002548100c3d0315401442d510107070110703143c440c40f400c065250741c2c0c0305007001000f4031941c0c030f407511040300d43c9601c0c0446417a00c1d84540a10907040c03025118034400034042d608bc800d0360f0820328000a081c87e10554880800e00003504c0d43d03150a045400b4000032205080400d0f02e592a451800800207004102000c000c14140c0d44102e03c86c03aa0788003410340558006211844034840f1259800800c650104803412a042110204643c0b1507121001020b4024000d10320b506009004c014001c40d982400286d03030860b0800c0c1075a030140d0798884198100c80 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 438073390 1250 438072140 438072163
    0xf18070203210108150c0f0703051c0603021c14330105010903080a0e09070801090608030705030f0912030d0501030605071b020105090402280809060103121d04020c01060f0503 77
    0x280401c124941c45e01881c40d5994002084181031843d01400320b146601c1c43c0d00c4040118006100010400523000c19030b03400003030180c0071100a102052441d000505000f031146601c010817112403100c1010840103030724805c01071048030140c0ba0514038900d06d0360fa000d101c1c850407100615103103101081d001080d08526040c0c503416150401d01c0760640d00c644016030000750320310041c4054284500c7e41940c9a000180c403480f0340d40d980e00c03255070500d4a8103080e0b512592020100381d00500460000501c0441a12603034940d140e410744c4c4810310540058102001e001c858480e40c04001502050f0201d1078200f0381c1680d000701401e21890715100011107207852000900f01e0006411890720006600c14402480c68000041c030160500010860700c0a000a59031740c0d4403001d01d40a440140110341010240d03a100025802502c8558515254216810310041c0c03800700f04205c0c0b010404d060700405080040701c1402078011515141c0103201c1c3e07070082c242e03070081c00c075003000c80180002c191400240c19500007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 438074640 1250 438073390 438073393
    0x10516020303041e0206071511040506120603070518040501050705070816020105040f090203041a0f130515010e090708010b030c0405061804051b06070209060f18070203210108 77
    0x60340c41351110452400d40c88100b00d034150401165601580c2c4840c0900f41c03103401503040321410201f0f004803100f16610410002d500e0001030008100942c0c446060740c0b4550402d2114402d150342d40e00000c1e080c0182a00031542c41580c0441c519407003c480c030b43c483e1107548204001c00c0140c49441c0301381c46500811400400c00b00d010042281948888142d00c2022407040c1440c60070562103c04543d03030841c2a0b00031080d510b90100401c401e120001341006400c54100c0902d203d241403e4040b4812031030001c10480f0f5524501e030f403500820901700845105454055084816940c64401942d034078541a690100184903007140031902101c103100d1601100c9000b0000e01031f9004280900c405010001c001070f900080c10b4038020041404681403603c01c61240019000003411300314881d100c6400101340900a081c00e00c090401078451301c040700d0704010100c8081800a102c0700004920044600c031171081c500b032030001d0041d01c940020151040303a0702d08140c411070503003c408800940c4800d100e800400d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 438075890 1250 438074640 438074647
    0x605070c0b131403030703150f0303080105060310030816030836030c0a06052208093001050105010f0203070b070827030918060108070e0f090f0103050105160203 71
    0x624642200214810b000c8482d0b64007000d1503c5095400c2241d008002ca40c50741050700315070840e4140c0001422100200015160954800401c5814140143e41c081c11000000c83d81c40034000700000020756201c400255511540240746800b0702c0d06402c00c5002c2404000810750b28402102c22159014421140c05078040814850302c1c54082112150b81880c081000111030100d41070004e100042c0c0039107408159030416030310103407643c941b0007024540c040c501284a00091000d00440700411401c40703249001070000d43d0711583c1004044045180301401158040e4a01c1d0706400031412520300362a20140300000c49401ea0300ca00c20900d008000ca400000002c03000360081c04001d8000c1403203901c8000f0b0042c40b00403080c0c04040320344600c485074800300f88041c140c035150441d00030b02046084c100c281c5040540000e0b105d0807014001400780031040c811110503842e007040440071050010516101801c214030007a203051428007081d00c4550130480090400745042045101609080e40150318 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 438077140 1250 438075890 438075901
    0x1a0606180103150329010e0403021902010917280b061e030a0332180609060a030905010e010e0d0f02070e011e140a05040506040209040c0503040605070c0b 68
    0x80c5440c6000141d2001090400300110341702282440e2004c5804030325001d03c584404105e05200016482030144c40e403c40b0402000070750100303030540d41c0400f0042e020500d102c2880140d80600f019002031030304101040c003583c6829400a07440d403000b202c03501c00d040c850741c004c40d00a03098510308102800403494074021505a040131030043c441580e20202041d952502140080d060a8841c81c081d40000c58080d4240c519110070002e10076030300c088401d41c03403c1e4113031580310b1881d5006400d50101603400904001c1d0640c3c131084100c80380c43c20000e003050f58420601001600a01056005a54941c84d143e580018064140b0a201105c6070002c004c0030074420891045031420400702d407103021405810b01c0080d01c400d056056a000e01032038504808410398036900020081020390112402c4c800d201340902072515014445d1058a03800d6902180f81d654003004140a403281c0141c0c80c1c0c01501d00a49030100a42c05000b55000c0c920469050205844015040740d0400c0d000314003900e2030410314003042 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 438078390 1250 438077140 438077147
    0x6060403080c070504090b090c060415030c200d0917070e040f06020304030c110a14060702010905060d1e050c0d05090f0d020c120615100903050106031a06061801 71
    0x1c1c10142c5000c82c0d500d00c2e00c1c0c0300450140c601d207030700803103120f038940081c0888450280300726a0899410788000e41420300c1c0801d9203052101c85801501410350307803401d031400684100311030703040c0303000018541a4074001100d0301b59644648400c2c107400214030410201d8a403180e60b50014030001c00c40c0092424500f01050501e109401030012a001d41d2801e10800000b031041c0041d520803802619801032070941e45c00c1440808176044240c030301c1a40c2c1a0020b02c588240080c0410310b45000340d64107038803038105200503207850715641c00090f409480071407480003c0c600e40e0050072050001074580c041055540d1072450640700143e1b084141c0d07020510800d41d500710366030b220395845070140b400c0319003407026100d1860500ca00130340c1d95070058008607603001d060301340ba4508500007800c0c900101914607204002011960310300a90610a8614407035840c9424404c4481901543d0080020810503982e0319003444440e4540c04d02603512803000d00051514a0420160380080c0c080c4c00b80b12180b41d070b0b03490044 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 438079640 1250 438078390 438078397
    0x5061303020906031e0a0b07021603030806010c080f04170d120c0903140706020105071d0603040804030b0907140d031205091218130603030f05030a06211a0606040308 73
    0x143d058807413080d0460500001c8442c410700c044508001c0c00a00506c0e052003941c0b00c01c0102680155400310142c0d00c803488485c10200116505460054240e40341c110040703d500301070550181807144007250a46102030014001c10468994405d01d081e10385814180d00c0e25502d01d640600d02040c4122001e62a100160304100605081464107200403a01d0b03681c1e080c60b0603050f41c0340005039401040706001c0c040d0240b00741c07900004c0d41e060481c10034409283c4504c940709510035440c024400440401d04011210094074042c60f4403c40001d0300d8601030000603500c1e800d07841810301c10302c0000903240c11803d040d20265000c07509a41d4210b00d030603954500d0710143c040900012041d109070a00809003a0001d00074000f1444d25a800f13101484504003080f001c04c80303003014086141d141c1202000003c2d00495207100c01e41d9141800354a80e561341d0007900081520358054070a0003000100c0300701c8e030516021076000750380c41442c450100385000181007110355011100a9004601004240f001c50f0054014 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 438080890 1250 438079640 438079651
    0x40b1c0e07031a0718180f0203090705060705010b04020a08070806010c1a0601090306150303140f030601080a0204030204050c07060c140f0706150909120c030804030509010e0306070f09050613030209 87
    0x54105040585c200f6400c0c50742c4c403802c1c071494842411000d4050f04e00441040941004066045042800244d0f482e070120703114251090b480010351030308003c2d080d0401c80c000b900c0244215190007106c1d8002c8c240c00c8d42200c8110000d0700c079500058196020721b050240b4235070040104510140201c00964140c4000707401c0ea03050254084c4008001040c078011040700c03441d41881010380c03e180d8a40a002c401545985801c0000144201c035807492014003942c0e44414246440d00e00303501d403048040028801d80e080a034000b8108003c0003e00307084a801400c0e11446007200300304e00814144100e030074041a40c1c02d4940380c20704001e9000c041c20002c000d0070b1128024040024040084003000805d240e01d034ac84505605c0d22112102c0c24170801304914640c01d5500e04002001c1801039030002d044400050005003404408140c80031030b64811940300d5103207440901140c81904040802a101c070f0304011604002540408000c90a0704103981a17907441d0301d4261070380100034110750030004a036200514 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 438082140 1250 438080890 438080897
    0x1505010318170a020c010c080a0c0c08070f1404020306030a020105030a0e0105190c0507050a020d170304110a0807030b0402090414030a0f02100b0108130305040b1c0e07031a07 77
    0x88240464600e002105041c038400c2480c980d640380f2200301a003081144400f01d414000c016407441e0124880d1011580c80c0c564038901159580500d15004a0300e41c550707002400c0921071840042508566025003001361480005c01c01c0710404004101f0090f440204c91146c0c1540200b0050784c019400754000d1a0003542211001c140d121290003464212407084030985000504440420b4041c05244221010799031507182c101d1401c00c0646440740d03203800c00c000003405441c5810f2504207010003034000c0c0340000c1c4000007440c1e89040030f0408242074140208803078400c402c848000035912100180c040102e070780c4884018003582d6190200b1184000041c03082d0b4802d2001c1c2c002c24040306043c0020306004841d0b848020208440450007883c04001000140005281524a0090760f03000200355602600501340b194800740c00b883c0c22255070080e13034090400b15001007180740d0440a0b140d42140d0403c404481000181e040743c504030b83d42c5403140b1025184030101800215800c00e100c041ca54401032504 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 438083390 1250 438082140 438082181
    0x1f020906121b070c03020906040e1c0e090112060b0a050a06051809010b04030b010801060b0913060b0a030b03011103040b06061b0a0605180c03100209030a02060301140108090115050103 81
    0x40640343d44042e41c103c880890100c2c050086140c11b0b401c6907009807050f40c080145040641141e99100b8244000740303c45039020441c0d401e01c501c01c03c0800001c2402400b00c0c0010f5039140307103441306090411400c0340c4403030401301c0c42061030030610420030489000410302c501940c5001400e4606501690024410b00041da44140d9a03459400140f0300812000c01510350396465400e10061544040c1c000f003005905115040102c0a624820340b089140100c03400780301c0d141044c0d91140100070941c007034442084089080e1380c3c0749406900061800710309030300a019088410003056054442190018450400380e00801d41d1420914060029110b1204000c00451503081b4050b14112179903004643c180d88070820004e2015007c8c0820701e202c250b010003425103500f043c0000341c0351003580c0303109854a64007281404081c0c0d42040600401900900741075a296102c080c107000c10410082c1072800b04030207034003003440c44805200300526a00c41c51401ca0300303a801d00c00118058a44403400a109030b00030b0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 438084640 1250 438083390 438083431
    0x3060d030329030f030712050f070606300807080f070525060c052a040e0f010608031201030609020a0801021801140a08150406080f1f02090612 63
    0x50210020120704034841468203910341007014540302c14000c04d154540c00504c81c00002070890b4440085813041810034a071101c07041e541003100b900030b0b900c010700320b5800e2080002e0981d9442e0b203100c50b2141c2660b0040381c6462200030190102d441604028015002004518046401400505906600c400d4428a010260340381d0628002c203a009242c0c0c86603104100011040441d0002c6005050340d040c8005161001d4407681d444c0c0c0c44484aa1001c0703200031404030010f1888001100054000800802044010149542d510041d244082c45103602e1b0a4002c40c07540c3c000001e44440701c070000c00004a681c02d5680f040054441004c049800616400c00407442071820b00180c114407c2c0c90b00240e2880d08501e0006103541146074014800315802c00480328915400341c5810345c041d2101c040c5045100c030700c1e004180209200d6101d803010b03000b00b0106600014010826003800403600c0044040084075280200403481460a000d500402c2081412540d0a10402c40d0740d020b40304440107503242200 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 438085890 1250 438084640 438084671
    0x3040e060d080309010f0b0406061e0207080a080403050d18060f030906020a05090901050603070219020a120b010806010806060a15022803020f06060604120c15030605011b050303060d0303 82
    0xf642d504c0400c0c2d444035001c100c0002284121580000c04990a0200515140c1c01602c001c01220800c2c110f4084902c0400050f402044404024001c01045424a16480c20651040c0e08980000c8419001d8201e104906074400c0040b115200c490402110920346840010340310a00858011407e02d0f88900c81c00d40803403010b00c0031b0b04001c5819115141d55158450800c4003401c1c0581046d80300b51028400d0280c119030000300d079001c240304040510500281c40c000104036401c0c90344400b69a11100146104205606040504942c00c0d80d0469110780d0f01d17007036401c0c1c55010495400341c1121300004200103400140c6607180c50110b0b0741c015070b12038806038000065a41d11030b120103100507030701e014030740109a4100180f00e0b095860102925140c10f20704000b9000744034910480c1c04a0540f1007115060050794407050b8014841315200314107003a00b0680240140440341300751070100d80043c0c0f040c8120001c00c502c508109500c0000f9514650b01c0001704211266461000d508156807081030340c010285 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 438087140 1250 438085890 438085897
    0x7150c060e100507230d0b03100f09030f020703020f01030c1b051c08040c030b04051e101a01170a020d02040801090b06181302011713030206071103040e060d08 70
    0x70700400403400b03240004000d000400170303600242c02d40030a654100d115030348003000c0e0750324005403210204180e8012030010340340c51545400491900c0c17a245e09202074010f0381c5d0203010703664469207850f1425042c1c12400ea0319503003c0d12002e5040190f4101c001007540c46030b070018081c0c0d98a403e1414104045180d1013200b0170180e00101c90035408440301c4190402c0220980340b080045103000c802514180c0c2c1c0700315804032948001130034000280301282c100002401b0f240350048400c04803415510140c001959a80541459824510b241104404420f12030b49022544620b041e156444410031303428528101100040050302400d80c281f0000960354014001040100f0408001082804071800d1401c0d60040c090040c1e84500c210300c0c858002401400040c55003e0307031400ca00607051030f007070006039070203050380300c0e91440070082c401040281d49000f0056003040f4001e030b08480655651100544094120740306520556009200c00c10a81d80d60f081000c0d0f1008010b800000c4032030813562203a03400d42 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 438088390 1250 438087140 438087163
    0x80f0705150105120d0e12010e1603020901050a06021c180b0d050601050405010906030e072d0b0f0904090510020307050c0c0105040b030a0b010309020303032707150c060e 75
    0x7034600100072901c3c2400c400c0f9481c06242c0003401c40c1d008402c00c06442010104803441c094062980e440400c10001c1d032200e40307034041d443c0588446420320f107070b000142d1006010032071040f10307030000206450401c168020183c41c00390f00244150700c185008020340c1801840e20804020780d400c03040e8244003001d8028002003803080b171071540303510700c002e45001503420081a86040100900c001c01003070380d2182002045411600340024990307800c01070b403410100103800c4600709600104041d050500c179405102c401d01041e110308003e071a22010500403501c954800d07004108001e01c035851062803e54880b1141c0c80c810022500c8540038040d50f081a038108a68000101d5004900075002001c01d10600321004402d180403883c050400740e24107a140400340422003c00c4c0c1c0ca401191299009034040d15501d038005048a4880c0303020300e0400d40c0c4142c4078071407442c0d00c034410070070417007600e00092030b102900c03101541b460740c0d00f16040c41201c003c0d4580000f601d000da11401c401514404c180032491488 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 438089640 1250 438088390 438088423
    0x6151a120609070504032d14010513080405100201090609051e0708060c0a0c050a0804050f0109030203060106140708120618090c100e03030c03030402040e030f0403080f0705 76
    0x204104910340c0c8100c0c200400c042e015049003810405aa82e003c4100c8064943c402d801503000c038480c11101a22044070140d10119820340b510b80420301180d40041036100c41100002c0c08280d032100c400c9083d020b2000c0c0c3c01451403105120601451a02c100f184a55210328400010f16619544601d0b06441201c0d030b06450700d404c02071048031418140780d104403401a264000b80aaa441c214980390303207041c01055901195404940c0304103a520621483c45c00c1a0820111032401c030043c280510658080d100b420302c519031890140308654000c06c8080c040300c3e00103002c1c0c22968a0018150350f0002d40c83d0300400030350000c00c0705000240300c000103807805989580008441d8900381c024800811010000c0ca407048242a080101c0d40c0e400203518000c001098880085d44102280c060342d2002c00b10400541c1400b011a0810801000201540c03040d0b0084400b0700079651407615080e142d01c540b031464004e00700200000d0000c03620300307801001b0601b20034146501d0b100c965200c590400301c074550002080c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 438090890 1250 438089640 438089647
    0x7080d0605040624180b0a0f02012012070504030f0c0305063402160e060f1219020d0c0801051b0301060c03080c04080312040302071a03010306151a 65
    0xb81083d201d09400341002010030051000e01440b90312460030311407130100812240000108100f549000d02d440107064000e4101d803605103108000e030103002c2c10f0007481300541c41e00c03e090080382c034500d50341304001200d100b9451516102c40c6030b041c01d24400a0891051013810400000040c5900040c2441d1501509841da042820b40c5450f03418404050200b0b125440348541d0401d4403036050301e00d8106640c88500c030110004220500360300f071400e9058079041480441c4000151403032100c1059210304401c992181034020300f60f042020781459480c815026600000d1480700c800c240c142002d4a45000034001c9402441d16035424412142d55000380100d86d46a5050108c5101000c400b1f89980d0000713184d041c2198184003005010550064014041018078000708401090542c02c503005444800241c03030341c1d01101c0e410280071110035035044005105213880000e03c8080101c910030528200c03050249543d00e1511010081c05498100c1000b00500c00300002d880c1840c1c1d038580b100c4968800f1500d44 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 438092140 1250 438090890 438090899
    0x1903020609120415030f0c05071a040c0b030a02070c1508150f0f0d05010213030b010b0703080a090203010e0f01050106030f0605091321020c0a061704080c010207080d06 74
    0xc00001034070003003240e4807800080d406005040181c1c0c0c00c0c2d441d001d15160f855106110114080c1c640d2003661031109150404c0b402616600c503004240aa0182c0c0b01d014010380e00e8403541440d460101e4015100d502c42c22010701001c040300c002150082100e85000d41421203603101c01441102076444201c4914155000025040c0c01400c200e6021240d403000c2442000480c002c04e8614081e841d01c64414000400400070968410407080403098000c80219110445081410b2050070f04e40815100325460400015540c2e1803002180c2c5d0781507055071a908141c40e50000c05000c1c0070300203012079140d52101504110f20008004002140000b41d00200305545051809030840344040740c564403060400f4410702150300c8040807107802420150000f551004903007429030101031004003030000c1c8039600c03000480b5160b000a40241600046800f2030541e66248000e071800c003080d02d074040522540c20000340226100340b001c0c00b12205544005440d00049540c0d144c51503005400c1c000415139503110500 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 438093390 1250 438092140 438092143
    0xe031608030307080708040c050f0118080606010314040302070e04080409020a0305150604060c0b0c1608120a05070c0f0318091506180b0d0b040e0c04151d04060e190302 74
    0x42d04881700e400c0860440c01c01303845000c01e000d854018507000341e004001040b4140d200c1e140b12a00c02c49600328402d1070b641c82c1e0b035515442e104161007003400241040d100402481d600300445020b2641500208602860b0020542e070040000380300f540c3c1b0a40030b0000154040b080d00040070640d05035900082c0700e10340180c0c0c4c2c0c203190f0303200d00c4040e0083d581408140709076500640c0031946143c200700002040d42d24074041c07000754030a071b49003d05000f110100f031030100003000d0068401d10025410711303803c03541d407d0590400c035081110000b0010b0b03610304000c008201000183c001150280c640031080080f001c021a0000c1e0040d0b00201100d50755141018060003200031040c05046140b03070480a05801c1c80c0250301d009007034058400c542d1b40c00514001080d0907030b803100c00e005202800901080400101894944c9007600040c1d000d2401c1114460340089540e295500380c3e4030008c000000e910300c0b410301c410340344801003080320b1070340d5141c1e0400120b01c0c040012006201081d2080c0e15891094074009 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 438094640 1250 438093390 438093407
    0x90a020a1703040611031605100627021b03031e160509100504030f0308010303080f0702030f0c010212010f030c06020304050319020f10030623100e031608030307 71
    0x4428a51012103404000c41020003254222503841c41e1101d50246417103c0d2905511034160312214506000450404100e0301044c0700b05042c2c009042000190b41e1a43d4003084100079014113000410f04041c400341000389980640003c02c201102c500d503d060b80d60100f407a582c8240c0f481e04c0800c4c0f01d00c81204003155095010f9901c10a0082c841e03294058261000d0200c0c0a66900c2e188501805040c2c910010310501c10b8400441c0c000400c001005103a0801524290b400e0005030002648a80002c0070304410840c010b01a419a500071490a2100e54503042d42d608200c200c20160b5400b0000c0354003510106e2011750103080d4074904904814514a094000044c05901030700c04d64000b0f0104100d5541c011540d903240403000024030030a070304203100045014019002c00c60303225000080200c4801d03410703808441074038907404812003c074411003201c10100c00c1c94100b00f544440c0c41030951516510604810180340310160440d0b40a0b2540b42e840c1c150041c0700e030040c410661021081002082c0d100205 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 438095890 1250 438094640 438094649
    0x180911091503010e12181503010b1e09090a02090f030604290108150c0c06090a0c050103060803070f06062106050f01080d14040504020a021606080f1f03020405090a020a 74
    0x4000f105030820388014a40200c006c0c0401c02c8a00a0310308150752910903200ea0322090502c84542d4039078503401e0b0500d030794115212000540c541c1100b62010001601c04554040000030507561065480b800c0250185d804508034035040103c00a500302c50f03490800800d4040d51003030000400450540d4000b84c0080c103c450f03c002c404015000412a00401042e490f0000c00703aa07002003000d41d10714030613030301e2031064000040075441000200b20310b804000c00c0928509204100c50030729903581c0d40044050750124003a48090b5001040342400003201d80c00404905031050708c0105940ba640e41901084640c04010039000c2c03103000b9001c1003001014031881e944464060121030065040c800c00070341e21044c01c240782c07040c03258030300f5007018100d82c0105841c01001f00500a40d80c900d00c2c20b800a481d95004803180f5034216588401044c0503000300040c5200300115100035625542d242e00c0c4605c0001c1d00c0d0b010711030319404a0b0020015840c0c501905218403036000003004c040d4003078810301c541a0742a130f10 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 438097140 1250 438095890 438095893
    0xa0302091e10050a141b0d030e2e05070221070c05060c071a0c1c0503040201050a0332090c100c06110705160609180911091503010e 58
    0x8140907142c0c0d46815050540003649003542c0c9408071391500382c90003000360b11070f103d400c2c00c080303402081641c0040c100e0465030311036000ea42084a14002c1039003a902c2d04400c0703501503000b22900d242c42460300803ca0350580c441010a0b00c148030b041009030122002906c0c40d40058001d00121142c040c00e500000322850940404181f80400c203448200c1c400f03646000c0e9600c6820000b83c4444426800c1010300050a408400c00c81509010314400c00d42d40c0c401c00d00c124090043c0e007450320715071400409401e405162030306c03080c2c516551940115900e900c51403420f802d05a03107001c00c560124054030808910004c1c00c040070840c50303488486c80031041c0003e000701c0c1d1a1740b011041802685802c9441030104005041180004580d403400300082e11110529403481a00441c42d04240040040c100584080248404003034a4440d58125a0201c0701d0288903083c0f91a0800c100c1d1000c441e50080340303070900071704090400a8401d40000e103070302d006446c5070200c1034190703c82207a81e14081c401c400d0b21098920 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 438098390 1250 438097140 438097189
    0x40e0115050a080a09060c030b10020c0f060304031403160306080d0212090409020915010306150806010c0606080a030e0306010504091502130e0f0703150303171b0a030209 75
    0x100c0240140b20b041109003c1012000c08691340c24040d1301304d00415a8051010300408000c0320303000707000700421078845109410b8040803103419400400d01c50702c200405452026217001000922220b075001801c01c40402c4824065680c0104222010314001c139544c400348856040300b810001c05481c1160004074051304250300f14900c0d145c00040040d60f42c500e4100c0580c460f80400d0004005081d000d8000c0d410031140020000e5441c418640c0c184d01c400300740c070200541d649030189030040113074500755200803901c3d442c00300e1000c1d030217801520b10f0701e44181800705015441da4401740c1002000d04040300072611450018450349410321515000d03100070750b8104800c0c05a0b031a0302c8010a003402c0d4503c4099400145405000c02d08010040030b0142c40c0341c0c8802c0c03410701d48083c1c400c5c54001c80e04000001d14020720100e903080040c0000d4201da41665402c607030300d0394800300042c410101400c034400080d07070052008440c2480001601d84c000003030f1001a00c0e61110000d0003060010400c00065061000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 438099640 1250 438098390 438098429
    0x9090f0c01081509040203030408100204170105060915030c041112150a1a0f030112060606080610080907030212070311040506010c0b04050a0b0a021810021b061e040e01 74
    0xf01e9002c010203e00702c800307100d603444e00e0002c0790440c456500b01150034014031203000c0b1103208a0300184116100054041321a00b1720b400200c0c01c0300d40668066510200d40e4021604d245503d032a22901e4040043c142c48080d000407000404941c000030411a04c0c0742c002c07807040710b080e81e61901c0a0b4003000424108000e10780403400241e000d072141c024070700300b0595050303442004040700051f20072040000e2042075403561100d588022544070780900300c2e1002c0c1082c001150f054840c0c41d21500500c0301808410101050807000d68034203600400c0c41080c0e1042e00c0d00000541d03a10044528036102d91000303440c2d5203046041c01928880c007000100d000d9400c200c244034503642e01503d11180d650300074841d8100f50b11240303010383c07c0418420018060b41e481600b400070f801d54030360081021024201c4a0f072105900c800c18050a5440c0010070030142e001581d5200361041c40382e000f0300d09401c00520f1540791905440c90081c00ba000200766011f618030110f8144101c0c00080d0020780580400d000c91202e941c3d10 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 438100890 1250 438099640 438099661
    0x60b011b05061303021f1d01020906030402150c070902030a0b03010e100c050408010c0203042115020c0705090f04030806030a15020904020c01140f070e060f030601050909090f0c0108 80
    0x1c0d0001012200f2100484249842440300b4260b50350307440e5214400d03401d580c0300c20016141100d085091105020f85401e44014140300b1582012000340102d4159651502001000c0c0f680d00c904103401082000342c2d10004005201c4400500060030700140c50f811301c10103042c1150280e11025019070b02d00540d0b82c9050b2030001c6d6081000d00a0400400d96100b0300c03004032083d000b143e1010159608041d40146900e4011010f8001c1d1100c0b08445e900105d00759420240c0d8040c0004042c00d100c1300040e00e450792884d10380090234401080f10499265a030351b40702140c0710b54030849418488003054000d00c420141c1c0103402e0f6401c50350440081030600c003242c55503040c0010340c800ba2148a54002903c8030f180d04e40782c041e94102c20325980204598200258560b080003008c440040f180c8a81c0e03000036880c0c43c050184d04015203006003550742080c04e0104440040d50028050a045c080f003842410807075500c56104611600202000e00501145005028584800200614140081c102c10000341000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 438102140 1250 438100890 438100903
    0x12150102071409062e03180b1303180605071b050f101116030501060801020c060c0705011824020c070303180b0c0706030501091107020915190609080703110607060b03030403060b011b05 81
    0x50140341510f89c0c480f45030540700e2074160350b2403001200c40356000058050b040800307441e000d03014240840320b015a0319405289003100e4000e11343d00160407070314111641807041501010130014201100e68000310b164481c03a00d0340b107051a07024100844410f0040160a000e481d00070600440298100411075040da912074600415409441d10301245c5213080c00001d40200001d030303640b040601c007214158280800704080881c1c0c0604a811005c10000c00030b0740c2803003198009021500074103070143c12b564003290050707813104c0460748000080002050f40c02800d0014104d40320b00000800e030b44e40c0380c0034010f02a108140c0c44a5160361510070000002081c1c20704a481065045940c02c14694440c1001100c051100340a25080000210508503402e000346820040e1a5952a89495180e55121040d5550443d01008117944542940c0306050f00344500941030b6548580004608110740002183c55500b1603031042c0d943c5511103143c940c0315600120180203440d840c911070f4040710902d8590580d20304 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 438103390 1250 438102140 438102151
    0x11b11011a1c0204051915060e06130b0408010b1305061e04230a1413170f0c0304030201030c111c05090612150102071409062e03180b 59
    0xb03246040d4498210300b2440c40b0070501c0d5009208220900345251481d401e115008400304425140c074895030a8108640c0351541124200d940e20140c58682c0c0c010700a05802c01c0c203101c5c143e9081410080b0701a60a20041d002400c10b0b0000002e20409903004c02013819554104007050900d8482801525180c104800100e02814010b00f1440f145440c04200101040315407500043d45884040158460184003180642800b4509002008960150106107503041c0c07580002c2c48501845d180000e40c1c00144014100b001d0501c01741407041c0511040e9540e403080690322007039000040d05104540e01031003090100d880900d401984038221055003a0340d9542e80c3c804401000e64000c2e00340295114900f158000700010308120307202c0e1107844d00360651520584143d105001904441c100552001503c2d00450b0301303002e04c641314150102c05018002c2d00c09426150090040aa044d01d80c1c036180b0508543d03c003208aa8480c050141440142161000c2072810b05403150400c0c01800b05281c4000640c100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 438104640 1250 438103390 438103399
    0x13093219021804020a091a1611040b060309010207030311040302010c0f023006090a0804090b030a06050106020303070f0f05040b0306181303110106050d03050d0e011b11011a 76
    0x42064044101c0c8501d030070b01d1956809400060142e0215600000c040101c43d442c5043e4900401c01890003c0310380101030750740c0c510210581c00003011031001340f04050489406440000d02a1496001ca003c59204481c0203c05a40001c2c1800030107505105203007098080d1082d1600b400c0c1142d000034001e0f400d10b00b02401d402140302c0d00078255960381c1c044120003495600c9100c1da100050b895050440c124801801141c09440000f07080c4000104040790341d15031016285242c1800c00a86030b0007445103900854146c4101c10800c00098014840d09001e009150011034491410b000000c146d070030b2034070b21a810081006400341c982a04503064078155a86a10600e4890b509c500104008940354801d6030fa400d40d00b0411f2200d40b50b00880b01c0e410150081daa42510000c12102e03250984505114054100021440003008a0322520181103031424120700400e00000d01c1a03414252a031039400c400c0a00c0c00d4000c2001c1040c0c1200d003035959041000c0003401f00762240d000c2d102d00c0e00c000420740c9009 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 438105890 1250 438104640 438104647
    0x80609040213020714010e1e06010b16110312030411010905130b03010906090b040c06030203011a07030e211e06220f03080103030e04021e1309321902 66
    0x10002e00c05001e05c2d504240100070007000040d658841c0d03403052424110b649250201302030607401140420403606031851140d1081c5401051807034425001700981c000c1d0740500c0d9203046610540c1e0144000102d003d400034203140c880c1040d003800c8031843c4003c1416410b02485100c100455150030005500030b000352140050329240b410702281c050000800028081c6180825200401c103030080701c0b5015038050140d546205031941c4003541280300030f004000007012246c80c18090014041c000f03000c0103202e450b0101441da140303404681c141d141c1900c5482c21089805a00803459010469009014058500e080500c0c20802085071941c4c4007420030552041020301c0080c84440100c4014602a4414040550040b21b42070040c800d0200307000c104d0000e8201c01040c0c03558038041c0207032104002d00091450046405208180c0e048d0301081d02c82100030046a40003c1091313041c851400c5c85c600d1501e0006004c003a6000c603001c210719540035154049480024400b01c5d010402d60780c00b10004c4a0310040c0d8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 438107140 1250 438105890 438105893
    0xc070203060c03090118050114130c05040f020702040203090f0105070c02211c0503011a0a020c010f030f09200a0f180603150e0f060106050a08101a0a0806090402130207 74
    0x2d400020301d1b00c44600e590441039410001c0551103103010900c8800003048645807082026028050000040c00c0310740342c000107008078982a07000b1949801c00031070042c90018554081400e036002110010303a9600301001e8460030031000e0180e11391101c6a860300e6803903046c02e580040d0b1080c0701ca0103407242c4105050b4130090404810030640c0d41c84d046401d0b16552404558400501c036500c00d000f4000c43c488403503020780c4030b80c140105072140129246c001e41005103072080115034000c2e070803281008161b19141d65140c400704c903101707841c0070b280602c1501802030303001220300601c0c00c038241c502406102080b50420960100c01040d00a540c0c950a09070507504030080150b000c2c03d0581c0014003020611080301c0103030f843d07543c4081000410b0704151919082d441881030f46a0409107d0710000c584200009007070300c2e206e0507040b6403044181d0100794556440340c0212114602c4005c403140310110000d2003d08113604000201d5208404031400025442d1540c0442c202c81984084004002c2c0c0200b071840 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 438108390 1250 438107140 438107143
    0x4030605100308030f0901110a0f0305060333100806060d0311060a0b010e0a0f1503090c1409090610060e030f1c030e06150d0515010b030f0c070203060c0309 69
    0x307008541151169031242400030038480c084900b9101c44080e58a81003144840c115440c0c00c3d210740a40c980c5410560780e40c0002c059004d0880107001319418002d0074441d41c40c540c445420000310010591070402005a0300420800805010f01032208d40b10b600300d0108240c03980000d140e98041000c0d02c0580b0904514a0300f621a401c0e25401d400c03450207100c04100e118040c03540f000e510508240d030350100410783d40050112440c081c0c007806241881041c0240b003103804c0f2072600344d031218071840c00281c0c1c10620745407030f071405d402e03034000d607594210124000050385000c89511707030080c1859029140c10b0910f495030000010080c81380800748001800f071541d140d80c2c21b10a5070320007104041991401410440c3c4030f44800752180740c8002103803510102c5203910100040d400d00c41c0020140c2244007100700c1c0100400c48070f141c0d0b070031500e510a041c44a03110000ca800a540205900380c00952a420031501d000d1180314002c0c60031003046010f000c400c0140c1e85c001103458200701d140d80c0c119a252200440742d03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 438109640 1250 438108390 438108421
    0x9052215030602030420100c0b0c04170309100f2a05150a0507110703140102190815040536010207051f050708010b180a030f02041a0604030605 63
    0x103082d030761020080000f4044c850000314034603441404000304a03400c403010440da542e091580d200000d402100f05d000012003040030740d40c0000c0410245030070540e461440300c03d8040c90350020f140a810100b100c14040c20085140e03243c12415040a200f020802440100800c51007040140641c86044080c81c290581010319440160450140c0300041c002c201c007291071040070b490320f42e4400d181000058041e80700b070030700c02c00005100c000b8208181c61070700c03110409000043e23001d099540c00c000d004084e00c008001d00185c0403140d1940300792071408506158000c2d0040018601a50a002c1003102281450007001000d98801101c1c4254072842c440007011100c002c624000307158130020382c9000340b0074001014407c048110752204c0e140618a0190000e4620540d100c5000c41c010304010701520420300e000d00041c00c01c1d40c9016500cac0071400001030f45115254000e03900ca000c0d040009095080c58000d000356020b20354495401010b5240c0410400c2c4103920014000669900202d1580c0c9510484c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 438110890 1250 438109640 438109643
    0x50a03030f1b08040201021b150306150307020a0506090105040b01050d0606090e010603060b0409050a02130b03060709090c0206060307060c0212120c0f0a031704030e100207060905221503 82
    0x71100d0b801815009000380c0c0c0b041d40e01760f0140c412064022403200d500b1b10405145000980514140c650340c4d03039000965000940a0340d8405008128070003411a1500514402d02660b40109100f000074104a402c2c040c0c0a44441c295906190800001c6461907110700e045440580b1050b0500b00e0609200700103291581041c0401e44c1030514a0100c03500541105046e680145420441a44018100b00407501030602c02005d90704100d582c0e40251401e0540322580c040104008112103007540006805c0c00400c85404010442203407082c81143c209100320460020740e40000c240310b091520010303681e883c40d8801c200c1080301c0300c0d01050843d01c500c018603003992031041c202e0b8002d6003188241d46454000c42104c0304648504c041c14002d941c80020114001030b019184c02500d00c106106a00141c10000c10a50600030081c00c2000d131622541c010302d8040c10a64041c000b21410000c000304201c4aa504c075512440802d18004050001181c0d215a01c102003003000966803401100341c80d604890340d00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 438112140 1250 438110890 438110921
    0x1106090901140429090402060d09060903030b0f010c0b3102030d050316143a1104090905190305070309050a03080706051008100603060e03030103050a03030f 69
    0x144409000e01c02441070900f220280010351100c8102860b40e03c051001d600f100d10700d00030040e15418000c1440f50018000760000c0e10300243c0f400d4500580b2034400049550607030b070f84000024141d052151101881c2c0469510001304101c0c00021302990032810080c02c00507100d00400c10011103881841c4410004541d850aa102550092055001640302c00c1c0d01a0192508503044140314070203c03071154901d1100758002c1c0488940499680219412903040c0b24001c2028801c4000e101c68801e03401002d80c03e020382904001c118440c41081c2e1904100f14503401e140711451411505025541560300031100000c000714103003403a0b46000000f280000e6441100d00c096030a0560203001800c40c07602a031181c000785607440c0d0620907900c11034803000d00030b10024000040000c21681003030350003420300c840d054009510360315000d040c071401c800d01032101682c4c0c080810403c00340b801042e295203288400f0718250761554032a03903121a1000744c01001c16641d14003442040c80694001d0004022100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 438113390 1250 438112140 438112159
    0x6030b060d0f1820040e12030903091f090506030105010e0105070501021e040320010909020a210e010b0604060f180e0c430611030a02040608010918110609 68
    0x10541c0c80001c0c002e400d0020303801c0d40142104117042c1400740f007000d407440304000c1c035180281010450f441c0e00090b001e150540410480490280d6645441103003007640040c031100c0f103170013442e805042e1015540c081c0d40180c105000400240ea0050740744044000c085c200141e40700000c4c58050300a20602c8005c2c065940701c1100e8202c0d00441e0005002624410700091000d8000d0401500d602000705400b0380c00102c00072810b101c40e0084c0e4010b003001e060282844405640007181e0300150348801c006050301155208403140005109000d1001103000580d80e0901d45030a00c0001440980300755034010910810f400b01010a0201d4000c500080c800ca03031640e0510b050082c4000810303400000d612100e9222459080c00b00e180720f02c0d11100c00041c800104010000c400903d010f0400e0011003a19080d0707031410428601c4e06c1d5080150b00c00c0d004080010b80d144d08180024141180680145180601c1c2868480030075a4a45220203020340040f814030042a540001400510600e1481034000b49000c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 438114640 1250 438113390 438113393
    0x309110d060c02060a0603050a030c0213050a0b0f0604050d021212030f040201080a0c120e1501092a14070804030203010218041a1807020717030304030906030b060d0f18 74
    0x80c0d00054209410f80d080c0d8103581c8032922507030b064890502000c3c0c102c0d0000310003480003a00420440503c5c0340301910015111001b040144100c400c00c0b69281a0356841c0c0891401c0c034a007401080d00e40d01000ca4165007003500b410b02080c4020701207400240904010308500d07010203000c104d0701c0135001500c900b2565914240d07440540d03611080c0c030121301041001000c2010003c0f0b40c001c8601641140e9614005803002c2c80300e44003d0400900c140382540941450341300320305c1070980001d0182c00041c1000c211001c0803031028040c1003101101e07080041d00b55810030710181d13200181429951444c004242c03101121f05003c0703143e01c2240d100a41c5903200040e080080c80d0070b500101d182c0882141d0070010040054000e19444103500c41950307008001000c2d24522103e1940c001d030b0840350501c100c5507070300c2d1203d052500c00404032400140a034004001c01040681c000d0000d03014080b20f2070203100d050015801715905000e8405040c203403507215042c141c5080e03066400003194655200c00c00401c6500c0e03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 438115890 1250 438114640 438114653
    0x13080705060c0a030b041107121b03020f0d0819110f071b05030d020a03030e150921130509130206040b0715110901081803041508070914010309110d 65
    0x2243c00000700c1e0401c00d20012501c0c1c684202d0711060035414400b89002e140340d46600264402e21843c070103200c0320340040600031880160307a0502c1d1b031207a0014041980d44031079052529030500a005d0800008034200941d80040a40d42c3c1170081c0e14130b1020803060000c4e070032101c8c18040c181b12800040804100c007014070141d40320152108020710782c1c2c10880f580340c409040e00c91480c0c071121400b41e80020003141c000f91007076100c1d0a0201014054408109000b01680c80b04003060b0340810f8103a11541c450340e040044c6021500e140c1d65651021450a41800320702c00481005101d22442187d07458000740345a404506024800c070b50041c4016134481d02c5989000b038641195006940c1d103501c0c501211a038980340d214815070045448040780c144582c42004603000b02c001800303815003c030501c410807500902000580003030320070b400d000c5034101c0007040001c2582900810800c01c01007001410401115034954026401c407081c039011178180c000e4181480c11196140510b03400c82c0c659190341c0180400f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 438117140 1250 438115890 438115897
    0x10c0302030a0b04060f12060e070b0307090609050102070b0a18030804090e0712240e0309090f0f040620041806060503010308091c0b151302040e13080705060c 70
    0x403080c2c00c11007003810900380f02c21902d450107929448102d8900038890702d400c0c0c0d16001c80c06032246401091140a08098070b040031840d1340085803d00c004400d000380c0941203038030030700a0903032403500701034191400000075510400392080d00070180c3d00240004c8034504c103404140201025000785907007540c1e24644294598001d02c1650117461600031041e407841030100c2e84908030381c00507283c10314030030742505c8090f01c19910824003e540740501c0d0001e83d0784103c5015882c0001d1100014540361030b40c0c101030110078200104004c2c2d044100780200052b01203075426168025410181c0000c41007040ea02e02e504c140369110b81c10780c041c407000c40c00040d04003250720b00b003c17103112804080c00107503614441500c0a00081c08028424082031010315031a0500d42e031002241d82840c01c0c10000c0c0081500c1e0003010701c00a13594940960382195268016040440c2c0c0d0268042d11b20313108615181ca131406800074084003904280a0803001e11840003807208480607580e5860300001034a004bc01d184144520030750 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 438118390 1250 438117140 438117151
    0x50604140d0507060c170403030b03010507140a030f0b1306030606050a0f0608060604030605010e16020c01171e0c04082107020d03111c1106070207030f050f010c030203 74
    0x11000140080040c001140030841a101c98856504001c8030380c0d200c8024010003108181048a80b410340c51000303800d80105e0f07026038000e803000030350b41041d0400c0c1800c0d117200030500418003c0c41026520340980e03200440b100c144240c0740001e0003840d260f0012001d4803841c1c00701c960200302821000010300441d803018007140d21401080110319640c400b0320102e1f601922405002d0f83c51203804100140c05021007680c481002049585003c0c0c0b00e5442404440c2c0c2a0801c0301c00d21241c104000f4211440755051500c10894001065803c2c1c641c80024105050321402e02000818400414181800e80520181048004143e01d2061412184d04601170308140b0413520103102d501982105010090382413403e10300c00100780740ca00b440907000d0005c041c0085100300c042040e0048900c0f900641405500000c9061a805c0f22a5640c401c030010240e5a2100d8008000d070040024802190b400045007400c807507000260840001041c14000d0a00a9486030000c4a50800548448503541580110300c2a0f = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 438119640 1250 438118390 438118403
    0x190902181c020a050603090102090307090b040f11271e0109061403160c02030d0e0406050f0a032406060c030824040203130c0f030309150c11010c020d050604 69
    0x92400d0480e2510010071400081c1d040645080180301e42d061400c01035501846420000d03250201440110303150404030b0344051440e680d200580b80551400e40100f0300341e040700820501c08e41c074440720105440d100c0e100025250803422203900030400510108021030842c004c10190024844007a015005001001030b103000441110f00480c240d4020b8050248a00c0e41c0c010250655440c038008040d1b41807200d174640140240c01c4550f60041c0e03010440500b0100032a43ca00030000c0155050206903030340703078201901c41d00c1507111084064a070f01d4080c4c1c003242c0d0040380d2680418028040400c402900040c441c100604100002c0713262a0007a01c8910114429520402655602d100010f8044007502d955850f504250881c1c03881481c0940195801071a0121801141c1610f030396072244c1490b10b94000c500700c0b09414000c00070306801203a060000e000ca03540d00c1203048905074000341704900100005140303c1c3c4100c1802900d1f4465504c1a075095400342c4500c6055050303062555a4981c111800c40301d0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 438120890 1250 438119640 438119659
    0xa020d0c0e1b0304030f0908190309080109031e03180804050f010503040203101a03010617060705070f0f0c0b030103050a110303090a0612090c06120b010507080919090218 75
    0x10750b1400c035054101881c1071070003401d41d01e40355411502c000e2820f60120800c180c070400482c140d8814032110440140c48150f038120407540303103800b900c00002e951100206916200d805808203030062003003514074410400c1032802d0b02000c402a0010240b0b040243d20111420700704108026807070000708140d9400f11180c40340c0e072211302e004440c503210450380250540c200c058015102c2145d40c10107880050b00e2100340f034404051801080c00c42e02542c1c485d450f00f56040d140c40b407a1180038000340307402c41400c0c40e0062500000c2d440d0891082c0ca03181c4c00400d0b401a58109030188445820700001601200c046155296540c2c200f441e51580b9070340060f0303401e12000b801e42000385000021160309a40242580c00c415103080c01c1a1103100d40b02204402180e21000c0e90000503494150301c60140c5a9900d802c07000800e01158101143c00d2041c070141400b00400041c404108a10255a02e402044034804481030000146501100103540840a40c3c0c0c004a441141000c2c000c80300080c6072802e0705d4410b10b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 438122140 1250 438120890 438120901
    0x314010e0d0914420f040303081006090b0c1009060c03150806240d050d0909090506010e06010314010e1504090c121e03020303010e0f090d110a020d0c0e 67
    0x40050706030700b60004500c1042d114036a0240d4002e021306107458141c0403183d180c0e202582621164450f003040000f22900107400d008054120700701c0c03500071220f440c5030101d0900340513005c0c140c0b02c002c0c01906140b020104404c0c122680c1041845c0d00720f070038035205100d01801032070000c000d010006103900c0480d00b0315104850481001711200d08459a600c02080107445814626000c503034410060718020761055481c4020740c40d00780e6000f5aa40c8100300406441030342c040001c2903a181d50700701d42c168030b05250340e10b80419000249541543c2c202030b8084061b444030001a002440c0e40d4113541c44984160000096180c9540c2d4110721075038000c04192034520784030040204481407803600401c5074842140910845141c2100d08919601c103814442144d04a1803250140880800d03003200164400001800b10342c0154002a8004016070111652400d00c0e00007107845150455940081240a00c042d0360400003c00a04800a030050003445800b0003d05020302e07506900d00613440502c04803c081034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 438123390 1250 438122140 438122149
    0x9060905010e030a0201110322030204060501140d0c0e090a0c030c111213030209090604050c011b0f05070f090b031c02030a0507020402090604060c0501050f09070314010e0d0914 78
    0x12100003008018041304185540155100203511610283c0c40c882406404022036080c015004080c2c1c0995010512600c0d6104000c2522050780203207040002c0002e43c2d5170020700842c10781740b400c040b180d004143c0204264049540500c990b2001707910010030b5051201c0440c5603482811800000d94040c003540781c7d800c0041e188180130616502c140d03482920101e81d400d09403805402030b060101d10010b00560341c0e80000b4050345050780e01250a8001d80c0500040200c2000003001c801020709003103100000c000324080500c40e1084014000d1480e0028035410480103000b0314024140e07001d00e6910f00c9881302c0008004080c00c00c0028020b20880341400c448006c813061080701113080d035000794981507000c1000c5505800040080b60066001e02415265a6992004d04058801561011207210090600c1400e45e4000f90452a06070851418012a04008900c82096070381149030400200603d0800f980101a41042640c66004188020068079800006070044401d140300107009000c1990400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 438124640 1250 438123390 438123407
    0x2150901020307241506080a0902101209020402031807080a050319120207111f02030a031104031a0601020609031804090303020d110301051003020c06060f031c0906090501 75
    0x40e025902c14008400002c0914120711800e800c103181c0380d082681c6555110040c0d41a10f011103080001d418401d0040690140318180c0c40481c4070024007180c5116004107942c181d00d891003004015511801305210b141e941c200100299010348115600c0ca01a2020b16030320801403006a91402949000904020000f508503045500300c00910324203070604861403070074082a194207013484034100d80c1c0c0844810500c081c141c860701480c2080840d081031010070035050595104001060500d9a100c001c0350350010a50b40141c504c2c3c14005000048104040001c0c06140e1009000c1c3c8214403001c03228040f0440c405010b840d0a0b000c80f4507686442013001d441c3d00400704a0500301d4038107907104c00b252a19400ca070320000d000e418014500700480300810150b8424055805090200200400042c14040001800461a4a021400c2000c220a01c586401d000703442c6901c0f440031460701c91300c07582d428080604004505c1d1015402c3c18000500a400c041c1244910030101d90392b4080000d46e9401837112 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 438125890 1250 438124640 438124657
    0xf1506030706030c0c0b01080606041b0e0f0f13020d0b06030f0408090607060c02071503060303091208160b0a1a130f0e0703030302091c1a0601020a020612040215 71
    0x1422810341842c80480040680d00d4200040040546494001c540ca0700c4450713000c1d0040030064582440c00e0340c14001a200c0180b42c10300220704c1d40d0034842c605540128001c5040a0444d80c102c040518100044d03002c01c50100119880407083d00389120901b2254020100c41d408d6000c1401504681810401503010440d05038000150100000300012031803070041462520043c5060b09040036034807907030201c800d880c5641016030701056081c4081000700001e041b1400d00c501e0240045411560b004092036424810081110002c82880d02000a80b42c2620035107070031440c03004134408040c140801c0500c0c0689042c0c1c0400d207400e0940d0301100320700c20000600000904000d0b03601c40c04402800091a440081840382651303580a0b00544400b0710140c5c000314025034015031070b28048030400444003103d059200c0207071a00c040d017800182c03140c0e41e12005405440c41d0700c8811345d10100140d04180b22080c0c000e51081c80000c2c0403e00c600c51415440c05603000b0b541c84002238200c401120960b101e00e451 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 438127140 1250 438125890 438125893
    0x90907031806020f1b010507090803031009090203010b040203132603040b0402010905090c04050a091413050c0a06120c03091104020a02070806010303081b030105010c02010522080f150603 82
    0x4505000c241560001d00e4000031284e441031030003922203203620215186110640160751900140907519501a2000c405403004502451942c101072070150100040e900c02c0b120080d0711529410701b035540a500072034070101c01602c2036549203413415a5140080340c03100126102e01c0d0b50f40002040d001098030040c010031516050a1944c0c0315034481e04001c010040c0101d0401001c0d84002c68103840307030900607018059004c2a01d45031802c000400a03c90403a0300316040d881d141c040640f00c1d495030030300d0140e041600a00407844158180c01d00c1c0d8101404e0070344140d04003078004400111030b0362281342007103402184441000600101c01d012020396003003840c007500c000d0080f038400134503140a5004240407000347c0112000990b41c0c440050520740709900076004960210100070000200c0d20148482540c80501e4503e19814100083c0c0700303861146010741040300c0856000c100b43c40100384428101410121040c0050b501c08042d5036525009008040303d0050401d07905580407401e1040f8040d000080 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 438128390 1250 438127140 438127181
    0x60703090b0a022511100302120402100903060212010f08010e1b0409060504110109080a0305030c030a020405041a030d0e060d0e010603120f021c0804141f0209090703 73
    0x40b00070700079400c01e030510003c10b111a5080c1a140740b42d4840d6000701d030300c95000051001007100410195a0102403070a060600400100c81c0302403e252046034450780c1110700e10f1b0681c82e80002180e91010640000301b055200080401c0d1030f42120381d1180c100c44c610f400a69165455a90260995000c0b98081440c3c0c0d020b5a04010142070300c000b05445030b580038000042c121042e450f0381c0262076003500c047d41c00a0050350f1041007544e0000320f13071001d003150300b000300400d845a56005045200c01410000c02e43c81c088085488400d0b80c0d0100d5006140081040c0040e0806c1e510681600c499011094400c0c841c4281085081d0702440708000143c00060019040444514900000d030500a4030001c0035562044007000084001c00f002c0d03100c0d9170b0b9655210b511208160040d14002d548001680c081291704103003c5500d512003000d03548554402d00041448020348007035450304904080881c460000074030300c0c0c0104081c99024022503042181d0f00005030f100c0c110146c04542c501c1031882c08030000d82 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 438129496 1106 438128390 438128401
    0xa090f051f0804030302070c0b0a02011a0d0f02040608070f1d0f0705130f0b0d0506040c02031e042606090f030417120c030408060703090b 61
    0x192011400345400700750001071000c810401e00c08100d0b0010020303003013501c2a0141d070074095002d03001140304d81e03e82c0007121094000d20302801c0150f1900d4168415550781540002148134050300e8034030b1150702500c403000542c20f0010181d0b0040d4450000040301c0764104440001400090000851541841d0184429212080a441c168010781d41800030604051400d01d42000c12401e10640e40c00000c0c02107000e1320380c5540301101c03480302c03408009a18030000004015a5198200c01c012582d203000802003101d48031103084005078820b01600c3d101e401c50390100640c8980c400c0c102c074105643e40c10160229800340c0b60304584801c8803a00200c40000821510381c210250070064108100c18034000e030b540340501c0c420404521382c0e1030a8008011000e005060742c020280c4d039000d5540c02c03030322001d50b500e5205120316803441c0314a10010341d00500c6889282001607100804141e0398441 = true := by decide +kernel

theorem cover : BRFrame.Cov 437949640 438129496 := by
  have h0 := BRFrame.cov_init 437949640
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437949640 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 437949640 ≤ n) (h2 : n < 438129496) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
