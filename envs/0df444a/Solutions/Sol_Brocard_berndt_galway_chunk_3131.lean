-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3131
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:45:21.596971+00:00
-- url     : https://prove2.me/submissions/1fb5c3e8-b206-4dcc-abaa-40e92277465f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 562949640 ≤ n < 563129496 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 562950890 1250 562949640 562949683
    0x4080901030f0207030903020f031204140a08030412030e100f08150a14130b01051b011503060e0706020f031b12040f03050c0d080a0c17040b04030221 66
    0x1941d01039084035a18044001d4115035818003418000c00054150108a201d1304001c5500c0740c103403900281d0154101510300703a0924041c64480f041c025915034841c0300b5040040041c00166580e0180013030001403d100001034402c2035103140040482801940d8031b0320640241c902440e1080c2c1c4001d045013811034600b00f40040c0e854400131013103081802c203843c65001c004804045580c0b0405000001490000c3d603000b45058800785102d420340303100201190018505009002c4291100c115485009609000004540001c120910402d03007154100f81c2c0e0454540c1c0c1c4c801d0040804020402c000c100034405002045003580b092503c034491050b140500c0c0140465141400c00240002d0f00c60300d040074103541e5100e9440b495010030900910081c5c809028041c0c2c08111400c1035a9002070407548400384d1450700d89080c03020b55480c2c1c2d03000c10540362b2104824590320b00342c0412005102902101107500e40303c52440c41008130b11a100d044010a04003c90341d99550400300140012040444040a044 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 562952140 1250 562950890 562950907
    0xb011d010c020d06020d0c120c02150c07081b0f06091b0f030a030c0218060319060216030207210807080c1212040308090a0201021203090106081002030f01120b0408 72
    0x5071500d443c040581801d00c00215010202119070001e807001c203030303611104502540c6010070411510f20821202c0560445a04940004c410352007d6900410707001001d4101105a200c10419070003c2500d010000c8070b41e40d121015950070032500c40d0180c28080101000d140c460711441d122940000000c585102180300000c0c1c0e079039801031000c3c801c038001c1c04450340348010b800e00400e036540c0c68900341d001d00c007421108a6000c07409070034a44074200280c0100009207850314000711307141d040881518680ea0a200e20403c0c0051010a05040f500a034004c1c10140e04001d2040c0c110040ba032040385240c0810344c10301c0c000518520503240000d030407462280d20707400c4141200303007401b0100010605480d40040e180d041215542c40c0e1902482c06503688804954440b858156200c402c0c840113400740e806407610b94400e0205000856100d40070700c001280d00c1c2d82e900d079410303d46195040b11080503038000c41003020034051214802c1c0140b17104d501080030f41d025902c4e10342d0300c60030103440a810040001203801 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 562953390 1250 562952140 562952149
    0x3120c0e0607050606041d06041b080a150c0509011b0309081510050108010e040204051b0f03092b081003080c030a03050108010e031b0a1407090b011d010c02 69
    0xc08960003a15480e034401c2207107007142d04d40c40c007200c100348907a2501801042e242ca07200d50140d12003004c10000d04803511130340c55940c2410003c0d01c4050195200325408149003509211040440c1e1095110070441305104e0841c409560150349500200b2006015008403aa401959492400904070b44050420319909040f610b80e02c1f5900305aa036803244410b0510704948140a29115003491a2440d00e080d03201c20044800600a00c5504005c1d2105404100946015030007946c102100d0000481428444980000d0710b030003802d03420042c0000401040341068040c04000703100035010840310700783c1100c400c1c195525400540404104002100098000b041c03034003d00010b1a0444103031900c034810303260f40c40c1c1d036075000780300081c0020706100c00010750060500814000f1440100074504141d0190f040d500a0652084290703042d100790304034039010a507804c0300c000b11100c81002600000d070800e500348041c1c8851859070740c108590600341041c0b814460340140100b480920303154007808114000203 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 562954640 1250 562953390 562953407
    0x240c01020c0607120c0c031205130b0c09010e040c090e0411031c0e01031103221502090306090c152b062606070e130203040501050f011203120c 63
    0x401107101c1c1000340a1204d8006200348403401c1050341c10b21480309111412694209210001070100b52100381070b07484100140c200e15489100110410030805640d11a0400d24200b6520520845c8000420840300d5030b110b034800d40030b08001d50303060090304488007000f0302d8612240f049131000c0382e841020038100180c0c0e460180303154500404541c3c04140d840d4450056900310078011000c500804003100303242d4003034021843c500303606040c5641140d843c25128940b02502c0322005800791603e00c2c1c9100020b101c90100418800b84000c01a00c504d07401d01071618002d00036200464560040350882620768510702161081d02d00d000c4050b8031201280103e02840210f0b024003800c0c03108040120307403000a250700c031004450380300200290000100701641c1c1e2a14140b102c0100c00e80103400000e03140c9002d1902c00040040207801c00322440a50f20000040b608107440c200d501d039444d00140807004504804040c00345c6200552060022829900901100f625030409203606e500e981c418810107008801e0ba = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 562955890 1250 562954640 562954657
    0xa03320403020a0b150a080f0705010518031e010b01020a05030d36050607110c0d0206250c060e06120403210b0a060c0308040303050a0b18060f240c0102 67
    0x507459034140100345c0c000c11203c0c000d01c18041c00340c151000404020010350840f0010030480600805030038100115215403003041580d40711001d0270000300158a007080442c0003802150a100010650441601d003541d1010242504560001c6060408070340c000c0102d481c900640b50001496105403030b0011700c1c40908000d10341c1d11030640c2001c4001d661200411703e04032407084080d260300e5601d1180a68800c0700a482410182d4000700040342c040c141031229110450004000d58180501000d0408850320550308421030081c450314000108000910120003402d00390610340d00421910001c111180a840d800c0010546131f03c01181c02d041c01250003c00701c402040c20641c1484007851000d000c0d1000712101d03030040112650000c4c19601c603040c2008190740c566260803158a5036282203024000103006925a41c0c0c0e1104510595a18542c0819072010010840c5000c0d00c0e01c102081440030319400900d0003031034081005810865400303040341c0700d85400d45c9529110a0551141307402405010381303 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 562957140 1250 562955890 562955903
    0x3100b0301060201091103121209010605030d0207140a060c120306030506100503060c03040b04080a1b0b060102060f060a090f02090604081c021507030c230a03320403020a 75
    0x22400365030641104445500406c100c0c550411510181941c0d0544440c541001c48400d00510f540c45000b035215581003085100042608d03a200c000107418038040c40d100502581c00a007040203e80003014540380c2a4004940c000b8446107403400241c418a11484020070700a04811000e0f00300e4007036400311001e0b640100844d2514a0101508003d0000b2409440d129201d4413001404110164044a1003154010007206403910b4650b02c0c0360841d001075a00c2010300c10784003148101403424050440071503014086403080c40c1800070000e410081e01801c0714a001001f14200075445e1a40301443c0126060702200081c0da51700c401c4500028082d00c0c2d40654465400200006d40300c400060141014404a05400d2445223078902a03940e03074004980c1e0906150400300140aa50281d481001150f04070700340340c07000c80340b41c0e1100d12900c072200780001076080d0045040e010701030b494810b039403ca041440b004140d922158038002c2c001c9040c0a4444000548a0001001c143c420300800001551000c0c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 562958390 1250 562957140 562957147
    0xb0a1406070f0c050f060403020f091e040302060109060806100522060e04032d0e0112020c060a0b0402070c0e070e0915100306050120071d1501020313060503100b 71
    0x10304100d0024162289500c5045c1280fa55549450250200c0d0101d907802030445c0038681c00041401344a100007000d629180c5903403040c080040309640483c2e4070a40c0700c2d0b4040c00c45581440803000894020781c012078800d40c0401c0421512600796003191007640e8007210300540d1071010740c402d00d4801d0b0034030461464103402c3c1070000404400c4604854000c1c1d00c00c1c0c8138000003421884510380348140310700a41c0b41c041c0700c94042c80601806020b8842101c1c0d0107141c041102c01010301610309991009190010540c0440200030803014544181d010107002101c09519003041038990380500503860260503030501e0000c010640c12405850b421301c090740090315031310503440c0009020500700f060441041c000c2d11003240500a8510911030310098400523144e2406d00b4010a0000d4015152580c080e01140300703405011451b1610540220305d00c0034200c10030803d42c940000c000c40d43c031505504075030541d402406854410302d03007551540190b50983c0761907602d95a82001e01d00380000b050340001e10824002 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 562959640 1250 562958390 562958393
    0x306011d1005090f150d020702041d0c01080f36011506021002070b011202010215091608060c0a0507030903060f020403140c03120f1b0d020f010b0a1406070f 69
    0x14082d11020300204d0f809071840c00c00f070040c015140908016800c03041010481440142c00541c054024103001900001e030384102d00005400d03e035118142e80e40f1a900c14041c00c20a0740c0c2c40304210b41e000b101000a43c4240c280020b604107001c4900481c081109045440d1420030358031020782c8175049201000230300024a0390342900c00c07851400d0040070300600549481c1c1d954000a40215a003290f4450104a4140e01e454601c82c40900403010483c114012501810200c0b9005c61001e4000c180080151501c1c80200701164036208243e0302036801d41e080041000903020702c90090b5005a0628240240c0c0c3e00050320b0100d4600c0ea46801c010a22440c0200031162503074243c4c0500b098910516410036540941c801c07035981c0d242150045603040d071142c40c018110002d88400f41c002030014680300c60400c80700d103941404a000e00410500258410b9172000c01999042207005040d9081a0007000500204000f14003082e010b4040c0200710b48001c000d2100c1c944880c012078440c69044039000700d6a1050303 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 562960890 1250 562959640 562959647
    0x2090f090c220b0a03020a12050a0b030c040b030a03030905190308160318060209060d0f1418070e060112020d050403301805030307080907090608030306011d10 70
    0x140841a000d00c11480c224100103518a00b0344103079180c80b2081420000d03d40c80850117584622618030400184504112001030a4000c0d540108074150001c5550101181850301d4101c003282c8203480b560409505c02c0040d10003141100e0003541519000c00e0340703d0700f41081481e11059a6050707000070441500281070581c80b0720b01d98019400b85200c0c1c10307940c0e1024003c8082c0c50002c43e840e1a00444c0444d04170010b5404d900801a03070001512090038a07540c0c450b040200c0f07685903910201c0d6a03d0305010403e4000300124107030300c510341d80464800c551681e000305940b40304c1c50095400411988001c070360283c0c01940e15881d4a80c24902c159503074030a104000010303010541d02100812641102e042c080201e20010300b00d44200c5000e002d944107080c55150020b04000c18080383d8100c1909450404200c0500080d440750226840f0210313a810071107c09850103000d688a070b400945806418042c2c4500801101c0c0c00200901e07203c401c80d030b1a1006640160b0000490a40c4200b030440840031080d007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 562962140 1250 562960890 562960897
    0x303020405060d0e1203040b0f07021c0810050108010312050a0314041a06010221070602070203060f04110a03080a03020a020f1c200601060518191509030b0a02090f090c 74
    0x1911003911001a0b4002d1aa0b12a00091f58014200751030031001502d202d1070000000c6e80411140704403101d4000480b450340c404560340b9682d000084100c41003004c015990310000c0e000341400e01e4030408070361451320381e043c0b4400145205400c1150005a801e0382e00c1c4a60084a055030041c4002404c1e07080500d440c0035403038400d01014011070040000100107600100d100b12046031a001200c03075840d0182d42c00c800310790040c001120019804e202000150700c0070003c40c7d12903042e6a003c0411030900381025004034202c20049441740151840c01e0001401010554407070100c0303802d0140e00d80d00040801d0341080041d04043c109403181d41402d03005080c4d40c0300e183c18074100c607440d06002e20290407494440301030b00c00e000c03580300d521010040020a1103400109200314090042c040c003524200009058400e07124098074544200c5002840100d03000703c01e04041152905180300c8062840c0d54159440c403004200103041640403d1007111516112030b010307013035074000b884103007903107002c5007071080350b40 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 562963390 1250 562962140 562962161
    0x5120706110d0501090c211806020301030b0f150f01080703020d09150c170112080c030a0305040c09020304020108180f030c01020703020105070918110f070507031407210303020405060d 81
    0x50402e85c07081b400e140680038415106070003110742e00c10700301440304000286c001c0c4a1822960b00314240140c002c20400d101440c0039602c103085850190a255416041e61600981039032294545041c09217026500c0e408152031141c1e082c20710b01c16555524000341e00078020340040302d0726142007500c6074042100044c00031040041044040007804100b4008071004801c00001141c2c19030480300600450398000003200c20b0074460b288c000e140c0001c046045013541c2100d011000425181e4042c0420807640c07000c848007414503a0030850540c80c198000034400079025059003940014543c464008805c1808a00c07074010542003280c1c0e03291001c0782502d000b54000d80007907006510300000314102c0c5106070031100403103104c503203000702d040d43c1c40b901d1000501c1e15180542620400b08801c02c0c00c501c0380801307080d00c140900007405000e4907604102045034003102d050b2003507800044061000301c6003191312041800c143c0100990b00030103407400307038003e1246402440d80802c000c1242c3d0401d0301a1b070458050b00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 562964640 1250 562963390 562963409
    0x809010f090f060e0316050607080705180906030115060e0a09060501090e0c16030e031b010c08090a050402130918020f010c020f280b0705120706110d0501 68
    0x20002080d001007200c540750030040505100c01d0301c500104106400007007508800b04180c2c0d00d042840944085100303800c0004803695000035041020b840e412643c15580072040d420705502c2c200102e00901040b000084c401c911070b2100d800071460300c0d1025444012000d4014100042107a250030015010503105000d8620441c01124045210b0b1041d0007517404448040e1603844109090032209001c2a00052855260307034030511140a2036140c0240300d0360b425010341c41d00041c041200c0141070030892003031460a921308180300201d07481d0741e00085c600821034110305000c0d01e8209906c002003500300744d031f03000e00da0160001c1092440280b020048904643e441042000358681941102032662030701079029600801c2c1d0304e4124500d50081840c40411803000f0074100d08002044001410a401c8005040b09104500100c40880c11021062805800e071307007060a00f0640d8641d240382c0d44000d00c0415146807400441d8690801c0f22540041c2c1e07000c803810a10750b0315039081103407020042030244540002c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 562965890 1250 562964640 562964651
    0xc03020f010e011d1908030a090803010e06030c100206180a234b011e0e0a0b0a0e0f0a080a03110306090f0601050f121602030a022a030d080901 63
    0x113240c0001854000b080c460310352001ca840e81c9403070760b0b01a500010904403c080d1100058000101910021400b911504c00c1c6000a400d200080c14074043e450340000f40202c143c0c442d14042c00f030f000907050754040101100101d494202a20480c2407042070103000300855001400861040010280d075503003d002c60b030481d000d1200c0002050550400f01524010918100e000c06640d03070002c1c1488441940300340c80000107a05002450350845040c02d4110901840074031100c42808802c0c02f80204190b0070100030f1000d0003842c0c540e004160790140180800c19503031245541c40c00740a002100140010a096a0b40c420701420010415400a01c01900091406070030810300f02e910001c0d203001c0c2c140038100d80e40e00e6990214018409001919583c14007600b4080c440030004040c0040070403408000100e041428525001c10401400500d0f40c401c1d50018070108200590014a41210b0707052160310710700d01c1e401c00682c0a104098000140d0300350240502d528001c91300100220b00032100e0340c1c0204034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 562967140 1250 562965890 562965941
    0x14040203120a2d231602010507021309020f0f0108010e0702011b080108120301080d03150513020403150c120c031119080a020c03220b0c0f07060e060301060c03020f010e01 75
    0x910032840e5885845400140094100f1600402c041c175080345c410b05090340350001580005010741c07418402400f40680340c5d0309003011414441100781f640707041501c0343c6c440c03051210006043c0c00014010607000ca18080000b400c3d0030b100750040100b03201044490305034251120b0008220280034040c603103c0e88540d68900c0400d207100c0c002c0340e040700c41180c00750001c101010030490240a401d88040d00e03184410501203184c1d41c55070031030502124840780c0181e0312843d41c038000303440402600c80d104440f803421040d0845aa0000310b10150300802110009440c000c21200b5002030131000c00030304001d880800d04035509003d03040e907403e000e4020344910a07c0d645040241c0141d05c0b4074100350340e45400601c55041407141014422100c2003240310740100711601c1d000700c9021074000142c1076109a100c452151100002442000301a010383c0c6440c046118140340440c1070380c40184100b20401900001070801c6c14424410325250b042d41000a2069004807039105000e0121009140320418082800c0306 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 562968390 1250 562967140 562967177
    0x30c08060906071706030a12030209010e27190612061a01020726010c03020418090f0809040219080114190303140d060f0914040203120a2d 61
    0x10711030b83e00c6075102c02c0d400c8842a800d000d003110241103650180319010f0a500029041100040059070951700181c8442d0380e07600040540c00c50414890080c00040403000c03002d0814599aa0005600b201c0e141203a00d030380950400307030782c69003070f080c0e240700e01e01003010070440541403500a10074096002442240790190b641454980600702403800369004010400c0024144c0c00c0c9801c81d8000c16511848085501031000c0c00c2d0f800c41000880040d600290500054004c02c03400800c41d40110410010b040340d81d61000114040c80e90b0103480b601d00490a00c609964a070100c45200c0d1400c0c800400810f44d02c14060a40807083c040d080c0c180c1619292010103042181403a54034101032501d0035151407071a141540d21a080241200398050100041d201c14401405680000c0200900c80b0364207903d004220812076062080340e94001c41405c050101680c0c0014000240990803150203584140d0814140c0d986100c2a141115245400c2e814550041a050565900e5403441c0c07240806040001c00c10b4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 562969640 1250 562968390 562968403
    0x1b01050d0c020c010905120c1c05070810050906010b0403060f0603050a06060e15010210020d060503070f0f050d0222180501090c050f0108070c0f17030a0f11040b070c0f030c080609 79
    0x1d00716441000c070700c40c0c54541030520318140d949c44107510511000300c3e2a1182441c0700c50300074030410fa01000e00002900a5841b505030b00c0a0303100e002c2c190340d50400003095018401c51002030f0600d80c490844c000f810100e0342c407000003158480c080f01c06020740d43c9001e4000d4483c03441501c0107000c1801c0000c5650f208199205060301b8140d024000040c10841124001c1d00b221032081030b540d41e15180811681c40800c00341f4050b10880c0c200d0b1024603d0308902c04000625500418003580411100c20010f0719200481034921404048408450264041c680000c0408050280c11860f160300c20030140041940803580c0700780501d05040940b929107062000c6070070034461a60000d4a000d000596a91003501812802481404d00191070501a15920789804c00100000c0c408540082407000915280c4105400c600d156030003441500d42d17004080050b4080c62048900d020800074618081100b400605005800012400181c0742d40302d090000003590b1500441c4150310412001c96000a80080c01 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 562970890 1250 562969640 562969669
    0x111c02060703150501051204110a06020a0b01050d11090a1103070c03120c0e1c0503070803010905100b0d020d0b1f08010b03040503091e030106171e1b01050d0c020c010905 75
    0xd25182007407c9598604004000788240c681354491118007047c0c3d5500d42c802c1000b402a640104000c00d40741c200303001e01c103d06030f100c0b0344070b07695031180100041e589807242000003e044a6002030307603542c41c0b044e0000d041c4045002c1c0d03003c4400410421110380019601c0c100c14007a40d26030031408144494101112031400c00c150110300480c89000044c60115403c65003400492456071502142d680c4485c903540000070704407100f110200060002d00c8407032084550041d0740c0540950083d2a09140c483c0501c01d1085e445600e80c5c00080c900014001604503080d8003030b0151440315000010080c1e00100d01e518a0780038000703242180001450078201040d80d00a607003000c0914038100d140410001c0d110030400241c41910402c401c94541581c0a101e80b2001f080c0f40340c007400030f00d4106800c00d41403482030f05110640e8080300e015013034110400141d440b5400c0c087c42c0403000100354500140d8003801000000800d0701c4c00e0600c181c000070b50200310b4074210700307007038a805480e242c480c01003040d0f00110301903 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 562972140 1250 562970890 562970897
    0x6090b1e07030210090b010e0702010519020a0905090a090611070309060c0c05040203100512160905070915051207031107061e060b18060c0d111c02060703150501 71
    0x404848401450000c1103064800d004031503144d11079507002c50540b0ba40c1c50742911350802c40380040100d50106006103900550351310003001149000080550f401d020440e81c44203265010858012441c0229000d101408006041448038078220500d00c0152151950441d0b501d401c02c0740fa41404e4000f082560101030703040d01c030191568140f0000302c504130a461416500b4105100780012507441d988011400b0315071500340d4248142c02c0000f400700c2ea448108000703005500070720100d10198841c0300c2c50402e590104101040c2901c032580300b00c510000b143c0240200c101485c10032090300790040000c0110b8112242d036160603650380001034080307484068808a21741010440400024156400b1000f40c401c0d503501d180802c84003850240884017180c00000c0d8650000805c5003900319044107030019040201c8116142025510826803107441c12580d0300280400c0300300c81c103080c000600c82c6101805440c00c0c0c090050384e140308000d594020558a0704042031400090004003e6008070074010f8807010385 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 562973390 1250 562972140 562972177
    0x6010b0415031404060c110714150d050903070302060603031303080a03060b1c06170304050105071103100b010f091514040905130209220233030106090b 67
    0x320000071240c0200340e0041559619150070600c0c0c0d0f1036401401503018880005006410103c05404a045001030f500e060340411420070109007c01070441c1001410f6903000754852203501c4038070140c001d002d0841c0925007403d04125101c00c0c0007010b014294081e600b110328544800092540b05c0c07040c501104881d0355600c1c0e00b400490030703803001480c06407213525000808669a6903007110700c0d0000e00c29151219410008201c955076180a00c2003d0458006040c1d100e0300742e40300b110703604c0c401c80c840c1c5d9043c8000880c1280500c50b0740c40d82c1c1c2030807601c00b4040d1414401c4402004004000b18142079011410a080c068002445250342006681c45810441021424150141d0350110640a0007003402030422000c609541035028407401400c41403040d400743e541910400081060040122104596245d42c6040700000c490360750302059019110384004090740200c1e030800228002d104000c12032070b1091269442c001c0401141215036a6440c00c043c80d40325010065a407081604c4d003100e060268 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 562974640 1250 562973390 562973399
    0x60b03071406072a060f1409030703030806130f02030a0f0506010c061a0316140612061e060a02070306182105220603060b03010303020316020301020f040b070606060206010b04 77
    0x1c0c4d0000b2a1140007061a0303200548000644a00007290b17005a000202c82c48020203910750070660480c10300380c800c480c1c0381c10300d0b0081c0c0101790f9961341c40c440502040f0080010031115111401a681c0d6082d060400740300801e4840c03c0a0080c0d0300c2540c1c0d101c101481c00035680d030240c4407882071718000c640596960b02d6101440e2580c002801d202809520b9117004503900d101213030f50420003031010148500010032203900d4030307500284030f8481c601c42c135000e04410406550f280d488084102c0e84810101d400c0c6c1000781c84617004010701001d090302c00c2d80102000132112805a0006a01c0c01282e01c030b803900740010003118501907111108048000c040110002110780c3d425607141071020b02440a1410a090140f42d071110001c0341884800080c00300c625a60270300820740d040c010034018140c124091841d652466900a50f20f11440030300f40101e885450401045607000c2d011035030074030000020305880d0b5881c0d00a154007684400e100300d5844d4a07084d000101e442c0003082c960304a135803d80c280741c11b042c03a2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 562975890 1250 562974640 562974653
    0x61b0801050108160e06120103052506031a120303040507051c0602090f0916020d05030c030a0203040203100e030d0f11041a0409110901082a0a030204080a060b0307140607 75
    0xc0d00c07940400d0240c82100c245c095220200586580c03e4042040d03080781d45982441c0c1e0030641f0b05c0e03103020307902e03007200c7d440a00c607841007040b440850700c05280005d00c4030f18078440554125000c0c141d09500c26000340e001011458000051802540a0303070664140070b40c0d4208002e100380345509000d0001038040382840200304a58090034004102501da0f91140c0c0d10781001503801581240c0c001b910208110180001c0c44d410802004413500c00c3c00d2051540c0cc0450030781e06a800010a4001c0301c540000001d821914144113450404c052403506100754506500c210780c03203400404007100003915004071148070417040c4c0210b400c40854071341c5091030302d42098802c501d50048400d030040c20aa00300800502e044041c400d8240c1c101c040e44c0d00303a441d441c44500042c00d01c3c90180c011154141064860342e251240a21600d040360000c1c544199941c11640e01074001c1c3c041c51f8407501440c0500c040035814413119810030250b00f101141520100c84e16120a845400304603099250003080900c00c3d040010705 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 562977140 1250 562975890 562975921
    0x20706020709110f0c070e090303041e03170a06060e010e0d2904110103050a050721090c0e0601022a040203040804030210110d0f230f0403061b0801050108 68
    0x104103001518201130900d00e0349403988109003a003607903841501c0030003860f81031300c14541e00440040c024520350f09007030315026403205044030b8000000396000700c0802014040da05960703407400c1d040c0c0131040313511741034525400a10052007460080340c0d15500404481d0b1142000005e540c5000b09104001d002d551140311340d500c014400500c031032184003440031180c4001082d0a1090f8496035043d4414042040010141c8102510342c8454034101410310443c150040383c444066485500940c0040d001a2031800103040c800c003020b050400250408610220240d40003881002c1c02c1e0201d030081c1940f21407191034190040702d443c3c41205843e40e5689503252940085030000d0051064505154030b03a0002003d03000c2c40b103580700106440b0364890010b03c405000b003483d800b1030ba09118500d2242d01802620795120200c1315240710402c0d020214214444409444448002c010742d540c8441d10780c5461002010020384030064589034a180848051103545d906051b2101a51a405242c07200c01c901070f03010343d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 562978390 1250 562977140 562977161
    0x30203041403012403020f0108061c050c270c0c030f1318050a0b04111204080403060c0f0306080102031510090503240109060501020c270a05011401020706020709 71
    0x15202d014036a902602c0111184110302070404039130500d0704c1c6204111104500c40c0b8080d0500101c0d20070000c069450350480b078440701b02901e61b1030311298140303805400d2100220445138807030141d0840380c602525941c60140c070744640b1803034026503132076411b042d89080c001d4030b9640c41c0f41d070300c00c008a804150f000f801602048110095a40c065501c031550075507850342101400d80465a11810442001000d014103918003800381c0f030800c1100b280000311401881030f903c045000c0b10081021400f0000784504540040d81c10490400400300c9101000308a5071044c540c4000103400d200000c49e07440f00620849006548903148007904003081c805000701c8070035001c222424441d5891002405490a0040c51200c40c0b407501031081c100c0b2502c0b02c000003e601a0041e500140c0380c100e0504c1140d80002e030005440d40211030b10012014001d80c98400711100c1050401a000c00c181804110101e03500f0443c181c0303c400e050b981d064040703100120f80d1403440e880346d000107911501c400c1040c035030968006400380307 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 562979640 1250 562978390 562978393
    0x150902280e0603070314160e040207021207060305191505010c080705100b030709150b03060a1203120b010305040b0c1305040203040f170435010903030b0109080703030203041403 78
    0x9020590000c0c0042d00f04482c42004642c4960241d015100d000c0d45181d44209900c49040398440e995100916903541c4818490140307a0016102081d583c41a105910400d488403c403551070b5210a8000c01912064901da201005540c80b0242130704680c2c002c04003200c0d510860401407601d003500449a5100244c2c00f034504610030446400402c00900030051070400603900402c1055003402410300e0140260302080740710b803801986111108050386120103d410810316151a500c64000041c410810341d406000036001c008031150070141c100110032120311070030000700305000c503140054007502c404460007003001c0070f1800000c145441d188007074405500760721010781d01c860312080442c003203a005450990702d1211180c91103003008405254010b100c02e41121f00b5090614000c1081c80d00510484000090040c03890b03c00242801c1c010345032b10303205070b445c02482009124103018000b440d10030b106030700245441c0c001080c007210020b42c080469074980d000314030b401e10f0034507510588400c0c1403d0581c507 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 562980890 1250 562979640 562979657
    0x1e07030507260711120d020a090506031e060d0f0b07120c020a05010c0e0d0609060f0c03020c010b060c0a0f0204060806040b010905010e100306090c0302090a15090228 73
    0x42c245100080a1481155074100c140d4100084040e0501520002000b482c0c0c2c880785944410010550688800e0301e21014050303100c0201c01025a00e08080d07800480d004400441002b001c000f0310864990072220038003494210f0386450050041c140200030028041d5203a00340050009820b4030259641300445141c02c502001018004000340d401d00010324005078850140c1400380315083c4900d11445020381080310040c00c499000c5a10340c0c51110010b40001d82e00c400c4030040c800c0a0308203043d203e001c240f080000c00b002c0c0002078025040410480819840c14000c0803890500c00d044500c1c0341c81c0c0b84000c0011a0165076044194044c2c0300c4200d0b001610dd4000050842c420401035000320311800e814012503060141102c101d4005038032103c19584500148110750860540c0501500c2c3c1100001c12450f80a083c480c0100c3c665a0000303400c54642000c100b44040558044075030f9803648082040000d50f40d005600c181d005040c12814074075030401ca01c400004610624100c480340710308104d0803 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 562982140 1250 562980890 562980917
    0x22090503040f0501110f0a0201050f040308040b0c0c1005090d1e1212110703200d1107060e061210120c060f020d090e09010b0d08121e07030507 63
    0x45802a5120050004002c4414401c540e003180182e0800354003c402042d200e0400f01c4015600e0b07140702d1000c6d052080024080c140c4038011002c84000e1038001070f540d96626a10049800598081315941c540303030248094500b0b4615208508040542603583d44034100025803040050001000b41e080f1051001c01d07c02c103140b40c01240d0008051400b03407104586840120f0f401800c0612805140c036178880c43c003000c6101c105650026201020340610b0069000443c00140c0d941c1703910340c4040b0400c1031280c51102005c06a0180202000d61064001c3c2d5070596a20303841942e148208180340e0360302c04014000700ca03040d0f040c42d400d941d010500c070505406150340c40400d000c140e8450001500c584485e044203004441e0841c0034007002c090944000c201122514400501d800990300420005400c80070203ea4008800d420030f03106520000c2400d140721140303251115603644015103035000e4210040c00100c18003080d800b4079480500b28164004079660301c0c04210010500100300509101d6189043d80 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 562983390 1250 562982140 562982143
    0x90a060306090803010f080d09060804110306090706031a030730061a0a06120b030f0708160603060b0a03180606170c060306060904180b0c0a080a0902220905 69
    0x11010f029140c195500e50509501e84042c03c051f402c40d1020f5808140f541c0c40c0140d22030104002c548682c80d10000945551400b02c070794050b528291641407040505000a01e031000c81d1460890745070342c504002d00b850300e10340b56a0201c8490700080c2e15070020304003040070400405e0318122a264a001980d8030300308822070494900b611000907681203955900194110720507a80351080844100c82802d106441e0010040285281c1d07403042800c00d85601007250261000c004034110028824141c451640d21070049035030301c070040d880302100c0040012000030350b18006d1298100352680408001e00d0038800d060140c01505400d02c54050f540701c04508000810307032a1007144042c1003812600300304009038003007440c60811502c10a034440c117001c109118203940d41e0011030b0f810460680c0e01051444100c0e4051881201c40304002c0c011030f84050030001312050050040c490140583ca1788500c54540c0411a400c84039400002074002d8400240410008029054030484011500000c5a01811070340c603c0d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 562984640 1250 562983390 562983401
    0x50106090212070f05030411010c050114010b13050a0b040b0a2706080f010509012108070f02031b0d141f020a0212031006030e0f0304030b0f0108010e060105090a060306 74
    0xe03502d085602d0180202a9070007800d02d841d0126516040e400e40c01c00351240ca0102c00804200c1e0f061204a0b182a4204602034001c00c90000901c2100b40035580d441141c009240c3c0042c0100940c0c00201e20042000d28004080e50241c460116400b8181350502c901e11400e03500501101c02800307064084002c2c041c0840c1c600a1804001d0f00940071054900315001d02013041c00b07044c0d00c98510740c060050000d6203d508181c2d044591350300c400502c060302c180d42541000100700c0d000e049448001040d9040c07094040600e03080ca8402c3c1e08650315030104c00b0401143d142c0402c1c125902400381c0d03894030081081855205c44020511054a02400c4101c0300343d104055518504804160081203a8920540500000e41907204840b5074500d0351500d110b00c10820540740c02401c00381951810544000307601006035140040350801240d6807203880b8101660002d42c1210804440e61480002150706c03034045c05400720010180c0014102642094200401920000e1655001a80c5d074040040403441500a1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 562985890 1250 562984640 562984657
    0x15060c030901261003060501090b031b04141509061203090d11090f01080c0607050c040f0b120106081b0306070e011115090c100504030f030c02150d0b01020105070f0c0501060902 78
    0x30381c0071450343c0b1b042c0080d00c005a00001e020351400e040160603850218042c203500e4903286640050071454130001d0000d0900311906005110180c04000c46107041c0c03500a00701c418221103a10440e83d40ca000c201c011003a10780e8400303940c0c106101d14a91410001e584864080c8a1040410015112004600b0b5080110b07001080760030028010400840203024141384075005945a500d46034254440607520f450b400c2c8414029650381c1003146422810360b102c030a022400405039488c0c200c00c0c0b1030030750207003809004598640c021000010541554110320103806240a001f034841ca0355210741c00c0d00c1d020112003000381401480820845c006c5018810400140083d545140186c02c001e0314181c6011140c604080c000d150800c80150095003003800d4500b00d036070004c9000d40b000002d2070100c07042c0c4c50060000750420b0318164042089550f2101900b1b030903141840c10498107061400490036100e041e01d188000c14040110101028030940011110500410000c1980ca945559400890784110b18 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 562987140 1250 562985890 562985911
    0x904110f030c01090e18070b0705010c0810030b04140f07060917120c01020d090606030b0f150112090203030a0f0908060c0a08041b03050615060c03090126 68
    0x2a450146030800d12440c450809a00030507034000d0382d10000c0c1c1003d01c28003450f15a82c40400000f01d09000b103020005c032054a0600707941104d5558080e064054010040841d519400d00c0c00c03865070f691103014014440c030100c031510880c840c50340d111440a13038005001a1071110054203064141d040403c0100402d00b001001410307a2460071500501d40d00194000c4a041c509d243c40c50072503220000b804a00c4218500d0f1515642c0c01600b00d114020b00c0703401c15401311030f81442c040300103010792503101c0c0303040b0781c060152441e9030b40d22030144018001c0100c81c04d410410303d0712005921540715014405004078101070001354601150000386c0b858100304441800a1400c2c0d081540c000c1c0e026003444002c01710070008210506003185081070314061b0010700e50421000600003824403402c0d81819440007441103800e10340c02c0d100e0600c152103c000300d45142d8922070701000e105e40750801408035195548004d001d98140801f940044800001416484108410516800c492031224102450041c900b410 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 562988390 1250 562987140 562987163
    0x3050306030106291605070b130503060405120c0a0f080304110607031e090312080a1107020904060f02190c0201120b0d020f0406080304060909060b0f16020f0904 71
    0x24105425a6031540115211400e041804e01c502d908003482d0a0700c0346001d500158407464005072004194807404c0e0040c0061040d000300044250081d001003006000300c4080e41003194851062507505c1d40c007a64001d2540c0d00c11003881490f00c506c0b0003e401c0444501d8142d0304204425100c0c10300b0b8009200c401d807842c00d8000103201c204880310b100200b08400a039059030400b40641c0300545114404500407144808003000d040280b4480c3e40058003844c2c2c0141418400c560f000c500178a500011a402d0f9800791401c0003402a840d035140c10b0b100d102d503000f00980d08981d200d551f080050941803030203680d1540c0921401e40358060007178062041419a540d0207128600a00005040040d241c000300000c07807a2004919081e00c89a0b19003000a80559401842d490340901180c02000070380e00c020b03058003000c503011801e19400300c000c00480c9c0d0000f0302880030a48401c140381c8a4480c41d045181051030400100c80c060303070843c1c02030341c14070f0005140d035081640b0003000c20200702080310111040c4640744d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 562989640 1250 562988390 562988401
    0x30e0c0a032a03030801030f05030f0703030e1204050607060b0411070525030c03060911091003053f04050a0b040612050f01060e0d060e0303060307060509030709021c09030503 77
    0x100c0d0042c00c81c403485a0034106074559200076181120600010301800c0e528074983c4103001c81003084802124a00000568409141c10014001c002e4036150307030640c0c02103e0500d05450740303900a450035130f00000c001a140c0340c0950b46141c024101c001c440c580058594091410314800a80500002405030000d0035000031400000c0c0700c4021044144580e071303100440d0a00200e4252400082a03d50001d00000c0d03a0704c0b9410079840b10070141031081ea101480508020102ea500b101410441e0302c03c6c811505403910140700c000350041420034001c408013901405145000091040a040c00c0e5689281c070322701a118408103082c3da0098026604080002900300881940810000c508040640c0304101e2130030309681c18180000184589410842d18104041444c8e5843c04029001e907030180080100f80617940c0400d0f101d8004440d424403070301600e80001082400b820840d900081c0003006040c3c9541003141e15402504220304101d425026a240c002c6000460300c180094240241c940e5926484c20 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 562990890 1250 562989640 562989683
    0x90a0209310609121b060b19080c010e0d05330703020405090105121f0e0a0b06011b030816031b08091011090d06020f0a050d062103030e0c0a03 63
    0xa0b182084c1c02c0050301c55500800200d940b0000c902d0a900c50804106401c4103c00900104580f8034032084c0d20500d4080024098000501460440c02c2a211040d08400c00801c01c40410303143e08024150307810a0011a0b0000742240e074524112404ca480c0359013414441465420700c55080346c0c035602182d400501485035261082000e4010a022180548003a00d02202c2c2916000e03041155510411408030005150049030082400c803400e40d8100c070604541400d26111984003070f07070100e0210701b56048000343e45c204026103031100741d0981c81d0303489141c81d07240300f4840b1001039064110802d5a101342040c0900400510108040c80c4c958030519141096000b450034580420401c41441e17160417001544100741800b031380c60108003100c0840c2d218141e0f0500d10044d21813240f101034540300000321390009941143c06440011030300002040b04c1500e40d20703022589540340e080148820038000c030900002e407003600060200c5440c4800e9800e0341044101145100d0300326002210b082c1000350310880c10200 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 562992140 1250 562990890 562990913
    0x13050a0f05210703170a06090f060f0e010b0412050a02040c1112030121230a0311060601050d15150f020f010c0906110f1002040e090a0209310609 64
    0x110b007031500d07190340703550054400700c000a60b0202d0f80d140000094541840d82d80200c00420106030b081c02200d803035981382401084a40141c00b0582007030900868010603152440d8169088012424581405c2003124003d005c2001400c44642c81a0005980162203d000b16403280ca066201e00350820140200c482c00d0454240d54003440d60401d00041003100e440390f00f0b0409200c4850441251820f042c20168000d203054120511030380444c0243c0d13844218006800705045020b940e5100701c100c4510301c1d6039111041a10ba01e4005217082c0702c0f02284450592003898020a120001c0102555561210501c560300042e080041055100c00120554040c88003002c1038910200030081c4040c03851001c0c007945002e020380d2003004000d00d4605500340e020090344410240e58404c44900820200c1190003070751003805518102c0c07240350b000c1140000300140c0780c074200340d0051429465548540640c030306103070000c6441c80c2070000b11140000340b00c110301400241a0044402081ca10000d0400c14038048 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 562993390 1250 562992140 562992193
    0x50d030e0304060e0a0909030806120d140d1503050105091b0a060e060f040803030402211002160602070501051609060503040201200322060e0913050a0f05 68
    0x10304021001084120100854059035902d051440c04030301d556011a1940b0040e80060000c1313441c05901000303058004441c24030401d010bc41c4070031203102d102d81d01c54840d21001c003c0f5001c00c1400d48044c00c1480030901500021140c401d000a14455914201d41a203220b54015901659a04140b0094100502c074149001c0440c0320400d02c00d1032440041095101244601400c10000003001580e59880b0740445003030f1120300003000d03180d47e215403141d6141e40c41558224800d002070714080684640b00050f0102d12086540034081d0001108008000b0750710102e48006079034013803140107000603e07500c054a101401500001868a00343ca2158100d0b203080a00790141304824004201607a0f100301101d80c0a9420319251120180d0003030189d88000181409910500000c01e484002420003030310425448040e03c10b9002c0155101d00603507128080e1120345411030440030005442211075081000c2c814811800c42e0300c01c0103240c070746540d98071142c030085a994105900c250071801102e419001144d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 562994640 1250 562993390 562993397
    0xd06060f050d0803010509061206070906020c09091c031d010f050a05091c0c0209041a070318081b011104140a0509040303050624040305010e120901110c06070609050d 73
    0x20300c915101c0d40004d000501c01ea0384200f2820b030004d502500c4100350a01c1e043d45082c21180541000c1e0005000b00440b0b000b000018403c4010480f924902000010300500100780075102c1680c0c205103499014070003940340c409143e00e4041c021136025a681a8a0003000103a000054001c410603690080d50005454a409141804240504110080382d0710117983e001082c2c0180c2d500d2040415600d044090780d001e940307e03155008000510000c0c038003984549840f4081103860b81d55200003a421a607840030042000c00ea40b074602000684d100c0003c07c402065210308400d844500c0c0b1201e807e41c1c1c41c40e0885001d41710701050800c042d00c01d84040b41800002140c850000b01d0501c0017290a80400070405401c00d5216004189151904012841d2902003441821005608501601425030251104840c9903103072401e0906c0e001800300315071301e40a2810359060329166240004580c0201500d560715190f004d02d02c0d040e0758940c0ca1600610704207200b560042130b603114506086003070600074881c1d8030a2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 562995890 1250 562994640 562994659
    0x1140d020c250b1b030f1206030a03020601050d03090905010801020a17091f021204030e18011a130b07060c0305090c090604020c030403050619050c0a090e150d06060f05 74
    0x2050610040718169114520269104c98500c0340e2007081d144c05180d1a0224040090304034540c03a00e090040a20503600b160b454540c3d20b806043c503940d4001914091b005030801d100601c01c43c81c00c10b0030001058080d182120840d900c801100c01210b500303034002c0c0d80d5694002140014241c02100b448102c0000d1200c5442d00d1500d04051500d540b00c02c404082c61f9855003000495400455054038000000010b00c400c0a14013850007502420420003210b220b8030341590302d500c1090340d40485038141d07001c243d02103e02e4140842405296009441014907410341d41c0000310354010b001000d002d045001e4400414188000c060180407680d001d0810405070300150075844050325580c42d9590000815900140c4d80c0c0241d503503241c00d40c002c0390002000c1d80121018400b0982c1000350b420348003180510204601c1d161205048000d03c81e1880030008216400000c10a0070b8000f01410b40c00100216550100203820000465292505074200c0b6010b0384c50600b0301455250056480c040d29040d281c80b4035 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 562997140 1250 562995890 562995943
    0x30a03201b010212070305090d0f050a03020a1403040617091507021f02270f1009030605220b0717092a011722050f011109010903060b01140d020c 64
    0xc00d200301c0088d00d02070643c22420034204000d071854285034035080016119a0704c0301e031400035142c1642403816991200c00400366040040c020003150211026902c0e07003ca060740e40c080074441107200034038152030350150800800c3c08003c10710030035100702c500d907010302503040c00041c0750b07840606241d0003840c1c01403042c461241032072030b00181c0221403041c00034124100154100007807030f00307980703409030503005446000740510864000040c00141c038401e440c24031140d03075803020281e080c04003064010317a41010180c994010481c0d031415680c01690300e2900c8823517080da052005500340000c2d54000b8240e44074034011804000f0040720a0b80d10b01401254506400030b400c00207103008000303000141c1c0000c490012504065400280d03001130041c0742c10b50050214941050b546034a4009071299080d400c03c002003001c98200b030200c3d0307100c2905846462500e0f0030741c0c46042c000c0c41c05c1001e89040c01608044401e0340c0c2000c0e409810402c2c00300c0005684d42e00340e101602e09258052007924414440030b1007404 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 562998390 1250 562997140 562997147
    0x6030e15070c0f05101e020c0307030c0f0c06120c11120a201c02120f071a1006020d020a21050412060524030a03201b0102120703 57
    0x540007001842c0403040c0c507050f4281041e1480a0060007812480350101e10170004d5600d40180d1101170030511380c0740001e0f040d192480103a10900c880040709400c1048080000790081d41020401070045040140403030300ca61355101e1403c2d0a402820200b035440c4028a0181b80d140215001c880052402c1c0f0171140456610a645403915480180102c0c408600a0703405031040458005502c0c506400b1486031001600c100c0d154005580103808902110f11203a14244c000224104005d150600c1180b03040100f40404641e5002018100c58216641012118246044110a000d03c08002050358007600d00180030340390034580380c00c0c1c0041d5000340e6080c4000c1201007001c0b001c0d905071a0700c400e080c820601c108035079500c130b15000040f002084258940c203000e16944045c1c440ca042ca001c10200310180088a40311030000c52a441d4182c1c464614800040d200c0c400c041112594a01880300d06001c00c203943d810260824000010380c0781403140c504466904000301d0381880d00c0300c02c855107400070031344005 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 562999640 1250 562998390 562998433
    0xa0206040303020a0225080d17190b041a1914040b0a030c08030a2309010c060f060e0a060e040b04060b0a0902070b060f01050f0a030b0f03120406030e 66
    0x260505501181d0515600c0c004d0191b180541e2850444651500c240f14980300c0312071140c0a80c101510801440508031401009100200c03003040e1040790301551003103110044140944117180c4040e0300c0c0e4000710000d45441c0a0504413500009006186541c2e40c0188966401d00c04035014004500f00703010403180d1040329500c58151804d550114241c0b0044010a0041026030300003007000d10103240004c1c0885020000d00322403401030f1364600c8072449030284c403881c0030710b16000c0581d6214100306685c0ca560240d07000390942c1d44580008148940a91680e2044035002d0380150000c0618000300b200c03080703003849200d0181841c501e10303001600300b988508095030001000109481e6a41750310421b55520150403c0007045241025940c0310700600e40104000d20079120703240500000d80301e08406600510580c2d4060508040040c03d01640303180440207001503410b0160080c1c00a0004a1180c0b0b05122605c03094134202c0032503585901d8100000c085071050320030420309800c5803244070302c3c201001080303 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 563000890 1250 562999640 562999643
    0xf06030504111203030406150509070807020c061801080f0f0c0703020a0501050c0d0c020a0b0a020f0409020408030a0216030f020405190609230412202e020a020604 72
    0x164a544601d8040c51141c2d840081c6a0f0041c1d15242c240c0691000000851046100c0c240c188030300312220242d145041214060681e10803000400115021b2003800700e158484c030342d4411910644111000b083e460b41c060301c400c0c81e600e000f18181c4041c0d560040c004640103c141d1300e0b820380a20700030041c008001030151040f402d1003400240001454070820900d245560030030000c000d6810410149901d40d071025009011150410003060681ea00214411410079040020011142d607402e152600a6021110a0122107801d00001c01c0c0c4040602c081c001a1542600540e6150b0000700041d181c004d41d9035860345c50024104090002030289802c0d07500050381a94085504e4440701610524001108848200c1a00e04000040ca4a507943c114044c85580340c01100070b08008d4800b02c000410080b070b03000d04100030395001c51007060b00ca075032100e00c04c1021016190916444d254403d00702488a1000312004944030300d41e4149c3c1c1d41c4922001d4000155403401c6140001680004e0340381c0800400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 563002140 1250 563000890 563000897
    0x307031a030c100507080f03040c0e06090601030b0a081e070e010311062104060b0a061107330201050a0b010c030f20030d050f070908120304020415061e05040f06 71
    0x20400490255090756085d5a00012844e2203e10f0760f401128542c100b22000d4034691510040010b03a03081c00c800881c050400540281c480b03656000056020b040801c0043d500074070341c1c1400080502c4240b00901203200c40548800d440e80100015a00d40340303003170f0800100101d660004000181100444109a400c01d40b4542d89541800c0e1500350444411541e9000d225025003c010400c5500d40c03002d00c9010b81181c000140b103803a0030007200c2c900710840c202c014942c0000d509000d82c26020010a20855600c3d080680e404595401c0000c03104601058101603910354050090600c124024510320310001c3c42c205c499050f2540b401400b8048034030500302404ac01c04884082c01c005800d80c007803c6996401100c0e6528801540600200801c491400184070803c0201c0c0503144180d000c03000b242c4c01603004052655803040508680c0d800904200d83c032075594604200246070a400c0c12000341110388484c030016102c02c0b1081a030260303c941881c10030104020901c04e1400e40204482640d6180c503 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 563003390 1250 563002140 563002159
    0x20a170f0910090303020d0203040809031006050a050f030f1c033206030f01061811030438100302010e01140a050705030f07080715180204050403020a170307031a030c 73
    0x44c1130f0000d11405402c8076100b400002044280302d0008000c0417002415011540c407090004882002c0b0340380c0340101d541c4000c5082c8104a1440d201111f020384080c01000e842d10750200115552a094442c2600c05240c0021400e19402641510800c10484a030000d55103c1c1203080d003281c0086a031200c840032142c8102c03004100c4071f407000c002000d00792103a80002c01c0019218441c1e50404200e20711a240114242065800119001d009490003240d0044907441e200000000340e20741140d804c1c06240c0e007102d8840140490020000c400390013060b5019080400c3d9003107000041209202c44201c0341806600241c9907105d110300011108070113041d242080d11449140741c018254410340d5401603256801003440340034408520700030404036216140d1640284900c60043c2c0507a0901d0000c40b00001040000340d01504064101640c0039200303105480d0300c0507003a03803210410510500e816441590200800c0358040e010720460030351480c0d0003008915080f0901c0080c1d541d11400440328051440704 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 563004640 1250 563003390 563003393
    0x90507020a03110c03060406020c07050a0510141303150608011505090903041a250c030201052107120b010203070b1b1b03070302070504060e0721020a170f091009 71
    0x144941380440c030005040d60554203017070605070b01a400c501c00100302406081400111031410410380300494a000d020300010880e084402c1c2ea070300300801d089041034501044242c200740100800d0340080c52183c01c00c85c24921212035000b044498a4210f40110382c0f402c8416614415015440c004540341160b000c00c1c0f543e20302d40141e09501499010b1251441004110401e81d490b400240a4260703111740100c4001010030222021504010b001911404a01d0002d1002d544907900404075402c4014541003200c00c035007a0222010070880e41100020740036a0309c0e034440d5005000300b11074038009100460410071140c403003002e81c84018142c094005100b921000500c140d003416500d40320498540c02203203654001c4070540340d52092034110b006026001000c1a0361805218541c251403000658400c55a2181004ea401148101c4207528a41c031845003405841001c1c0010900000f4035600c00942c00d58810700c44400c104042d2070340000740742c014200702c21048002514078460803500400700c1d61031281e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 563005890 1250 563004640 563004643
    0xa0b0604020405092701020c01091a04022803020a151202130e09282f0415030209090a03080c120423151e10060309140102041e090507020a0311 63
    0x100d014201701540040703103031410000198801035040d409103d02003110000c014425825000440e0020f40c842d2048010200800d880300070429803181e55040e04035030689036000108141e1665000c8005070bc1c80070001007801d0741c4040320440300701180200f0343c2881c481c000c0400c500e12071805042c10b00c0480500040ca50a800c01540300021000903011491310307414420701c40d047d10a60310640c1d24400210005600c0030f0a12030f8616030350315208840d8424806e14080001929040c507034514014007100c000320240c0d0b601c181d4140980d601800500076111b2900d4060000100108150821078080c02208090088050300c164000d602c00c02d03034840d07080c080103080c1400002d1000003a052241d00c2c40c64240344100ca00032800382422244005100005920074590190704440711101881e10704020040c0d10b0194000c010080d00c0340f1001503241042910240c22030700706c1d500114515001545507440314001d41d141401130300410900b88594509683c000c0d5444c004610018101f005c82010b40c004c0e801f0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 563007140 1250 563005890 563005951
    0x13050d0306030809131508010903081602070e18250504060506040603090309080601060201020a14070c1e082a100815060d0905062403060a1d030406020a0b060402040509 74
    0xa00d18541c101547c813041218001d042621049001c030b955000402d820078100c0801ca41c00302d0700d5a00520a450800780c1c60440b80e030010b410910b805101828100c00c40c04240f040400702494500021540000c41080205030724030340c1c0c0f1460046d4a1712401744507940700c03441160700b55049810085010800e9140840300341280d0b510094040c02101c00210304c8a5041d001444884803e55540c0300340b62034086401c190380b24a180c000d16050861f282001100d180d4441032051480403050000c0681c0c2d248400da00740098200c0d41410318848a088a03404600b000c01c400d02117106603a9230400c040203a00250402e0f1010340304015440250080c0803d554988007255003690300d580041c05070324038600e4031a40d203c030181c5070022540d05240381e5604a100b8152800868640140100b440c2e883d428010b20040035001e0350200180c810003031822a14008100400090500b507004001d1014030303040800c500b25001d0320103071156004100c10481c1d541da82600715002603103a204c0c030f040c00d6904111a001e10b038 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 563008390 1250 563007140 563007161
    0x1b090a0e16060c03020601050f181b0a080610050a02060117120f1308062205030403060603050717010203010e06040b0307080d0314060603090a1b03020913050d030603080913 76
    0x7030305200125080c0d03032081d2403081151003902200c0d60342e600c4c0c10800c10140b104135000c3c1d4000c40c240345040302c40b02c581da40850b04140940000e0400d840c07090380300d486590101d42c58001081110341440380600700300786890a80030b024600942005c0d4001c1000791140301c180f040c6c1c501c0f41018170300352004140c00c2c003414401c401c0c00c0928503541c0001741d41c0e105494002031035000c60300e6045180050440f801191262040e0f8521001c0019980308489824100b009603009503801d220500010001403858412503000d140100300800040f89000170141c0850081200c0c04016401400100846078900307804a1f000310007140d010503070004440110345019510390100b410b43c45840080c0c0d0031103405501c1300c507525034000c84a80361980c0e0481801034506c01506c0501681d44080e02c4000450a914101c2c840c0c00c03580c0f14002182990390700092960a0244d468a00800203502ca44c3c08105003000f000c00d0300c4c030490030248032903480e6440301c518501078107100c9401020205464524030103d54000543c07074 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 563009640 1250 563008390 563008423
    0x10080c0d020a0e120109050303130f060501080106180207050a1101020f100e0c061c0b0a081c030b09091f06050a0305010c0f174003021b090a0e 63
    0x940c10154000c00d2081d2503c00580140c40780441c0050000060141c203e00e2034000006518545889204500d40e120b400e4040d522060689043c800041d4140100d034000c0c810100042000380c20300c14069071003ca944c1e40620500c0c410003403000020b9010031000c5400c0d400102d4021064040001031703080c260b40c03c1c403002c1d842c042c03005100c01e640c00c658401d10207010500f00300c0d600382c00660140110341c8204109281c6c00520720b410301c42101c2c0c66400030a10150040d00d90ba101e5075803814818501011580340d214000c03402d04800c2e071178541c98880d02ca105a4115460800b40c1001a08d50340c0710002c0d9841e905108050029480c19078403640c0180c001000c02401d40e1414650301d081c128024461520f481380010a0010300c03444234ad00c82c42d0106503002e80f450001e04d41d81c0790846502580c4c408031389090304031700c4420350000d5403034000741045041c16000a11194505c0303491a0003803c1032001c0c4400c002da01c0207101d92141035201c1100300da9000509010010300c400c400245189402911800310080 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 563010890 1250 563009640 563009647
    0x80607032a0f08070c03050d05070201090b04050601210b0711032203022e0c030c0c14040606112802060a110609060105130906090606120c0503010b10080c0d02 70
    0x460b0303800900c10b494220300b6922101c0d6a25006000c4410221004019000038428000b50819000603404a80c1001160000152a1341241d50b0040d0510301124141d0340ba810034401001a41c00300c249449580c00c16511050340c200305584d41c400380c0c1c43e001d8448410132024040d400c1c900401001100c146c0301d2249812404180c030482c000c01d0030b103e41e01049000e01807a0046c2c410340805299404044040d0000102000014000442d50090b44c0c01056040100c050000c3c0c011442e6035068070702034200c458032440c0344000e02052000360341c0700da0320040821101915007403410601041c0c03490003181d0104030300d450b035031003568000703030f600ca03003d0042e5018400003260100c007600402c00819035070200382940c0321030740d03003020003a00c81c3c200b481600e40101807a506400340440b1503201d02c0b1180d110342d80020304000e07652201c40441c0c0180d00820000381c0e04134a590144108000e1000c010310085000740100742615020508110311426078009010102020808007400e032010707692456140d003400c548 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 563012140 1250 563010890 563010971
    0xb0718080706120504020a03030f0c0c181505060a03150b030906040506090601152a08090f0411120c07051603060c08040507060509060c070807090b0a08060703 70
    0x101d81d1103a101e1400801c0700381c0c0c00402c0466031401024440c40d001010420301900e90748050b5025001c41c1c03140410031800e0f003950000180007901c103c0150001c1408108a0b80d40903900404a9604011007000703a200c4100c10410ba907140811105071100900d000b24292410592003403111805421202160391302000300019000d0016049105d94003640803259680c588041d21074a40d2003c0c090b0003032040c2c1c49100c495849004200c400c24066041005124996011401842c8140803010444030010001102c40c01440d14a0551080c20703c04c0302c0030850f05c08542c61400540c8210100400c2c0c1921210002d5459480507040e512801c1d00007023900e0011010348140c1003440d032140800c13900303030f490b00f07082461080c891040c4d45c0c459503002000b01200d81c2001d605403129000040881e0f805001082100300707a50050017884001c0013003200420407031781400d05820648580c5a0554040d481c0c4160402a03140c0014450340c1010403414009880b02458040c1c00911104044060b00003554402016 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 563013390 1250 563012140 563012143
    0xe01053f0a0203061c050715170403020601050108070e090402120304051903060606080103020108150f060c01020c0f060c07060e0a0212060f0a020306030a02191203090e0a180b071808 80
    0x188140c20440c1c03c910000850520421003003018200980647e000841c103200c06840c8440142c4820401d0510001c5880c02201c031000c0d501044404600680111004105951304030100070b4112040341003d84000c0004004140c098000a001034841d0640a07064018501c061044030060107000c3e26104d400c201c2000c00d803945001510040740c070146001c0e0b0004201e48a070300c2e140d040e654141d40b03480258660107001c9629095240d04581d200c10303125402c0030345580e0103004204a48800002503103e00852a104d400d2000100c8641c5040d00904100000701c5101e200b01c4d8481c3c0e6102900081c00010001d5241c0340c0720501000a4100304149a0110039440020383d180c07003001700c0f00750036603507942e6040c0c440168042074031541d030145d021140240c01403400c040d000e51620356001e0f0995a4070790720700c1e91035000710b100002500800d20a620a00040d42030141a03580041d8410080c007005040d20820045a80811030180c0000900030104900714400c0f02c3c448001410315110001d241e4a500c80d01e03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 563014640 1250 563013390 563013397
    0x918070803070314040609030201050c010b120a0204060503010614120f010501121104060b040b160b0a270203030711130606030f0c0305060f06031e0f070e01053f0a02 73
    0xf500401c80c00a010501a800074040300c007512459030b100b201883c559401511a03800540200301c0c29500d0b079000203e251103d040c1030121462110003001300280d00c1c0140000c031101504001c3c041d90400b90284002d40a010a001c40144159480d55288400600b504e0900742e545a1b1440213500f40400001c100c0c9030a000c0400042c0955011041c251011042204991040c46541d04010f8103002c02c00c15104a41c0c041c10444075070310480d81d04030301155274405610300100c41c5250011790b01e0354034803401d2003502c060781841e8400d00d25500510342d903900069642d0240000040000440008001c030684410081036090b890418041c001d00b606d554020700505542840c070791080345005860030140344640161800380001428413020890542d00b80b113607950000b81010015a1350b00d4a1400600050b00c60781d10130540c00940301540d0a001200a2000b810011031904101d414040301e07084c1c503202c40018941020b07040140b0102083c181410502d10812035200303404166030010010748a041e50002c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 563015890 1250 563014640 563014643
    0x4020d12170115081f080307140609030a120906110d0f0c03020901090e0601030b12010209030106151b03020c03160512120a08330405061e091807080307 67
    0x84600782e03032500b825418060305465000c00150010300030400003544d0402d80481203802140c042e03a1503803188102c0b0301e140e0280c001220100035001907601e00e00c4044c4000e5410014010103107260a068040051031840003441d030703003001580c4052070350070070042d0b51014100e88003030300c100307600d802c80408248000c050401c020300a0328100644e044000344203201b00d9140400503114828031a0505207504d011030340061200d0305044d40c9144070b4202c0d540d07c403003618000c00304000141e41c0e1400b000034582915242d13401a402e6014684c08a4a20f42e04050044190701041d00b008640040d1400e00b00e19103240d030315010b030301030003080c0d808120554088090f100b551030650f81c11900611655050750784403082c4004105149050000940403072040c1001508481c080c082031005013204800c40d409510710007202920381071300c0107048605d41414040c42c6e034049000c41d4280c044030240390b0f401c2028210202d00c0c1c5d124240082c0010918820b25542031050f00901c01100e6041d6107034004507a499100010 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 563017140 1250 563015890 563015927
    0x180a150305180a08030a06090905160b04030b0c1602041802030c06040605220503030f030103120305101203030e0102030117060a020703020c1005090d03090504060b030402030a080304020d12 83
    0xb4400029405021030b001c00050010a4201d0854071340315441d8002030040c13200941c440c4030020f0b0154650080c1d108103030041c400b401402c0711600380c42c0181000e13544000f044440611003000414504801564003408080040ba55040d644100042000806c00000d510500d420607400685e0840d00f909504103100341d0450f0124441c03201000100d003d1132140400290f42040a4032518000d031006420b111860300040e10300640b240002821a0004241a4002580880100700b03101c0384011581c4400070f80c1c2401c00c11420420341e02e01d5042c00038010006182d081500600c20144a50f002ca0306450900000719180c0d6141d070307451010000598052010748c484e040109540c09031a100b01c80590b0b074075400400c000045281448540c8001000c844284642449004001c1c1c980340c5400031400e100e60f84081401c1e04210800c001c0311032542224001c00814400c000050300c0000d08110b44980103d00140c60f542c0e144000b84001e411408000d100e101500d0080d88025000b200c3d03078421100c60f10 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 563018390 1250 563017140 563017151
    0xf07061d0105030103080702010c1a070c060c08041205210901020405010806150307032309151501080f130206070503070203101a0123040f050307090507050708180a1503 74
    0x1401102d6502080c000a041442e04104e9000158018540c10031458890400804002003c804404001d601103428601103146800c46900f0400301d441109681810350509901c01d00701600d400401d40100845541032040020b01c4044041b00c0c900c40e006821031005980f030607460300f451002c0c086d410a01c903150100b042440801e00302d14042000c0c00918180f14050390840e9140f01045001d44002032031501c0003019100c40a80c0c103824074101c0c41c8100800c40007040c00070b08200514080c00300c010980891441520220038090382e00401454000c0020000070b9115110b428007007000710089c038002940207500260804c104036012014001150080b025101030010060640307040da041c1c003407410075050408911790792940c01078407249280800c0e401d4005582010030715030042548550807003917011100040c108802d240c1009000041c0480780c605101c5402c0015001e001c3e8050084001c03c45200840c60148030a17110924610720354000341422541c965a05a54041034141c000c00c100103401d14 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 563019640 1250 563018390 563018447
    0x31b0309030f0118080a141b060919080f0f040806160302030f0f1504020d0605030c060a02031b0f07031505090c1c08090904050303190c0801170f0706 66
    0x42c0309900c101c640f0740039078014100346943e80005d07942c0002041018445a00c02c440201c0c84941c0281008858001c510350310140b040410b280340c00340040040c4000d600145046413200c08813000d040700c0b55880004e00da00ca00d04050590402d01070403040424541c00071600260401300043d0180c0500003029580258a800e000102c0c2a440215540320200c000070010502c44041c0021044d807083c034803604c0c03a8a0380c0b004400141643e1184009616141d1600400c2c400c0303180034003100b880407108440f000c0c585600149d0103502d0f805403d051070782c0d100c0301a50761a1812020701070088000310140c2919611b907103c0c82d2541809113180b0803502400d29100004054100009400c08280001411a58400b501c07074041202a520901d0440d50307a44184180c07030107a21440c0b4854083c071310800140d5160b2424407245003582d4030030b0707030525a00e41c1405480c04c0861340001103d41959600d000e0880c02881c1440075070b180c40350180c2c003440148145e910002c1d64a6104070302c10f03401c14003c0d1506c521100d40 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 563020890 1250 563019640 563019643
    0x210106080c1b10051602010606030213051c120807031a0f13021b0d0e0a03030c170403080d0b0a050a03050619150b0c0601050a080607080405031b0309030f 68
    0x21101550445010400c0030403129800d902c1494520716541200c0460250f00000e0701502c0b82500c602818100c0824a039501e20340a01452002d09460715046050040400b07804020f00c0ca64416940242180c103043e1000b02d0754480318999442e0888003440580c02442e100803d9540c044494000003407520014140300d50490001c45242d80c001400c04a000c505c00342080700030004d58802d5036020384c0c08c008050820059184002000380c1d00b002512000b404040003918801c0f60f017100314417551100e24207100007a0030401a50341150400c8440040307a48000b10a0605d20840d0405044442c002c079000300e400450f500f0032a400b140540f10540342c1643c0d0700610240e0f8049000041c11604041c1c0061007600b4042c000314010000c500c40032510301901c06511026a4a9801907400890009580000c010007001800e0050105030b07502c108031071401050948501c0c010f003501c0208215100854280311040054034881ca8012605402d03480819481580d02d91140748414080c0c0225034480454a10 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 563022140 1250 563020890 563020907
    0x215010b03070804030f0908070303020109060b06030f04060c0e040e010506012d110102070c0305070603111e0d061a090a090605031c050403050304030308190c0f05130b210106 77
    0x155443e015100d45a65170160b80c0e000e400b81c3e522080040400d00000d001c1410403000006600a80000030003508500700082a40c1e203100740310b8042d0700100103201f0181141748600b0740c0160400780001e014001410101d5161079070124180d8020300708506000d05a8040d80403601440003602da890410400814101c03500740198a0001d19120040959007034034001c9011488444d400d0300018502070302c503582c05040305600c3c0c00c1990302c0c0d40060070500501d50075110314240302c11058101400e003001c0c5602500e0b200000722048402280100b04428100412b80025024106d40c541c0c0c50308180e000e0010300d00c560024149244100c1c280440002d912990348154015510054082c28290144082600c23801c490343c0c07040e40402030100000000304600303001800c06144a07a40d51420f034107080d00340f220720340000017030119094608ac0400c1c82c01500465030042020040c10b103240c403a4958651411050b03002e602c41c22002c4130003e84001ca207210800700100d6000d05044068070381c0d8852104a23031006 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 563023390 1250 563022140 563022151
    0x90e190e010905100911040c080601110c0a0302010f0c020301090501020c0111130b0912101a060a0f030b0a0302090408120f090a0f11062215080f071e0215010b03 71
    0x8004580d002582125600450309046c000d042d1003001c01c0500c004070301100c1280c000e4400051225091100c2d40da400099409011120350044c60702c0e80680c00010320300308003880000c1c1071007690368000400e6400360641e0404242c00070020003c41d10741d42440b0b4041c0d40300d0b00080c9119480c1010000c5409081010346540810307454800a616081900a00550b400302e0000355001415181c4441e40c0310381040a0849020341ca04007060030380150000302a4041c280c0e00c0f5501c0f0f40717018414030640350341c0010300340c804411915003c00e0101c248000701c0c0303a04946401c0a500103520800300710a10a201d0300503c0c0b5181c0032041210710741e40b2224240080c000030785812140d500680c00d064082000101801221130161408041d10b008000c0014203581c011444900c0b40316591966100d90050202000700420b05002c3d8000d03503c2d8421401031407041d00500800300b6150b82c8003c901d28a200302c0007043c0e00d59214941d04446e9002d4a806580c031002d9806054607100c180d0004680c515400c000d41c0d0040c0d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 563024640 1250 563023390 563023393
    0x12030b0f01180b1b0a030905090c030705161b0816050d0b0f0c04050a0303020606120102030603101109090106090306110a080a0506030c1c1707020604060f090e190e010905 75
    0x1d08188036140c06074085207130ba4682d115101404070b1030800600810405034829100c0301542032416040c041011002084608903510900c10071a0186e006400c44a520440306000840c01003140b901040341d161044c480300b0746048500f8041031510002402c0803441d10380e1441c00c5140b9039039008004110403540e5008100e2510840490a0044007030309e060b412403055900302e4107040c0c44d01e02059546180c1c0d030054005030702080c1403200f1428500f50005050464000a616524211022a60340c1c00c0c0c00784070031005a500c145203620050390788151036004800901d41c90303041d6960300e8010003001e620300041e540346280c2017008549201c000c0869545d61410b40303408a48c0d031b4603001c3c02c4004240003040141c050060380c0040042c0d60321005484844281c41c45c1010f5000a00d09084010307980c9618583c0001c80c040040c0800f40e528035061310106d411500c0c001c00a00e10104045a90030440d5005a000c4d21404040c04810f001421f096220b0502d01c42c0200204135214403010700343d400240000d0040d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 563025890 1250 563024640 563024687
    0x1f36053a061104060e0f0f010e0103110406030c020f06090703171303150e010506030304092a0c0209090d08061003140901091a0c0409150312030b0f01 66
    0x4010420546009810394040d100503046600d8950000b0b07070316035140e81c01e0308040004052100310b400284001e40030800f501c3c6071403c0c200c10008155040781c47e10407181400310158821059a10903041100a21a40501039031950380ea82c6014024000e1041220054050404c0500b000c100000e0242c0c41210a80e0007040018956201d180280e0780c20b1343c405041c036200b000f03075060b01348043c6000070007581718141181180322101c07150022070f08400101190350341490103203d465a400000d490590b9041480002c00c245821034440030344c81c000300b00302582da020702e039035490300d6400080e2400814002d4440381319590318405107030340b100c54000c0e18502140d0020042803160401545c4510008080e05001500451209112074010405c440504d00c681d1601c92200410001e00d484d603208801c50b4807054a9820f00c000c4100301401a4025049141d5071011002221401d03101448011a00180c00d0f0f02c1c203448440f8000e0140142016440c094021128182d031694410158080e890402095072200d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 563027140 1250 563025890 563025949
    0x30908060c1603030906050f10050a0f17011b180b270a0b0d1b02031e0c0a02090702150c0a0903030804050c091603060506091f3605 58
    0x1160b80780720506500b0180d072076284d1030006900d0b10803103002da00d90b841c10f50424a0554003040508140760080c0c0d02500fa030703100400c800c8040d01d8a00003650414420300f2044425101c00c0c500602545001100038a041c410514855420481c01c9034240c1120380c00c240301d20b8645481c00d0140c803c4065407101440f207950015044480d8000d054030f084130007810300c2c2d031303541d42d86c41141e980b42c01c61601100490b944001d055124841d42003140e450b0f0101d4006141484d02d12030b44201c068080000200c040480010f080c005c8040038041230101550003000070704d140c10720480082d50f802541820a008003280000302d1044500202510307490142a0b980646103401c5650496901c400507001b26424498000480307499072700c40070340c00d1050001b00c5082c2c032800f40d00000241652202d91111b4080c010401175141552280405084c1c8469205000e010503001404116031041180c09440b281003500390781c03a00d904040304581c0d0181da865449600503242c80e403040000004040310100003c4200308448a03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 563028390 1250 563027140 563027167
    0x50702030f0313050414010302400b010f020c0f0607060b03060c0c070b07030921050a050303150a0e070f050c030a050406030f021c0216020402070f030908060c 70
    0x51684040d003611640c01200914510355000000b01803160105004103015600781880b0701070400c000381030180410352654012030005041d80c0a0780030310501c072005003d0400312004403001c09001842c0c000140101400c01b1400070b04001c06c1003800182c00b186000c2d000b070302c00100c0700c0461384000d101080b000211420040320b988100800c075006503d035103800d080c03a03030140500c0d442907000e0012166100d114070401400c156aa40140d10940014080c2a011944c040120300c1501e44034034004010182d00002c0e425403107030000004002c0d101d6000380b00c0c00c024010005e5405001c8031404410000c0708407013000602d6425019000002e400a80020712042c82500600c07500900d90500c28a0514010700c0307503085501200d000300100b00005003c105a40e072600c0b84140c0e01c148a001141001031000d184040c3c100520b41c20010143c0108050b90711403e0022100b94850f030090003103556400d030385069000350700d9400e070680200d10300101c009152640494560f01c0cc404003801940b03008130000c0c000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 563029640 1250 563028390 563028397
    0x100f0e010210090b06030f16060c03050d05070e040f0c0e040f0b030a030305011e060e09060a0f08070e070e131e0507110705100507020105091201020a0507121d0105 72
    0x1103045110320038a40305002810710810b04502c0c00383e00704811034580030341890b00c1d0200ba144414900d9004044900042c132002c2080d4080e200b4910b8625040a1203003801c0f2420b014100340b620800b1b1900701440842074002d0078038850580e042d1340500c00c2501c0c2010030f400b2106814074140110b480909000864a0306610094440e00300400c001007050280010034a845c0c20008200c0100369038000610044103020703d54016005001c80d10402c6a0030854002c0449009042c6540640001400300d0707c141d81c1e018900c0d018094600f41080040d64440e0040e642d00050f100340c00c88150381030302051540c0e201b041001050b40c0041c20403e02000d07121086401060142501003100502d0040300624007854020540180c0c05039680c45200c0c8003410505003041150352240303100b80c0641854080310303500401521941030702402d10a80b50203412011520b9024200800100c951001440d80311241d0010090840907016801c5001d508152a0055900503080000b4094104051210541079032080004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 563030890 1250 563029640 563029667
    0x30d090507030c03081305040c0c23060c04030b0c07020603040f0602091f031406090115180605040e1803160501020c0d0806120303040b1501111504030905100f 70
    0x1c94081540d00d840d0910219180c0d0030403038203110002140c120040440340b14102900044908011203001e40790b000c2d20000172900002d01c0c072001d009030200400c131101c0c031008006010750b0a485540c9420140c00c1904e500901049440d0104900860f8008000c5025194003550203040305141d5141c6854107482c4166450003255041c0d020811114691991078802d07420902e07010305450422501c110141c15501c0350185450050300000800c8000d5890f118400d04591204a00c10000704240b4411680b03219101c04621442490032000280c1e10b41c882e00a1045401c240b41e20245a12110350b14203448588100ca03641541c030600c1022464801d941089102038498000107140c0b05400120f141050400040640855141e03020000d140c144460031118a00151010f5071441c0303455035500381c644c18040e0030040c0d0914104040d8100b6400b544d0308603480990303441110741058420000680c0709400f2a400c8000841e142c2000400c0c3c14a08080a61040c0c140c883e0700609a40b2a0103d5560080010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 563032140 1250 563030890 563030893
    0x111040b18130c050415030b030d0f020c0a0f0801110a090b090f090f09100b01050315031504050102090a0b0f031b04050d05010e0d0504050306011a0d02030114010201110a02030d0905 80
    0x200c0e0b07000d19485108601044115446181d00c1c4d034a020680ca840e80a044052020b141c20300075028203503a0042402c0300034030751a04241140c00030100d030407450400400d05060304600320302800300e8280e68400c10740d4200d0301554000d1041d40c42d004c1d00d881980c09850f0480c0040f81040105003c080f083c5002b0b00554000603049241e500c00704000030750303051029a43c2c840004500010b0044040c3c050198500030740c0c00d08030038054602c014000070b201c1d1000405140e0012800c1003a5600c0740da050008800f00c0f810000405164100303030400a0003544580f51745c61080550300c80000d0060036403000d1b03c02c0c0c1c44103503103250700716500c40c108010b14000007198409400b9042001042c80d0340e900c54154422800741000052981468510900c2d120000031450240b0400740801c101c15079000812905507008840c0120890f030b840446103403180940c0103010540fa001000120300d8044150b000c90f02d41c0c90903030080c0b09842c000000f01d0020b02c1a0340c0402c005800800102001c10350b2900035580041c803410 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 563033390 1250 563032140 563032159
    0x5030c091c1a0601090e0604062606070c0c0b03070c0210020703060b1912080c01090f1203060f06110703021002070612060b0a0309021804140111040b18 67
    0x80000d40640c40341c8008030540311041c805406208a48400040c4a00e40161644081c1003440000e0304d220481d118101d03404031040300080540d100c6400002c006d150310381c0c40700c4e1544007030203116401d00b07082c81ca4107840b8030460000600342403281141e101e005401c01449803045040503618001d640c40100300c1c2c01030100d50a0303010016100d0f2030b82060800c50320360162000d0382c1540342c03803810f8584010040388a04114030075000092480840c1c001200d02a00c14285c007040a0301c1c0c49403650207414075034500c551a00c04101c06000b450403401800078425440030f40c058000302802d80482d203a900030041c44003403140040c000b0034051460861001060b4044600d800d82e2a800a05542c4100c4030040060300400020800c0903089070788011444504c6100788945414241d51100178001d05c10a001050f0f205c102420554a80400034280c0750980054282079240a003031100c0c01620082c5070411640c80c0216801c03c0e60381c01015a4140d03002018079901d0481c110703030340600f80c00050032207641c000130701c9 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 563034640 1250 563033390 563033407
    0xc0a1b05070f080d020f10020924090f041404030e030a17040f061706090c040b03090604050c0303042301030e06071d01170417040b07060f0c020f0a0305030c 69
    0x100103881c0106414107150a8090928807440e05083d1404694000d55221111801400c2004552800c1c036200c801d00c0107840e01e01120028040205148801c981901030408c0550345c2000c1e0401085e204030180c079001d50b110200750510007103400212042d0845c00d2040d02140020744a40c42040071020f005040f107660b4003140c3c881c9000300c4c2c900181c8a02c9100c0004003000140c0e0100400c00051025040655400711846080034000c00300401540c89000450300140c7d03d0307207004003900c001d003001490b919141d282c0402c0090307550768140e6084e41e00d48a011503104582c03600104481c2a5502c0300b421504e8400c0021481481c14188140b1606040d110004554806810400e50b0f01c138103400d664421400d4101082883e203507489406181c10400c003460b01040d10654074a01c035403c1a8411041c441c00c85c890001ea02285c01141c0111480d0440018032000b802000c0e0003405c8000ba80c00700410010f40021010b903074902c81c50402a040780c00086025012900170030183d0782c4048003180d540e01c0d00c500c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 563035890 1250 563034640 563034643
    0x712211d090c0904110304020a060c0206041509031a07021b1c021f090f050603070f0c020d02060c0d030f06050315070909110a021e030f0a03090203060106030506180c0a1b05 76
    0x4107000b0a41241e8040204403d600c9c2c0211203400905180c1086c4442030219004209240300d81d005180d880c100c8540c11302c50140c45001800d00860300704015052602a09014400c3c400054030000300612502002415040e0350f900c418031508401400a00b10003141c4440000720200032005982c0480100702c045810303070020034031308002c0000d580c4d0b0224541c1000703c1c81c0042d9103150080d6006080034410084c42a41200c4c0e80b040c1d8408500301150a03100b1440080c100006201000350003c20111341841c2d03081002038600720b001800e032000d11640301c1d40d0000e9411106541b00303942d4554007540c200207401c20002ba11541000291804113409510703550f80780b060703400681004060f10750000d00345070900d6040c040000c0c12682d59020000710029a41c0d12944c81c00b5400703000d001c5800005101410501036480702101c50390240944096680d03544028004110840e182d600800710008440200301c04000e08500ca4020100c455040032a411411035169485c032920148807101210f0000c0403600 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 563037140 1250 563035890 563035901
    0xf0138071212050403022806060303090611030c0a0f1406010e010303030c050903060610030e10020705150106050a0318060e0a021009060503040f050712211d090c0904 73
    0x10a540644a45640c000800c002d9208040d0042c540c0342c40240700000e54085820b1038240d0459035001462020706400d40060200085c1c01003900d03182480000c00c040d00300240b9002c5035141c0c1c07581e8403a0b003c55105182c0b82d00c11480d84480f22307000500c51800240c1c0e00f241c1d02440c28020001c0c0d0032007822030341d0300b00c0c90260207030801d45a12003085d00410805500d40900d40784016545441801c01e144080400c0e0341360300c0900828481d0040b0300001200522a90064200020140071a0119102000480c000b984110421381d8580268009001c2103801590103070704032902566801c9c502210001d08800400d52061000405200554250003040107406610210311050b400707840d0344002071042110410400c402502800615441000140e4102c0c085e80ea1254112002c0d00c02c128a5182050070701c5465002034000f04c1d0302c0c5404600b40900c06140e111f0102e0015135040060392141001c1e01e410039036100340994608400e201d51a84c3c101844070a821071a041c00c120308140780400011709a56 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 563038390 1250 563037140 563037143
    0xb0d05100503030403260903060a09030519090e06090910090302120c0d080a06180e0c090c03070908060c0715060513090620070b090a0b040305120f013807 68
    0x180c0203102800003511800c6c800c0a002000b060392460042d6900109489000c001e061910f81c1e81d1714511981454019000c45515407201d007106010b5108041e4094112442c6010b880041d42d2240300240a60925039019409070030080000c05a120540c1c004901802140b40101c046004040c0114240c803450400381c06d10364025009003840c10403090380100f129800825005000c0c0c1003a000308510000001c10301c100103020700010500001201c04145032410049440d50090007030b20800080307844800146001d1002d03643d884040503500c0b07031525512171003501c404080c00303001c01008000a40000c0042c1051302034000120749595148001090300a40c000c06542c02a22000e01c042000100d1242941d4501403020518900c0016200c40b1054012030000404030310844022a00080e42040141d2810b0b40c0607810321600e14191400402681182c0e560351031086607030780451b040c10f184603100da040e42c034404101455104821040c0c010017103545443c814160200d8a8003003401310100c01004103d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 563039640 1250 563038390 563038403
    0x12260c1b040b0406140d061112071e09270507030219080c03010b1303060e1f1b0f03020903010e0f0d020316020904021305070e0102160b0d05100503030403 68
    0x11039401081c041074070602e40e01c1c0ca100d1854990300b4081c05da041c0e103c002a44500740e490207502c854515011004003050140c82c1c06480700403510900c0746d0b00181d08a40300e107140380d8448032441200c038581303191032403003811308000707d01d2855092140315507140a03004102c4aa51103d244040c4003a11401291401d0343c030b6000080d0001441c00040c030368440d00990301c442500d0044043c0c50000b042442e240410b001c1d5214039900064090700141c02c814400c0061034000f02c040054100002e6030666071903140d400d61040341c00e4810b002d0340e09a274078424403403040e542c072000b64110384445038100c40d08268401d0729024540e0a002c09142038500740714808130b40e80b03148014003912546c6c0445a1030300c0c9002024808551040140701105800e07801207a1a081d4180e40041664a6038800540415045602c5d403d81c0b0b460300c400c1003089617000402040380c0e8801e07000ea070311040044500d00e1201c5041e00034840381e14010800506814000e41c8900e0f840b04107901030130b140548500c002803c5501a510544d0351 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 563040890 1250 563039640 563039683
    0xf04050d1106070c0311010f1205040c03020303040608060f100203030412030e010903050403170a050409020702040f0504032007121e02060f0c0f190b131b090612260c 73
    0x2c06c050406050581202401c1400102c20740c0c49000b446020b513550010300d65034580c0081010001d110315000701031540181038036140c0b600c6020007070442400315002c611032610b0060b807602c070b420300d400e060b07406088a13409540b840d603c0c1c0d11540035044030710410f4400c140da15103038051403600c284982c594080c804d0781c6182d5100e01c6e500781051060b003403012178554450100f080d050348507003100c1201d0480e400c1120140c1c4804050000600802d4041100c500c42400c00081000301544441c6101340f0640128003a48600304504015644804600907620261540c039441c901044420542080c002d0580003182d032140b1180e0f0208850350804031242602490102c2d18880801d014031020b02103070003110007421140360030b2050b401480c0d04202c0c0030701104184400701b0031003000760440101c019003010b8800392031030704202a0094840035104e0080894640b40011881c00311a80701075142580180a580440d2500c4540607150030400c0814590424200840488801c051108140501009000842 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 563042140 1250 563040890 563040893
    0x30b0111070501020703020d1b09091214030c1e0c0a02030f0f0c010f1814010f02031303020613090c02100b01020f0706030f1e0615050f04050d1106070c03 68
    0xc84500000a004a078024290500a99a0000d43c0c4000c072501192031100e40d07502c608288000d075104111286043c5000c0c0c0b00450b40030510740120380380d01e1040008200b03401c2c10540488403401800880c031462641000403030213402c1d05038081d0001444000300104824408010402030794816004c40b011601301034000401c0d881c06111301840000b000000d01541d01c0400301d02500c4c3e0b401491500c2c1408800c01008020344e00c20322482e00054690720003120100c1d00c3e2000d064810303050f00c1c106400100032400f9034040070300c08000c0d210410810000c20507054215801c01001e07070841d040e1041030b092403540c000f07102c1249004d601c1000225030068201e480c800140b0b0410b991148003114159448070b680c481c1e42c00b90000e400c80c221403080c038001440713150310058103014161007200030081080003159a6440e80d4180e2100342141c0c1145000345902076440307403e40359400f0300d45d032114003400c092104001505244a800e04214801c94a03c0141c01ca0540010b00a410034803040d40c060f14070090500 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 563043390 1250 563042140 563042147
    0xb03010204120c1d010b070f0203010c020703120219060902040212010b0d0501090e0c041d0a0302250510120207080c01140106080c04062133060c240c030b01 69
    0x901a01e080c038039101640b004140610300401303041c483c0c48948040002c01405014415421013003d5500030001d01041ea550b60000356664064042600e40658000691514600002e46150300040c4a524414225000d49030b0344000d048501060340c016408006010b21524071030541d5000e4403480138003586a544c140c943e141111416003106006a103041e08003403030700300300041c00358180c41b003142e001ca03100d55210300003000300010040c030080611420702940c003015000302c0c19000c40c40500804450031096449020341002051180c070350002a0030301e60b22800e900c20b40100c0c442d003440b42405403419500752342e07609403035100701b071300e4107540c1d64583c5030800003826450840d0061100e4905400c9030300b00248241d08903c918441c400c2070205046500c0340c1c51240f002e0480f00c7c0094074004200c00e403c00002403102c1c00340442c0a0755180c04131002d00c038420154080e00c006880c036554940c041c030300042e56841400500041d5030040d14104140915580300e440c01b91a000280980e4082082c0c007030500050b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 563044640 1250 563043390 563043413
    0xc07030f0e06030c07020a0302040f09021801051c05010e061504050f150402250b061503010614030c13090b040c0801051507031701080a020a0b0316120b0301020412 72
    0x24041208080c603014070756490300103580c1c004141c0c11145550745100e20008a20310055440250000d050681c0505407000c2a805906200d0094840c03030186000f8501202040c2c0c1c09004039035221094515100c40d400e540142840014800c400000340030040756141d9107008400c0b504d031110f401c5540180845800d00d4094079402908049550006052481c419800c07003402c02002800389074003103030308100b04005601031141c514901c50070312900350786810041e02803001240c465014004c16203564011612a03003c0300e04a584555920010100d20702402d000c9030300141a25803c82400d10400074881074440100005104914002501c07065020900c01982d8503100c2c440c00f8407141c00c0040003d0f4403041e0200544005044006641300d20034601612195201101c1c60b65440300303400040b03080d1200045903078a050080740c090754220b036140c2c60308040784400c640c8842040e540010250205014040e03241c840c0d13000c0707074002c140036240c0c00101e8226005a4041e00b070046210040c50188042d800301d0303 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 563045890 1250 563044640 563044667
    0x906061206060d11010e1c060608070e0a02090127172b030204230406092a020c031b10030c0503070c020406090204060201020a030e030a020d0c080f030c0703 69
    0xa046140b912100062080036031601c0074140c0c0816604900c0942e204522441d80b401001f0f02c0005100c01c02ea4040540300c1d41500c045034110300c0c0000214030044000b07108011992000e07141d4000d907a84410000103500204481814170403104866211009990207a40e21020043c182d058020302c1c01400c1c110800380301c084034000c1d401a0a62900d03c685502603507508000c13103c2880b14402c01a00110001d02c02c992061801300011940c0100019280c8011120480210380c240301017516051490215080818090940c2c4410502c0310050402d00301000420407090054644100700003002c01d08041042031031421049003222080c00610b016504041c03a502c0341d29040041501549001e495444094129002e005102d0041801c40d52180c00c000094042d1032803d648807907032440080c0c0030b0b40045c080040031074184202039070204c800200780e94200b02d942d8001c06241103500001e03128441503140607900c0d44000c00094410f40540002980101c085c4050b45a440105040041c02c0072081800e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 563047140 1250 563045890 563045893
    0x504030815010e151b15060604141e090a0c2601060809010f020406030b2e0e030a050a03020c180c030109050a0b0405070e150c12031e09060612 63
    0x104180c16903480803c81c0400030065a1003010440c05804040c001c4c003030f000c40808005110042d0032001c800219000c883c480210345828080e031200e10810085024602502c04046010b000400c054500813460352840e0f0059a844a031101c5c90307001040380ca8104544034101070342c4a0411805459104204170039441d01000c0e40030703880148104004058a040c030580c02001000004070f154048294070030b00c0d84c01d004c5c0c1801c540c0d4075503070b13000038001d010000da00610030744c050b034603c0c80300041c0442c00c1001001d40c00c81018160b00d482500382d4100c0c100110b40c0b901440303039001035000120108032000020340203800511000c40001c0070030180301030300c00914481c204824140f1150a608070152419030f00c1c03003000422183d43d900b01c40e80c020079000018540c010b08180502510a0f00244090380302c002c01c0c0c0d908030090703c9400c1088501d120796000500e25600081c8010708403400c41018540111051054031040c00d03800c6218056042d094480344d240f0303001038060100350300d0300307113000c0c07040b07600050 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 563048390 1250 563047140 563047171
    0x90d1205181c0b04050f0d0903120c0f060e0a080c4e120a0605010201060b07080429040306020d1a1e0102010e1605030c09090a1515030605040308 64
    0x30001090440d11960040c04030034400f0110382040707801d00411100d01c0750744003101e04405e94468001c011400b00d00c001c9d40c0c2000f80c01b51a800d41c6104d0300020ba1040d4100b404508844003d07950b0300020240404065418020b040080c3c0c0021001c600500715242c2110040c80c0001407041001041071004100d400403902440309c2d9990107040c0c0c240403034003108016860a8007421481c2c2c0480c944210300c441010440d08804001d000e0328a03070321400540d14207a000b0851207458001041c4607108a14014140c07040c28042000040c941c0189190f41891641490352102c19140c00751800d90055042140c1e0240c010800c050030085901c15035500e50b00d0302d10042075550320000443d9202d0030504c44295501c000003290407499000350001e01d000d440d03401c2180c110503d520a221200955030180511900400c1c8190800b4905045000e0107114000d010304840395403947d5246440c0201e0880b44046a2541c2440d40d454414046e4580254041c50740401d0502d054900284a01002045041d003100c241 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 563049640 1250 563048390 563048419
    0xb1009031a0f0c0c0718020c120a051c0e0706110606040207020d020f01030b03070f051810210206030c030f160518010e041803180b030a02090d120518 66
    0xb0358565070007a42e940290740e6180b0b1981d040600b08052038002d0329060542c41000030b07502029a00400010423501d09658030312112003481540c912415500c10006101805803d80304405a0074010381a00741c0700d0000b98140038100058180781c01c2d03500610124041e0310f840d0151003030500100303510481c11641146003c24940c0018181c1c0c001c40d2001c0d01440d0340061500e501c1e40217501c1400480c000030304503011070360b03559074646558101303000c0e041c06240c0850040f031035403071b0700300c515400303000000302c0c1f00e0b451070174403a6412028281405900030a02c1525100000d0b03262000154041da9030346501c01d0f900e203410003000d60360307d0011740721082500c801e851701c403c11b0341c0c0002644c0c0d0441304485003515040b03d040049500c451840a015841458810401c40050219842490341403280e252030a00600079041e940041845100d8810701203010030000d5505900b070390042c051020000d0100103540c0154803522518000ca41006010850009448922004440c080300c1400000c9600440c8066113 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 563050890 1250 563049640 563049661
    0xc0b04061d0102010209151308010902100e06130b0301050108070f171306050a0b0405070f231b0105010521030f030c12040807030f0c050307020907030b1009031a 71
    0x15122a06100601074100d80340c0c400e40488440300d800400d480901d034050240d9612039071207550b080d4089000564001200d00041c010f0b02880b540040001141841c2030a00303440105000c8035040d0300c9003081203100b481440c0c0c49454000b401d90111207136200d44c14540094031000c0043c0c00401071000c50b000010701280e00c803060001c0c81c0c1c911f45482c00710341c03603038055180851f5420702c0c018a020f0620f010015406003580c0850301010003100c003440261036406040c2c88035050544110b002412000c2c940074074208611000c000a032451901c1031500d0418002c0781c6001c0529681c030751580c0d442d0740c01004145000c809503580900442d1b1402e44040c8108080d981ea407240d60324400050b0800300008003c6060f050a8800e825105440001907240500d001d0001c0c0d84040c5048020503400c0d805015020703c1110228001a0722100842c0340802ca81c003040100c0c080204000c041646030100e1032142e8075090350001c4050304648590303c88074114903210408210395000300d544102c2e00e00800c0850f503076 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 563052140 1250 563050890 563050907
    0x91202061b03040f0b0c1608061612091b080106080d0c05030910020a030809010204050108010b090f1f090b0c0d0507030c1209080f0705130f06051c0c0b0406 69
    0x140e4100c0380d1141250201c0d21411030040364000760030b0203406000000d020141e00010003040c4204000d682c541d2900409440c0710f4806402009183d9001c080010590608525614054246c034200038084030403101100c4180c5071242c6044400740b564000080c001811030540c803000d84030b141e000380301c05030410540340d6565039908061801c02c0b002002850a1203003d004031010040094049040c041040d40040d50391003035010118001040080011b06100041c030036141514016518101c550740307480010403403030304190072240d030200350228030741c08076030744c2141c1c050780c410a003004043e01c0b241250014014a0080c0e2000300c03504001c1014809026000c05c490661031103504080c0d840301041d040840d640d600c501c500a0a0701c1008030020200e54100c0450340c00c4070760000403141c8a071800ca02072511105944070710f0390010003440c1e003202500b009400c540ea0250070400005450b84d551800100c8842c6000680c281034014205200c0610888000c09030113019540070031032405141200c010410074 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 563053390 1250 563052140 563052157
    0x40b0405090f0c2b06031a070504080309150909070806040c021504020105030915130c08190809060c0102070f1202152805090c010909090b150105070515040309120206 73
    0x4c1c22034040b4194498040b00e00c64860345400704011705600c80c5421026500581c00070340c0448405000200b4044c41101184c055440b10000b540c200b20302c400500480c80f0140b440d108070302000340314020181d1904003099100d01c0701c030303590b4811905100d01800f0031608031103001e4003103400c5240c0100c259070220b1070480c1c00940c2860415541d03502c0d46040703424030301d03130700e200402c04100d40051144150b603600c101d500301c038020004c5a07207996a509100350303111200520004c0f541d03c1e9000040c0807440c0310b0302901c1030010107004141390001e0316880b542207910046003100c1c1d40080f10000360031310414649081311800b04c3e000411403664103407036480045900502c0a140c0901700e02e042000c481100300340d54555040c0c0d020512050410810451f110039402c2c440b9400036056010005006c5182d0142141158000304c00301e119460f4041c11440313521850801e203050000402c0306c4800101c0420094914503e11408860641442d1400030700305102c40c0d104040c01402501c40c0d80259855104564001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 563054640 1250 563053390 563053417
    0x801050d17091903060b211905010e030703052205010c0b070e0a08030a08070302030c040506071a1003120203040e060f0a0e1315060605070b100902040b0405090f0c 72
    0x500440001440c2c3d0144514074088a41e2400c40c00010040a9001803400c000301b2071f0036244003019940c1008030031a0381c5d842058140c0c04410304507211103a4815010149010301c00100d40c3c00b101c1c01070203203542e0101800720001b9000041c0d44603160310400150003c2c505810282c0400b1340362900082c840d6014980141c6010b41810200d288a8007505a0341c0540300c0c06880607041c2907462100329260303040950108003241040d030002c0d081038820300c2201c0c03181812416150400d414a0144045030f00211700482e400020300c248282461082d5030000c4c4145021119052920f0a52500d14180400b10304a04199442888144040649880e502c0c0c4e00039419207217903040b50b01000000390251415841083e2505a48042c041d20750260020300041034042e085044403013500d4a85001140c0e0f052140d040054800e200b10b80014031a0303d203030f5030080030300a80d800c540344c2c07031b115000304980c00b03548564442e810001e42080181000c503119680011107000b502c459207405030703030341c0301510601e503880402 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 563055890 1250 563054640 563054647
    0x30a0204030b1501030e010926040b0c031b010203071b0213050408030601090e04020307150504150302090a15091401020a050f0a0b0c0703050d0b01032a0801050d17 72
    0x1150164162001950082c000d41440d04104802060702c015408005001a00f080074010f00004c0c14090b0b03c50444c2d00c512502d141c09002c4100401c0a01d40c089200429101003100040504148010f0308620003c040078641e50040c4915030b001c0c5a0706181c11400590040c002c00210070b4100c0b2400c01403450040801c10400c169100180005110a60100c0fa81d40703010244800e000c0ca10011b107205603802e884840c500307510390540c124050021a002580b66206080c00c1c405128221a00503502440d1708000c1d007010348802d001546000100700003400030360f011070000b84078544a00c1040042100c08510404030000620051840000b40502e02c1c064040c03440302419030b40b023048005081500481a2181100604200b54176100400d80642d1700441c0700e00840c1e9050320940c11506040d1341511254034000c0c0118030000a81000d1008505041d07960164441c500302c1302c1901c400c080c040c0308980030711107100072021700070b4601a00180c2c06a0f800074120000640c80405154a440180411944 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 563057140 1250 563055890 563055901
    0x6030405151602031e120f2d0411060408070803190801080303061504080304030303051009020301080613170d1b050901210204030602120103060e1605091003050f0304140f03060c03 79
    0x84911901b40b45040070744000c1b04000d004050740c820356001d0740301100034600c20000d060701c000e05414506c82140c0c1195015000c1000548144284c4104041c0500481d0038a9a6104183e04000c1703513a102e00901d0b000092640441d410103012480740075075070b041062155041c0303d48156240030040500e0f0141c6035011102c0d000b032009400351001018510216540c03140c030703480c0080c09040b090b00d050119801001c00810040c3d2940240c80c1641c2071580141030b22341c0c0342c4a04a100766020041580d1030f100200f0209008207241000f4181445003a80c0800d07000301d910315a140c0708862022000410805001090160380e00c450b4aa04404001d0983c4400d0b95032018540e00030701c03031540020001480003600240c90244803107518100c0380251420000e446000301c129403502198174149101142e0303a941800316241c0868403c2d000100040d0f1000c4030f684a07a15285000c400f08801c480f00e60020408001042c0706c03c107940031480c01940da44840c060306c840860754801020b080d003814038501000090 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 563058390 1250 563057140 563057197
    0xa03120c050c0103051e100b160201031b39030e010807090f050d03031407020c030f0606090105120307060f0e0d02150c03280203061c051e0c0603040515160203 70
    0x40509050003402e99072703145a440500350728401c48401c0740402d00300004d44002032082da0780c203003200001c0e444407841c07910001c040860103e010a070400111000d0322100558001202c80c21030703214803c1d00c941c9480c5141c00c0003d01360100c01444241000010003050000c0d00b420b0100008540b025102602c01c0000d0340f4058002e40100700710000c1c00141c080411464a0340000c1ca151f64800550a542100041031038180d21824111100f40d0040039403001007100741800d1030b80c01c2081803060309403070400c580c9030340725016110040c015107551a210171900c81344210900c1080f1038206540020021011514500540c0000c010800c510719100840010702d04880100a492600c451035581200c00e0b8032246000c2c000d41042d52490b000d616488030a0001c1100142461402c0d50060700070070045960801d240c9543e00d090302d44403481c0c00307500c4070b0030340545604001d5405248244050941c02c44400281c1d90706080041c841d050321510303203c86040c10b5801004903682d005400d002100300744800b19400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 563059640 1250 563058390 563058421
    0x140109051c0c02041a04050c03090d0f0e030105040605010e01060507110d0201031b08090d05030c0d050a110d020702031912030c02031c150906051e0a03120c050c0103051e 75
    0x6500a0700b17201070404041c80c5c1c0b0ba010102d040301110100240d0700c03a03038030b91b010f0b03404103c640006550210380942c0702140034a141200304455840c041d22410708030008207080d540301317581c00c99a581d203500c0103000004000d0340c12800b400b01454940e05002568aa41560400041905002e80098000c560969203e50001c01c3c0b501101c00b10511580c4030100c2c020812401141c6030750f40b5009500992507124401c8048030b005080300c0303401c0c9003030003080311080008160190404a84607500c4c00510036800504002d0040a8011b80005864900b5401454181908908c1c1c10302c440380c81d68403400008020f40c030b5000c94804646000280e05000c0f0030280c0c0365100d02d0a1401245034902c80e1400d203000c4c036420031070340301c5400e40003450311070f0b5210690310a41c0d0b600c4c01550340c0078180010440c407040307400c0514010300100420761442c00f69652070304806404c80d5440c010009144d5640e07038013031110800030110310020a107000c0106160050380f00c0c5032440c111540010b207100d11000304d0020350f00030b26403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 563060890 1250 563059640 563059643
    0x20409050103030f0207051f08091609020c1b150a03060317190c0b07030b03070909030206070f052811100e07060203070b0a0b060c0d03020304140109051c0c 69
    0x800c42540c60341406081410016103e000511a011010a0a083c4424850307800d880d181e10b0329010400701c0e601076035580e900034904405841107011100b131010145032003000415540e0790040c1da0700c0140c00ca9074100030000010f10b108a92681444005840b28411842402c81c800541c40e03c818001d64120301800b65980050448042c14100c032100a09260090001c010000408129072840800944d1100b070f44500180ca99801c0900051050340690089604918014243c1c1d03160382d1078950220850326226000e40c01a4040000c004009400c010400440455070500905000c402c2118041c0040fa4903000429034484080c050082030080c08202401903240007550f4413100c1c403101000060001c80003c40d100d00c030345440010242c0c0013008940085030000c2d20b42d81d01d50396200823040580340a0394039030341005042204c10164001070060991a61056901595a0609080131540207801c482050301c0303649407594039000240300040310011203141c074409081005c00c8142c2912080c440850 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 563062140 1250 563060890 563060909
    0x50108030d24030b0a0b0f0f1c020a0b0a03061e03020613180504020306151305040809130c12020a0f0c02040b1002011d0f0706080907090612030e040203060307050906040204 76
    0x841007128640740f0900c45c10108208000d07924000c010410031207a5844504d403c0001030142410340e06201201e04034400741c10115502403190750340440c0d0350f0f0106a104c400c2595021941c4c3c1e510031384c5800381c100103010050041041c0c180c0d44400100040040c403000b48200301c0090650818240c1001d040c000700284031078013821404400c1a1409403000710b404030311a02890000030b160b882c0d00c9400d962000000f0b0882030740c0030301c07103d030500041401400039240c40d2020b0190f0956940d079080b241d50b1501c038000d000710f20051000300c01b414071808600c030b0700d00d00340c014040d2060442d8060034180c501150780c540045400e4407400841d008200b0080e00540010700c0d100e014000f980c0540200c0001c003064030340080414030301d80d0340d00c0e1038110f0f02c0d64442843d0003060301000528403c243c5a0340003640350058400e4169644030f44003c03070f8001e91059240000c801202014075821107141644048181d500b98510304d02203001a0b1107407064040d841c4142402c001040040d25168103030780c0500700005 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 563063390 1250 563062140 563062211
    0xd090c0f120201020c0103020307091a040306020a050c2b081902040b120123010c03020309090a0e0c01020d0504090c122c010e0a031407020301060f1503050108030d 72
    0x4071046055200d01c416800b6114040c0c640030715500c2031003228410141030380c0d02d0000c0c5080c4840c0c0c0700d81000c001790600d0000c10a220200c00b041c2184010314803403400741c90f466a180c0c14120142e003000447d900700200000c4040148400d10f141108001840c0d0399450003100d1035940d400114030100840f40304690240c070200380410603149900041c60682099071182656030b07aa00342104818548c44081c3ca00d100341e010204a130f550040c07041c3c00b41c151083c0140ca0401c0d00d140d0204000329811102c40011035240d005d9900e040c807003848070b811000c03428800f500640041c140007800c0c0d4801c0748110f400c4165103090f81598540304000c000007103140031001f808400000d407074080208051358200e590512640541d5108442c05104a0001030992000303410302c000305440c10f03514260300245500101004000d0f4000598083c81140054280d034800c20014505049071b06849028020803842030625000052000140c00411390380340d0702d50b60b407000c80d621041480d0546504000c029483c14445000d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 563064640 1250 563063390 563063399
    0x4050a030f2304060e04051005190b0c2109010c1101020a0602040b031006092103030b04021b1606020a0f0f05032b09083a140108120d090c0f 62
    0x100051003144c80950b15440c40c805030800704812203000f5642c81c61a912085002c0001e13003081e845620101d840c15100d40c040c3c603a224600b0410b40d00c607001071a8a5000b00c081003c010010300d0300798a030042180c21082c03c051a110000c0d041c13000007100a89070141d91512009241c1c030801103100d5850740500195207690b6103944040158106544c40810851a07440205450748500718040441e0300d80b81220840c1400c200b08060f10042030041903040544680301c076407040c0c940c0c1c001400222000c0f0b5564a102e00516021410400354070214210300640d40070802c003490b0b00190780080303a600031400401c8140c50346031070101e14030109402007443c0030101c3c2d00c00d14256501039144200c0003010b01d8031a0713940d00c110780c18220f59190034000e03c80c0300184503144120354015880f144d410100c54050380107010801e1410460803450403107962141e02c07100f1002100d0b624191150040954000409400b4580c1c84403001a0080b4900712400340e03602c011017400d100c1c1484810005051485403074506640703a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 563065890 1250 563064640 563064707
    0xb040b0913180809030708190b06010e220507030513241b02070b0a1b02040f050c0d0b06031501050313020a060c02090f01180c030b04020a110d0804050a030f 69
    0x5030307013024441e02441d540000c0c01c902c08555181e46030071030013803440025955075560b260300401030031550400940b000c42d05001c1d100c00351b00c1d402c901e40e00c228403444005406002816036100404100405060105010b01c40002d00c0c002c44905a0001144400141403007c20101c04c52241f00641c18500300078404034100b03980d511a018481559080d20381c0a6203d8200b00614403506811000181e003a00c5130b94a0780308100c14040403684001e1000c144403450b00d40c604140d07076054070380806001002070071200000c03c80c8103545445c8000d0b2071036429403800010030303000024024403840c144a80000000c5114503003c0b00054a0b80c0d005181d442e0442d00c80340010043d51842400701e008014001c0400c1c2061801d41080307048500000007141e2050315484210701401c820003105081c0740d2a40642841a43c5600152000112665504c000601e140c1c40f01d504c1e0807401403140c802d2080da4002d02c030100d80d001ca00840075681505124060700c000c414100c0c6c00203600c0c4420b6802e40b100554005000300c4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 563067140 1250 563065890 563065897
    0xf0304031b0b1308090a0305060a0e0a020310110408060906042d1e050304090504022103090f06040305011d0c010e09190222050a0b040b09131808 64
    0xa80c0d651104507a1418524848210103001601d0319000100240c4100b5100140301150f62180c1d07005410000320304042011a441900203c582e50044420001d059226104508180c81d102000300308008140c0c010036120340314020f0b110361141e00c41240c0403041035844100d40060400e101100c1c064542a2005c5032650000d96046070310b002e01c030344501c2e250032105424645140320035540c91b00002050380c1c1d285d070071070b10382d80419220300c840407000c00407500c240041c00040030303600408210303460140704011907481400e0f0b05105a80c11038801102d006800000e0700c0b04440d0a482d1040300201400008000c0d01403540001c095600306052540c2d2505500c07003001d8414105002c46081559410065514019405c2c5180d00181d0ba1400134a03010100310310706086080c0080300500e003c80459880140d40c0031810004c81e0310035460020040e81c181001182c3c0200228120241441e0a0001d0921144254400c06100324241c001140310102c0e1f81e808038015032842c0760b0100c154002843d10010790341 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 563068390 1250 563067140 563067143
    0xf030d050c0c030904050712180209090105010e1915060e0a1521020c0a03080f3313020412060b0907050307050c0c150d0507020a030e1c080f0304 64
    0x141004041a8610502810350700c60042c804051824580441d0a0000411004003008104410b11560603020302807032085242e22048034882c049070084074018000001d002801565480e80742c03100406c000306426807020b8001119080c41a000c84440100c100500003116103001009545c40780090419040350207440e10010543d8481d14080d55803844401488074002040081400e000c4188030744c7c0c3c100c000b2804046d1141e43c00500384660185200d00e0400c1403d41140424202010b2004c42044a00c06592115417585a00c510841c0a80314103143c04400c80c2009030180407291030700c3d071551151500c02c101c2c1580e03642103440e1962520018400f991101098520900c5c05218500604101541e04d116030210f071115880c5480303081c0103d03023643c489911b0501d1801001420034240da02c3c161000044c840140b031450300c03406190840400c0303c030003034030030b0040d984810800740c0029040000308160040886a02d125145902140085813100660040070b600300064007010040c5610090f5014a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 563069640 1250 563068390 563068417
    0xd0501080129040f060e1003021201230402010201022b0b010c02100806120304090902040b040e0d180519030302070b030106080610051b0106050f15040e090c030f03 72
    0x150003603a0804010341211002075650307000188140345040641101c4c030b240d00b68040c0003d0842d030381c55003441c419400f0b950030303840841175100030015890045184040c00b402c5000800042c22103012010a100ba44105110488115000030307007503a00030350564240c80c03011b440700c40d0340940300380d940400b80010501281180d846d01c96504415407150860100055018059043d00d81c1c400c0c0081c0c608240050001d5804109a048001c1f4060140040c000038020410045545842c0b84100020750f113030780580600552404900c1c00188600281401111a44e802c00c00b2011041c001c10720002240381d01724a80200c68104e05549070940b410581044900075400e4840380d5480365140e01143c4028820f510006640300d0218500740742c05c51f00c078070303038100b56040061901401000400310140c01c2c0c4004d400c2655603100c00c109909050000c0d00c07114000316818010800e44800ca0b003100c0c0110b01450b10007100396000200c1f105030400100701050b00050071140c1003040b0f00780c8540c4d00d6000c41c1c1c821141 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 563070890 1250 563069640 563069651
    0x712090c080613230705121b0907050d052a0715060b030106030f0b09041401050c0c100914160311090411010c110a1206180f020108040f080d05010801 66
    0x100444601154005901460071610030440315280a00481144001300441c002d0b190002945e588400c07024030128030a9001c0c004400d002100c14000c0340001c0e40c51402000d0030000c05c920142e202044030150940c05200103190741b1020240d049129004640780c5089c4203c7c50406920100d1502a2051510600c00101c40c16101c0301100103842c0b40348140c0b03401c40010320050000c01d0081d042002c20741040180014121140800140100b006450689020381412454a400b0000380100d030b27400241554081d103810984140f07203a5900b08190300c410041c1e99000c00350200100d1104c3c0205500d620740445100241c144803219041050748421074501044180a04860601c0d80c402c91041d5000a002400038086000559404078810021150303204805004406c1b43c2d00c1030000b001400003500501c007514418a0a07000702c84540aa031035205110001080005600c0d800010f100c0740d081c60814003640340c91410108041052000420400c8040b40209008070a540030b54101c0d04030000070704c02c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 563072140 1250 563070890 563070901
    0x5011e050c04120221010606090501110a12110f0a03050c060a0b010503010308033301021b090612120a03021305010f0210110705070b0304062904050712090c0806 71
    0x90500c954424000b0010a182a00015107490101710702d8060400c089003920403101991942140c1030350700404086841c4070028412943c1c07000c4041c500d4101c4800415554205484003403441d4400850308081000c0518412002c110901400400e102d414044074080030031440c018001e0b0f0050311510740c144c0b00d80c01c0003e00c1c260070b40c02400707414441a15004d2950342151180304051340014921425070b803d01e10000c030302050130310500b4100c4001c04d2020440c01d94890009050015600c0005158103001c5500b9443c3d50354281220f0b0401c1d02100c1803a5402504c0740003d06245441858600302800420f100301041d4064004003201d400080503603107859126030042d03680c03000241c2520010fa000481492000003141d10400140360f0780c045071405e064542e600d0524001c0140c004141c2d1071404028001048054050076012040c07d150340314600c40364032040d040716140d24400f9032259803144041101f0500400c0c01651310400e0807014000070685043c039000c080c0d501d1040700201d100350030000300c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 563073390 1250 563072140 563072161
    0x409061406130302131b0804020312040f14121608060a0c02030a0f021204030312050106020a020d080a0903150e0c030c0a121104050414070f1203080a0905011e05 71
    0x1d40b12a40d00d1040e01005045030240701a800070301c071000c001180e9031108075160261111001c0c1251030310303540760455450284181401e1500080707101100420912081c868201d06550000a0740c1207503034802194005680082d00e0070702015029030041c09402d101c0c0300303102c0d0b000d83c3c980c068407205021507d03142c0307403850480c04541a0b88107140068000344010700c000c5201e2100c8400c40c907410310450b0003c010f6107410001306d920a51085020500c2c0090b41d1118541e5030261a00600080c00580000452500443c0d031aa03d6140014500c040015400b039005004c0c440c0d4001542e00b00d0742c507000f19509001510010160b180c15208503100351440700410385000207540030880e00c050444200c02c0e15200c0c0c00001c1402031403044a0b13605001d1504e003034031345591040f244610b003e020b0510030081403400c02410041950400c0d07407a1924104144501241001c80c80107103a410300d00b907a015603868a00000402c2c00950042981d42029180d00c26144640320209020101071400c0000392900c04071030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 563074640 1250 563073390 563073397
    0x30a30050423040f0509031c05040f080705070b16030206240d06091a0610050403020102061801021306120c050304020f09181005070806040c0e060f0403080409061406 73
    0x901a030070072502108400c2d0385400b10701c0715400c400341000c11480354481c0e900082e210102c0e5020555070000c1454083d0030381511101451102c03890b0104018106902d581da1001c48001c40a46455000100c5400b0868200b04c0c280c010500c2d0708041d911070046840f918000760030040250010320503000446c12440c460002940b0300182d48035028542e015401c14820a400305600940d01d00741c2daa0044004079201d08984840094000d84c01011868480c0401c9108c4a50340b02c40810801d0900c410700040c0d0300000d0540d040303148403088081c024962101c09019100c6c4020b400f60444600d00d0003d00107406c000001240b54a00806200c4411140e000310343d41d0100b205c0180d40075494a000030407904017009041d4000e0103282d0f0085d664018807001d140b80042e0039004a23840c540e180100720f0010303400b541103908110111810703c0203c078142e400900811100145c944a0100000c0131722000031702d40115001076501000c0c2584a40c1c0e50340c00207004000c2c40c440e440c011041e55060a129241c00d4086 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 563075890 1250 563074640 563074649
    0xc090609080f1e0c0a0f0302040e0a0b0c16080705070e0a090507150e15030402100f0503040b0c04091103010503010e0a0309060e06120a020a02160f14030a300504 71
    0x400c0900710200d02ca142c3d01c910078000c111a40034101d003100e121703215408400083c207620310180584500c0c601c14001100d071540080c410a40051074071000144040c40c080e80c0000820740c0d0941c6420128041304241a004c03c4020b088a1001034044c040080126201d0100c510413001036890f80c0d50487c0301415111030303840013001c58126010900103207801d40002c50485035145005008030540c00007145030740c40590110780000802000300011403802c1100c490381e00c50340786801d02111003480c0f005046400051300c0102036148120000e48800800c4040c0c4009183d20301c8213220b03442003200e4490342640301380120750280d401e04001601031040020003e910316803580d10b403020a451b12004a80700d00c8001c050f9079103c0c01c00c216040381c0c2d40d0000720203070042d07001d2000160345100781034000e4134102d41d24031115014031500f007003001240c104502030780440c0c0300c12070a140a038020500103410144080e1004140b510200400300801c0c0f019000c586040b00d6510a1207950026600306451a004902c107 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 563077140 1250 563075890 563075893
    0xf0105040302011211030108070e0a090320010f180302010e030304050303010e1009090804180e031602151206030601091a01050a110a030f0e060906041202010207090c090609080f 78
    0x400c01544600850752004c403d1301c000080d459811042c58019a000717a10002d40c9511054003405660480500590000c640520070007030410300da500a403822581d0244c00e02070031203403841d0900c071800c00e4001c941140c0c01c03150104108500d68030b02c101242008502580190300c0c5c0080070030203202c00800c403402250440000d6003160f02e820301c03585090500030304e50761103c48007940005095881d4014002854480e10000d511242040c2c141c1500c02070000045130030609003840c8000d000c01c0402200c0104100c2d100c4840c954180d030010521003003070821541c8000200040030403403c195407041c140203600460548900381d907103803140340503190b840d0074180207080c0c40103034002c207507019800030304202c0003030308040c281c000d102548641400c408000a901203451001e0140f20f45502c44070741003078100200d4020341410380c0c0301d0100301a0301550280d01c0c145103442e51040c0543e0300070031400005100c50081807010000c0900024400c1140d0710484020038034820022510103408540c0b000e200c0e14a03030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 563078390 1250 563077140 563077147
    0x5040803042306090102042103120507020c0607120906020d020d20030c060a111222120201020c150105032e1401050a0803040602151009061409060f0105 67
    0x21140301c1422889040c5000400680c002c0380d014001c1401210700c144106000161910b2900b03111440001c00c81041001caa5007150756000040d800c48071030100060b01d00c0f0005810340e0b03850f406034605050424115842500860948200199007000c2d00400300780e6500c0c14030440e40c49106a030f541c2c20300c0c0740d01e40241c0c018804010040e0710030811074881200013064021020f24040d2541c0c02d642c41243d45a1040d0407170000c00000d013925001d5220142040000c1710325200003500c260300c0036007010f081c0c007540c0b083c0f0b4281703908009443d8265080752500050a00c4100c81c4800020f0300030762001d00c0c814640c1c0500c0072001b1081104802c154100d9102502034250b00c0d8403a02d104c84490858422407003e030304c1c80d41044500c81c0c400d2160060324000310001c0740341941040c0421020340410b82c440c50880c1d008010611005034040707054101404219808006922041c02031500b10340c080d04000009884d100d4006424401004240c1854006503a8103155440c3c003c00e00c0f00e82501014101c2c0800c8041 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 563079640 1250 563078390 563078393
    0x906050f041e0e0c0d0303050609010509010501020706050c0309100503100e06090121061b081308040605130317030a0b1503070c02040b0a0608040b010b0405010804121116080c040504080304 83
    0x503040007110485800135209001642800900020742102d400c2d800a50345038104074460402c03802050140c48200c80ca51415858040000d5461860b4050301003005004101451011010400d903041d841004010f0b0007012a0b0342c100501581040384c5804442e2901000055526208040280544400b0307003e10043e031f0a0a00e41102c0d802c8203406076031b007a6501c40f00c2001003051445020b11079840001031038241441d1000050030130101070b0030085001401c04078400069081c4045500f107500b18144141c0316640303040b0788001240107a1020304000315001540c001494114002d41c03166041400402201b47c909052294019580a102c609142e04201040469015a1944141900c0100082403075120034011441185a80e07101ca0042a559001c6c0000c1011917168603025000c4d9203007441c00c281c03801000034116103002c1c0000d803201c2d01b501b0107400d01900c2182c61034910801d440880d143d8498902a8109201481c410b05a5030301500605c82c105250602032a40125005106107040d611107 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 563080890 1250 563079640 563079701
    0x30201020a0f02030307212604022404080d1d01090302010e040f1b031d0a020d06021210170f0325120305090705010f0f080702010b0a0906050f04 64
    0x640000e0b6414072051003d070000a40e41c4034000030078490040c1c4140c40b140565000b03080824070014031230b101c41d44504401401d60441d004640d0054040318034070303003840d1020130460b00940c100034540f00b10b500015010401d010300040741043c4500b655902c0d24100c200040b80d8821950001105000400b803100802c0550320555061403507607070040000400051780c11440c0700b26039003046008014207a031404000740039014411018030b0b02c071420081010760a9070245070b4941c01d00d0f00009114800300c09241e024481c1079410385000c2c1c0c2d089540c1c0c04150074418060040c5000e10f104140c021009034481200c4000c0c0030030a5032040300781000560601d80f00d215104080a90480d0b0b200c922210314400b800803c800d0a260200580c590320005280e0610421035424940550403040c180100704d1607226445522000d0f80b15181b00d9490294455240c40c401280036013010224260321248604001c00ca03180540e0283d02252422504068520a84402e00007511040001102c10400340031203a41c3d820070 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 563082140 1250 563080890 563080913
    0xa1421030c01020c01090209060906180a140106080f011719050a0b010e0106090911090603040f120f0908070803030622020a05030108010c110c121c0807120501030201020a 75
    0x14110599007003074021421070342240c00c040b0350f100150791958070000940c14040c400c02d810030000e4070802014a070400111760030030600900c0501a03074070f00c00003520141d655480301c0911a5060b82c0442c1c0c03541d403002e004000c136a05440c0400c4c2401b072540005940c2c1445c542d58801407181001805441c140c202240c140340d8040e030400c5e51540a00c10002c4000390007280d01a01825440c810300c4c201c0d5040010060084000350480307403006107020080c1030030700380300c41c1034480e450703801c80d09243c0d00c1c2d4440c5419201d0544c01a00101050700301401d00c5c3e80b42d5040301d520b01c152a5a551071024039541c4180c41559070780c442c4200030144e0000c0010940314248400d00050700006182072081c000c848007501012a400300301880000750703020006105c0140700f03000799000480545071080c0030002c201300860b2111031038020300d0b208225804003000214402c1c4031040d2022065070707000780306410004021703010400032070b0008001101c2110000880615108481c1607a4041c0d0080051851a544418159a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 563083390 1250 563082140 563082199
    0x9250909020f030313060210200a180602030c0d1817160e0a0b10081f0306060b070308010f030b07081e0a14060301091113090209150a14 60
    0x110b0b480040c0480740c50070001000c0c07081d2160a2858510b250810003414003e041c009200303114100070201c8101325055980e01c0150104014166544041c0034094511b9500350040d000d1400480078001f441d150080040d00c01d6080900c103841e408250100100d0383e014030803901040048002ca810300403a51410fa000c80c070001090100c5459445500100c807a2500680c408001428020104841c09002d03000344040c0c50410784034060068202d10000e094450004c081c0390150010141c481c09084071000c1c950019034200c24104401900c0700f540450b41d40c05600107070045185107000003641031407655400212600a18000c3e5691074881c1d049500440103814250080501a010100c41c202540014041c0b0444a400108608440c5864214002c0280041c0c401c0c0d24101e074101c0031580141005c95104422100d2500f02a100d42c92440280300c1404041d4204a0070001c005103c108150301d540011022600ca81c9950b55910318203101c1003016003502d40000482d990710400c113518402100c4002d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 563084640 1250 563083390 563083399
    0x15031505071b0c03030e040516080603100e0a0219080d050a02070f1e36200d0e0105160804061b0c141929010e0925090902 54
    0x211007000751600c502c1404000742e9602c0c03189201002099000801103014180599090080b860301000c8650ba0b85880c003101e60901c908080000d0071650240302c40d200105034241c040190000340ca14941d580e420600e0202c2c06511900350013a0813503800340541c42110b04603c0100411791010700c04817043d0300214090b1040d84648080071840030421010100903110400c200c2c0c503030840d6421b900c581e140107a409100d61600045441419598000002c4009034246240429000407591400e0051250070a070441494000c1c03842403070800488000d19403c402c4500a12940c100e43d94440d00701d44091b55079850201c4c5070100c80f00d400f405510040ea08c1030242e400003800c030000405c2080300f007403c0b00802c2d0014003203162003c200008581410709200e255401000c0c0725044200da80441703e8001ea014102e40410000104191924040091420240c14800520703580d140c08040310804217a4080015010301c050440782d04062070b55120810308213100901d02c83e0301d05490030006183c207210a9812 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 563085890 1250 563084640 563084657
    0x2060406142b0c030b0a150909140403020f15040b190c12150b03010501050c0718140a0504030903110a090219140f0f09041b0807031503150507 63
    0x503265200040b03079080000442c2050140201d00204049610082540051501c3c050b101c403020b482d0000900d0544d41c10001240000c80078000503121104542e2080b141e442c145042c1c01056280300310101d00480c0b298080f640c0700703152008455103030f0382161111400003144000040202d0803902480d43c1040c14500b44110a4107280864003d40300d402c068680404c1caa0029056400c0040c418181c819103003800c1802104c0c10700039031540c64032041c41034030304215000c80c40c890515002e2204000030262000101c40719112004e409014243c1c0031f042c8803903003000e88009565600c660203028071503a4569503000c001e605682d1000300503404034403840c0e0801000c0e0300100340e42140e4801007940e4800300c4c21804003007442e40e40090540c0c0d106058843c0380300d42400054020348054040d07808900c0340b03201e11901d030048100810010208100c10340c03945151402c18040980c1c02c0f1400b40c2c003a40b950f5400740400315032000b160303400f51001c1c4002849103a4440c401e100c001d6499001540000d000d1801000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 563087140 1250 563085890 563085907
    0x12030a05180d0c0614120f0601170114010f030614120304121419030c0b04020301090210030903080a150504050c040b070804091b05030420030f03120903070206040614 73
    0x165034200303050032540402e483d24144595508101004842c60680300c1083c94013049002c00300c48070b10040c0840c2d40c0c1d41e1007440401c803d03a00440c1003130107031080ea1225100560f07440542074002e10701c8203c251f0214060280c4d620340c0d18803d004071020381e50010000700d8810314840c24400038150402e40010b09000501001c2000704021143c800d0303040c040d102183c11b048006041c14140a90802cbca003007500985003040b00000d40100205103c50381044000102e40d41d2070011074058680c2b80030095200c00c3c140000e40300c240d01035001902040c00381d51140415511070303056400300ca50344d62100013811651641001586841c0d00890303406001510103d09195461410000c44d070014007044800e640c0104041c030520b401c0b445516000c601058540c41d81041484c00a030841c403000d88060980b141841c0510142c5e0090000506180e10160840d4200c041a8080517103d4014149452010241c40c02248041d01c4c0042a19580394000340307064a043c2c41c0170400c0d038000354000070105441c242881080c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 563088390 1250 563087140 563087149
    0xb03040c030512041a0901020d180b030f04060509060403021905160311100e210a020312030717040b0f09070b070501020928090e0f0604060e0c12030a0518 68
    0x741003180c0d1403015a02c6504141103610b201061900c1020315007411b1082c8009aa40010383c91030040d8581015051204510484a5540c400f0f03004034001e20400800d110842081e60900303840746004041c01c02550700c0f40c005198a4100c265000b4005070322600c3c040c0002540e04419403c2d040c8200e08607a00c1c003240d903141551400c0c03d03500c00d0710300c001c2c003503e861b480b8103141c601a0003107041454108910303002e18000408070200010b07044130980742c0549039101308400700460058150002d003262042c1408071502c010390761003102d114001624002c25449019580032400d40116800b010603540e690740c03050481603041004150006520900c039002402600c050018400d003401040051b0344d41d52000240004840800c0d1240300100a01181035411008510360109075202d82ca40480c88541d078910191400340003110001c4940603040c148400c02502d40e0000c143d40520741c0c1651082c0b00c0300c1c0304000423200c115008202a0b00100417902c01184600000e02d21103c4880307214400007400710104 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 563089640 1250 563088390 563088403
    0x7110c12030318121602060702090f0103020301110a0e060a18090e1c020c040506031015030506070c0b010306050c070c0306150b04061706040e060f0a0c08100b03040c0305 75
    0x14650800014408941c544200841100300e20a00502d5416000b80c18a4507070300c25400e0f004910005200c881d406c643d9144115114540c00401020b0207090a0040700c1c10000c3c2884124460f600c0c00c00048403581c600800d0b600c1c021f20319250490905414028880315070710400c5640100100d60000d0031002000d0710703d000c0540200d07400040c810504000d9603140241e000590f1124401c20300380c032041240d00103a07180400c8426900402c5a84500c2c011030b10b17001001403401d51560805c1c17440b03040b2100c8502d02d84100c90080301140c4054031290020344007200f120720040c021160100050010510307a070010f43c1c1080303511004618005494a8255001c1b01e65041100c403e03171651000384002025400b98805042e001390300c1c51400e40780400140003003241000904401101c100091082e90b10b075403149441071407110544241d4a400b11840b86c1820084402007035a40c540340280c110644281c1c2c90728480c4849540454010b81400d03100307451030300002c0003111958801e910220000d08280501c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 563090890 1250 563089640 563089669
    0x4060207171314090711152d0f06060304080d051005191511030904020c03070302070b03011d0402030f010e160b030c04092f030103060b090f07110c 65
    0xc141c0c480442100b03103040d295503070b8003020010080503540c2c001a41c90186080d00403102e420020030108105601c28100400185007804156281040240b1100e03034140d000380e4410204803104010b0000f0140b0040f0000c251015040084044002481810302100550300240203c58440c1090022805142543c4080390301b6040c07603080980401460a02ea00b880050b104203e03402880c3d40d0a003882090300c0421540610208841d005800c140389000b401100c180550241080d03503120005040c242d034a50204401314014801e076440000c46103044810390741a00c0440380c202c62442d5081e0030070507180d440900241ea050240f0381030b50640410920540440c2070303002019284100309042e807001308e550103a100c000030100400c1003003004c24040b82100d0680b08906800110000c44100c05080c10107a8500088034400b03110100703140e0010300c006141220301c2a41d09103c000d590300c062010200041d90b00001003e020030128140768014450ba0000100c01c07400c848003440c4050001b9585490041c8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 563092140 1250 563090890 563090933
    0x3020d050f0a030c020a05010f02120d06080a0b070e0613051005040902120402011d0d0f0f051f0501050a24030e0304090e0c0603040323071211010f06150804060207 72
    0x351300d0114104800100b000301400d080c401a45290044042e4480040144509104100080b41122200e9943c00240941500c0382100d081c840c103846e000e8122402a2901d201080c189147c09000b4a091000c1b5620000100110360941d4901000c0c0402e400c0d443c40342105212040c00040303056007461004d41070070069080c440040b0300f46400050900b9075000c00c1c54004050443d040c10007500c82030203540c401c40d4404140d0300703201558140361050b040c3e4502d0050040c001c2c15407501900030110040705850a40003030420141e680c0d40108030078a445407182184031a1080a07181005243e42220040340042d410041a0030a248858500310381c0a07402c201c861560750903c0d0421010108811102c000e410b5551924600b025100544401d82e002000c4800c0c4508107485880a00207005841c110359200c032135551003180c24403001d000d0803107070068503800703601e4000012654030f894000e2208540b0001100c40d016081510102c0324900010710a80d10690200640c000007651215484140c00c03e401 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 563093390 1250 563092140 563092157
    0xd080a0b040b0d033002091539150405060f010f03080306030a080c1b0402041d0a0e100c1b0c090f060302060c03040338060f030a0305041802030f0103020d050f0a03 72
    0x47c10403a580c3d000c005107000d804802e210140704805002d90f40d401e403400140f00c0c00c0d140010960100d005103d0401d06080a0144d000400740340c000140429006501c141c003581c0c0141d44824403540c40742d07400d114180c00e403000050104081410840150313000311014042c0c035040003454441204036841412448559802840c0d00242c0601d06507103c2414002110298071381807404c0340c001e003c840754409898170140d440020808501035a030140e03e07400c0610050b00d0034030461940c08001008107600d0400441c80858203c04a41c030085180050207038080c0d000d500d440e091000e50f030300404207259a81c10050340d60101102503030714000980782c0b10440000556440d819464070b00d0750489032110780362446864042d03006103400c8c01801103409485600700901e480c1d82d28800600903c00143c00759070580540c90079001030680c004000c1060380d034807185c14400300d0002180d03c2c040b88012a42c455550929900510061605004c098403031400f42c421074003c5070450f1882e50420000180c12004140d568 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 563094640 1250 563093390 563093407
    0xa030608030f0906091311042408040303180b10050a080f06011a0904050f040314040812031803030f07091d180f0d080a0b040b0d033002 60
    0x1409840040d062980c0514100300c0c03030b507900303614030f01405401a20030403001c60001820f864070400000f00e0303c2030540030b0106a9003018420400e074002c0c040c403800c214100700003500044066200a4058145507108403c0380c0e201d840840c0140307400700f10210300f018440500c03004140264100c900030403d0041ca0316545107094204080d40f02c0d00d6200c10002e0304a10305514107940c01103600d50445880c08615510300d0314032250183c041c45424002c692081c90b0900307101c95040c0032550240700e148261a201c0c1d03102544440010ba60085203d004d103c0e070303c84401844c680360440080c3d0340100c2248180c05512014048041c210380007202d01385100d104a40c00c1180b11980984440001c0c507444101e0800c00d05c0ea00214810f4600003060050322004404071034030844001c000542d2003030900c405440380c3d4000b2580003410081c05031f0b19680c0041c101462242240303031078071508030890fa008114202c9840e0b80e81d0280d901151039501d105040040200f02000480011743c0d1418203481240016a5000c80 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 563095890 1250 563094640 563094647
    0x1203030501050405010611060f06010e0d060207051006081207080705071217030412051e04081509010516080a060306050421030506010e150c03041217120f04020f030a05030a 76
    0x50740010100501c00b0215481007c02191058010200004105042c1d590f8401604d40e5001d0542080d00580c94807201c60602006501a043c05071040c8180c901c0300e074044007014244e8040d8040c4184541040819800c098002c000070034020348100c10036810304669888035800d10b42c0980c400c01818a100c2d034100b04011042e0000806400204c85c26801d60a040c0c0701c035507a04100d40c10060902138002040e00f210140448800880a034503496a965180c860142a4841d14815070342c070f03141c80703070540420300741070040c0035035482400169140c0804820324902211030001c05494000c1590745d40d040403010a40e02d0090f5407050b40508258900103c0791015041d440d000040c810302011315080c10f02c84036070307031000100722211b40444100d5003100000c03a00824610610716082c1c00d6220004000074040e540d04504030359940507a0f00d014014503040b10414141c4100c42408a0981d01303c400204511400c011755070700140058003181b050700110000c40e25144040703c06540035440800c115501691 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 563097140 1250 563095890 563095901
    0x203100305061b12150307180b0411071205161a090a020f01050306041103010f08120a080403120e0604061e0b0f06070501270c320a12030305010504 65
    0x2c10b00031030343d030031009504945840d00070b581a410702c0200b0b03000070800704410640c010760003400040c150361143d5643c251550102c42c3c11101c8014017828801c0317040305442c00b881f85c2d0600c0c1107840866403401445030b5451f004d180158009500b8440d05201204000171410040a00700b4800c911541c05811800464002c0c0e43d00202407411680c4801c01110050f21101e031880c00c020000e00785a40c0780e486180009001c0c080140c41010904e10100000448500d8420400101d038210415503040302240301522400c0c0c46100e100c1c03800f1440c280e002ca0006445906008030b05403404e13200195003c0200042418604151350a40e82982c9945440000d209050700308850600721050410a016100300031960044641803a1403040c0310115850050043c00c1d086450500d40c1125164030300e4511403051146480e1011066594881d400400b0600249406100c022070350007460010290482d005d12401071042066214bc000d00c40120024840450601c00000340d4825100414103605000a1004455 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 563098390 1250 563097140 563097151
    0x7030b0121030e0310240504110a081b0406050d06090513080c070e04050706020d03050f011205070306060b0c010b09010b07120201200703030b09090d050913020310030506 75
    0xc911a105038200440d600d00200c24541c141400c003001000f880001c3c0c00c00e559050280034050034041003400c20481c1d0f0711445440410100754908403915242448110b480d070b001218007602c0d0400140c03400ba0b0042e040c46038488901c0100c5100c0705a52006030342035403c1070f480400810030108208100300c43e1030203000c0241041800070409454504440d00940d2144800a04034400004083c092800288404009040b00300d40301d280d5800d1030300d0b2469039603502c0d01c110700050040b0519450424400c0c0100c038010740e0b010034610441d908010f00e8101d000c10411007203501c1e00c1220b000000056082c0128001000340400c00c9448201c441885800d4070703003480340d151040d6501001888040720340402d84078184d8010350000034601045034240d0040000800c54440d080c2d80c0e444245181c00000010040d0521035139060001054403410701803508802d5406000e9a002100508019840348001e4040040000c00400b0f006425080260481c0d0050b0341070741c50110703051820300c14004204121900003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 563099640 1250 563098390 563098409
    0xc0409021803010c1106010b0a0e310b010c02120f100c030c030e060a02090a0e0f06040c0206070905090c09120d0201290d0312142d0a0b031c0207030b01 67
    0x45c10201342017901c80c00b0501480040e1000405c03441308942c401d4004101340400502200b10800c0000041c01034051075080a8903012400144a03184034001d01a00c0d40602c0180c403805014801a4200804c00301c0c0032115400521400c60180e800140130442c00b00001e014600000300100851001825500b02c003d144060604001484962003000100f4991002c500341c00182c8540040e80000d04424191784984994202d620070701c008510030400460044e84202c8040050b5420003000340d8030740c50b0488426000c02d01140040186041080f5200d52040da0301803418613064890000803c120580c44041c44194001d10010208513024030550041c07001100ca00e8007600c2a203d1810085c000d10040e40b802411400300b00c7d07080501035164a544c0310351481090180c290440e05200403810b044a160751603407800c110612881007040100d07000700d40d02d4000718015655118800c00130b4010701030469014414407125184c0101d0645e910b000640955002c0e102140c90740c1480b502c3d10070180c03ca0f2594 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 563100890 1250 563099640 563099657
    0x30501140d050601090e0a02030a0303050f31020609040903050304020a0602161502070302040f14070f021207052d011a0a0e072c03101407080c0409021803010c 70
    0x1c250700040950445020380004251501c0406c0c07150f05240071641c0c001c0d094401c042c2140d04044c7c054200a104525004030090f1a03501c80d6903c0c1d9100c408014004d03d0700c8010460544024420a00c06000600103840c0c00d1804011b103002c80e007104c05001c000e8002a201006100841c0740c104121001820a031005000b560200030788041200d00c140f18066985641c215048021802440004011500140100200714070140030b000940301c00c1041152011003100024107550280c04403201d410b40540c0140081414005440c030142c0c80442e007519a8410040a010b90240c045817240320036583c2404070029007a022000d6094940c031044d80491155000785030704017519100c2c18001181d01c0c0b10b1180f601c54944510545543d10720f03080100843c80ca01c00400e80c00e03078034542010100700040e41150080c880341410700c000c030303011400c81c0a02c001d000c0b80070489040c841d60b140c98001c80d01d0440e051030070f41c1e14515441264004104080641d0349480030381d03082d00c2c087c850440d40801d242050303c0b8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 563102140 1250 563100890 563100893
    0xc040b04050f1303140a0c031e020d030e0304120303140108010513020402030c1306020705030706081e1b03160807050a0801031527060c1407060c0509060a030501140d 73
    0x60b80d0300000c000f88241c180d40d40300401032612420364100c0b0781541c046904d6880c04c1014009003500704100c020340100b10001d10140501452103442d400c412190743c090400040002411800307404900b595080900c020b200c0411811000c440380c00f4141e209880c00a4201400742c000412680141d1090031142d14240c108500c040ca00d00c0a185c4c8140d04443c010b943c0c1d40d904035120014003d0b01242d008883c070701200410465000642581911000c030100c681540d90343d1012076960208032491020031800c40c1c01c0c190540c450005060700203608182100c41402020b0f03800440d600112909500c03844d0f070600751566079801105e090741040ca68540203107084068080a0140c600600c0010013049200000640c5035449610200700200000408404c0b452403101903041c60300756040584a01c1e2501000181c024000d4041143c52880140e406e8106655601c0f00402010398464031000e1080402041a20f40c1c0c40d80010301d030880007901c002540794103180502c0c00307400c01030030100e003e040c44415610 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 563103390 1250 563102140 563102161
    0x6011716110a050309040f02040e0f01031511071b03020603040602120f070818010e0a06050906060303211e010b030a0c3605040207031d01030b0d03081b0c0c040b0405 73
    0xc030350b110700781c501051f001000001c030402442181d2101140d0020744050000c0d40065640860403a4002c41c0301d0100326038424003442c06c1310014012428840c3d0108003103400184d59405031020480d0303004031030080e0355880d0082003503548115000c4031000e900264402c3d00d03107034804a45401903614106100c90786010b46016101da000503015a0141c103520400d99000402504154044440b0005680c41045c00f4900607000c0e00e004e4604246a0040c0f100040560070000b09942d0404910009040101070b07420782040c2036100909004034034804400951440c003240e042c241d008054003403e040e564642501c81d00c0c102d480a0260b0400c008019240c8160722840c43c0d401d41c6d42110b80e11054007503400d100c840042001050740450b402500101c2c0707010515400610300b800310243c6414000c2c0700301c0fa04004504031414418901c0d4045d01356401100070030301c16210185d20101003110151204244001c1180302d070048274292050f40d100d001c4413641800d040c002e000c0314141c242da06010f2800c00b100d640 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 563104640 1250 563103390 563103397
    0x10b0c01060812180f120a0606080606010f3b040b04060e01090e0f0f1507140d180f050309030c0d020d1e06060f03120f08010e06011716110a0503 64
    0x100c4e00e000711441c2c81c42641e130301e003a40103002110003807000c051a110300e41c1d415240c415045081e51210301c3c00c94002612900400c00c20300c2404165a6110102c41d404d0041d10181d80c00c10000401c1c00f10b510b0484412140000c100c80d04084950404d0001e06202c6e0402003920504000d881c0106d04100c02041070501d0600020306640081d4400321b0f0707942c00c0d401940e01d00700620b0310908440c4202e1032600005a00400caa5480c0c0988181c2c11115645646050710405031484164041d0881000044681c0d40941d11040001940b6108140c1c9810588c590304011998100159481e03040040e04407420301d01081080d000c42d1050703d8444150b0307001c0d00000ea041d800c1e80b2019025101e4602100c0503500390b070602c81c0c03500d90b00520401a40e5201c80c1c2c030ba00007108901084602c0703144d0900070600240a00315500600030150380d4040070360f003806214150508040c04e813a050040347c00120303041501240d41e0910864403034080582c4031150940007400500c0715072070441d980c1c00c6541441c6c08140b01204a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 563105890 1250 563104640 563104657
    0x10f060e130e030c030715110c03180a05030f0f0d09050310050723070501050708090316030915030e01050c0901020304031e020904030c0204050702062e0e010b0c01060812 75
    0x241066404078480d0a502c141c04203500607010001e4004100003064002c06021f00e5110707c100410052042c03403003010320542c0d00e03550348d55000b17100d0b000050340c1e005440c210b1030b04041d000a05240d0703a600070034509112031300412601d4200403503004e42c4150070400c80082142d00e24003412503134a0f010200f600e03541c030709444100650312800022840c80c05003038a5400755165601c540e0203815040d640e44080e030032501c0100c0f020750924004c210f035503100340c0296001c3e0359a28091881c0c4000410400c0802107041403c605101800e200040c4e611071420b600c00e4842155200400c030941c11484a03800c4844c0100980b800350414407900c40305903800000d0394190303075100c00c010f42001c400300d5071242e0710781c01028006e510490030b40030001050b90200d1000c400602c00c4e02d00b404940c440d40002e9231903240031030340700d01c50b011326001d0207010310100c8010900d0840c195200b40c110b1910f9202c3e40d6541d860036003001226940018002012041c01d10400f4002c00504000c0e2090404035102c801c118490340381c0b13 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 563107140 1250 563105890 563105929
    0x10f030c09032303071a0a090308130203100f06290f031003151e050103080a05090d020a170d08100506030a1508011a0307051332010f060e 61
    0xc10803e04801d00f107006191820849440380090324151000c440071007141c2c025001d1740004140a492a8058080c07180e03819150445107036540b200707101e90402c3c3d120060342d05200d401003400c080c02d514441c802d6180003540740407071082d0500480799205240101d03d0803128035440c0e003886160600c2000d5840e40f100c1e1b242c540d41d80781c4130840c0c0f80d2160b004940000c0e100048140510502c030f40b060380075200c907060156001100501c02010302003214024440a000030342d0400003429524491801802c4081c0e0050010041d16019004613034060202e407c15601100d03000e210210150b801c111480e0103041900c0c04a00b18a040740d50921500c11a10445000782c2000c00892228840d81d04800d40070204403404595450f95150300030b020b413000340300984800e0035001001c20b95041c08105030f0240d4102510380b41d80c50501c805458010b1500c051841ea0540c510013854050300ca50300e030a40020300c44c019102a00394106a0002c02803082c1e54068814010000700003da60784441e0500d00410b211802d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 563108390 1250 563107140 563107163
    0x201050c0708150f0a09030909150e10170a0c09090213140604050c16020904020109150305010303020606010516110112060f091a01140d0b09010b09010f030c0903 71
    0x222140c07a0250360380110030035028a000c0c040d040362049400714070071201d01e43d81400c00c0c0c0300c007108801160704035140a000101d103440203010f41d14858100c00c503110220602c088016075a01040e511505040e10321160300110303c0002c00080d04602800d03000c000c0b4070742c060440700010f83d440920342e0060344a03c4a16079103a240d003074150340d640d1002c0c4400840c40d007801c5c0703d02a019509294040c2045801501c241d18150202d8000e507190402d41d460302000780c0c0311011070943c40d000c110a01000500880c100049039601046000f4900c0040c805002d468402240703650451502034108600100380d2810000288610004900c1c8800b0f542d0304a50419442000706408600488a510174030312118459800c089000980e100e03d41000003c4580900040001e200d10012810403400c00508040c0050040509410f00c128240e00920450580c544001141d0340041c002c262110001d0f03124101c07492011038418640d503007003603240c8603003071701c0f072804000e0940005030107481455680805855400e001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 563109640 1250 563108390 563108407
    0x20f070501300b090f070f020c03031c02070f05030d060603050c070f020f030105091b030a2a0504290a050604060c03051b030705070608070504171606110106050616020105 75
    0x2507000e6881080050541311180c82d080d2030107510410181d0340100000c42c0304421903882ea10120304820b8084004000d0b501e0700d0751180c100044a5541000422072507070800103d00011114000442600c2c440c0f40955100c15140c0c1c14401103840c95130010041c142000c0030441c424140380103c81910f0b41c4541c03c8042e0002d40d0003c0303030140c200110120780662902c170074401400b0002030000c0d4412980e5500d60030880084080c10b840c1d0f840c090340203061044051034030008001c440d51899019801c0d0700b40780c0e07401c3d80c0c5070700140c10b403800809c3e203c4021134070003400d842400328500c603022100c400b40d80c440740d003074a00004284a84241e200b84401c011110302030500b0180700720304a44c10106410750041c0d039001e052035001c2c0c5981c02100212518841c0c580002825802000100e201c0c408a403206c03400d19207000d80d003a0306040f000700c401030240100708041841d0241142030300b028019690740c1c40c89010050003503500f1071300685c100c14442e2006104050a600340c82c0c0ea148641a42860f00580780d0910f03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 563110890 1250 563109640 563109737
    0x90a120f020a0b04050a05010c0b0f06010c0b0f0709060309200411070602180901080c010c06241502150414010b060a02030a120903020604060c140a020f070501 70
    0x403600298000646200011004980006001512011038029038007039514801500d03100c001010040c20841100009074800b09081041d070350041042c1890841c51044e5030b83c1c80b16a4000b01d58030440a140c120500110f26031080d0301c503024114038102041000301c592608010703900d10081c8000e000340c03450340000e01ca44554005055491081d000a9142d0f549031411602a4220b541c110100e2202d0f404002c1880c544804618103d407141c2002d401d11801d64001114100401101928250307114140c110800810300141e40c103c2c040501110209418070280044050b100d1406c1c07411903210b801c20500400c1c00c140880e070060f602030700d41054078075403208a0703000d01528900564000300120f41400420380100052840891558070020941842c0300c4000c12115190750140c010b0b0b000c2d400150001c0d040f58401444e40c0c02600b01946800c040400c1490b4642c010069103005030402a60b40c801d55404005103800f5080908040303100343c03e01c1200c01c80c106c002d001e071036003160364103054640318040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 563112140 1250 563110890 563110913
    0x503060a050a060b04080a0501050604110d020d0912030c11031804050613230603060f040b0405100606051c05070c0f03030204080111090f01020f0c060a1106090607020d0203090a12 79
    0xa40c074030800c5d2203590720f03400c0b1519158807030300c00e0303a8650030103000402c03030315080c4510064a03a44600b81814951307000c2e80c03e00250408082e200d02243d481f40000042422000d5003801c50601d6500880c082e00907081c01000c480941c90070b010240e1042c8280c0c0c2040c012000b84012002042e10005099510071002560801742000c5840046190610b089002441d12100d40b00c0f0000c44003010030282c454000741a03803010125100700c8019115004600019081c24210360001e0181040700c000d407510903100c00885d05954800000b08800141844001e1411a210079449855078001c1099141585015000c840407000041034403106100490426000746d040c1c9000d02082d2000b00704507004404101569031118000a100d80303051000c50402d0740c40004da1440f0070b00600003030302000480c1401e100003900a00042000e01c1038200790315900c03203801c0000030f00c6081013000511442c20200006814032203004040400c54000b0881c112854480b80200e404454080c020405414110305005030000e0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 563113390 1250 563112140 563112149
    0xc0903060c0305090f03120106080a0209120f0c0306060d1101090803040e0717090c300d17010e0105270a2004120807020102120714010b0a0503060a050a06 68
    0x80c074100041da0442c1e41036001602c80d5050b0300444d5180c181c0c0c29440c69036801912010301a0585c4d80e4018483e4610a05005421548c0520701500304150a0005030740c2001480809401303a1000703015109421081019031800300c0c081e0040d2445080000106004100140d00601240b6074180d5000f416489640c001d002403235a034040d40e0f111520341440328905101514400002080031031200305c0c00075114803550140c000040204150103041c0240a0065110021a2641400030702c41c2400101103601c107050032403908014000105e9680310142c030003d40110b00303000061540c1e0041c41545400200b580c10f540e01118201c2c0c02103030154008080c0900d4091000e114486002800302e81c080a070044007001e225400750712100390201c440c41500c0c0c0a40c2c4a49000243d04140e8039010a49203002006002d00620554012030001021400f0a40c8070090031601000691980c00080704203204055900108441c14024585410002a511031014084044140d07a610210358842c2e4258030240051 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 563114640 1250 563113390 563113403
    0x3060906061309091a0106050d0915060e0103020910030b011404090c06020c010221041701020d05010f090c050a08060603070c0b0702150114060f03090c0a1203110c03100c0903 77
    0xe40f12010b90b005021200d00480d001c214442d007200400040216040c16240380759115820603c501150b1406060f4076941070302c041b054500c840c40e061703000b0301a0001600c14155804c1c0306501d14030604c01c4604004040020f010710888080c00000c4807004030504481e00c00710310b0072118041d0340000f40141400c810080c02c0c8112607030700041486d008250758240140c00d8007a58400b10b5900300213100e074044494101a480401c01003400451020702d03000f4091283c0030300050034150540d08180c1190001c0e0000e03080717141088010070000d221405012840a40e0740750a5051a1891401400c0460007814051242c1d1000c40004c0b0b07441e01c20790107034040c0e50300062607454509210034081c2d210311015405001e5924540300114603400410b1b0a080c8001000d44107074030b02903c1c80410380c0719403c0603022171b000c0d001e170b900c02145950f1000d4004018107040988400584c46a18018044103800400114140c00a84060826680114201110f47e50780d42d80070030b403200040750403198102c071504000d00d40f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 563115890 1250 563114640 563114677
    0xf0c0504090309050f18010b070c1d0405071e1a0d050106050d060f030203030f1b030703030f0605090f060907140711090c070b04110a210201030c0c080306090606 71
    0xb03041e0700c003240340c0489400795600251185000244106c940c00c1d12812501c01d85a48010042400d00c20024001180200d800d8124a41c9a0380444100782401c8414049008100288020b0201c280164002811040d8601c507040c40c860ba00d011004e40d05202e551580d03007040405881c0b52000c04105d43d00000126810001c070341e15948003070840d801c201e008000040c44d02c1001b00d0310034080c01180044d00e070020000c5040000a02e01c0d070250354020290500c3d000140c10a00034040c1c410000f501a0505c20788010070010215010001129015030105100b8404d100c01c0c080c81c5d10081d207c07940c0206003501d407000980e480d81016a450700381a92910f01d681d500054100c180102c1c00c41c010518001160140a143c1740c03d40201c07414014418054130300b03140100410001001100c1c5e1a000890150101004d190354008030a51100d03e0940034600a070603415020456038144500701c0354200310b0426031a000d40d00d0b113400074240070003410a4002e8040001155907995040301303442001d00920800242e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 563117140 1250 563115890 563115893
    0x1d030f01090b1501020a061512030e010f0305010501120e0f0a20010503010812071a01030b0a2a1b0206031602150402010e1c080a091e050a030f0c050409 67
    0xc08500c003003541c004030b1542c0821103c04100c100030780088416401007100021035103c01c402816908041c94400b000860000358003180e048100c1c2c403050180d01c035541010b1049001406055919025104061a190060100f40e8100e2030490350800c80d5040029018034401d040b0346000140c2c0280301c0c851241d0581c59041145403843c1d032886034001c488004a02030440019a4203004c20301070340040740c000c808020070503071110024111040c01810702d407642c0ca10072800d0403440703c800e0300243e0700390300180c0c20070400b03407018010800307032098100b083d40340c07840380c50620764130001c01c400c61404000d900440d03800001d0301030518134200758005003101c2d03917410b04102c20005000040702c500c016004000200380f02c180d61a1000d4400c0350107031251144904540d0801c0b1445030b03000104541407420001c46070100f03d00340050015003075a5203840c8100e5040046e06410400642c0c0840b94807910364000740000d072946078000085941c03100c45403601618900c2c0000401c1602d401c202d81107403800e40703c0c10 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 563118390 1250 563117140 563117143
    0x1401021e0a050c04140420040c030c180303080a0e03120c0712031103190e1b030f06091b060d020d060f0e24060d050103060c0906050301060806011d030f 67
    0xc1c0c0b403049080340c218400351400c0c04261150f0002c52183c00013010300280200c2e00c1020a80e200407000d04220000840c0680086c5c2200c230075180d64400259034150000c0040e400c1480c2d0341040600c69801c0165600c1c5070380051440f50020881c4e03014980310100f000840004000f07442d060f03001059545d44a00e000e0000f4411a00314440542e00c0e000d920300c1035859503000e481242046880340808600d1540c0e101c1c01c929844c51078503d04270059541c0c45036150401c03004d0110f030740110002100b900800341010f0030140b4114000c12142c60b26088030007032040d07001c3d00085c0c001050703808044c4c44440c000f8400001340c007402601d40340d110b01c600014030080514140d030b0201c02a1510903054101c40c0791a25010500510119285944202d000c1147d01c1003441d007c0c5150650b2000800c031914020340d40105200b07481e000e9004459190303d90040c58100350300b0008402c051315407440d16504561408500500d42000980b50134107006050003c51341840c500310144c8010070002d402c0b5000c40d012040d1aa = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 563119640 1250 563118390 563118403
    0x30e0d02031c080c190509060408100609060b1c0903110619050c0f16061104031a01081603060905070522060501021c0302030a151214010203010303091401021e 70
    0x400c009024a40081c0030202c194003941c0d115102000319201c8492840c0091b07500394020381c604c60f231010042c400018042010400d010462071007210102e01c1502c5d003540c21041c2e4503941c000da800140c05200d58100d40002c00001164024000400b10f00c1c8421402d0a94000c10f03028580555801040104040298014204500c01c032186804112559842840229a0103041e070745554541d03081010380900740400c8c002031949070042e640010b401030806c94840351588281d20440e0910440e207440b01c24a40191100b41c01098140064501c00800c82ca8509459681c0c0c0001401d42d0350707940380b0405020b001c100c02d10151201402018000000340307520340f103420000c809020002d04203100440e06501c08a400d2051085002e207e011046183c0429070181d00010102840c265450b0005540042a290f56500402c10300c0030503400c008190900c0710300321411240c10341c4a83c2c010001040000e41c0080c0041c00c64240c4044443c80001c4000103c0c1000340d40c422100d03c240c0c110036103112523440030410 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 563120890 1250 563119640 563119693
    0x11120910090b131103030307021506091b0f0d09111905060d0c0309080a0c05060c09030303040605060d0b04230609030d09020d051c03060503010513030e0d0203 70
    0x4464010a165141030306603041c1d9040100780925640c04510ba924100408103d024071400c44034602c0d00740000841d00d9604102c82c55401a8460305004900909000780f20346c001e44151144d042c20b02d4244620b4181120aa014481c413040001d42ca8840c814483c017540c59040c0c10000600119805041000150b8a15451148520104440d041200c9408580d60701181c402404490912007682059030040c0b16442d9210189901c404921000462103002002032030603a4803804880078207030404902d030100c028000301021780c00f00684145964001f040d00d0303105600041c04160307681e40d1404119014403c000c01410b020407101448200940720080130440c002129480207178242c2250703d1942c40b1419a0000c1c256001044800c654620300c0d0007030641c650024100602c1000642d62302c80c6410542c0102e9039070001e0303901c0310041c2c169040c000c403002044110024400e9003003200c120b141c420445040242403103160000703600b003900e80360020324140da0002c0c01d442c5501f4007104000c032070105110780d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 563122140 1250 563120890 563120893
    0x1a090a12080f0f090a080321150d0506010603050615040515160c06270e100e07020c010e181513151806081504020402040312020313050a05010c080d111209 68
    0x21701080c0040c0010551301c541c8040100000b004154062221030650082d00c1206941000080314005454500f4010f84240c8904002c040740c1d0b1514200500704d50014040e1032080c0788011120750382d00070103402c4e503040c4d400031070301e030903900c0200c0b04040410301c105000e07210010586400002407260740e80e120404c443d000d440e03111a00c000980098641c8049490010b0032140c03900c402d004100daa02c60342903001c50001c0c901d900b010740310841c4515850044034050010380c4401c101400d6540c0c4031500d8650201c040e500700b000062403070817203841c026000300410027030110b000398841d00381c0d81c170512303505030340403c4900708000340d028124143c44070024052064503826a0002c01c40100c1c080c4680021100300b20b0140016920f100e4200c11105400340003607078402d0702130001002007030101010300743e0b482950b00116074820101d58405021007066100350f20820b50b0f44803c000d564cc001040b00c14143d400202540d859848030700e60320003840b03083c00c15240628007162516803424102d06043c02004802e0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 563123390 1250 563122140 563122159
    0x100f09060e0727060915090b091003031b140a021813033039030e0106030f0f020901080705010f0302180306101a090a12080f0f09 57
    0x7a0000d03034503403072485818203500080c11030440c03040f60440c0340400c0c4020b00c10f0100301255074200e28401d80341541e480020869030180204030f109200e2249824924080e00c0e4425140b80205810611000794400036043c0022200c00131590481e0002c2007260075400f0b8003424241030440d0b03585640308001034089004480e40184007040d403060f4a181780c80780c2868550902a10710668088818580140c5c81c00024038100c80080c1d0541e400ea20b021041c0040d8140009980440c640422092202801610b001620003d4505d0182100d10024650008503080c08100c0c000c020b00158010021541301500326403001084da020081260b00c113408090003143d45112690301c030644a915040a8825280400da84140d240c0256012740c0250005000c0700b502c2c504005508004079080c140215980004012941000d01c00c170119580c0440c40c4855440c0c20b5401c000c000d01c003080e4038400900071302a8182c0b4505407001004030351003c82e80010004402c0e50388030003071803103115001d401c503241551080d143c08 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 563124640 1250 563123390 563123411
    0xa060b0304020a050d050313032603130308150607080a0905180a0506010923031e1e010207050d022b0c0605150a030809190305060a0e100f0906 63
    0x500303032802070750020070380303851a85460100411030821020440c0c4501040c0881503200b29506001c4001310301600c04010701500942c01e01c140e1020035a85c0d86c42c0b0f44018800c1c13208070450301d401e58418582c107003404859a151081c0c0a5504c2c015124001c0e80801c00159440c00c003c41d800c05854451015211140e41c10f407070700100883d0031a00c070300d00203030104290001401d0300c0d80b58010360b0308030106041117a5070a80300c9044440025400729002070043c0d0b0f50348102824141080000c182401d15403440300f0103007040e200161103440740750700f07080c0d010b29107201040740700002c3d4100c42100c3c0d4464202c0f451000025000380d1a5461611000d60346201e80980c00b4801e00b044a1503400e146151b5540090900c45960b10002410043d240c0d101094181d031580d0407540f41c0904007009103004050490311400c1c01c000304100302c6042e0005400c030b907e00c41003c0002404c00240b258101d05078810124881000540320b61920400355404c800d45801c00203804905c4c3c5240c3d214106e214000d00c001e00038040321 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 563125890 1250 563124640 563124659
    0x40906060801062c0604090b01080a1104090e0c1206151e060a0c060f020d1b08180312180610050a14030106030f0303061509050904020603090a0f03080a06 68
    0xb445100c0110701d513040c0a44808010101000c420410540390240910508021410304d03040ba802030310f241340d515441c0250960f08958031a603c01d81c0030b90140882215444000141d0065200e802211500c0f1525007429010601c40040ea004001c1c000312101c40d401c0e51050380d2140203a4610068000a000150719030500341d200300e4a440d00c03071071001202d00e01c13542803101e550b119903101c00c00c010541c001c1e03800041e079a000708200d10f448400c01588030805d50325910300f10390401c040030900c1046c55a401c0340d0320360080c2800380d00116100b14074100124090341c65045104021401407880482d20400c00780401004884030205070342d00840e076243d40c0d05044a240c08200f03005080c0d20050244d000c0100d441d20324503c2c2c05544003d40041815039580c2d0b200e03100d10303286005c200c0200741c503140c0034040c0a20980d1603401102a501e403429031079103000c0c045061002d02401c00790207003100100041011000b0001d103821039902c0030155010f1070103418028007000b03040e101921240c1c01c4c0310001500180 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 563127140 1250 563125890 563125907
    0x60e010b0a05090d030e280816140a0b0c07060809010213180e0708100b031c030203060d050a05011b0f0e0402031f03030518040501061707020f0f0304090606 69
    0x4241c40b0140303006100d80802860401c0b018086040085018000d6110703100c1c41103c1012103501c40307441440440d030681d2200544c1c426001102280d012040040502d400d40c03500400b110041c0b042c28401c0146000458a1080300750000195030400086402025600007200c5007201c0c910390f03e0100f10b49411100e1420303031081d07016030031145215500030b0004c1200035501c07500c1d414491000142013039050b880a410480343c3d030b01051198110708121005140a07001d6512652401c0317001d00b9410903565400808500b00b100c0700e008160340403000034855121200c0502d07000303410004444a1003800e141090182c5504040c140c01419100e141141650003031602d0307005a0003984030301860341d0b98030040c00000e4100804802200e500e00f07a90003c140802580500610702aa035a9a03503001d55040c440c07100300040f90890301862034040108000c503030264400c0440b81000944005a4581c14022407800940b020b502100340100c82c5100b03c07000c40007008004070303101c0480030f0007419580c503070907a21050b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 563128390 1250 563127140 563127157
    0x150c0c0e130212010b100c0c05010801150c0c0902030108100f05060d080313060c02031b150114040f020406030f060b0c151e0f04030806030f0c0409020612040501060e010b 75
    0x70110900080180361004403880301092035000050640b1100300004c2590000e080c0200c0459885040386050084402c88400030304000c1c20005143e502d058030b104004058016284100101d68070914108180011024000c0801c00c07025900c0303503150003444d80c46140702482c9500d07803880d0298000700b59859006062080e5002044c0b040046555141c04000e81e000a244041e24048142440c000500a104c0e10200c4a0241c1c0103689450820100003045074100303020203856404244203c024490200d00241508d032004418210b0b00d03c0b00700800d014003031800004259500209021a40d5076042d070ac14110003444a030244101076940e00c02590710712030002280d034540c10034005c02c3e440950380b410250b000010381c41c280d021480450400c0300303c3c002c207803840d102c9044104144010f155000e460950080012000360504190f074800c500c0d6510398889801d030080707403107a210f00199a0b49070b0944001c800030403403401e600c3c03807c0d1030040d00070007041c020656040100d44c00405c1102c0064103844109 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 563129496 1106 563128390 563128411
    0x100c050d0c02030901170f0c0a1205091b06070f0f0f062309010c0e01031a13090204050708040b0103150b060d320a05060a150c0c0e 58
    0x3107040ea0000c002c6c41d445403080c082449160342c00e40d50001441c030340b100c2d6190092a003e0355020b89800c0c000004500e00400c00001d05408100441c4083c2c2101c181303459109942e0422090303004900018104010620301704000603981c00c094580180220595400d10410750f844400360b0741d900b1004105084000d141c1040203103901c0c080764024002c04000c1c0700b10701003140300405019003024914101034981c1e00d044480c0b0300c24001c401c001800640300035030300f90300700d60080003034200070008a0240d80b426000403002842a0466030043e580400c40072800e0f461511902c82003070303858800744151a17448016031295544c01e40109007501c504c00c004035803003920b554004510b0313002d0044000c52180d03003000e040906d1441c20b051980312007011000181c0e0303101c0b00d001c01c2c801517050b0003c4a130482c5040041c0c8029800511801307115100c4d0003a1150a901c0d000c20004880303081d0385a01c06c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 562949640 563129496 := by
  have h0 := BRFrame.cov_init 562949640
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562949640 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 562949640 ≤ n) (h2 : n < 563129496) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
