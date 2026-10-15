-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4926
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:10:43.088382+00:00
-- url     : https://prove2.me/submissions/8b4e4525-9483-4ac7-a44e-e4b6e4cc6479

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 885791366 ≤ n < 885971223 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 885792616 1250 885791366 885791369
    0x130e0604050610080d0827250803041502030d0509240405100509010e12071703070807030c050403051605130c020a14070305060a0213090b030307060504080f070804 72
    0x101e05507101d690b21403003404810141401200d1040d84011080000710380150101900b02954014400104a04145400342c03034082420030700c1e080d041400380b8426200607a60038444100202c4c0711100c81802c01c605141c1e02d0042d48518510784c00c0c0c8801030110940240200d851040c4000380912403454003074255581c8012051100d50341d4030300420040400610b1707a201131302841e404800340c160034080c58a1000502405070420000307550381c80c050f510254007007120840d004140502c554403403225080c03840154562020704408082c04100f0011255481036200fa4010094100001c0c19440c00408490902450300000c0040c803c420303200c1e10504030300c0d070550200d90f07040b6008a0380c009100c4011050b10030311602d285c0980e000c0e540e842c0000e200da00311403202c020001e046070740c0941e580e15040c0c50b001d01610f0071845164005091145418400f501001800700a43c0900c000050940030075541e201d038010160900f1343e120041030400c00b5107011a1045460b02c200c0a803180340c0f509094500d42d000703 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 885793866 1250 885792616 885792623
    0x5090909010212280c0504080a050105060306130c21170d0608120a0e1306060c030e03070509060d03140408030d05060301060e0402100e150702010f080c18130e0604 72
    0x5000642001d001913a0188092544030200b440910142c01290181540c800c04000f4004207000114207000304200c403100c8640603400225241c28860145820940c001e041f14888070031000032140840d110110000031125444071154224003466001d580d1040c0410bc02410340581c1800030300c0c02c180c0c000280180d007910704000c10056541e1484d075596040034081c8030f1040c1c6070074810507210314018420380e0311012010341050360611200720003c08a608a0b00040302107803010070b0340300c103240d40000c1c4005403403022b43c010950281094000b605101000701624803502a80c601d4034101031103021b080400c00340c100c1c0142e45039a20341840075281d40100c904140c84621f0400054014030b414040e0300100c07007080c0e0380440c130390b01d554003031141c40c0910744c54240501001480711301050b11030003001612100f120b10580c0d12182c00f44001050a5001c61350041080030f00e82c28010203150400c100d6411108120045200840c0c500100320103a14500b0100c8180717103000303040c8030f20007008035409218600c03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 885795116 1250 885793866 885793897
    0x51c0f02030102040e18072304060305010213170d0909020a02101401061202120c0c030c0312040606270b01140d0e0f060108032d03100e0c0702130c050909090102 71
    0x1b005000c3d950702c02d1849035000400c40240060342c00002c1e040710182c00351001e400404ca481d160b4039400c4c2603a12050740001840c9600400700090151018000c2d0000e81043c042c0034100110740001f00b01c0d48442c0196030741140d0010f00c41404500800c83c0c0e05080c030050200780510341c820320020907104400d11408003c03ea05003007032105043d80703101702c41d021701d51165103c503151960b4000e086070790032202c40608240b104111030000300104201502d150b4070b0240076030104d464185041d0b000c1c4c3d944d0f13911040d1801c3d0000c400e500c0c1c0f403a82d1841100d0b0101c0d41c100009002c540c1600403511031503024111800102d001400c00b044007125004145042d18540403241021794100520740d40e681e0034410341c060758005002c86400316640940808040390b06000101041c88145403817115a8000d0303807405004c40b04d0031010400c0d00122403003180d000d1002c0c582c0d1070034012640c0204060902400115418540c3d441480c2030f071354020820358a14100c054920101e034900100000c4c000e60200704403140b10341c1c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 885796366 1250 885795116 885795151
    0x10050103020f1c12020a0b010906061b0302100b031002070308091b0307031704091a2409060304020d0813030c140d12111b010315051c0f02030102040e 66
    0x203207031a250b0f010b80104070702d290f003101e4580c0350880d000700d500c03041e08214012111860049105006901d01030b115030b0900051603441c01c3c0c40508940d81104030180442407205044021a40204410b13003024240980807603c4107117400001c0c100220281301500191011031080c00381a8001d801e01e2040c032442d01124121500b10501d0001c205620010301d500d40e2020106000044841a860b6000c0c0c0d9246142403e103601c90150001307888403000151100011000141003a02e00080031901806281d12084ca0122108010030014031071040c1c8640030308030001c007050840d201d000340c650049401c000c4860302c0c1c82081d0f0700d003101d02d40c0303510098500e800c85c14800309038076411a03011030b5076450041042400c094030b60340b0383c15941100d1b1803031400d020341d10820460010060001850110300c0c04004410313a608040054120303140075800c0d10425100d1b2000780001d80b151800300248088002040c0000c50040ca09605c800041542c020b41650020800003446008861114000c4090445100d01e01c0c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 885797616 1250 885796366 885796369
    0xf12020c0c15040302030c06070c030f031e0e130c0c0b0a091725030c020d0b071101054506011409040308062205010b030601080c07080415090810050103020f 69
    0x10f02407400081d5058015a1002d00709152802c01421514401d10210703060355940d0b1101c0d04200c00c4080c0c11303008641c25000100c040c00100441c0c0046542c241845051142d51802107180c40d00100070030740b1000e6650250007030b2140034020f20403c84d507020000700b075586005003055002e00f02080c401c0380c4d4014500202c0c00080014000e40e8410500c403c942001d00c40741080074a0748005201003907092010f13a891010240e11055030300c000f0580581d80c1c030191400c00d407200903c0c0e440c2450302051503902d45000d0090b40d05405a895603d03403401e00010790b01040c07200020070035031244040d07060000102c992290480d880410964100c2c1c0d600d1201c60319812007001032016515080b6401000252050000343c00e03441c00c0703182c40f81010140f10058002d00d441801410444500ba000314161b140e0100070400d45c0c3da031150045a220a00d14181c03410045a95503800b4030340554020b807584940060040c3c01220b1040c850207004010318021101d4400c6c501d0080310081034280000c0c1d00400040c00b184005 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 885798866 1250 885797616 885797659
    0x803180708060906070804150c020105060901090c0212130b161e150515040e030d0501271113030b070f11100b040f051602101b0f12020c0c 61
    0xd0f40058002c1c01d000d03920324134200d0749900024422628500310312140c0103041031600c942c81901c20160000210350404808100d11020140e110b0741c00c5c0ba040200040c034480e408203000d40003005080c2d07127645a501410420142500c2900009810f1101140b01c050120b6441508107481340103900000c0702203064044203540c191007100281154500c2c0e40c003aa5030325829030001d5400001070083d0320500e84581c0025068a0101002c54102d60000c618800c5007540c0388210342c01007403480060708000b502910000d200d20310101c00c230030b1490342d102c1d8903600c8820a102180d801807404c1040304500380d01c0303190010039480c040c1e841c100061102c0004041170b901a410388413285510794024400b01a0b603e00317003409014100c03a969002600e5080c2220b40e02124000e0700e0062005188912000980500003850321000035403064101e82407607118200c1a480e140c401c0e8aa103210301d001505011003400c1501c1080c0629001d2560300c0c4001000e9404240116521159a00484801800c580c01d0a080e803031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 885800116 1250 885798866 885798871
    0x1e06030619020306033d051510030b1903060501080a030c030f0e09070801080c1e04090501140408120c07080a0f021504081312080306060304032102030109140907030b090a080318070806 81
    0xb4182c2e07040022152271800340d03500c01004010703140115450180d4000306205030b00001c805152444446000e2003044400e00829000d4407000c0010100e00c00b944d100103107100144140602440f140b45c204448262041d10885c4500c5c2000d0001c0d01c11b070803c83c13401480c2c03440c00d200d4031101e07002e0402401c0307461802081000c1c090ac01049640c0c000c0050004010041c108440c00301c405d507589180304880003d01a109511640c05048800e459012207506440050401441c1c480c40c081c08101c507000003188442900d00204551600142b41c0b00c51344403c0e442c111203e5140e1260010b104200720800050300010b048000b4104480c070103ca48e29903039914021400000188902004c0c00021484e080c044095540540207240c02c96410340a04023088103140c070761020a841c9130f00000107003c01c0782c640c0a4440c0700e0350600b8122025240c0040981d44920041c000140900c65a04c08288200c1041115003810341c1c008030b078669203042075041b99403081507000c0d00060324000c1101c00607040380081503403403 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 885801366 1250 885800116 885800131
    0x70c0b21070206010e15030604150e060415050a021215031b030a060213030816061811094305031608040305121e06030619020306033d05 60
    0x500d039080174161001400002c000700c4486600c495000c500f9502080310500582c06101403c2412a130080004280d528181c500015980f06038140800124000784c203136880b1811a40000341a20340f8507081002c2d01c581c1c42c100d02d066038034006010001d040c0321404010b58104070200c5002c518841e1a00542a4000c00041d038180c201e46000404a00140c00400b450700d00390787d40c0300c00b0307903166510f9250395041300c141c100014040d0405101000790768801c00c0980c011101000c00c7d14001a40c442c980d9044d6240c505024a1007907000c5402e041d000b003500000580c4a5900001084500309846502c85010300c1820381c81d42c280d0040e000d401e008100310380c05480750300401e84141da00c0030b40c2940c42884c050030850800c0380c20010040414454140355000d0004e404c0030255018201071b00e04080500074000d18442e810040c148040004075480d203040e8407000fa42c025890b65202c0000070b04040e20040d60b908885011080205103403400071001950720a19602ca40301c84070404a0141150000c44000c2c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 885802616 1250 885801366 885801373
    0x151305040e100902030c0a060f090e041101230f0706140907051909020f040503010e01140109090318060f110a1e05010905010e0105100e040203070515070c0b210702 72
    0x802074940141c001c032843c180040c0484941c100f100d000708660b131100350b11000003d450140c50104055002103540c000306400c0340b2280341806c09031107001207050500c1d0242d0500041c44601e10392100350f4030103141614001e1440c81e480764581510b041050380592011503001d4640282015400c0800c1c0b4543d0080842d030f0001d0901f0750620f420700a1102c40d00c102c150a5a00180f00000c0d0961180020205688120780d0700f03807910301c0d0a051509407009803001d0f50a0380d050400c000155085d1180c2907044030410400458813681038103066039400c0701d00c800701d00c1e500d040c00e002043c51a0080034100700610f1070f55412184403150560399494003021900189002c007550781100a84c5120090303020214069400082e040c606035079010f0840705190201c000380e075168001c010481b02c0c00307107220009040c84020700d421803500364000f0b61604494042c45104180e8980e8800003c000d100c1560314030755000e110007400680752120711480d42c101080310b480c0d814500c1c0246009691203000b42d4001d034210f0300203 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 885803866 1250 885802616 885802633
    0x5060d0b09070207360902030f03190e1f0f030609020c0604020a06080c0307030b1f021e03040f12050c0d030806132c10090b010e010801050106080a020a0e151305040e 73
    0xc80c1c000d451b004200ba41d251041120b5088108818801000760001021503201d8000c001c20380540035840e0407060383c0c80741a507001c0e80f50009841401852990840745880980b400d02400c5c20f4004000c103410854107107201182c070454107040065400d002d14000c6440c1224a0350f0303807904907038070b800440c0c8030080c0850070300c00b0440303070740c06900030628940000304116001200890000400000c403414280141d04c0440c007210303400101c4c032420000e185410082c5151074105041e00103000800c1c800e022080400c940c1510034800107200d40c080c1e5038002070800c040d5901c2c9080092401e0410b950251140c0c3d82c400d001d022085043c4241400007058800c0e0044824240302d070300b0400000302c461041d01d80140940358106200c0c0d44122804644180002400d65050000e00c05603144160000b61140c0e15090042c480c41d03801020701c41d03002502035800369403080c0350401112611400b0195541080c0300d251040640300320700f005172403200c0ba8a6540b0940a96500400007994501501e010094205004 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 885805116 1250 885803866 885803969
    0xd0f03090609140a030306050118060e0a031a09060709140105030703060510020d030b040c082208040f08010b0f1311130608180a0c05060d0b09070207 66
    0x400c5800740101d900041c1100340740c49001c420072002c0b080400c1c54110b4122101050f4041c455100904000c0ca803207140014080132007044c20f0032070700442c03040c000a40c031140803a640c1d8450340405564000000002c6070f8590803182c2c2e500740281c6585d04c1501900000907806440b030103044003211110789540d0030351800344005592503480680520100f41d26520301140549488840b1124140e81d5802010f101c0c2410400508407014003003024490340c10b1410b8640170f1540310303120740e4105000000c500030101170058058580028600003c180c0c00300418001681e10f88001c01508886245000b070014900b110100004590b106642903802844c0b811442c200c1151a0f003c8a0707030f905407142d15850b0030503c0f4022460400a41d01000025005d00304001074034003001a81e001d03200c00000206201d40d019610302e001c500842c00340c60300ac6c2501040c035405056040d008160043e00203046035149003400f03103000b5201c2407240a00d00700e140091940c042c13070100384000500c1e10901008100341c418420792 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 885806366 1250 885805116 885805121
    0x6020a020307060f030b0d0c09150311010302030903070605010306060e180717070f031119030b01090203130609120906020d080a021e2706040303080f1f0b030f0105030d0f03 76
    0x4d105003010b503518100c2e203071074903290792080003240100401e0410f62704e401c102744245ea45800c014140e6281f881020400181004032502184809007000340e1655228240c5038554002d566000d80044d050034000028040d459000d0303030650310f020b050f40c141e0341d4940610100051901055524030f50000100b0800d480e03014481e030104601e00ea00b91041c00303958201c000550746450300207540103001e181280c074580c0b5120700454030742c0400d04000d240162854a400070340340014824541c01d9600000042d070507180b495003484480b6400101005011402e041140d003190305103600310301248141101280c440e0000603106035110195445001d1a9510038102000e500080d00058815420308543c2070300400b40320150145c0000707010484100d86081d8403808030a039104d12528003605c1c041006102007076100880039401140b418100c011901c50300c0304c03264404201e0007400554000080e010520601c1c10004500820000c0303003210440c1d13210400c1540760b0b40414a0800454044240b0424441c00303034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 885807616 1250 885806366 885806387
    0x1f0204150e010c1b120302061005120a0305030606070804120308310204020c01020406021b190302010c0c0f23090108060736030308150918010608030f031006020a02030706 75
    0xf03600341ca070641d603241031005c0f0792240c0c004401681150041203551882e500d241d41c02090120703403044503002503140054948520b071601608010700000040e64503181c40701201c0e00d039580603070703040d68450341c4400b00c0301c180d50801011800100b0043c04600d07150a40c0700050f030b8141d070751500300f0006180d1125a01c01c41c80c1080c41260016000d1000d003450450030f10151005100503000780c012100725000e41d001d21128011304510905a41c04844980c0c41710001034820340b682802c1451484445040c42101001294040000d0010030300c0c000c11900d220100c1e0071042c0301090601b4480111200402808440174000c503d0076030311034400501c0040c40341c03585c00c100294070005440342d1909290010a851b5800a000302d101800e40410000c15500c23441441d07102d100f180c00c10007240c41d100c00040790040043c00c030208205051f03080070941102076000c1301c000c040e8201240d54491111000031025003088032803215450f031041c80042c003a4004560380a020f54010081c0c121681420003d440b10b8001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 885808866 1250 885807616 885807653
    0xe01090b01141b1002041409100b090103020711040507020709110c0d200d170106030b0a1406160c050420030412090e180d0e030c121f0204150e010c 65
    0x75030541a0180c0b54510080024005070891f1140801c1441c1c1880244080078080c0c1044180c0721904001c2c8610070b80640e01e01107400d280241e0384181c0d038201010309591540104d60b21900c0c120500180c150001500c5044503180c0c0801e03c01c800050801100a0140075954052504403031070810105109030844841d80380b0b01d2501c21380e0340c1d912000c0c0318501003c0e103c011001c202072503c0d1861003515550b10a004000616080c0041901c01001c5507050030b040c40746168810820f060207001e90b5404040d075240c4000c1d500c00c030f1403012060505d20341400380d41c03149602407441c12682e0140341c030f001c0920b640c40d003200c250306600d5601c1c3d6076907421009805083d0340741001f5207072170b0219010690300e48040c09030b084109000403000c0c8100529060a030110704c450144442c046012000b0740b00800c0c0d03140030303007030403106210803044038407030319040903040049401d95101590f105c815507e02e0394050710a41d0350a540c01d12110888a0090310080395994005000c44d00000522000511105030090300c00316 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 885810116 1250 885808866 885808873
    0x705040b04021b0105040b1005030d111e06060f0d032c12030901021506220f0204060210060506070804030b15120102040302120a020a0b0d06030c0e01090b01141b 71
    0x55005041d40040061280e000c01c0765120f45c00d000a2150000200350411081c0780300d640d101c4d2400e00003c5e901c01000700e03810240f00b07640010000e000d809001d04060014500304449652940b100d41075100c10003102e000b441034103204006a240d00300b110411720966815110161404020300b808200d000c02c80e814080015805e821150194462400e40e941c485106402541c5420580c070000e0700341441c1e011107100450038001004555920804890b80720510710320300c1c02000301d50350040310141c08244001c04070745000280c001855030340090340e00210550b2440412a05468600f001114844d0f8200908544000d000c24000f00d000c140d1040d400603010740400c86100e5214000c20b49409201400d01e20a950100f001c0056091800c40494001c3d82c460282503004420f60001f04d0400703550040b000312520100727074403c03580356551148026680110051012954441108030152030074054841040d0601d560002154085c824040c0150342064490703040c41e2984a10902421a001d0260713490321 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 885811366 1250 885810116 885810127
    0x322080f0703080a1407050d0c120615020706050c0a1113050a0e01140c07060b01020a1a0a27060209030c0a080a020f0102030a0e0f0d061a0a06020106080705040b0402 73
    0x10403980108220361007501ca58030a881c10301c405200b100d01d01e00150000302d448504001d10540e01200300c80d03030841a08400520001400750403640c40b07000d407145c03040c1c0c40d140c1280400c0c130b01d90601810076051015802c864069440350812035080c001e91890100d41d6100b40003002c00200d09a19005000001070402c80b2200c00340041702043e50300a94100e40c100c0c0d61402101084e00e400c1c061000a004802c00030189820207401008040c854a200076044030b0361030b541d61846a10a001118840307070031450300803407a8a20800380280e1001554101000c034a00048401040c00c0c80c2e01c0705485080600801040c00451340740c00300650301042045601d805002c01854903955130304440b40140a401004182503d2603205110070003400c4944035040d5441446014441d03039100c54140c801d41c1c010307110114803070f1164001c41e1003c0f8402500030b2141d4180700e103040584140000b0764460860466641c01e499036600c005030700303d9880740a083e0694001110910440c2030a820020a240e4050710062402 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 885812616 1250 885811366 885811387
    0xf21020d02160309050402040e18070f090b100c030e040c09050406260705061803010b0402030f0403020c061c0209030703020a180c08100303080402031e010c0212032208 74
    0x240d102d2064002816015031950781415482014403014060a407411490142841806412248000c0079100300b4a075800d084c0303250842c02e02071a001004082050400030340c90b100003002410b40184160b0041e0581003c02407118440c034900782c1c1d40c43d0941c131810050017000040c0800750003480031100502100ca440014280c886100323540003091040c0c0d5204000b02840428154609051402034940c1d010000c240811743d03d01040700c402c2c03d80b124103003480c3c0c5403000c01310b400340407005c4151b94810702c084100141a0960362016125903c65401d0700d0703000520794100030280c0181c000120120b00d4178100b0120b041350300e80c003c00c0b080400030119004540d680c0d0004800f620f19030842c0c1e41700c2d05403c02c0d81c1c000c2c1c103150245d945060701034107007009a840c220004501d083d64921001c2d08000903d0040360075514188044500604c004407072400c05007258088501800c2800b030648010b100750740e400400c1060303807030a40c1c0c040c8d5103480d12007030750301d80c01440200304950f10041920408010000c00304075 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 885813866 1250 885812616 885812621
    0x10c02031612051b0a0b0c15100e0f0c220519031208091b0f1519030203040203060403200a050d0305150906040c030b03060f0105100f21020d 62
    0x30700c0c90302d41d00082d4094500d040c84c2040c0c0c0f158000e20418000440700c02c2165104602d05080c0c68031070580c20b4462209051a914041c40c00280e81c1c0202510780c02c0c00b003a54500740074a02a90f00c1c11841c81860344030080801c0c280d00d001c603080403200609100c1852490803050302072604400a0722003280154903000000c0d11040788036204800300c1c500910802c03c100c46e4004184600e8040c1c10710508034500680c41c0c0703031680b00f01c2c0d03290052200000d4480406031345d038040c140000000a05040441802c0d040045166403101487c807861094140000c82118030070f000300c0f031060303901a010305016101c69806540b401401e51145480006030005441d5640041010440c110300940c018403000000c110040d08072080a403440510540d228403140c0c2ca501c948245541101c82610001840c010340c8604400030f100d001c60071039042c09060300b4070484119200f002d82c180c81088400c2c2070411240300d01a40c040c59500020000b08443d0403c03021900c0c0d100c101d00780d83c084901d0700503250034800884a400c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 885815116 1250 885813866 885813869
    0xc07030b0a0209030312090f0613020103051015030902030f070506070f031e030501060810060c11010e04110409050a0b1305070513061809020a27030501140106081003030509010c020316 81
    0x1882c906c55001c101145504001171400c2c400c03200d001e40744c00c0c10814481c101d101b1400071301034103042d01c07100403c1c0c00e140704d08a0400100111089954207561580b4020060500c10005a229101c0c12030064182400031440d0400c0b110010002441d110140c0d507500c200148150094062045200250740d900c0900701c40484190815500040d87c0d40c100140030740307020710141030740200e0000785800b4010382d40c000c440c40207a075400c401e107400499843c0700102c6034150340300381e8144c0290421422154400c1041c014109403051001e051185649620144048900107617045038030090b589200701200301c1d03c2e403005402c4541850981d20b0802d8130980c8a1a4038480c0d804580001c2d1034058072001003007031055002c00380818840661628171454401071444025000c150761341e801140d011071820107500040001154403500038085034241554000400c40d0920a02000c81c03180000104001c4041040780f041c1c9038151142810411408011580da0032039900890301445108415259008c04135454070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 885816366 1250 885815116 885815137
    0x41211030717100504170d0603080c0f010b040b06070b0403030204030f0b01090b0d02030303011a120702010c020d0513151110061a040509010608060d12051b030c07030b0a02090303 79
    0x42c015104124103803603e0019200208074615103024800000d0f0300401c40e501c0e0807180e489203501d401108842c10024001680300500501000031030a1020a010607a0f0507810342c036000800042d069001484243e030318450f8120f03803040d401c006210008904bd2a13068000e4001e10300181420f07200d0340c84090281c2041c00c103a410401a000400203078409010300c0d84064401d54803003841c1d070f0b070550100359070703010600482d04480003001014101c10400e2050740c03801042d0109501041c20038410190003002c611502e000180903900912642e14018011549101c94803040c1c14401807519000410b0b6614841084041000f038900b42c01c49040700704000030b5040d01d11140095414603100c1429240081030300160140780051104216941d900340f25941103c0441c00c0000d119507518000440c8a54100c0000b000a4603440039140161f91040151905520000080031802d07a0107a1480e524061401a10a1584002e10a00020300304d00101a000740942001509000704000082e095800000900 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 885817616 1250 885816366 885816389
    0xc07080607200d080a180206070c060801080304150807030f020a0201060f050d0f02090a110406020c09071119060605130506091302030604030c030210110d1506050412110307 76
    0x46040414041412a003545401c01000c00c04102d44010f411450001e00c038000b01c42d035450710b41c442c5402c81001b920754268000c081701c1c3c1e64005468040024a903901038440002e06c000c0010440040000c1102c09aa5580c0e481140c20348082c4c2044a22a6006000d18105601c0b08031040000c4480e0014104100041c4c001040c1ca40c2490400c40d901e03200c81d4811031049801290140111b0b866180341c407060740e0141e800f031981e0381e80e07500c1c1c4101030704401c000344091001c0020002240b590101d02800100e42c221a60741581d258001c044500d0603006805810380e411281156118400302c541026203648254004520542d032003000400a00030350b2084100075031110f0400100d840c00003030281c0d02c00140700c00c85100715155004a80d540000800c02014080e24004150a0500803c034035160200c600c18107002102002d003072400307140c000d200b00310107490800e04801203c2000c02c07481030030380e4495038607e41481c0c54288088401c1d0f000c1c1d041500e001d803001280c003544e84c5081c04880054501e02010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 885818866 1250 885817616 885817637
    0x10306150c0b070503060a0e0402061b0601090506040203040201120b150d0b04050105040c0507030507031107150f082401140f07140307020603151207030b2a030406020c07080607 78
    0x450380320b00000d14002c10003400704100300741540d4040640c000d40d03c6030750030000d00340d8a0b8408107016120303090850100d43c0c140c044417408070b40000303180d505850019809004503214202400144c2c0425603009020911403101c0e000c0c0040c10344d0007040d445500400c184548083c0a010700116840020202038050b1101c103010340b01d0401c1d01030f682c014102540c0400ca498030f801401482c41c01880320080400c0300000d840d00600d44610541d07403045102d601902e1045958420b090405180f2448081c0450321858041c0e07411801803c3d114401c00d00401194071410301001120388041c00000c1c00c03810311280e0f0819004150b50ba40207405000341002c0c6545d41d41806041116047d80078a1141901c0d0f03004205010041e260700003a2600501a10400c1d949581580006400003042081850701b600c1140c4c0c00000b402241c43c1914019244540c102130020040d00184000075042524003070800d10030030105001403290f0340100b100304075100507551039980f00c809141c20404107a460500040343e5581 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 885820116 1250 885818866 885818873
    0x41e140603192c0708120a270617090705280806040c0e01061704021302070f02010e04020703021c020f0f0709054210030608010f0920010306150c 64
    0x407403e07801c0500c600240784940c50320700080e81e114642d410840605201081c078546035401982c40c0701c1c074101c0c003503160511516045940c000c07540c845c4c030820000609076000c6c5613132400c501c008a0300030002c0c203025002d07603420302e014428048503044900308100c804449000605401410315000390a55001074256030074181040407441a040d0840c00b0101c005000400202e5001184150740d01000710002c0425604d0707000013640c1c440500c22000110b03000046c068200141c851450034004e00c00d0300c1e070000ca20220740a020480c0146800200568004116200d20a2003060a142030141520448101d0399850100b07506001c41600f6500d0305a00c808028068010719000d1550302042c0654040380000f90b442c0381381130030202c10032003c1214800031016620640040c1d0124092403011308184413202c2500801002000c403403080b01041d5117810600c0d0111501c0d03002c0c4215858014244003807881920307a824074403503101c101c814149951031900103280d60f503020b0700120031441911850304001071030a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 885821366 1250 885820116 885820181
    0x80f040902040f3f020a03111306060c03081b0a020f190f020f040603080301060216090b030312130f03080603010b0108010303051608040902040803041e14060319 71
    0x4114103051301c3c150698158028114003200114440c0058a0058040c00c105100d0862200100650480c2c4410004000d100e08494254540601542c201201d0b000c068101c0040b1003141c003030712000481100344800030074403603102160130412102e03a8203114601190300c1c120503404000d8110242c0c11100c15021044030610201d15a0b0300d9203c4000001c07000d56548004560a0403c0248503808607040c001c01502c0307582c1b2980c00346610030a6140c1e00d58403040701965030019400500307280e501c0c0b5000850303003d9040c0606409080301600079030038582c00d0a00b03c61042d00007000c1d48007000725540c2c00d0700802c0740000c00303002c114080c0d112032100c1d0910000b49400e4070302500c0700b6814001050010400260300004a80e2059070480100301200b010b841c0021881c89a58854070380c030b41c000b080c04207550a0100c0180200c0d03094010300e101c1d000800b031014106a01c0ea01c10030b154842d60420184043c14000001c681c002004651041c107042c414015504032420f240d08025400064000f007810400d507903 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 885822616 1250 885821366 885821369
    0x30c07031b0e06060721032f0a08130b0115080c0705070b0927070305010f080d05070c12201c061a030a03020d02060105100e0d080f040902040f 63
    0xc0708003041c0103050070500c07044000050043e5001e030b1000901e07982440240c10180350a54039260300342c018030384c100d9002400b1380a80c0103510700000210b81a4030a0b407820744519a81814140840c5040460511052358407020003801c1c10303c071081080380e210001d40142d61480c040c201090680340702c0d03017005000608a460042c0480301e000d20401c50701000c1500002c0110481d242c07100180e90320940100403911288031014100b40781e60a000e00e48503147d10418032030b4410400342c0d074100842e0780d84405040c10340c0b51910803640250400c240b4100c60f0341c03044008244841c061105040d44980c1d480c3d9807164020b0f81141035492554140c40c0c05980a46030030f00d0150000700303c40c1c80e030f40d080c0c4070300d0060761541182000038200e59846544054050340e010303803003480e450018290340740d650860501039103a02e4081441340040c000d034000418540b0b8080c241030001640e6507500b4140c010b804040c8082140a91010750f0452001d10200c910258510000d0014111300c401c00b6031a00c1c50071201c0441101103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 885823866 1250 885822616 885822653
    0x7090b040306051b1204200307030602180402040e132301050412030204080c1c060c0c290610090b1812030315060a050c0607030203042102072303030c0703 68
    0x411510050007158105160011f8102c0005400c80c242110101e14240d030104110750980035050000050003429809046003400301182080070b07800d80400c0001700c0c0b042c0e0080020701540d1902184002e280006e08085c7c2c40d120b00140d0211482e10729407001c40c1d03114030203804600d030f4481007000108402ca00e88a029000c842c1070070340c249401d01c01d555482d8201c0e0b014007801807050f1810242101681070b800103220350460000c010001290200501d075140c2d00b01c0c251000c111404004000c40340e8078807200d411120780070048149403200000c1005601c2c0c5407205500b0050b4040e03020803c1207484004000f240800400c200104611109000c0706107945a0f40726090f800a0080003c0a01c04028021000b40119141a6901940f45040d030703582c051101001014880c0e03808110801d90940c5c0103600440c01880600701480170021013940310030150580c3c2c00180c00030350042054481a88140661030245070340b041c00d0312103500200340b56402684001580c2c0c0d004600c200280401c960a59050444 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 885825116 1250 885823866 885823921
    0x300c0307032a030b0106030e030f070803040c0e091e03070c0b270d030509030a06090309050405061c1101230301030c05151e040b030f090c041e0507090b04030605 71
    0x142d42c880b04184d1034144100c2041c152901805c00d100c19091027200e140004051880781c0310720722420729072003941048030f04440c11005d02c5030200da41440d0801c45842009440c1c02801c80c803000300c162001d8810180b11000440c8010b2101000291700038190001508042e0391241d11031141140005110f40d203001c0b1004054141c84d0842c0c000e4880c0601c003a050350f0582000c40d5207142860100b1f24050030b40001800241c60103904000f01640311200b84219030302110305100070344580040046200103481400c0d003100d204100c3c0c5002501680e103031403401c0814140010a0303e9a003404043d20740049440c4218500700200500801031090b200f0400341c075060b1454401498040d58100c403d21502440e03150144803180703200402038031441211702070034141c550b01d522401d08104001e800c0354155000c2c0494002c4200310320103030405119941ca981c1640c01640419060f036155640141350240c805030170806460004a0f062040c00018001181710340000140c2c1e05c0d207900320200101189800510205 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 885826366 1250 885825116 885825119
    0x2010b0414132108040201031413060b030118060e2e09110d061b030b01120905030705030a0903142415040c050c010506300c0307032a 59
    0x80c0440207071644000b03802d04804a5a04070304181d01d4011816003a8004030309000212124958064032140c0128401e0302c00740812440d644000039070000446907007005051480c10080460016000800d00c801c01400000740740320b2111103000c00a003c40d100f514003a80f100d0044d240b000041104000c07a5040b2000b0600059282503000d100080c810404509a500d0302c0c207030780030f00100c0307850604070400050000b150b400203480c080019004507524a02c005001980a02c03085000f4006d040c0c5141c01603440d950260510b010540c000c010050f0300ba50355200c107100b90070000308100003e14209109488a01885145250000f074088450440719019003010040a0128028000d81d03007640c0211403160005070341d05180e4005644c0c0d6000344a031b000b41083c103150141a04800186154000c0000134032599541c2d409212821010146800d0600100085000c441e01c588955103242d444800940d0080095503000a02c1c1c200a600f00303503404c1407004803c04042d039500540c1358a1050f07100c4049105c6 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 885827616 1250 885826366 885826391
    0x1502030403032a0c150806061b16030803040209180606040902120a140106050316050d08040902040e010504050708091b0a05030601140a1706010b0a12020c0105040302010b04 76
    0x2409284401000d00c41c00720580b0800505a0541c010b00c0d054030100c481c2c9043ca181008000c214051040c0c010400300900c000c54424800c10580384109405081e003460980202502104c2484c09400985079029021510b031000004605410003140954070b142d8481c1490b00400900c00b40c0507081b4406030a912030240e90700304010a0140e03128204680025403480e8900115003d040341505181c42406214141402c10503440c09402022101100820009880e0b80c14155106520400c4861a803840c05081040d45082d00180d07a940d445606e00a08240d6116000341c1a41c0160704064064450720300180f125003840c1c460194040c0c1c1c3d500d4000428103100c0880354840e64019560843c041c001402103a450704e4296003200103150240440d0300940c0d60398100e50803001c03003114162041010f2540040c1d40f08402041500308a0401c0280c403031a480d000844480b5030001c940303c0300f4844021580e404400392031026014a201420000c5414501803030700a08458480e11503500c510324048245840 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 885828866 1250 885827616 885827623
    0x203070c030308040218180f0c010c080a0513120b0a09031b031b0b040203010b10121a04140702010f0e03070201030f0207060e0a1a04120305041104061e1502 69
    0x8036905403c116195071214004900b098264540f86c2c40000520b10038080304600000c5140b00604022003941c040c8402c048441d174449002000702c60002c0c4240450501040c106002800da9900c00d0620342c2c41c2800409031a40030450951105c100d6405229030380707060003103100890f6400001d18004100800d1399941c0a0540c1382d6074405210162070f114004030406000340f43c0014015800e408070100c5040d689405040d00d04205c0e422070003035091407080c0303410382040004904c2030322007070b100c1c40c400d450721502000c0206040c0203000c0c0980c00c82c1c5560390b80b40d103451250842d040c40b403108100e061300d4162400790940342180b00092107140b0f41141941c6201011081e11b5a8075824038001c0b624207003480c041c034041d010b080c2010308424680f0f810701c400e0038070005007141d406200d11404112403101c2c42040030038440490b00601569070002843d02028400ea02203a4003c1c8a40044200b00d107002d0302190032100580c000100101c02002030100e5894040b118000034020140004020811800700030745 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 885830116 1250 885828866 885828869
    0xa1a0c0906220509011e120819170414060906100b0a030f0f020406023304050f07030303060f05060f090409020d06020a2f0703140f060f07030c0203070c 67
    0x2501e0242e030100198800070000700010b11004141068650b1500304450712000003c0c1e04c030300603540300c5030005282d100075841200420342155030b0508000d00c1d4601c881111940024040420070b0003030010240307108121865004a000d644500810745d4210075140c0742144c041d028514681c08401000307410243d144441007501c070304035402030320b490b6a044243c02600c110004410200d040108031680c0488503130182040f145c55a00312000901c40d440d844445c24454940d5401c003198070740880c001e50108000700b0f03030043d10500031a682c05010489280c1051040d402c1200025100c10782007103050003491026029050031106240740080c0d1440501462191f20b91543c029034840320048159038038000c03405081500711206540d10030b0710520007804e00f45952040b600584120008001c0c0605010900140484100c01061440d00f55211880040400c4602c0c802a00c1207845a100251050110b240190569108481c0c1c900f000d2402500303070354464980e0011035009204c0e600104003841190350 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 885831366 1250 885830116 885830137
    0x150a0515011701090f0e19050d084b0106030510050904110a05060a0513060c05101a040603030903050c0619050c010612111305090309010813050a1a0c0906 68
    0x103d1481c0405e000c40548000d9030480d82c10b000b00c0c80094603e10070b69402c05a2a44103005132500101b0240080d280040141c419080c000c7c04088041403084c0c542060a4440031060141001001e617124070440041105420042c100100340c0108149a094021190030404003004400414140404540c020304000d1010300001242e03007200129480da00040005884040c0410703036100c3c10400301504070752100c1070550b45d4540c0100c001843c98450b60b11350100681c02005050300310501103841d4094070b0307105030190440340240c0342d80245076a1445524011407198a40104091071810b00c5400e080c80441d0040c0184d408112020610b104805501d4918115041550721604452242401024a42c11480c40c0c83d41d9014010305205003409010303d4440c0c00c0300c1e810b001c68035440d50a0107031581030790219000d074002e2144484a43c01030403d81c0e40300203201c0c50406400f40301e86171646040c2c2c59600995581900200340005954601e01c1035501c4005018014500090380c000304a8a105251024 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 885832616 1250 885831366 885831371
    0x9090714040207061d03040e010b040f030803152706090408190504030503130810110306041d0601030308010303080c0903061902070c080c010e011e030e150a051501170109 75
    0x70001c0001545c80040307141d441720072240900b000300301c4050b6203a0107806a0002c564200740001b551018204c21141501c00d110302e141211461b41d90b8204044d0400343c81640000d4589044101715258000180c42282d225030154060f0070625203032040c2d107400a030560b405100f0300d404000104440c0d50031a4102c9212111021092003104021205030040c2c0d0001009404000b076030324040c000c0c210b040c0d0150384840b000c0d1001c1c900448201002c980b10081c048452900520000e00c0528041d0310841000c0a40e1503441070111160741d03441c1c24900240c00450100d410200180b0605600c031030140e0340140c0100d150351030b001a8a00080d60b90100426140e9124005600300e82109038035019100c405a01c8000d840d10300da19425004e0f11440d10480b05400a00c0f840a0100c07150310558050746040400030034070488a49800040b00940031030642803110b480b4501d0348042502d42003007506c0c40b40100c00c20021302402c0c02a101015000b002c2403a5042040042c0100d60703140051038400e0440b100640c00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 885833866 1250 885832616 885832627
    0x609051527040f1a1908010f05040309060c030903120201020904020c010e06070513050d062715090b0f0c0702130f0b060405011709070518061005030f04120c20090907140402 76
    0x2840760301c40c51b0001186c42d400c1014801e880d07150740e008035010340c5c0700e40c40c0c4100094035020200c641d5601031001030f0010320110010400f1030398041c10303140f9254151001501c0d244070080464280d038000e84405040d40c0d580c4160000c4d00d5401e000258100b4181d00d04580b91480043d0a1203280611b0b0160314452500c61800c02c00f0024154040485030f01a803411701842d84400c0e5145803400075825043e200b88400c541900342d1400c5034840c2e101c03450b5028840c141240c540689401503003100070f1004d07502d007904118100250780c07051104040468030f100c01050355010b8071810400d403060000e00e54010f00c0d0600042c003040c2c1c3c020801d04140c501d105100d0145a4410141c00d1500d2a0b56006036040020310400f080c1c031507540c5e245036100d80b00c159188000c00303808800460301840115800001c9000141c08500043c060302d2020307074036100600d4035948030b66107a103a444080d001a241d0124111105000b514a828070b010010ba12a2100000e4801c051a244030544105044210184074ee6400581c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 885835116 1250 885833866 885833899
    0x2030601121b0e041b0c051002371418090c0d050c03071b060e0105011202040b1909020913020309060601020f01060609051527040f1a 59
    0x101d0600c41c410590180003203141c1c91001c00c0b5076007010300200002108903c00da041d034103241c01011001c12404c0c0383d44d0010410507100304c41e00720361103038100d4490080361050071600720f0a001401017104100011030f1600445442100400c1c064075142d00360788a0710f0b542148941d00002c03250724400c80e1403a526541c10403c10155007030128590125031004045041c410800040c0002c0d0030820841841000b945e22070300d00c113100c0b0340403c9130694002094483c089801107440301d8845840ca00c128070100d01c81c003c2101c07050964100f42c00c940d1440607400f8214095140c42e01a00310240b6050750490500601003610306080c200c9801900400398000a0308105078513121f45070580c4c503191100071501e85c2007507010107480c0c0400350b440d64011f20820700e40b07025904040c80313007100712800e40e1141d1401c1e41c42d060601c6003141d082e01c04085894002d20a0003039548442c0d8404111184914440d23040600c20350070402120960300140c04075134585540b4040c8401401000c0f804510200c0341c005100b0000003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 885836366 1250 885835116 885835127
    0x11401030e07030b061305150f03031b0d1b030f0f0e12030403060b100507200d0c030201030c140313050715090504050705070f060e16060507110d0302070902030601 72
    0x507080d003014030492800006200031080350a000b00811030340c00d20300650b1180203006031001901c0d00700024950345084440b6151000722940240c901a0642c0d080ca1203150420f040c0d03081c42864072500c0e03001801c10340000c1d0350201000d4510400e40d400c100300c0100c107450041884503600519400e0103d0700036500308040c02070085000a09008080402c60800003136090b8998205220031600e15042140f918082d01d0404105508001c4560750141001c1c555240c0101c0e00e9001200b40700203041002c5c0c4150340343c80390300f60405200c1c020785504208910713500c001011511100c0f0500c04000601080400110245080b80d8211f4044403207401c1e09142814134074104440741d030004038044000c40c403113010380d40c0015019007207440c112010481c5649110050340c1911501400500688603035504900240d030941c449102252100c1c110b44a8590100611482507c41d0b04140b021078000301d43d040800802c0801001c0c0100240d500920289a6607006503550300c00740070b00d0b940140c010000a03a5039200301c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 885837616 1250 885836366 885836381
    0x30c12040302030d0903170c0a080c0702061c090318061b021915090f0b07020103052a07060509070f0b0d0e0d1115061e041b0e0a1a0301140103 63
    0x42c0c13001c1183d0407041c0b9003e40400c100d982d0400b48003103008006000740c84043c051f620304040365201c50072180c1d9000d1000c0303000da022041c103d030311103414020b8101c81210460050b40114460b000040c0b601c8081c20302034980c0601020120b414048e840e01480f8103a408a0080d82801c04504450220016440001c1c00a0301071400403805000c3c21100144c42c12646c9844485c00c2e00e5a11042d107403a4a0781e07009031002c1c10030300030040e180314100a1100154802d501c810340c071426180d4000f44001c80302d041001c00e60011f68100318211004070b1414180f0142c0c0c41000d40101c003810081c080d241ca400740d4154840c00c507200b5200750040200b80280000c00079000120000c0c4200161440181000c501801c0c028904401c4050b40c410a29620800b0300e02c2c1c1d074500d0041d1001058002002c15100c411080052060304440d001a15032010000c00d81c4480712100d904015a02c0321804a01001c003403102c954450751166880c0e00a60b1030540d400b1004030202d905484054040d4000056200b0060300501032a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 885838866 1250 885837616 885837637
    0x303070b07031b050f0f03180703050706180510050714010606050316050a091a04050a0306020c24070e01110a05100b030d05040915210c0b030c1204030203 68
    0x91004014503194181d02c1000341c0d0103c6100d0144820000b0300072240d5014204078204503080030480c603980310700004059684064009000112001c64518441c14000240d00c1100c9640c00340206118264002c0c1c0030903c51042c075880808098074013800500090400080300c0c3c240305001800394280100000c5100c0340709030300c4000780032165445000420035841241c480800b0018130343c94901491140c011a40d428003560758a10101e0700704142c00035480c80d50402032042010800000515844440f4900b005502400380142c5549005108508089030032181c045902c180c41c2000750031440d00340718140c1140b160301d00800e80b1310494006a543d440b02d042c84084c02d02c02c1d150700d5010810300003407110004c003c0e0101440840f86031070505640e09001412840407500c140310038000040d1940c0002d103103040a40c0404800c036518445480302a000c10000904242d10f0103a2005004103c0c403070307400038812110703003602d5440e10786e40e03503581409806a040c0e1f0f0542c001d030114041c10300c03c0007035503600780c41e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 885840116 1250 885838866 885838883
    0x30a020703120c031e11011d19050a11060d021803070807080a150f02160302240103020603090a1218050a03031e0908070306020d180c14030307 63
    0x41050203540c505040c4811510407054101608085220312800f41e01c180c2d043d00e03030380e004180030060440140408070302e80003000000c0c5085200e2180c240200304000241c079a425180b140215402410301711a0303ca480111566440400e0005100180683c0c0031604000720701030056020700083d906114014031076032a240081081d1018040c0561100e4142c10100e00f10360101d0b5460345d0442d124685841910003d0f0000001c420124400340150782180146520000d4542682e41c0d500007240c02500e18840c40502d40c19850b0105901082108500743c906000f07603c1c0300c800810f070002d03030071014080240a03803400f001054105900704048603810354040000013a40c009100d0007882c0c03c000c2d40a0f81c148980401340004e0354102040c40000340ca80542c0c54099000208252041c500b044007070b00001c005140c0340008003440300303101c00800785100f11400341c1d60311104030400007940c524208e130a0101c0080c1051100013119120460102e5004200b800c80d4a241c50b00003c0c118066128054031821 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 885841366 1250 885840116 885840127
    0xc010e06070c020312030f0f040618062c0723030f07302a031b0902090f06071a0a090c080606010f0806010302070605040f0323041e12300c080a05090303 67
    0x111500000c0d20300003c40f40f00d0308032611440050440d800c00c075241c42c0dc140c12010b4103000117030020080c4988240440030303480721542c01901080c60405200c250b021540c121f038206000402c09562030305581c50050b80170840000c082403d038405040444001001c001a141c3c1c191050302110b0707890300f490904104620761140c1e49081c101c981040d010741e040c600540c01e00002c41c402d50103109450800401416141e100d2070403c041c08000c1e841070500f0340d0b030280d28114180445000d160b0192188910800c003241d4072446240c80c0203821195084a1490f42051040000326680422080315014107071612001540710240103900a10402002601050400b01088140719885030300c2e0b075020340b181e6070f18940499901e0114080515420300d80c105004100700400400510350b026400c12081c17901c00b514502c3c0d44030f011b002d4801a054044074035003c8150a0b0301d0b83c8034036a0300710101a4a03441c9100760081100d00081140c5a803601c004d1449902056001c1d84611036010f0701c6c0a644098226607503071 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 885842616 1250 885841366 885841373
    0xf030519051c120c0905030c040c120e1216050d0f080601030f0f0608010b130b150f04091a031e03040e0c0c250605070f02060c010e06070c020312030f0f040618 70
    0x10b60705030041c03e0082c420310005220a00b000e101c1c950301107500e40c1c1c803132f4508416030701010044e241c85c110300a02d621485502c82200d0782c0d45001405044140c48901c124500e00f4900760342030241500c91103040c84403c41110712240d03005041a03500075001d18000862860750341c080341c0103181c0c903009111041d2a2140c0440c040070705502075001250b08585a05031000031180750029074111900d01c54000410320141e8408506050241c605907000e034611604058035581920111501c0c104208050030212040c0341480c2014001040d40c450b4032444981585403140f45242d0f240f0072031107203c0003182c490000900c1c005c204c009a98091741c901003901c1c21600704000d01c0b5003807041c0b800c407085190811070b00092114007034000c0b00e03503a039030013000c48103550060703000c010540c1c0006001c40d800355203411040750107807070903c2924800c5070390b80c0361001640070380d00605240079440c00310803400607030070800d1141962000064a60001c5040a601c0b800c0e582c51034030f6006010714120188180c003540c03007180f082 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 885843866 1250 885842616 885842627
    0x310150602010e07060906050f09030307200111030a0c0c0e07090608010b04050102071202190e0a1d0715022b1b110105160c0f030519051c120c 63
    0x22200154001d0010151000f005910f0718030a00c5100d0205100c03c1c020080e150045000d040300e8007541e65481d061182c005c010a080d40d100d040116000120780300b81c05034071606254a400308800c01e04c1c3c06c00820311b10074070440c1c1d02c1c1301d60b01c650707014001e00031118800c000d0990703441805044040c491440740e00f40b00c03401070300c6041c540c0260800f08090400126403010408192022258141d0007400038514101d921030011014000c02d903041501d11401d294a220880003043c02044054070114440c9422580303e000c407000346604114007040c40c117031205410700002d48002955035000040c0040900e080c1c060345014118480c0144403030b00b000500311002c2d040f5a0071841c8e4019500d4a41c02035100b1180c0c2100416003403002801038482044074040313544a50041c0003504240c1c4100711501c0080d845406c00c1280c0c6030b00000d10061084d0b824400c210041c001c2140c4c0d03c0d0400002c20f49082c83c1e0351800e845404000c0d482d02042940c0f10b1010201e0721a00c4100000d00e0800f00401c0300c0c10100b60010407 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 885845116 1250 885843866 885843869
    0x1909050f130503070807031e0e0103060503150f2e0501030507080c0307030c031d0c040f0525020c061204050c031218030a02060307020718020324031015 67
    0xc4028600001405408401e80c41441c8580d001c00918980301c9030b030f81c4000e4190000c400540c1080060307050305c25900c810b038803003140d110381c50303182e4070703140c0320098001019500140c0240d07001313811240480f140040703410111b5400022441c03203044540d03206070200e9813500c05031561044940301e044040100a101d0420941036500a0360184601d81e924501034601c15020340c0d6500000c030003000002c0c0283c0c82a071280811800070b18011850a60303038000b091a122080d041c0c0c00e4250808a010708080c034162255000c041840201400140f50103100c1c0c44600062980c0714005440c209100e10040303100b8801d10380e03a10350042000c0c2d02e07041e90004001d040b060031501181d640c030503107401585034a00050462000441c010f02c10b8585907228601142c203a103501c030301580600c111003400d00140e4a0308041c51241c01c0c01d5000b415038500e40340c7c030490980360707910448001d58030400502003241407000c101130003066420420130300400741d10042850245000061a5804c2c079140321030040124181c200b80 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 885846366 1250 885845116 885845131
    0xf0402040e09120f160c03151d0a0804052b12020606040902100e030304030b0903250b01030609030c06060801200c06010e090f030a020d0f0507020915190905 69
    0x4800d00703900c2c2d00c84400d5204e140c01039040c4020500c04001c80580d0f408011501c1c41c480c034062402da940d030707a49505035600c00b810248000354480c42e003002154070f50090340901c0302081004140140305903c40501a114034014240035010000880540041040c21032600000c082e182ca900c50034241050301010a0100c0f2000040c001d03603010030241d140c580204035075150001c0c049814110b13400c50031340314026680859501404203020000c04a034960a0b550b200300da0080181d030b030b607520400d48043c001c920382c400709030b42c5520000510041007480c480107056990000300010148002d0405407450740c413640b8002c00850400d000070410380419000102c000036209007004a000c2400c0c0459102d02600342c3c404507903032040004110340704562000542021140098880e4003c244020300d00b1540962110b0016900c480b402054030355008c5207000002d40710f440d00c0303800c1c21155400641d107041d02529603001803514008804481e6581e20100001101c49418500c030740340e032111040042c2c0f000300d4500c0c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 885847616 1250 885846366 885846373
    0x20030a030b03060f15031510030c0b03090d030237090b0903100f0912030b030d050403031b14150f090a0c03060504030512090c15040506040b090f0402040e09 69
    0x1078035506002070f07100d003d41e15181c88111256540c59442081050202c03406625200d8070400c2d88840d0504031200d8040d1800c45100f00c002c0e4110700b0300d880307188003030f07440341c03641090030820446c2d400710105440d20b003001189030240e0740c1e400c0c00c0414104c950144407041d19141305020100c012203000c0e014580d802d01282c8495101e15900c52901e4028004d1000564060308100c1180505c44881d034401001080016070000e0f080c110340c3c58058101c00d03070201340c43c0402d55170381030003000c0d02d810072668404282a10708145041d055550003483e9950348032060707481c0b48e103c101c131340204002c040d081488c00c10442c041300d54a0460488001c3c0ba0941903812480607901c00001c10303090000410b5110315181c000040c1c2c40e41c2850b5596040080400910035401c1040c24400340008259000341103010b1010a401000c884810700c1c1040810a1043c50310200306004000c00c02031605d42100740d404868003040309036106c5602d4400303c0c41d070105191909502910001c3c01042c2004100d646502401a5000301e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 885848866 1250 885847616 885847631
    0x5030412050d060f151106130834060f0b010e0d0c15091701090b06060d0207080304110414070e060904020d020c1c08060a0b070f141b03240720030a03 66
    0x24682c0b2480c098801f0007003200a4030b000c1c00400c0490006210f0040694520f02a0031498078021001811003003442443cac40c01d00642006205032402500000008560204841451500068042d14160074042c0c02341c004c10200c0000c1c007488000e00300040009402c1214182c03a01103006220355101d0181c81c01d502807004101c10b111005126a504c41070307000c3d26400b09502d07010304100b0203400800c90310500580801c070300700018540d00080c1d40964490030409020030342c44020402600c0740500709c6584030074030408202c0810b91100e40c411030041e041c5c030744a60341d541d1340002c0b074040c5c810307034017178610f841d00005d89000c3c46440002c200d18400c40ca8592001500c120f004100e440c18030964a0542c0050204802c1c000b204103000100304c0c4030b1042c41d002c450030400e07503601944c0e402009602295070b0845071039102810f202c40b41c003020119044001d46518602806c64140540b100f100b0b01c0c503e5000d030320003d8081c40c003a080c020310307a90840070803400b11100300c0320f01da6a0f07a0009030402d0000c0d052507034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 885850116 1250 885848866 885848897
    0x62304120306120210030b1c051005070302120c09120601140102060609070f0e060702040507090311040612080d090b040f0201020d14030a091104140a0c05030412050d060f15 76
    0x200031003da603008000d400c240d028910200c002d060341107000b075440746041074210003504a41c00d4011902d44a50098002016610010012190000d1521040c0760040041c0d201091452079405c4c1c4c040906250181c41d908541d02084100249000c5501175100f444004a25900409800501c91000340d02b1104281d890609114510700141c94a02c04902c000c8204c07800c0030301034440103030b00f8030003d800e0324240b036800e4000405455064403e45c0c00728000380c0b028400d118040d040b034101c4100640d030a220341072403d46012000d0b4000396024152000200d413a0107407083c00c0d0458200d954211001001ca4245410a003004049000049015102d542106402d042c01a03103120a04410a24810304540e19101c189002d0101c1c5ca904841c0e60803143d03041100d0340da50703100b04a0418046040c0100518265200504955642e92041d00788030061042000003603a03030800300030402072440c0c101c0d10389150000036809042e440d004142c0c203000040c030204144151000c1420409031303551319030612251245 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 885851366 1250 885850116 885850139
    0x30e0c180f15030613050a0609030e0406080c0607020915101d18010b030907080303010f050a0b09060708070f080a0509040b090103020109051203090607060b09150a03062304120306 79
    0x15510f8240e00310100040010030004511008540503000f607507e0401c1981ea1101145c006810031404030303051b42d0841844d420140300d9000580070308401469104401d000142030b9014030705000384500d190b000000c81242003400b280c01000b90240c820141102e0720360000c3c10f0b80801026000740c1c00302c0d442c402c810305d113402c06021145095900050525034200116400b00c1c1e84010f20310205032089040002da000c4003080118002c01408001c0b40301c0e00c1c2040c0400045000300c1c1d20189040c0e9081c07052180c590384800444004940c00b80c0000d94130015860402001d42e483c000c0035044000201c0d02d0969281c1100044c00244000c5408004480c0c0b000c007080b18900c000c2c040640000c188260600050400b420100c501a941d02c04890600d001030001072404d622084d002c80b0020f07117039802c41459040400040750442c0c0d11540c2c1d171a152000c100815640080c511019040c2525071200c1d0701c004820002c2140240b0100607020110301e8241020f400c0040c2420a5200082c580ba4000071030380300f00c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 885852616 1250 885851366 885851401
    0x11060a1806050a090c0f2d0e04020a03080313140a0c0b030a0204081605120f120f04030812010f0812030a0c0212030406051e0115030e0c180f 62
    0x15105041540c506031103400042c800244500f0f485a541c10182022500d044928002440c42d024007036503032402c0079614030400550754510b09400d403035202070f8103141b00030107400c2e801d40307826031805072040c0c0e25400003401840301a40064210100041804a11084006013209032801010003070300004000568940d41c01050310060030b03c01901d14180012114a0001c64114164541c0581015100c100c52418118601c5202c40c10b5a02880c0070041ca082000c81000d40e02540f00160881104101302c26855000701e8a041480110000b01074000060840503280a0340d005800e1a4a031104184440381c10a020700808600311424032001401c02d000040f201d14505004101d142551203500030039014100306281003041d402869003051101c50a0400740d44100d005a40c04a00b6040c11060048518011415054941140c1c0300610190715032019a00d403007001e03131400090754144500d076181030200a15510354020030480e142046401d04803c540d0182e100c80588110540b903241c058891510072 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 885853866 1250 885852616 885852641
    0x613030e041d070b120c07170906040f080120030112110303040923100e060d060b04050a0f06050301021206150403050a080a170f010b161211060a 64
    0x51840c0300000d410035401004403140d078442200d00032908003032107034107001e00742d04203100700d400110705175000c00007501c4255003008071260741138541740064968440c0341c1c1c6902c4c0144100500002c00e812151540c00888000304500c03c1502070480d00e529115010703100c40c074000c0050180e441c0c0030040300300150048178121541034109542c811190755514400d101c14404ca41d501d400140300000d0390190034055032501704100214501100c0410565428000b809440d140c03e03e400a2820f004e06250503001a800080894030000461f4441c58904050844210f00300d0700a8101401c0c010304203880e0b0864810161245014400161118107140c202d01407568040c03803100d1110049000d0f801c045010b21204d150011141d0300e4107491340c0312649020f00c0000211130101c400122003810a500c400c003c040642c51680045190038010350031403c4031018000e2a6602400107260710400328425a400c0c00749034010804a000c60300050050407000c0c034103444c0880e0380601030000c1d840c80c403e4032480b00c036100c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 885855116 1250 885853866 885853877
    0x115030507081501030f022b181401020702031b120c090106031e091b0801020909041407121505160c08180d0b0703180309050906031914061303 63
    0x480b1030444910f156400c000d14180b6549642658400319140020084034034031112a5102070070241404c042d501e001c1d602000168509050b049101d8011180e8000b52508000c45c54014100c4904560080c41244002903062044c0c4407004a10b120304044c44414100c1268403480840038060000e0310340b00c0114050707504c140880010301c4200c0c0242e0041540050105880d452211410301c030004a0300c0c01c41066039100c2d0001c00c00a101034441611034043c28090009500701051a008114032080151004200c0c20480344518402c06c000c100c7c840080c45000548280d100050405984104000954100c45814100080c1c40804c600a030000745003c3c658400d000a5900c0d01c8034545030300a40451011441103141c00526962040c0d0b001d03001a010340550030107410b1440c0060100d44860311440b04186003002c0e1a00841e4004a0700c2c0100c80d825034240d4116503500d00040c0c1072468a0311b00042d042d21800090b0240942c07814030070b400d09141c50450b18582c64607c6d002101030b4144900900081 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 885856366 1250 885855116 885855121
    0x503060406180923150702030c0f0106030c05040204030f14010b0a0303080603060a060807062601090c020d020c13150302030604030903030f080f07031d190302010b04020c03160f0515011503050708 86
    0x242045c0045a200d242c51040d24100b0081d042e034203040c480601a01c0c0d0251f91207480c1841400b54602ca550024807040381c04601e003e2455031185544080d050018144101842264545207030a4011030031581e00142602c001503101d2501038001038055a03018000d22a40002410b406510701c81e600681e002e240052089a180c00710407141c200103a1000031501c4801120321400c1e484840711980a4032103c00007007016a2699802890040c1c220404000c5500011081b4074545400b0341d010707607540f0701300c01c007003090081c40380c581c10040c99983c0000d4052292404001c02e1642c002404019039100e42c0e01c031891103092110480300b22106840c4603070009503007000302c2c401d1402a40040002c0003801b0841c0f5a1b40c007000f0903a03050680c01403525810f00d00c9024204c040540c20700c0344e2500500d0840e401c40c00c2007100c006c0c0c03e030b0300d01030079045030440c0b00c0c4070f102c4c50240142032040e0850030381d00004807818403881d00d0340c6100c400001e00c00c4c0001070305642d4200c42c006000e40103940c4150015030b0f85c201540e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 885857616 1250 885856366 885856393
    0xf0e040b06071506050d080c0f070f140f06040f030b100e0f060118030b1b03010308040e0403020a0b090c04051e040b0c13151b05030a0503060406180923 67
    0x40c4001c5a00b03007404d0f0398000014032621400d505404003405000300c65200c01c19080c000b0f0800ba1500d0741640c00c1c1d000b00c4009c1c00f10701e0b24060030009841d01800c007041e0071064200030812040c0c1d0507810540c4078a01107030000f40d00c000c1a2440b0203072031260303c800d03016841d6403510101010450041806d9440d000d0002904401c18480140d8840414940441f846407002801e07421094250000c1c0c80f006100d004120360240422850340002d40d41c030000c1c43c42d644c0b4545588409005034080c42060801c0080400c043c10700c20001400c069400942c5080705041c1005460b81d00d004480807107003d03a00340360000710513074042400501d2540e0302081004907503440d940ca2641820000384a607a0b901307002c2c0404503804213100c00507006014031000200020043d00d0000d042820210909401c01403220482d0300064000300590303080f100242811a2281c0b10100002d0141000382c00105d43d100301c0c00c0c0074580c3c41400e9004141203d001c1e15104203262032030442d0070400c442114000340580c1c40780341c034010403 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 885858866 1250 885857616 885857633
    0x50604030b0402040209151c0b030a020306010b0c07051207060206060f010e0f030316050c180408040e0c0f0c010903090902160f0633061e050a020705100f0e040b0607 73
    0x307001000c080d0a4030a024242d61f0503044105043c100d02c413101e02440b4070014070320520311034450803401020652003550000cae41d508014000d07a88800c1d404201c81e9044c020802806001d0031008007042c1d0000700c0c04071302580c0d4802d14810303503005100c0c590215201781080c411044501d881a510960380c220340d10140840d540c40c007995142c01d840100050094000b958105e08005031040029000e0800c107402000302c03444a004122151a9a003028000007900907000c403030846214100008050b41d17402c1d100500c50160103181c01d0180c0703001170250001217044d406003640d14403d44070780e41807070b4554000604a0081103500700e50700e21080d4079500031401d0030010b410307401d01c81c00010820040310510002c000080c4248018502c040d919400d1252401c1c0c031068001d84a686410141d50f01c0151301a051401c0c420215424050000b1303c00b12250702c240300d45000342001400b03403840610110401010303200060301042c000b840c425000b0f1a1481e190141002e0101d00070a200d051244d2074940041 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 885860116 1250 885858866 885858877
    0x8100f0f03031b050d0c0b1e1602070b070602030f10030203070b0c010612050606150f030105010f0c060c0f020c010509090a0b1908030a1e0206011511010e0c030106050604030b04020402 81
    0x11082d100c00101c000601c00c00c0601d240f0052951146c240c0c1e412444c4c0442d445d540502a40c0c4d901000c90840a50341ca510400280e010040d130080d2200040d4545099040c0900c0340c01c9100c010000040d44001d01c101c03500254002da0740351035490116a1162000d20f0244820301000b5450b800c07511041020051a0010700000d60781440001051981c541d000e02d0188035040c0c04482a4220f01e0400403e49804850b421410400686951900c054102054440e00c01405001c1c103008443c604803072114400c01c50b40400c10750080d42003003c4040301c100a0322181c18010041c1c01403244400417407481d481a070550309244405085449981c488074400800f030714110301d5a5400c00d03a103064032006441101070b41401401c118002c1d594a0550300f10080200e00406c12095410405004800707002e07900254a604507102c0c8404050107130074440007103451054070001500c0c41e40c00d0950601c8203800c08034111400c410200e008105040d551401d0000d140940c1c400078200005150004026003001e800030034 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 885861366 1250 885860116 885860147
    0x1b21130f14250e06010216180f0f0501031e230102070f0308090c0418151d0c0f180a0c090e0a0c0320070213020d0c08100f0f0303 57
    0x8441c03100342c41e25191074442c010000c0103214207002c403c0011507880710042e40c0240d000c0c070142c4110040841228560310305c3d446900087d207280070a42441c4030b00c0d980a202c0c0741e201150288810315405801c00050a02800250384008002400d404508000d00140840550002c6d0a19018007180c05000344000140c2c40c9080954080014200140d035035040310810791300c6600d55003080d003001030744546002c0d5150a8240a00d1510210a8141d480c3d881d090b15074030361124040385a5032640c0300c6040501400e440c0ca41140c92000702c03080c8010360101c2e00304c0a1100c04d80c2c2034982c07040c0c2607040005003e40c203c403403405100c0a0380815603d41f0aa04000352110b840e08010900075912444441c100390201ca8003a03d4559500340c48516a5050242c072a0225510500d400c0041c0040350b1003142c0d1042e408004d201c0c111400002c19041c840d501038401c90750304a0410442003042c020050300c003200031945811030304041c11010405400740d00360300b0b05480103a01c4940d0984c0c21654156000d00c0c0351041503 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 885862616 1250 885861366 885861373
    0x601021e071508011e060e04020a021e030904051308030601260c1c060b0a0c020406080604060605030f0a0b070e03031e3f1b21130f14 59
    0x450000b816030964184040c066440f150a5850100c03402890500e4039203d8a80c05c407000010841d03680d120740c8a10300c0340412034005917a070403c2601a40f80c05042c035400c407030368400f1000665210702c020000e08001c010554050180e6610a21211105507440c0001000c1c40000c1c0046851940704100e01481691202c0c0a0b00394054420701050044500b1607108140c030301c1c0003400e1080c28070a0b07050303614100000b00080c00b1702414050956003502840391040200400300c05178100359581d40d001100213050503c2924907a081c00e007040d50140c082405030502911900e07805200a5000040d0304100d9500040d8000da1a02c651a08484e0320300c40040003645803000784451401507048605000e050041c64544a556803410462110010051440341080c003480348508140f401c080500424074000ca1312401c500d40d5110400306076000c01000c4102100034000c154014100b0028400004101d00140c41b004582c0d1508405411010b80b014010407400c01c5807004800a0110502000d465400d40c064 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 885863866 1250 885862616 885862619
    0xd0b130602030a021b030a0c0318090204030501090c290711030105070c021c0c090b0d170d0f02040302010509090403091a03160305010e040807080f0412020312030601021e07 76
    0x1030206a0b0415100d5909440d400a0840c80d18110f2104000341c10701c40784059030070624414405800000103480140c14004035101c0c07a0300700e4804a5080d00034003496801151101d80f60b0400500800800108079800040304601040d1000c070216504140c0c075010071000c0c00320340c1600c1031050300d42010800300d6400c0481181c0c1c200540c2c00b800b86511a00207585c27262035034112401041030404820107011060f24142170a1408134800308440c805403a5000f0740403030382903880d10110309156101c00300905400c480700b010582c1c0c40030010080c8281d484d40d1200388060005403502500300d11980c030009000c00d071304010a84250808002007075000c0e0084c200501050795420302200c014280e8051442c0c1d401d400402c0004441e002c000c40ca51045051804100f80c0d0306251420603a003070042d0002e00300541c042144810040700804a401c0300715104483ca031aa0ba403100405402d604031041240b10707010352608100c5191034001964440c2d84140e00070100094000403d00d941004409003074214000c03001c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 885865116 1250 885863866 885863873
    0x1b030c1109041a06010f1b0807021f022e0f0f060f091a0913170a11240601050d020c07080f060a0c1403071209031215050d0b13 56
    0x31552045000d1000c004030740000f01d42c40c04036540c000300310f281070040f5020400c0300382e5481580d107080078404803030110382c03020b40341445d02150241201c003c0d4011106103130418040104080f0041e5005030381c0031100a00030b031991441061181054400a0025000550481d11040c1e0080000502c002c0000950040f41c0420310081e10b890790041c090680094104005500c01e51042034612000c4041a1a01c0d5140d0000075000c8800070f0008192155040922000e002030018250100380d8002c0003141e6900c4102d402401c824080d0110b104180180c030302c003640d4000c06891000c06400219601205542c1d25001529660800d078441d87c481c84e4203101e081802001001440060301c18a4014501041042415407810000504805030390b0b045c0380e42418107980140c4100008414460070a803079654503007003198501c0c500c070700e6010072504000c400b00038940c001119406200d44a002404a03440c800100020001e85104003600500b080c80300401141e1001c07459034000d40541c82c0184010380a45 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 885866366 1250 885865116 885865129
    0x20607082d090f090c0a030c1b0507031202010c02120a0e04021206040b060403170a11060717010803040b030112050703020303030a1a120c09061f050c0105071b030c11 73
    0xc980090400005841d8100d4581146103000c000c2044441a20a203806000411540201c00b640c0043c96152484c060000d170040952102d020030180d274051061140307041456841450744819100c0d050700d640c0c9004824410301034104000e14607001400396130080c02c000c61140e444040000208007000c4a12a455030326030008206420301c861301075800e8180b80c005c00c13044031054122940b2402c1304000400000740700c4481c1502440c0d0004000307880300c005800c29142c0420a07140c1d120140540f1040000781070b0000c410000c000700051102c1c4403070f030320782800c685e03288110b009985041406200401c0030807a44141c400d0b00324032500554403a0b50b0341740c0c04a491504160b07111380040780c40d00240d1103070464075100b0b00d0205004503040003480d0000041c840d181c0c488424828041c190941c0040d601c1c0d11803480d89126200d064840105a842449000303280790041e0340191100e50034000403c00191044070b0200615000f4201080c14450300d5400b0f491420503281d04a907282c01680f101f00c3c4a03034492 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 885867616 1250 885866366 885866437
    0x1707080402120d0e03010c09050913020a1a2802070e0a020409141e01030f1b0f09151e0e1504050a02090306092a010c050102220f0302060708 62
    0xb41c503001e61303400e00700041600b900c204012020030406581820041d40d0381381407415411900340119040e16079940d00100f070340e40440350401000ca8420051f80d80401400c20b0040c91105110b07050f50504607100796030007003800c0418500ba4010381c8000300911114015508264228100c01401440d2641e21803861040c0da840503d0040b0404142c4100940e0160048401400c1040ea4030091030f00d40c190703901d20508039060b0102038601d02403200600050381000c050003010b0250140300c1d001c1503554552510103016007481c0b6075264609404001031548020695002c5c0400039102da8010b45c2c1003007146480d90400038030307181c10902404c0305c0103c80e84540c80b815002d0740502c040980e84001080c1130601d4814083e0010075154801e03000d00c03005051014a5549508801301600c40301074401c00121151007180c8809030041d4400a01610142d81840003401001c0c1d40002c1488140e64070181509420002d00c401380d0015420020040002d10003002030003106180d94141c0046000740b1045803900809 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 885868866 1250 885867616 885867643
    0x2010905161a031b0703110609160503210c3f0309210d060b0d060b0c0d08180303040c03050c0415051c0f050715170708040212 56
    0x11a0800d200300d0000710342601c982100000b80b1071030350510300e5100446807050140e42c0004e66022030580205031140c4500c01c20a01c813175003250102d0401050b41c6072140420410607115001000d000038007400c000c00da114075401c0d14442881c1c490f0b1252800c0c2c240d0386c4440305101c410300841d50050f10482894950180444040d8071981100020f5440b0f800030201401c01400145014000c009a5000024102d0b0748912150007005000c84000142d14071070082c0300901c00c0316030034500c02244006003440509042c9004250600c151540c40419242c1c500c100601a030054211118800815000e0b81c0001c0d0042960061611211902c0900ca030443e04291000c0b609564030800400c140501007041036568001100c0c200802e0413600d1244100c14094807030180101203440d42d0742c681002c3d03101500c0449821040e46000506c1600e0525215107003402000580c0c452030600d00f0500b445003120f00c0308031407a07100910040e12803040503070302c040c0000c204030382c00404146240d00b208410f2080c0c1d844080c8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 885870116 1250 885868866 885868903
    0x203070e06010c080a0e010201140105092806090f0f110d0e03070c081b03071206090501060509250813140a1b0e01211203090f08120a0b030304060f02010905 69
    0x21b440020b0940f0301032944c8040c01c01404006000540d140d03c500d5400c0100b0b00320b810013240100c03a40400d60b007074000802c0401c600c0c00300001032408803a0400100441a0340c0e0422010420f0780240307003180d44108100c5e06200c4c0500100722480f415611400e06200410102e9080c180703242c0c2c2d1a455010320782c0165406822407107034401e00408031902d0b100b0402c001c50140c10020305240f440c1c00080e06071507022f030800c0e46912070901884030030360010002d030801900e407000902e820400c001214280f800600d403542100c40c503894286115042d5035001d002c800d40704014681068650f0260010010302e8410240a120000030024503254101c05070f03000c49444c4800d40c2e5103807443c100100041680141a1000105142d600e0341d08070035400b000596000221224141d14440100c1c01401c9101c8010b048000d17418803002405444000741008456984d060303c681d84c0c0b01c03498030b400d98180e1b00c00e81d034241c0e1090005004580c0145025000200e451000013680302154899501d8a5215800e400000c0c9 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 885871366 1250 885870116 885870137
    0x10b3d0504062d260417090a030501060602030c0d02010501120609060f060f05040b1206162303190903090605031914041a0403050a0c0201090806070e0901060c0203070e06010c080a 79
    0x85110f019950451100340401e03050b0320b810f4995020300146c6e2002d1402079280012080250b982d40d05800c0c1c00703513030003500822140e034499102a41d60350044503420414820b600d44905014414000c940c140c50461001c2507140070f507561040007410a0a40803a900c0f6291a25100d541500d445120002c00603181c040c0030b2a072030241408121074000340d00500401b89224048014000000ea071a08806d12103070110040032268800c95411581c1c1508840160002d05010b9001c14a000994042c2c82e110041400124000504100b1a181306c007000340070038038a2904104040c0110091540891001c0700c440710b00c0489078140c01250b13640303400600c0f0894031100303010070322120001260b4180c071450900f890500300350314041d103a4094100000104400e1551a01c00c41e44912000c0c1d00500c01c030403c07920b413410802009094100f00d40d902d83d020f02d544100000320a0b100d102d4664907145c026001e0b201103070800100600b80710740100101d06000c1c08030710b0103000442c0d600c020180600261307500003282 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 885872616 1250 885871366 885871397
    0x80a0603080d0609180206070f061d010b040c0f080f09160305011b0e01051b01060315050f06010f1d06160b0114180703020705010b3d0504062d 63
    0x39030b0051030400314005d40480600040c3c41e26011282c100b42c0201c0001c3e14031850f450002c0c090880b9902244d10b11281800001460790305420404404808850030701820646400807207000040c0072240740000c1c411310102d886015020b85540d000f14514050710f02c5403100d07002a4940e90a07a83c0101d076983c0d501c000100300d2009008403d4409942c0e40b07045c0402e451224002820360280414840c000980000300f0204030310254070183c025984a802410480e2803085220001c5c10300712142d000004000340000c0081d882284450714020503601e0306000b101c815012280142050f1910039045881006091003480010261020b100d00c12140600b856062a02041e01010b42c944454060450b01000c00659a00d5400c1a540314080e4540180c5a00c458208140948094142950006000410340d0a040c0f070450140042d03004108031520360703c0c000c070076840010314000e00c42c1300012401e00050203c01e10589040e45845900032072a110fa0001c81c0d10105000040c0100e14041046054140d415 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 885873866 1250 885872616 885872621
    0x1141005031b0312130510050d0b090613090204090503070f0c08010501060e130f06080708070608060d02091305030d150b0a0c0611070b0f1b03010312080a0603080d0609 74
    0x105580d02c204400460030355000c80d80d18a155508044128408142d8140b4008401101e100030f00e0001c29038819404070b408041c189511220305015403c2c06c004400200d0b00f013000000307000e04006440f440349002c0d2010b10b03000400c2040405c0740d006844003040408124200003900c040742c041c1034441c1c00c0002500e0311001c022660740c8212a10390401d001080b4030b5400c60820007440d907059815072700380d040d0308000b0001412a030a0100140c1d1514401140d0b04c4000a4030710261040001211040c544075036055035141000c481255001000008200060412a48807a0004c101e1047c0d11006035095441c90700f15040030400d084580d544072050101000c54148290003060700b400201d203051882c2c94018641c44500c0d001508540e100d0a0b0051950a9841261203046e0000c000101d01c0c1004001c40401c86419030780c1d1036803030411005228040b000d800880381205d5000c1069030500071000000c0d0351008008007144003182d030300c09000010030101c1c0000c0690050660001a00904007001e0504 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 885875116 1250 885873866 885873883
    0x60f0f0c061b0d0f18061409030403230718020702090f04030206042604060207091109090a0b130c11060a1505010513050315010e15010516050114100503 67
    0x72124060105100d000022500711140b80d0060708001c60281c04c081c40341000b40100b41d1a58001c0e0b1102003000040c40700541c090014400c00803146003e540303800b014942d6900032400068040f2220751a8080d0300d540d0f106421010352401c10958140303594401c0e2154410400c5c8074441134050300018090b04525040c3c180d29480907018180d08900e0402e074400959514006100410b04c203201404608212491a00450341181050003155115101c110003512241703940f0a0301c40403810200c2d40c085a01c40c2c00280d03204072901428414450343d45100c0c200192480d0420550825120300c1070391031000c0796004a542010091711100518000b213581c0340d150400080c0f020710141d1a00c10301c0204009000d50a40480c2c0c424070784140c0f509642414055100c910b64481585031056a45500201d44800920390480b200d08002c0009c0b81c0e5518448500300410307400603070003c0d1040182c982c08040d2a02c00b9003869018600000c0c0d074200c5103840000c031b5001a03904416110312004104400d140411600d007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 885876366 1250 885875116 885875131
    0x50c0f090f091e06030721020102120a020a110607050c22020d09030e0f030d030b060f0301030615170d03050c21160504081c1e18050904021509060f0f0c06 68
    0x8100c40c600071860204d501d04080c00d680c44081c41f180a03043d0ba100708104109041714180c00c1d0341d21296424065969109404100d80300202400e601c040c500d40382040c2d480b00e640100140100d09800010010543c000600741d11100d82d41031003080d030b050102c1c07000e041c1e0311014a2001a90040030b0a020b40f0840140702542d2007518580c0d000300a685010036101e043c120341d801c0104004502400249080c00b41d400d24806901c2d001c4000030901440d5002041d0510b0b403441c0d60280d60323841d103200c1416804140030805155115082d481c60f92031080d4000c0f075100e00341034402c4e03051035034092511000404144800341100740c10402e000490304034070301050006515007801d44c40c1500d0018400d440f481c403042c0c1c46c1070003000c5071032192105024041803141011408203422020805040142c5940022a45106807640311200410729003020310304a1b000300d400402c95070a104a030395202e01305030300031001c240c3c004006100c50001c000010b4043d09400442c0041d00d901e6072401c0e5000c91404c4001030010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 885877616 1250 885876366 885876373
    0x120109021608090102010e01090c051f0c11040b100e01020705010302070203191a04050a0c0b030f0f042120032802210304030909050c0f090f091e0603 66
    0x58001441d00006541059000e80000e8a9001800044c2d005180c041c020300740950900322039034100300b05505060140c607000c44051088000415000920343c0070b80e9020008100c5140071b602c045105414203018121000b0404601101c6d030001051082e060118118041918403c16082c1580c060040e503018210a10341142860304d2500000d40c0c456203c80300c104444501c41c007080c00d00c00c1c80c40f8959400c1040500b0f00d19142007918099a80c0d841c501030907140c21003140e0001c920100c054080740d004800a21800c403143d22141c2250b0120740d8007500841d40002c03c40320300a0501e04298038441203c07010b4940014045422504004800c0c403110090140e4004103c644801440c4c03c001d01700184880d90460001c0b85546002d9182400d01d180c00780003550030500c015540304140380114805c40c401e03919100d049030345500c03410944009542c4041d81d05010f200200390b000c50301c005400040401802d036000100080081070340e078241583c0f400f101707090041c1c206030000c0d039448000f908403030282c005 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 885878866 1250 885877616 885877627
    0x10c0e0105031e150414090715122c0c030105060a03032f120a02010e010917070f0c0e01050a06090302130e030705060903090a0f030c2d0b12010902 65
    0x150521aa20032101a01441c002c0020808113090120803403108030010b001000800f03600380c2c490660581c21602d984042c803400c000031aa803a0010f03098015500107840344000b04482141c00406003401503240e54101601042c120241c0000c0c000f1028040c5105001c1e0121070034010078142540c40081400b406070754100020070001c0d500480b011440002c203241c030000c140e0440e18420880c0c1070f09201e50483e03c1188004840500d00341c1c000d0906420f00c0d0000c01900d04423076100b900b81d80500e4006448400700b000c1c03141c1d134040b104004000c00761080400f0700280700155a0746903000c90603004102da9040c003c005100fa0b0811100d46400307440710382400e1101601c0c641c0000e5800c182148003420541d1200c10000c0c0d0558100151140c40380d00c003041c1d521030300e0516a8a69644c12070340485114600c0c2e04400164440e9440024040e00c3c2c2200c00c001c20300d81011000200f5401a42c010300200f051900800b030f1080400640c00041c1c50302004040c1d03110551004a041d2a5040c0c10540109104022 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 885880116 1250 885878866 885878881
    0xd1401090c050705250b1c050a0516140c0102070b090c060304080409150b1909090b06030a0b0126061003180f05011116050105010e1e0405010b1002010c0e010503 71
    0x41006003030501000e14000354a45170b021460a0110340d1004031031030808141c00c4103549646098080e01461f9920400c400d55501e10307181c0513140180c500e101000b45840a60404038402c0180032000208808901d180c495020510b07403ca0348003480980c4c09a02403000e2041c8001f09004050840c80222521815414180c684e984280f2039031040c46e4050ba900c00c00711038040040c850311001448031444450311520380010700740c889046580c4042c00a23610760ba0203e800d00940c0b00340e410145025080b0342c1159940061a0010b128040c5200e0600641c01d07582e034100051020712005046138211a42d000b07041c010280309000495000c0100ac1c07604003841d50310311000b850300306640c00b038001c101c2d1051b14405041039801820101540b11002d0400030b085400302c1861006c0ca0301e001c4c0304e00c0003040241e1742d800c4050b9880e142039800300b90b1b00040007400c0c20494001ca1a803038205000c0d400000b04136001400040103030250140d040c0140c0d44803241d190b102030b003001c0c40901d511004c0c20070a145141009 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 885881366 1250 885880116 885880123
    0x1030c0504110d202706040609050d0206090901080d110d0c020d0318060530010b0d0b090a1b0306030201050a2307050a1401021806030406020d1401090c050705 70
    0x403596090b9603520032441e4505211200300c1081450b58401c415075403400400780381124016601050385490301030403175109605010b011102101d1443c1e40750740c0e41c582003004010002c10b4851041c0e074050000d1040d5051552000c204034020301d4100000c003891290302002406c1c130240c036042d401494002c009110790241d00314200d1200658100c601c000c90792100d1806985030751020781c0084403104c3c41140070828039008402400941047c251403843c4200c0c041c3c882c00c90031000c0004e03a2a8419000c01009612410406048103030b0700b005002c1020100b40b00131900c1440c084030f041b18081d0312105013083c4048150301140103c0050f25080c450384e825900043c04620444441c1802c0008181c80340c00280e4220401001000580310030b603558074280d0600a50b103180308001500c1d04140c88540a604c0c074014421104c9121400184450b084805010040c540d00004c0007600c4403902040040e03041d4049201f5020400c0e03000c403c401c43c03035041c103400b0004c0717501e034480806c1400b808000c84400300d507000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 885882616 1250 885881366 885881377
    0x10305160b07060b120106030b09121e0c1c090302040e0102070c21140304170f0a02010e0f0d210306050609040b04061a03040506070905010512090313090501030c050411 74
    0x1c40400e4850420003c05c40b00444004601015442c0c814080100b001c3c199000e801015001d049505020382d4403040c0c0210b100b400b04c007044240d01c030b80c5000c49600c04c1d44003a02c401148501542c0c4106458080f2844200d036446414000a801c840c043c01141780c030f0712420605103880e1000318200030640c1c3c0d903c14000794900642c00203044054000b210b002407081e503820455401681c5844035030460b4415135494019000e441c850141500040b084204001008180e2101c1c000040035040200d0300191080b0900f003e4658114801c40c0c0701d04840c1d00c078040c900400d1403192000507800307641020a10380c01a0b1180401c03080509251040090f40c1d10041035500c000021180010310fa84108005801401140d224030b10078000310303c0e80c7c2c01c044d01c400c000c0c40c400c90240c0261503255841010460768203810740281c03804102c040c458114250050034441d5440110202120b181c40400d40c52000c40d444141c0c4008441c0c2d842d1401401045003004542005050130740741442550365003201c1c04541d0081 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 885883866 1250 885882616 885882623
    0x19020733090b12100f0e0406050c2a0307060507021608160509060a15020307060b1c0b07093203060c03041704050d0c060e030d09150201020408010c0503010305160b07 73
    0x701d9002c901c2d0500c040c03d100d030003031040c170b001d00c4074035640c0e0440d004100b0b008a80c20340320145000001040d007035445048036440341c00d2082008a88080380207038200c3d2100303004080450300c0300707016200000380d213881904d0061800d50010046030402c3e1805030354070344131034005500039002003602222080420100805869045800000698401011400b40d043c10f07880712005184103404d100100740c0100c020082240550760034000301c00004140414041442d010741c10103031141045001259035038000a40000c0d061802205080c2d5451080300e404a11195080a800b0009184011f5050381400384008400c150060211403a09200c00b92480c00014409041502c0c1e900644244000540480e40a00401055290004050708041502941a008690101d07038144140d480b2450b00280e0030a14072903076a180c04200b400c1000c90100c15081c0c036010008d5640a0002040161081c000c2110000c880e80c0d40da9103c4d803444c03d045146c94604d403413075000d24900880c24032440d07095800301c41c0031542 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 885885116 1250 885883866 885883897
    0x30d050a030c022406090a0b010e1e030601030c2c06060a02031918060c050a0201050a020c06070f050c1005180a030b0a0504050d1419020733090b 64
    0x80801003a81000c084d054400d540003010046815080da030100c41030700800050740d130910a61303103451030741080384c0305540500c0c042a00d1080d00b0f0322a1404500c140001e0074400c0031419500c58200c04240703005d030b0070707002100c40350038441040c0801000d428803541084800c003070070300220200b804204801c200c05068140510310008a505000c6c4c02001203401046942d001030b08074410000005042180c1c0025100000607038190010b15644120002c03880c080c2c00202510b1451142d0340195090b601180a02c1c6c19401240d900d200c0c00e540300d0000d44201030258140c1e02201e0018a450350903e002c0f1240e40d4400c8007900380c480a42c44d441415200082c50740c04410a401c0c084500044098420ba0300c01450344240c3c90822850f044140c0000e40242d105500300c45a002c190070b8259580164080000c00b13a2000b404a40207120701440004100b62007070041e2855691034070311f46034550407030300c80700f1b20a10f83c509144562007086400d81078801d01d562520300c55040c140104600c241c86816241d0b40c07401d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 885886366 1250 885885116 885885131
    0x9010e1207110d031115060f0d030e01030f15060c06050f070c0605041109090a060b310221040b070503010e0f091e0705012303040209130b10050906030d050a03 70
    0x1070064501c04004034445c401c4030540494801a080d414104660701c030300544500425040500f02950b503a070036250705072103200b4626801c000450044c590301ca64580700903100c1c4d42034030700c20980c907121002a0001d6954414030117081c0c01e00c60705848019000302c03003d10a48040200e802c2c5d00000ea550455440b0b4030200d242c0d2983c0c149040c24140c441815648014598144802c11000041d2074413920f04c9801d09100135102202003000c24291b0b00302201c02410011010b8407075883c8450203111896102c40010300f45406409842c2c820f03203145d6040c1c0d040300c012009100074081c403480176680c8121607203805841c540c1000c1ca20046503002a2900084055000108544000a100390b50324000b0480c0401050503060705a00c6d52150103105883c0400e80e244c1c03203081da01280c10110319426041c1000289581c40d560b0074800c00f088020b2031480082c56190b4460002203007200c189008800030b80a41d81201e00745000c1014482015040c948030364000da80307203d030746604078003611130308105410f001404c02c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 885887616 1250 885886366 885886373
    0x90b01121e03081605040f0b09040e0c01021207030c05101415010c0f031e080a0f020c0a0f0507170c1206040b1f05030307120e060a0504031707050609010e1207110d 72
    0x24080c0d80c00403442d0b01307081c0401054a1a80502034186a600ac940030700281c804c680702d00c2d440d8080150341c03500682000300a800300721088001840c04034440c2c81d15031800070341d5031905400d000b00c0142920200352112442d01b1540c0041c10020342005410000386101c80501001038003100b10781c1c1000300b61002583c102c50034907018041c00d0008003046182c10003140c03190706008060788802ca030100703035503407030045081e201c19443d10a1b524031002c14801800c6140d241e4490045002201e58121610b00c1883c1d00482c1800c6000a00c0c2240905000200340e203a01c0d680c01c000f449d94001c0c1240390136621207420800415194a1002c0d0410110810070450380e00509041d03205031856001030750588000251030342000341204850b034100315507a848401800c2100b08114244c8074803000720001460034802030000c10340f1408019090b04401c5d5403546440c01c181e881ca4100481110b621550b41d641b08140349a12000b403040380d5440e11b803a541180782145940d2102d440e101d038003084c0b6004030700d003075412004c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 885888866 1250 885887616 885887627
    0x209040c05060304030804061a03070308032518140904140c12031e030103051e0109060f051009050c0720030105130302120f120a090b01121e030816 65
    0x50500900b48998a181608003d00301200948003110324a14001461346401c000c01a0721024980c01009405401d00c0c41e2200d02c034580014000f140c4030b003410500512040081c00c504c0b00b01e810b1a0b10352003c249100d5420312404c074a154041c0d200401c1006036050340e80e540d1075070b10b5800f5600100000000151641079131800507052420768014500c500b0603400c00c03d000014008150231a0040300295054001041305800b0a100c0240940d001348040303000c414000075a20b043e100444000540030f55247c650f17105669000382900c5e02c056840e4140b1000c502c0c20542000071300a146802d01c15402d140c0a10a00c6204074240a4001180d0803030881c241c0c0c1c40140c00b03031010040200280300314107000120282098030f002c070840251060b011301d01b107425110f505032840c0850100c4898203204c003030700c0d0312040b4003401040107003c0da80d40c00101d00024155400c09001e000c40950071100447c81c1d25140894810300b903601c030a1040d05048400001e5400703044603600801c01820000341c0c4d04a16000d440 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 885890116 1250 885888866 885888869
    0x60919140109090519080f180a0b031603060503030a03090203010212090c01080708060d0b0403180b0307020c0d0209060607080d06090f0f0207120e010c0605241801030209040c 77
    0x345680d40c100000c1c1200040d0028518140140c05492800420f0051200d1070307406610018020b001c241305001c40d44680b140507041004a803101008401305d52000601d032244035800c88001d11001100380580d0441e02c1390b510320808007c2c10b0401c145414040001e41d00d020710500c003000c26440b44171407070031500c0c00c0d015601c04070100f18a003065030505100d095150b0034142401c900040410002440881c071605070740d406040090102c0b01c914046881d458070a10000f4000d8090000003044212007016903441440140881106107481c0d0820030402810039800850031071150500a5240300541e983c844907a8000e4401c0b5066075035011a0b181c2120b0500039507407460700e44c51410500089104141e0000d5801e108031490804c00d04001e0904002280031724000a013201800c062600801c5009003501010b40005042c12000c0d4007217982c0d40000c3d1030040381d00420060b801b070305000f01a0107620011007030712021104100c0d40c032010340511900031030511020348200900700202e02803007281e220020 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 885891366 1250 885890116 885890141
    0x604060609140621120702041104030308062b050703030206161707031107081905180d0201050906130f0b031905040f06110901080105151b01060806010315060e060919 73
    0x20900c905e210a08a03181c3c00a04040c2d00079400e011115040351646001c44040d29450707141e0f58220344480c0c003802202445601a8a01954403514450401c1324001030031b03c15a1040c0c00404a43d402c42c9002030909070082c05612521150800b03904500390402ca82b0510030f600d002c0d50103810390300c034081140a800808000d00b141e143c0000c4400c1400100001054114040c0161071780c0d098036000225507034495940c02c10094100c45003450814640458030090300d0340140761150400f600d0100140b85503000c0000c2d003155415100040244032103580300310004080310840729095103443c4200a80c0140d4070440310001c036035180c00050412100c8281c07030042c281c1000e0100103401c41001041e103258008c40034580868204c2c0000035044c6007010782141040c04d002004d60601c00000304110181c50350100f056443d5480d4000030030244010002d442c0294011030000da4494680c00b2440229551600f00ca140281c9003401c000c2281c940090700d0382c0003942e220725540299501e580c0e01000f40390040c07001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 885892616 1250 885891366 885891373
    0x30f1602120d0f022406040906020301180b100f1808010c1119020a05060a090305031810030501030302061501030e01050f01060f08061810090504050604060609140621 73
    0x3004946070000e4022140041500c03410040601154283d03075034400700070402c2c0710b241d07460458100b041e00d05680b2500003078090404540e41039142e4803036050fa00241c0281c051252081040009030340701d4020b0311800c13002a148143d500f10300d04401002080f890700d20340240b245072180260340032034040c140001000c0303041c002c210a0031007120050201000428035407941c4100d03c0700e01d040462449030b09103520f600a09160320145040c1c03d002c05600400707107200c180840c207100080030410600041c42d00c28114030011000c10101c0003005078a5100e95101402c252030480144002500000c0541c0c2200600c0d0480ca000a4200012000303010b00c0d885034106542440c05124042442009150688800d40c03118281c20341e4940c01101c290208039200303544200718507a9103072076001541200e030b0040c00c2001d080a08544a190036010b0341d00545007220303954002c00410040c8000303440b45c8000380c0030022090020b00d480c00d015942100020340785610800300382102c4104000410414584042d050007503 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 885893866 1250 885892616 885892639
    0x50906030103020d1e080a0905180708090703020a031b2108072f090106051809060f1f1701061e1101180209010e06010c030507050a0c090b0f12030f1602 67
    0x1004070713400451f0154003191683c80c01113107600d40544030301d4103500205004c007413a9a440f441107907210700c080d02c104001c0c007a4000101c050b8503080c03690710241d40102286c1c594402a086004003020050b07100c205210318a12000c1242c0f22519004800d42d9000300e580c6840d5059806e00c081e0b0000e8412019603100051004004035200042000c0401d10048800b0311507070ba41c0c4e20b001d480034400d021600c820681d41c481040e200b45005120107401c0740300600702a80c6400580080343c4041211030608054508625000500c0d9500140d000019a68a44801d109514003000a4010200b40524400c09421400c3c1920a02c0c407692141d01040f40401c02401000c0e240c1c00000c0e010300000d030342a4080d550100010401c0e00c515070382c450140406a541000140240c0ca08a40d07542140c8401c4840b0300880b802a070210345c0582c8a9005000c8d0880300140c1c80010004102c501d500a980c02030103030040e42d41040c80c043d400700c287e0b10b221301c0b8082c0c49542c42d44641d001400f00740e51550000e504c980801d14 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 885895116 1250 885893866 885893873
    0xa05120603150f0907081f1812091809020f061b061503011d12030405031c1a120601061805130e060a1116060e0a03020309010f050906030103020d1e 65
    0x70f0710300540022041e03030007080e01c8040355501e415000301602c50307104220041c2c1a5426040c2d10615206401c01038808804005030340f80320f000066042900c000031340850f800d01c035000845881d110210f03000c2030100309204035980851804c0150605540c440c1d00c012440f40c41030515504c1c0568403950baa400d4480900e4441c042d04145600f0006047c041c0d1300e06194500c6d0400c3d015203403402d0301d40110003011394402d6203c010f151548001c2c007c03036050006001824500018001c1c042e481c16612501003800501301300000c102c409901d6680c0d129003c1044180e4041e07a0204005054949900c1d10040c05c000b9481d840d580704000394491a00110100454003802c41303039030301c0601208101c3e010340e10140c86080424080d02c0740c00e074000014140c100004410508825018202a032081402250701d90b01010400c1c03c22110103415809a000040d842000c1d41c1e200010000a03002030909904200300c41011592034001400024062012500240180121581c510902c90807400c0740b5040c3c0c2c0020b18 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 885896366 1250 885895116 885895141
    0x90c0d121809020a020d0507080f07081b06040b060103091a090a0206122a030606030a09060c110d14071203021909052103031603180302070e0c0a0512060315 69
    0x908950040c00b400a40d01b143d10701c80c0080703512094200302041c2c00c2052128045200d83d210500c103e07409401001821070503040341d00c41810b6012240041c11444c42d09080000d44c9079130080901c3d042616140ca1031000411110040d00030340481c400d00a0a5a41c20025038684800000081d40c060004240747c103006030825517452159070000b2069508a1807200c0c0c01107010400b644840c1821018400200b05003000009964007040d003480c0411400c9441d211181154503803c0d404000550b168446c104100003048820040d0905140c00c60941d543c10070701c0201c070701031800000c0100325015084580903200341c042c0d958401c103d01e00d1080e03803010300c20050321210440c42098010f4240c010040a204500868050000c440340701851643e5240e0001001864a000759002856a00c442d24140c1100b1000800c0d92184260000c1002c142000d6450303400b4800244905d03401a010007030501041e030b1000507030700306000e130214560780c60700c0f401c0000741001c6c4180b080c502d070380c0080b10030020701d2500c81 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 885897616 1250 885896366 885896377
    0x2030d030b310b0402041d04080712020c0f0f01021902060424120b0f13090503190801080601151812110103140103170904021b0d0206090c0d12180902 66
    0x400b00214aa10010304c01a4040ca11412003103040142140703c103160440039117170b8494401c910081c82c0c0f00440e030b207114004103200c02c3d0100580c004902003442e030500ea640700022840441d10302c9009068880001e43d80e20344900e00d0185140f98007d040d085444000c02d44002d855840c06075000d075000e20741006e04074090540484006412420310361000d001038440e40c041208040c010288480510302803200c051070140c05480510303501c0f011040450070a0018003400007500704280c00380703c02210001c00c04107045c0c0010100d82c100350010840c0c0d044d401020310404200f41442580303d448240c1201000311641d2141e20765601907004002086600c00b010483c410098904000304800004030b0f80c0800790900004184202c40008141040644d00140005100040002d464003007070505d090511a03500c0210722980d8010407012040640621403150301c00400700040031070944200002d82d134410403c1c4050100c90804e1044401980b1454142308007118185840c040070796103800900095101 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 885898866 1250 885897616 885897709
    0xb0a0e130c091706011419060f12020301050612061f080403120506010e01180521060105060c0a06020d060b03091006060f0905040e1509030409051302030d030b 70
    0x2098000701c3da820340300c09501906a0380500904080c1e003803034240765084001c040e4403540310601007074008072a012040910050a0740c0c0e61010400303402c5d900f001e00703501d005105680130f007401400103002d03985540003500d1039203903810402030b402d03151407000c186240d01b41c28a4091a4000b0741c50341c64030710f0300846058000d034883c1c0c9d640a45400c0441038142150741c280c1d18107000030b114403200d550715031080b4800f100740e064005200f041d032035803640095140600b6120302d042c2c0310140303c071104000c1c105004580c010704040d074504c6e05e44099105171303584403041484010300940d07001c02d440d00c0714001c0e623000e140607044401e84190340303080c0025010798408000c0c2c640c0c41c2407403c16101040707461041c040c504074690b9646980003410b080500f04400741041c252810020f02c034803840540c0784404801d41d81c0c0903690a070040c44d0340fa428651018281c810060802c1e08003044d0a000c04016103000070b841440390000c1c0b800140590010000030700000305200516415980d00011044259a10780c00110071100c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 885900116 1250 885898866 885898877
    0xa05062d0103031d0409030f08060112021c14010f060518150c011a060912010f020a1206140609040e1c09060e0d0807031101020708070f051e0303010b0a0e130c 70
    0x4080100000e440d01b502c4010002a0122024410680600307061508003005040c003181d1240021600c60407070f0020380c000711060010b20341d01585080940b0850f5004090480f20503080d604004a505e480c1c0e05a2068808101d00052440c01c40e01501c1045200300800502100d4024540e40f4100c18035042520003510369442e1048004440d6010300101226840180c502410f000700745040001241540541807581d540790f03d5404804510740c0b008113290780454864000000c85d0030440402c440190300032444070501900c1c44176982da01c0e1010b454044400b29008100309001040c05030512181b80004159407d0b401c0100310714507040741c02d80041d01c41d91340e03429030030f503121404204c03202c81c0001018180c000c041001d080071034892052440745607007180c00075180c000b6599a80c0001e50102c0740c149e030301120186c900000c0001c18807644401c0007194182c03045040440881c2078483c803040c03103200d800160005140380800d01603044504254130081c200e0400700700002c0300c00c0113010b1a518001c00141d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 885901366 1250 885900116 885900167
    0x50d090e090f07090e030d090317010602070e0a23190c020303010b030703020714150106030b0904050c1201140a0b0a080604150c140c070501020106080a05062d010303 73
    0x240002e1a1022010364001848407910b44035101d030003000050014403a9000400464190100c1c6026005405100e170341c0e00201e484071000042001c41d03043c1c128030115003000a0422401e01820101600002035800016005e44840380c03d08081d43d00380180c28070015003008210480300700c0001e40d40b01c1d4075100300038440a48c00100883e140c0c030003401100782d510070500c00302d40618800d901400c0850b02c902800b81044503010340780c500e411051051110f8495500c0018000b0030f5160152140000d4213540941c1681095500d20f5210f103010305d007982c0038054601c42da0304249001d4103c00034411905415104604242c0b0100e00680a00b000d40c0b03002d4560403000040b8030300005603583c0301c1d17500400040042c080021400b805080b6036607500d010000c0300010500b02510003001410f0340c050030300040c503419192000280c00e58240b907004a1294021003000d5010603800300f04c0070303440005605000c000000020300d07034010b03602d41600c0c103000014400002c002c00d42c10809150031031128000414140 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 885902616 1250 885901366 885901381
    0x314071e05010b0f060d02071a010b0a02160e1305010b15090a0b030717040c090507020c03010e120a03050a020d090c0306150b09010507020409021c031101150b070f050d090e 76
    0xe892106001d81c100b01e04000c041b04a00f10383d4050712819110744501218003051507120311a1510a0304511003020380000c2c02211150100800808195240810000946080c40e50030003810010904003008150420390340402a00b035020707407810b0394001d1402d2544042d0200728181c4c0e4201c3c881441c0140c41d000f0020400a801c6001e4910400e05950786e446038420f8404801041c03c005403040303445110006001c51507413180e0003294480c070280e50007010b0007000c6404060949140b09a9102c840d04440c030140f9510004901301e803821000c1e818041016154081010000d02c210401411800c1c50440d403981040486100b03041201d0007080148440300c0b894201026541d01d03842109034a0100308050b224550281d0080c0c48414001880040c8202c28ad40100300b0050a0380454820503812144178003c15800c180b2046123110004000c110407114070540c43c0c100c005501490441550129844042104004d00801010342c013900f81c5014072411003003d42928514002c1c00d407038001c0100082e109 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 885903866 1250 885902616 885902629
    0x2a09050910050c0c0d0f030906050109020d0b09010e150a1805040c171005060d150203190b0907210614120a0209010902030c0c01060f170610030314071e05010b 70
    0x1540130a4042c24045903001c10a60310100c40c80616018961a0308005c2c0100e8a2031050038020704403450056942c45408a03031004503008402100e01c03c220a4005002c010040c03c14145d018003140140050101c038000041d04080e183d41c081d801480007901403020513a1180c228501072482400301c5806642c558661001c5d007107400000c980710368003200c2140401201e07600281e803c00001f900011400083d51039510304800d0080c42040c80c00c0c3c000050050360078500828030300d6a4070101080203850420740002e205084083d00280400405800c1029031514000e00485440021181003000a5842c4400345058007900541e40c4079244400c0a04158480440c010301c40940c001c042e020140e08045050009420141034503101607828070000d81c07000740902c5084040e2000750b0821442501c1c0c200034807449200910440c3c4142c125100303020407401c00185000590742d0500701400e500403005e29001442c0141b00000d0201c60010a003a0040300e4942c4000c000c45001b030b402403000010fa901070000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 885905116 1250 885903866 885903877
    0x109020f100206060d0321140604090c12060b0d060c200319031e0b030d0e030303040f0201022d1002031605090604030b0c04140a032a09050910050c 65
    0x1580021001425620740550110b400910030b044c0000040e1f014030420a13066540b2013003400155030b80c03a098003100001c0b058980d0151046a05014803521552251130328081c0f8482c00c221515082d01750810006a900000302030b10b8040c0880c0440b50749030400d4000340c8903030310903080130440307003981c0341500c0a680380c44207240c40e118002503180a660000c0390140801500c80c1d142007660742e400500015240440c6002c000c400c40c40c01003900d0302d40300109410074060720b010f0001e1101d01c0c01840b101d070300c0110680c0d9016400c80407059408540c0d00060781024a907115010b0252402c500c031405084000b803400000c02d00602c03c60300301d09440088242240301c1620240e0580280c0c101140c4c1d011300ca4401080c0720f16024001506042d03580e910342e20294810f50340c4a160f5403000c0390a0240e6002c0d010880c07a507080032141e4a0045286449e4401d0f030031081c11140314403d0396001304420708010b4400200041c003401d0020425403900c01581074860451003190851542480040b801c0c840f2050151031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 885906366 1250 885905116 885905149
    0x108010b06090120060c12060402090d1221020309190309230604090b010210140a020f070c09050601020d03060e060d03090f0602060105100507150f15080109020f 71
    0x20b150050b02e20064400c00040b4458200d884148a100040200c06210346806511000c3c0d05644400781c1c0811800c0a03000208000c2c0201d00c18440c090031a510101500d2140d0b0700201046040307240088110344400d4805840041d81c2c0c9440000a14508542d000318866031580c0e0950f07119207030307480780e442c80e568050b02c024001484080381804152101001e100303c0d071444582c203041d81d50058000c2600e9420540c0f0801c016a80e13a03c8880b801e580600080910b07865800c01084945203c85c410420500d010b09940449980480c18030340312141541103a0b40c0f10f4001031203a000655460840001d02421100a0700601802c094503a4041c000d0251409640802040c11300c5991400305100310f85000e14000e500300400b081001034003441c0d4070130b98000f514466001c0c017595030402d0148245482c0042c2c0600420804001c0200491904183d1040160841c3d0f40410450300010403540907018409180341044241030002032004815400481110f101b9903034025400409801c1200354010400c140 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 885907616 1250 885906366 885906379
    0x1a040317071a0a0b0d0f051c09030b1b070501050a1116110d08070506152b0203030904060620190b0402060415050c012d150b210108010b 60
    0x40e505a0031488402d60320168011001031083d010300b00080602e0040c110503100c6920140102c030a01c00284503001c003001410200211345080e048004040116500c805841c4085220106040d041c4400c4144480c1c98032259894540d2940e00b01a07000b0a4181d0f8101a0549041808170b040050841900c2d55511015000d01c001ca0468640c0864a24001d0046921a400da4480400200c00d0000750104078064801001e840c41d010040c0c44030390410303007040c511848264910820b04241484584400382c82400c2c410501d489502c04246180151019544c0c0503060070300102c0c1c1e541d80b0401c07643d616002000300700300702c203881c42c441602d61031003903070b6a40104564580078000c191141860703500244050460346c80d065807880b828150040d103040c0f02c00001c400082980081e42c090041071240d074680404540003468101c5280e925a60310715a400c003683e101c01c04001000d24520b002001480c84402460740c41d0107025550001c0c0301452aa09405c0c801a0b0000c581d540d0305120b070b20b001000c060700d43c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 885908866 1250 885907616 885907643
    0x1050f04050c090a030b1902030f07110a14010f050114180712140a14150f0a030c0902093309030f072c04050303010b0708041a04031707 60
    0x28030010300402050582c005004220511481d20341d1502c40c0c000314002c141c0800c0030308003c1800c00c1d045400b860480e8409005005000d800e1010b0a001504848107043c243c280040080d116410141c0e4810302500c00d203044035081c0100d68064100050807034000c10100056a00c86c0000425032a10288680e0402c1080703550400b003008441035290007003002d05040001600c0440420151515098100e2040003448180322408a00b4000c106905540084c2c0c100d5a00c0c0100050b5001e9a101603030a10600c3c00d10001c0102ea02c0f010f00c07a902a60304200805440d9464104480107903004100950140c3c018115003118800350f054880b00c200403800c500190030190541d54090380e04004082981802241c03640004010b04000c140000c0c4000d102e103000030100746030f9038200c00303805480000d001c580301e204000005401004690544103001170850f01c2e600c941c145070069000359003129482d114040a90629006400042c0c001c4030700c50f18050034108020f41415110303005000d401000d0040901c0c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 885910116 1250 885908866 885908869
    0x60c030a031d030f070317040b0412030905010f060302031207050d03020f0c010504050c011211070210031401120c06030b130b060c010216020a0609030201051902150702030a030c0801050f 82
    0x1165a2040d06a450396142c0c00c1e0b81d03181142d0048003c19100f0b400052182d00b0150024900b142015590640c8401441c29031524062100020300007000b200c105214401c80758026070011412380e4200008000200302c02c4040c5000f0452400103034800c1c4520b0500008104102040700e885551001c082c00d48400f101c0025006504103a40d1015044410310140300e0801c0244101481903001c0c00041242e8001e50780090709204030031030440d00c0a414451490250010042280c440f41c0d815140b40b03c51401d01c0130201c00400f444220f107000a90454000252101c00030f08998580b070190401d0304080f036948406804907042d00161941000a501d5010700344600c03940840d0485c107026010a10b4011a01000c82c00ca9228100400ba0070100d0443e240a40c2000003940020380641e00380b40d00c3c0141903800107840c9004288ac1c040d42a4906444c5141943c8207000d54804c14654501ca0052410020000717500c1e6000440b00c000081e29088001c40d0042c030030341e10030341280c8015109048101c135090 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 885911366 1250 885910116 885910121
    0x7170102131e091103070306170703033203071d0d1e0c06030204080f0a0b130f0c1205010b010314180c1903140d20100e060114060c030a03 61
    0xa040b41c102c1a080c00100d010301070280490803808110841d940703260481000e401c6a00581000410080d5041e1140762050002801e4041d07a415007040c005003081100005407070010341e200c04820705403400000b81441e600c00082c5000d055070b0740b20b0404900c00c2080b920380055242940355030068035001e046004c1444030311000780a0b440c2c4140f486040303006031101300c403502580d484500000d034005000c000c2e4010501c500507441c4440e5000e40104035441e103410f81490000f03008a0b04201100b0311800070482e030f480c8044086a8400f000304a02a81c4008044075000105003d171455403d0070842c5d0303001d41c428416280c080f0f5480038424202d8807080e800f03008010310924620042d01c11842503030201e6030303071200c1c4a500ba0f41c4010610001d90940c9400384005407150942d486c10f9000224501c01160007d04506042042c0b03d502c4082e1110455898034203000705487d030313000c90316148405032807900204d4418107032030306034800350284c1c01e494040c842248603001402c01190414811000d40c0d62294 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 885912616 1250 885911366 885911399
    0x60912030613050a090624050d05120f1209010218061303120207050a24081003021017040c050f0a12020d0501090b0907031214070605061504080717010213 68
    0x1380400039294103035a0303c1d0011900c400c407090010061000301454011502d0b8a0203028080c19200030904400a541c1e581c3e40c0c001200100f10f02c5e00380401d1300704508a160341036410340c0950151144240c00c01841840c000d521a448011280640003800400c1d401c20500b241ca0406600e42944489459601c0756440720708a29282000c6020340e080008207a90303090a8400948442c20380d984036204074650900c5800041d000c000140100d003403c22800c6c03500c0b1007000c0b0880341c043d5080c2c0b6100240800c100c0d011551410084035541c810000d210501055001c44000d030b50b0141c074154842881002080340020080c8201c1a800072140c4030180142441070281642910400002c90030580c03507610708244140c11101951583e00050080051100c00c1e40c401c1d8240712030b13080082c81c403044104c0f180694030030000c0282189440d5004620f0980300c0780030948008070480b01c0182c44644881502c1d4640741903100d82c901a07590030030545030808043c404c4440301004001d83c502c1c07141c40e26001c0021640758 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 885913866 1250 885912616 885912631
    0x18040209041401150905012a150504020f0a0b040303110309062704050f010506070c09020f040504060906240c061a1c08250c060206091203061305 64
    0x2444a605107440c0c40c06001e9079089150801c9001d50b0501410394525007403810070104008003600304200340e9030000c0000321001d0b407a003800c0094000342c91156144007400709000b09082c0300b0700252a142c42803644030b107000790f1003103c41000304402c1001300030341d445450260001c1d11170700f00002c0002900440c01700c060030400c00240c4e401c0c54140030001e41d50f0f402506101c00f940350800300e040750070795461a00ca80401000c075020806030402c0d80441d4010a01405458000c160000d00501401080b0300c1074002003900900c1917644141d1f00c6941e480a400502c5114000e034109200862640b5142c0521070640e400c070105955140001c0c009840c902e0110544035050120040c41e20340800c07480e020701103203404202a00010515540e040c000c158a8050040c14181c038000704120010b51042d08407074101c5603080c071603560b01c02517a268002c3c0c0000040001d0606081c0c250001c0c183d6004280140308030642000c1d603000b440c8913880002c1c0c6100c107c1d111135104e80503406504000020f5806a608800d1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 885915116 1250 885913866 885913871
    0x510110f07050f0304030b01030c0b0c030909060d02030a030513270b2d0f010804050604031d06030906090705091009020a090506160b0108031620030a080a080a020403081804 76
    0x4142c3d0300030300b154041d40058500340b040c0c400510500c40001c20800080c0300c03840309607140500c3d900b41c4580701d004054009104890140101e42c0a90b0f03481500b03034455070001e00b43c42051800d490042e200b40d102c20444a11540f40c81400034809103080c00910a4403901c02c0f21107050882948003d0003051a0000b1a40c88000c01c44488181c8e031f080810580d00c0001d68442560045c2d0030f0082000700c5480c80b11190401004800f0400094000300d002600b16606080800c207000780c000b08402c0071035205030504d401c400702008110722450000394442c041c481c00703400c0d28811b41d00c0c0c1d801d100240104071142043c0d101c8100007005038110f141d0040103000c2c51450200b07581601c5a001a041d6440214070541c00c0344824080424010030307906c05070041c20b0001c000c41c0f800c11049040f209442201401030040c0000b8882d030740c40340c210100c2108840c2d2000b001e0b03d020b40c10ae8503100820340c000b00b00d500006041c00303001038800c0c4080d201300d0707090344c0d0424187c1d4103016440c040b04540390380da00000b0350041d4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 885916366 1250 885915116 885915133
    0x711070608041b030b0903030105150c0d0804060204051c0c0e040f080c0705040e0d0e0a12080f0d050f040501051302090123191805010e0105010f02010e06130510110f0705 75
    0x1175401c1865402041480055592945400c003000440d40d8000f503031200300312040121400d5480d00003003a0505020904140c0c98556490400c80000c1c0130740e03030141d0340080102c802c802074a040341042c6060704d0b2185d00c02070002c0d61900c4019083d002c0c00c5400800b0007140100360380205501c040502070b6182c0d038604959030503481d203020070150781108441d07140c194001c0c3c80b035034420360700302230084c040c4182515904e450b50f14145d070041507003001c94006031900038001a0044921101c40c119400300c8055003040c05a400d14001c03900b8a003030221800e0b00c445d480c11020903031804d0000040050650001c082418690070203c1c505803402c4506030392800c080704000c42c0040342d21103042201c0b032111340c0d034402003074149008007070800449407400c2c0001c82441c080c010701502030030740e20740d034152582840d050340181504402607005050301108a0b400d0310508003000013102000c40c00d1144540300344103440042107800384040a540890b100140500002d00c84c591000300c004024013031050168041f210200f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 885917616 1250 885916366 885916373
    0x180c0e1e0a121202010c091701110a090305160e070e040e0607020102130503071203030b03240411060a09092706021207020f030313020f180711070608041b03 69
    0x1c070500e522031000d40b070154125030180720220a4518110203140000d01100e00f188038002c001c808140107aa100064590903070041c0c3d00c003507001308040400e44103100c0d916a10703c40301401c00e0100c9e100c2240d051040b41c00c0c10a494134510b58a00466440d980d02c0341c0f16031149801a01c620f5120140a90070030368038254140b0801c4104000d500643c090307000183c5e10141f504905002c80860781106010398400f5204201c80841c124203800075075010f14000402e14414030000341442251051100c0c80054502c800f500c030390108095500840c8075000c4070b4032660410003404107070301404500d40046114603204011140103a001030840c0d51001800d60b40c00f0007030044402d642d12000e030b001c0d12031076804210040f490341644040c40c3c01c400c00e400101b00e52041c40904507502e21000f070400e85036550040703900702191503c00203803824203001000741c0100241121100650001115400000303900580026403480b0089100015110790356aa030b6107039a259212002684801c80d0091100f0711a40d6000011 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 885918866 1250 885917616 885917629
    0x150603010c050f04030f08300a0605031e03090a0f150c0b1303050904020d02091c0c14041104030b072d1b1a071403010e0a050604060906090204180c0e1e 67
    0x1585002d001c0c40000f010035623840241300046c110b2408a01d007120511050340c002a01d20309100038881c40507108480180654254054034400342c0d008050340802056102c803401c0064103640c003401c000d111004201a04542006103002e0180400700d001c0d010a44400001c0d0203098098007034105545888400c2c0302050072030b80211825003495502182c00f651900d02076505d18403e9800c8135549034201c00d15151010890418400c1c10164242e04071020510380325904025a0110228041f540352662800c010403009400c47d000400920201103180da800d1813604148800080105e41410158040340156103500100b2110707000707451104846c1001501100072412484c1001483d50340301d0815441c0500082c09a0004001016081c0018000715044441c2e19901c000540780100d00341d07c41d00003180007490150172040c56075007061000300b118040c40d001401240c071154407110500240f84a0a0119a0181c001c2e80002e407981d004140b5604d4114036a443c040740d6020038145000400000494 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 885920116 1250 885918866 885918907
    0xf0203060703090510050103051f0605030601090903170c04060c0804030b0c0c070e07020d0804021801090516030e0604030c02010908010c020a060c030506010917030408150603010c050f04030f08 85
    0x26120f595150800000703010342405407824071824440e550540c0d0301c2e031b0f895103000c01403070440c0c044001039010a80742c0743d00141c00920015094031440d507150740d107a034050210f081050700030a04003110750008100745010355201c0c8011200042c2030508141d41120030208103582170710f50703200a12010000c11000314200e07000d101c940d49800c5d9590004103c940c10a0416408a24a1141041000709846e0013054900a80010381750117001c0f070ba680d100160140c4000c0c2c07071951034a042c3c5800800d0b400266403101e0f00038000d9403c108005400464120103031540081148104d4104402080c0046d00403404095620b02c141807030b80025480d08051400c4075110b00f00c00340103038000152142484450b100d400180980c61409201a1405070006410360100c1d200e1001403850000c0c40350400d5505100f4ac0300600603c405440380e101e0045078040f00c000d000d803041d070303c694a000745584407136022383c0c110381001c04041e40d000e05003407541d00c40707403015840d2040c03e46480b18204144a00802481ca140d003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 885921366 1250 885920116 885920131
    0x907120e0709110717070803040b10090f0608060c0c070311150a090501030c1407030f03111b0c0d0b011205030d020a02031809130204090c05100203030108011b09030f0f020306 77
    0xb5182c0444e4284512480c01c07005441c2c080354010048031011425039011a45e10075001000c401e00c079224bd850300c0480c01d503070390300c50705a2a1900c040404001960b80010048409020840743c0d0f644890800048500c01c0c0c52615403942e104690805c000340c00304100395000344005101c544440800a4100c01507445060418001520014207005668051007105070515441c600309003070039030a0035140420300c5104c201805001c0540e00b14a045446034200307031440d14280d90100d8440100300b40442d000400c085e400015130081060341109800c2c03d02d2014152904605141e8142c0d1901119112451807a201514607020400400200074010f00062000c4d11590b4025640e500d00c3c0c000404134000e001c01402d100390b0f115002c0c00030700c0000c045d5440d82950115000074080e01c9615090102a4143d40069005400384603d2075246070080040c0d8101c1d000000284944c4805400d0f95102c2d1401301d814001189101005101043e044401300307003400d1081c14000703400e000f41d40000707103000d0040b203011 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 885922616 1250 885921366 885921401
    0x41b050307020f0c0a03030806210f010f0203090316030203040e190513030e0f01110105010306060e07020a050d050702010323090c010903021003091e0605150907120e0709 75
    0x2009442c0d04004500300722030190f014000e01c07070100b0300088503c205480701804009060021401c03d581d49407180003288000c01c10003246a90808080361140446615003043d5441c050b02540c6d011a00e0003224401c6550b4406180740c400301003240301c00c0ca00b02640c02d508512081c0804981c00960404050123541061100007080002d5038080098500c001e00703494960026070300c44d4000a410600d280c1400e9012030b00384100c4200e450040b94000c01c9801c00c44c00940c2030000001c01e00095a01503000d440500c0c65641d1213a8840c0020b0340c3d2100b40d000c2c000d0080c0e021003103d1080303e2044c800380c15034904c1450701041110300343c080300104074600610034500003201c90900a90310000c00032811005420300301480907503c1c540015045082002903c0d0505803520101410410380ca04400169284a2402d8602d8915400e03c0801003000315160356803c03a034120916607a2508142c07152144420703560300e01d003100b0108880c80280c238a1140d01e0035240302c0c100c1c0200d0b02a101b07004c0d40312081180e0021 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 885923866 1250 885922616 885922621
    0x19051204060f1a09040b090a0206041d10030c090915092114030606031015080a0501140f010c05032704060e10141f120501050906011d041b0503 63
    0x48003c844600014038424410100102001c0c0c03038403100254001e8100c445a4000c0d96040d00507410180d0490000b54070640004011880c0c1c0e40c6c10480040d0031001c5e48130301299a031500c4281e500d9030500c0c0005054580300080401c5082100d0b084440303024810722a030410041407090441c01c3d074024480441d01c454010310064180c0d000c0b070405503101101c40c80c06140d80081e04003012402d00c0301800c0d042c041d40307000000486050307404448a0040501c0c0603940e40c241103850005085d05800d03115060a0f41c00c140002812001506010b00c0d20600203291811102500005564000503010708645a002c18082c503656004e090481e200792100755407210106800010400c0304951250b00001211000402800034444130f8a0450040d190192050101d05101c040040d10592050f40000865042c1d00000907549511080c0c40c0d200d518030050500090340c0b5101040905134084a0441c00503902e0407016035080c141d108030030704400340904001900044610740c0d1001054030000740b008640c0000a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 885925116 1250 885923866 885923891
    0x10f02071a0a052202060f0f0d0c021522020a06030e1005100303230f070203010f1109040f0609090b07020f07140d08090306010f1e05061905120406 65
    0x40700d6502800d88802008a850002c0b0840c101070744100346501c000840440d000c0c21526000200d40c4d80c0c82c0c000010070b071a60948442d84000e944640144480d160401c09191107650001507001408078048580800b81c0d540d170320210242c00384001c0411280c040b114190805602c0b40c0c00944042c0106036004121407019100c440d01e4040034091103610a4540303420806541005c1c2c00c1e003002d074ce80c50300d80a098001d000c0c9529514840880d0400340b002400115112011450300040000740d100f50000d0000d03180742c29001c4d0480d06003001d514032000041050310854580b81c1e21501c07000c0751005002852544680598040301e20a0400f1202d0900720360500150540400081d124a680c100003414400c0c00c001d48000442501803034039000e42124000c002c02c1105000991343c4206002d401c89040390381d00d091100405c0f9080c03041d124408907202001050000d400c001c1da081d501e001e0881e030f182c610a12039030520b54031002149010400140040030442c101c1000c80360280c1e002d050080385010f030111 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 885926366 1250 885925116 885925163
    0x60f0602120d022811152208121005010801091a01120f05010807030b0f0c16020d14060a06170712110d03050903060604020a0c0b18121305010c031d03010f0207 70
    0x50412488a2204001e01d0001c4021f841802c070450b004052804d407840c1c03030b204006010f001c2c0c803c0780d0005001e0408c1401506d02d0750369005c03074201340d0315000540d07030b11103181003268181ca403481c490f0303c049000e044a80d4000c10b500c0d00248504000010b5602c5000202000c5540a070410040c6d504040d4040041c81424511550000181c420200003414103414800382403050740740030700000b0401c600c0c43c410365692541140d42160040303240c0071000c1e10f15640c00d0b00e600e030841c1c1000720645000c1002c80e14000004500c1040707d1407900801d281805c100a1418000c00790f881129246459200408152500d01e4210b490520a0b10b0385030310381201d241010300300540105494051441445041d60031503221140500c40760700038410030182c3d107904242c07010380444901c0a030002e2060024880e003809508004084076030941202c0010030b512540111600c000e01003000d0001048c1c06c03a034604511600c5030103e03480b8001030000400e4400c61903203c1c03e90300322500586e804648000b80020380119079 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 885927616 1250 885926366 885926383
    0x607060e070510090905060406120b061302040602070302210f0a0c05060306061210170c03160602150a060906032f0913050102090d06060f0602120d022811 68
    0x8945401d81600384a9000301341d00001d00c105d2060649803000318920340c646a1009000e4000100110100741c114142010300c08000c0d600d181c05880e10400d0b40601741098400c0d034080d41ea0640c05424464615000c0084074072a1320840e150101004040007140501089040c8099a400b00a0480c5007102d0505402660807a804580500d41c20010030442d0b60f240012102e94141e0102544010303107424582000709a80394114a9882c09408000703d50400002000e000200084084500642c001610b210700820144900c50242e0301c5020020748610700c070000d8a82c4006110380c0014003580c3c520180040e50b109a101395820744599410004040001e440d000d2520504000c1540da50325680205000e60740080060000d04001c0c171900c03040120a4044072915440105400c900100c107040c21002000244112502d12089210010751180003050710101c604106110784d04085042449401030342c080c0d0150030318020202c0021400314008401c0c4550344004e59250304d01d5820003e11207140040e0b0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 885928866 1250 885927616 885927619
    0xd080c060f010e0718120f05061f091406010804020112060e04121e11070f0306020d150602060c0904111201090627020c01020403080d0b03060f04020d0605090304050607060e0705 78
    0x1842d0500c8400c5403100480d0080340c07501c00c950898040c80e820011fa0380385d8007031801000d601130007043c420074039100460002403d019114030784103203075a006030004980c03a0f0306612160f83c1880d400540d40750700880c2a00d50290040c1003001c0c2c141c403510f000008556042e00a0940e4446c0d5100b88000d020b44d40350b200d9800062400c041245250100000a0841d1070070920760402468900841d2103c5040c032101004010003c03140f50083c2d16031818002940000325110703043d52915503181da41010000740401207a2076500a0002a10b40e416100706640c080301c5025007180d11013805042e44100d950040c031001c0d60040076800d8950401c145081502d44070760042c00342d070341d0702180026501c6100a0085071041107141c0140e5035100d505400d8068000c9a002806000c0301007094820781c0c50035005106030240c214240c6503265100ca54141c00d402c2c054034042d42112400d0024000608168012a00800501c00f108d0031700e66a040022140d0740400c004881007a120381c5c05031300d085420030202000e004d0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 885930116 1250 885928866 885928877
    0xf060403080421030219020103020c100e010e070609060c0812040f03270e1f0303050a030c2105040201030605190303081b0a120225110109080c0d080c060f010e07 71
    0x4551301d00a540e06100850411040d1040000000b1a030080d811240c1030340035041a6048818121240c0c002000101503005031542031000c0200d00303e0002c0340c000107481a60710f40340640d034288038048903c1075828408544a0604000c078201e01d44a0303030710306407007188281030850100d056450024000f900303060088581e040820044000d180050840b40151004840c40002d10395032050703404c01d001a00107000100b98010301d004070605601c85d0050001c80074a44050000710880c00c421150a0001c0c18106a03a07a108002004840c4443d00010781041c0145004640f40c2d858900003100c0f5000c610a40800340800c0303204004054200242c5a44a42445c644840c000e4240c240c6c504284150607400041000c422428002501d0950548203460380b9000e0509444622445d030018601c06898140d900c0a04541b640d0b01c150311620700c103019904100c0c090030070300da8413000703000f85101e14500031909041c0a11542c01401ea080010300e01c503c200303070401e82013545441a20b440740a00039041c40208503 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 885931366 1250 885930116 885930179
    0x5011101060503071502010f1409160e0606072a1a070503030c03070c0c06020d08060f01210609020d050a0b0607051c2f0c04090b150f0604030804 64
    0x343d020a00700c0c100d600079407000c0501c8000342d500303d004002c143d181c501c4461601d0342c80014a40c0d0890080d228025031001ca84264100000003081c45e6100d00c110782000d41401e0000d111070514178050400c0e54421101441c0200b0b5441c1c04039401510b0f0b41c440340016640840030007a12100328460301c80040e008111a141c0710664443c41c1e109d00c4000d00301d0300c10030000004107207018800c100c4c3c268855003185013903c1980c0c48900094071403c07904002030008981401095544c50440c408480d551016115842c400c2c981402c6010300c051071030840f120300303552907000281800040c001032140c440c1c4100006102d18004210608641d0428201400b48000b8030174400095400640b00c05480c0c80c9900360284083c2c1c1420846195011210300003a103042607a40f541c80c0124800c402452880304019644850014410b0008595150501038400c034180c0700818130044891407996401c050103091921140640f4001c109140d00c542d0040f222a90700180c10084007948080007408810342035102c41190 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 885932616 1250 885931366 885931369
    0x180a0504021c091b1d06010905010e2206030f060e0a080720040e0109060506010503070210180c0303121410060302160c060f0206090a05073804050111010605 69
    0x106008400309000f940d80070000c0900103c803c41c030a41c844000c95401646803070b11415020100f460003d0b05683e42d040001c64403a42c00350000000340d450694030b42000100034404c2050103864040c031840a0300c101240c041c0c3d40c0046010b140042c600850018140049034034252040301c03d07a05403192590000041d100c0003840c000202c41a06410902d2402c00b045c0004c44988a86c4500c9440f507401450440d1000b142038041d08841e10580c020b000400c0643d60380c02c0191024481201c0d2240181c014522a641e401d9a581c81025500034030030b050141c2085954507134500f202140c000744c020603404048441c20244900803040303504030780f008890290400d001205404000d60040344249074000c21a54402c140c0701c1c0303c50702041d0704807121010781a0341d0710010b0175184610300c6490040c09040009018500c00003507020015500c1002012418600714041a150480342d400001b0188040c0080321004101f441d85d103403050845545695951800002400c406803100c54104164140641088503 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 885933866 1250 885932616 885932647
    0x5070f080f06061605010209040212010512011a120f0f010203041b060f0809191b0603050f0f0c130602011505040b0901030303200c0a020f010810030f030311180a050402 74
    0x90025070b84c094107000d201c43c40c0a5019029414503190454408610107609001c03007203085040b6582070f12a018100c1040c00100c1c01d884440310004d04200c5d9442005900f8103000343c240b02408100030a0301c0400010894031820003c03090104075650b0340220a00c0203000000b1094002c4403078085c5a031040d075182140c0a440c00c40c800e070b5804240441d10300051040e01d0180040d0801d08810700c09025100202d162004000c91416100c011461348154086040341c003a04ca803a028482c405001c000696542c1c807400d003883c5008003c050400001d2140303021201c004040d6401820241c2c00108042540003203110400300c2c55803159225a007402542002d58030f1381038506041da60103140204041c0c088640c030725459403551640f034404110001e400f50b800d2401054140b00036208440c110720400b801c0c0011a0f05907402d45030f000d00008070150070000a000c10a01c21900384c400d013004107030580180d074503a03051380001c4c1400d0100015075080320000d2500014000180100310f800f1800e004007030022011 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 885935116 1250 885933866 885933877
    0x506011d0106050a12180b070201110d021305060a02061509010e04060f0b060f040801050a110f0304020310020a021e0723040b06130f0504051e150405070f080f0606 72
    0x10f00030300041d01c180c0c5622a00310402d5422041c582806a181d0400b01000d10700c02404060300c010300840c000c540054810b00640c80c0c40d1a0f81801e5604152070300c40020000d40c881844450304901100700020982c9909001c0c004200d1203802034030b51894020740a1250078500c401c030901c03509840005001e050044884540c00540100000174540399000000d4000d160060310300f0351021021404100c0ca0b600800284155210480240010307116200b46009841501d0086501107c0c140214000c0c4d200207005158014001003c41d103c2c7c04100c12468120b0317001c41c4144006070400c00d100042d40321100c10b00c540c0b04500e0801801060729001c400c138690101d508001d2807140c1241c0c59201a40e48541240c0048000140b45641e902945071105100308420b104003110384500d41000038041ca0107120748ae202c0e02d1007015001c01c0b03031020105024003840040010101014100a043c0d040d100e034812540f04101a440e110000d801200c005803030340c000140140b010a440404001281d20b407542a02d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 885936366 1250 885935116 885935129
    0xf010e06090f090c060417070801020403080f2101140306160e0f010e040c0801081b10080402190b0c0c19060513030b150f010503072118050a0506011d01 67
    0xc543d0302e4000c2e480d400c1c0340000c4042ea0b84104085030100f601c15585103651040141c510441c2c005580d10402c160a0b4040c601c405000e810080c0071685040f01030a00819841e400030301c1c01001034001102d8516442000c0c0c00c0000005411025603409080800c80355402541e031000a200a05103004e0052201c1381d031002c3d1a00440c401d110044659000da942d9602081300148140311080c03007040000d000c16024407443c2200d04c40c41802405ea0148054560b10a0b60040e2210f008044103c2c2e05607010031000d0002c0341c118030042e02c1c480c1501e040f03402041c06401c0d40d80c266540e400c01410910301d421244803c0e80d20460000810710750868900c03007588c080714405e00700540c440d50200c1c41107000c07680075403020701303540b10748004c0202c0d203950004039000c130100c101c0303e03140741701c18070001103609000c21141130300480e510b070301c000380b44401d18a0985e0b61501c10f035401080d03168100000503070000f429a0102c440350310908041042120a02200707024004030000300c0d51f203201031403000c8c2c0052010712406 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 885937616 1250 885936366 885936391
    0x7091b021f020c0c030f0c1c030804120504033005040b030112081c150f080606120f150a0506060306090a020708040f06020a020103050702030408030703030b041b080f010e0609 77
    0x1c500110f02448900e5041c400181a666000c520031540f9840718101020940318200c03202034004800740080b400d039003042d0156204c0c031940c0d0b0745680f016142d0104880c4c0c00c00f4040d0501c0000001401c6d003110b50061f4a40e02d912110f210711781502c0e001c107035412160910030701100740702c140041a000020f03641100c0205011040b04411818034141512403424048070107038408588070440d01b1580c1088010200256810300d109644070051001c078005800b40385080e4010314085000f900d003102e070700c8260003104030954403080b880d40203013440e2107450760348803c07a208560100300014509201d840e03882942543c10b42d00c0c51518000141000764001c1c00132100d1540030a4800a0141080a4030b0182c0100c1c40d4404c00036449040c06991341031a402c0c100d0010f4288000182424804000c0d03408460801c1c1c02107043c80c08036541540505403446440e5000341c3d6540c096060603903883d1961002541c582c46a010500f4440f405031071066050700041034801e140030500825866444003140d00c40d4a40b0b068 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 885938866 1250 885937616 885937627
    0x409020a03140610150e0f011103031609090b1005031e041a0a09110f0102010f1103090d020109050c06070f0501050412090f0f151107091b021f02 64
    0x129940901d0300090078022105015101186002980900904038500028802580c40c4c40e02a11100c210103500c3c002034112000140a0400d04003107080e455050401d440c01400e50380f842469500300300c603042c220000e801c00c40c0100581015180028000005082c0600610400450020700610306100100030b000000210782180b88042042c0780c50803004200300d24105414035440d203445610000b0803185607400030030080990f0348501e1040542c05a8500c034074001090401c0422551841b42c0d9055540b555030084030142c032889046a042c95400c01d5035281d0419000d500c0c03a101250015034103580c982003a810200b440010642c000c0d0b035045461503591070051030100d6441c0c9a150000740700e50300b880240700070404c440201c044044025510138014a644400d6512000b0301c0344246100410208010322605415031242c80d0550300c1410209504180c9103016031a00c10b01e540103034251642ca07001c401c42450004200c01d5640602d200070038101d250080210403c2c040700d40a080b000b41e00042 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 885940116 1250 885938866 885938869
    0x12050d2f2203030201090b0105120d0318020301090c03050c060f090f040609090506070305090c090c0a020c0907090315020a050901030902030f0d090e0106080c120601021507021509070b09040902 85
    0x1d007a01c019014080429200d40c0d0b82c9006130282c011298200c901c0c841160021038582070882c0000c000880d52001803008207403442051740141509014410581200c414040c00f6807402d0040e00071180c801c00c041c2c2d0a6900d542001400c0005064030b00f8070401c01003106040803c2d030030302901c44078601200d01c1c99100300031800007001809a944030161640c10b0025031024030001081c803034810509074806204a5580c0c4c00c002c0d86647d81026816032192660f00400d0f070013641c40020b807000e46400d004a031a0010650001005031804541050010720041e0301401002403502c1002c500410101e0150300704003001c14041d1185c0a20103c90b0304151f500d8080c1c2c810356404001c21803461103000b00707907081358501e82d02c01000859180030707074210110031100008080380f141c0005031042d400c100c005810441802c54850210102904190440c8030310214001c2c088105d943c80b0340038185e550000c060080048000d81c110010080241030075810480742000310013200c500700c87c01900e04590018054803140b0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 885941366 1250 885940116 885940147
    0x604150b061306050a020706090501210207050118170a0e0d02010309060204090b0f0604050f010c110a0b12060a030503031f08030a052101030f02040f0912050d2f 71
    0x19000e0071140030010b40011015003041c0202600c4400d5400d80c0c000b00c0d20b51000b0741d140205846030740e00040150183c600b50800020070070404803464000540f07003a00c43c1d103809081d41c0b00e02e00700407040781c1c0f1340002130308000340b040540303801c1d8514004c06030920040140c040c2c1009440010700e80030f010290600b10841e0320950204241c1503004004649440c0c548810400508400610764020349000501150514210f0f081e1012114014041e940d83c444c44801107030030180500c41101d800d2080c0e03000c0b2006a0b075030510300300981004259079403a102c103501c01c0f0080b10303c044e20380d074011840da40050003c2403010080380d030b0001b0700c50000d058007020114048a440d01580c01880355000200d002540c040c1d1142c010252641e040c070006180d10460501125412402e201c01842506894407070300040c105a0030a800c420005c400c0000c0510030398503440010055a0410000200001024045000c10f44a54820b501c085a014071042046043c0080400281d01c8240c40078031010070640b034085e1148 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 885942616 1250 885941366 885941377
    0x6340503190c110c0306011802090d170901031d0a0813080708030a0f0809030426030d0501080d0504120f0c12050d08070c1a090c0a080c120604150b06 66
    0x10008200e110b40481c1e008285000c21240c11196005201c44074030341d4900080c0243c140c0d0410140c150401003070f00807000084d40201c590700c1d08003101101c10070101d08411040811401d50301201c6680d0600400014101c400b414a5001086038401c1d404203520f0f0006403402255511080e810b64074040340c00714440e404c40350750207080700e44500100451400303c0030015045600090311000115a0702c12010341d00304100f03e4000e081540248020080c41c0000e000b124024504850041a888641c444403030642c0d0018000c00c034034035200c1c00100700065081125800e954000c1c80c20b01e081504009100031100210800174012003482040e034001e1100c615000402058070b0303002221144014980103854403820110100400da00000141c05203018848600c1d00301d03484240c001c1c0c8041c0300718500c20341e000007811083d828400d0201c03070300381c80c0c82d9003a600d0041c02d0010002c01001c048402000f0300b0f1001c2036002015504858203020003d003450456413800b000100011130400d0030000861814000d1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 885943866 1250 885942616 885942661
    0x90f17040f1d060306070c1209032f03030f0405090405010b0303040303111b010e1e04052e0f120f0b1006020c09010513020a0e060a0206340503 63
    0x100380c00581400c21600110009100c021a03600c1942c40d90f041544429017140c10102080b4100341d2840024005c80f01400c1401183c2080c6d0812512038880100700300c41e0f20013141c82000034207026503070240350049a10749200110f004600d0080c040410034180d001d030344199030180c40a4000308003001402e420420301240d001d41100e03101d80c0e42e42001003114600d410f5a001d2400388144621115003145014405050180c40d00521401510144080146141c03a10712107540344002c200311139620b034010140200014244003443c1c064610302000c5955851400c6100e45460403400c0100c88810f00c41042210106409030341d00301c03401e040011221001960003030038980018100a030741214400c160b01610166800c48458005101c28803440d40380070b0084580c40310f114815001000c80680041c0812505403904c102442070070004104290061030310b40b000340c0c101c4410040e10725a904410034500946031482241001c03054065044a0b80d40e001c80c004000d0004006849200505d0101011000c0c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 885945116 1250 885943866 885943889
    0x20307030f03030902090f04050316060b0d21051c0e0a05060f01090c081b0c0f030d0c181a0703170f0a0b01020a0507121403070b19090f1704 62
    0x21494010010710214100700e119200305001f15001d80044407650348582c0c0d1000013145400300400040d201c00c0d4005e0004c0f24a11b880e014140da003603c42c00003d41c2ca2074855180390b40000c01400b00c081d0660b01040c1c4035010020184102080840d440c144202d0820000b14005441040ca440d03590410350040000390041c826801440a000c000c521500e04980302c000381048207441d4808200c800310402d40301e2042c402d8000308c80000e142c12020041075107201d041c2c02c0710520380107241d415003150400d0710152001a5101812a5000d4010058407a184d080310104440c0034241180040d07804484802c861074201c001c1270540815005402e10181760b0003580c0c0300490342c0740c0f4880c1454002d4007104d030304420070f003826000060355000168001517280d0000282ca0094144124400242c1561000fa50141c2c101e114000e041c8d20144010017505000380c580d07c2582c5401d141a06007148030004540e402843c181012002ca0b980f0081700c01120346c0711081c072071904040400c01030540100d4000004002 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 885946366 1250 885945116 885945143
    0x50304060909140103080307140d0608030d05070e0325050a32060d15120c0f0f031208090f0d0c06110301050f060a03110a0918050c0a0c02030703 64
    0x680111a9104403840703910140a0848400b8552140f01c10a100c010406c201c10300200760050b008007500c900d10072080b024241088a68180c1101352803656201c0d001d560000286a1201e031030500030b403a8040320354201394024441440120380d03903041440d41480c0c4601020094040c0c800d00a07001401014002c06001c049600c034126a40000a003080158500500190644180840b080d4503122840d00500315814a10000350380c001820f02141c0351800a40d841d2000f003105400c070000f60054500429844441c0c074200b28180000c00100d411040941501e084204002085041c246540144510300441291182b00fa03c2c2d2402010395411001d600030b0400c19440c80d0390081d50382c54581c0c09480300380004509501701a903070748002c0c0034054104104100c1602e240c1401d40017818030048614000650711800e03414107425801a0200c140003030319640007080040c074486070302c040c400035000c01040729042c09a41c2c074420b8480e9800920034059260120010366400340540c1e0300460f00150782da003220 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 885947616 1250 885946366 885946379
    0x4080702090702071a03010623030a090501090803010b040f0e06130905150a0e1009020607030509012a1a13020f150c030309070f0806011211030109030906030b0627030a050304 77
    0x246c10034024a000201c850315511004000e010001600c07a41c404c444502d161940010600545100c4006844943d02d400300c240008500000a41c0241450091941c0b61814001c55407011805680148040300b288018029035550740c540e078804242c85507200140314205440c0960604552101107030f034105512042140079242c5801c104124010380c0145c90340e852100d51540c0031a1982e00c4043d410034002d00010300000c0c09a00100003003641410262001c1040c01204031500710302c0c40100084c0c1444013030110401181e00c900d0a850444840207071114038041c2e4041442100b0228068401c4003015288415512000f10b1500710f007011081140ea0b5840c0c008030f1940c0d82c0d00544104035030341f00d441400913030144440c0d44041514001350180c038141c0d00e05904a40905c426001c03d442e0180601021400780d5400d00c203901d03512344652102e0309624079050001e13007100c0e1241c0027907019141c00c0101c0c807600c400600701c0c0b504481291a00c02c07003481c00900400c1c582040b2074001080c0d48400500810903 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 885948866 1250 885947616 885947669
    0x309070909060f0f2a080612120c1c2a020a08011404020f010908061f0906030f020108010b040b09121e07171c051b1006031401050408070209070207 65
    0x48149000038951245038a40460460761180d0040000401b880040b403040d20f0048400380c1b8280c080002c0360309881d68945011450380c41100095050341c01402820a009001031003031241a04504090080500c8403144000c1100b44041041004c0c410010724000c6507542040080500b22002c020803410b0100000d452140f001550142d1040c07000c8070051003698410151142a250390b0000b030021916221500303546c121650120b402080c3c000c120200d101c3c9014802d4000650250b4803078150410140009000c012040c1c2091000740400c00003441518024012034003402c000381c54035040c41010440381801e2040c10380c420321042e29130407152680c82c9000180c200c107a03482c0d00025110508425044d079500c0c0c41c03e80300564110100384030052001e000d88064039504603e00341c22000304a810080300d081c03103001402c0190395944d600c0107000388190210600641440d10000308007900700b079290b04959010f071600c0248520195000214524800e000000c02403c2c0c218103081e9a0b0155040c0441 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 885950116 1250 885948866 885948881
    0x60b0307080c1e041d13022d030d05041706100b090d0b1315150e15090405100f061410120c030203151906080a0e03180301060501050309070909060f0f 66
    0xa040d01e41c0c000c14606046c00e40020b1260354001c0500c0d40c14203203025484030034030103510038684140903407203050080c2d28144400544203003035640315076890f0700b42095068030030300501c03268403168400c00030000e004042502070005e13509610032075900c801c07000d4002040060492401406001d807801444003030402e290600e8901846007915818000b024602d440461b0000f41401074032610b000c80401c02d0030101012150850101064607444441240101c1c0b4400c1d025a81204c095100d159600c1e01c448047c07041d20401b101242c814419245012110700e100c04650280a210328281d11900c0c036a6405200a40101038826009202281d1503001c007400a40044400328010b600030380549486144c15920207c410410741440c0da8240d040c40e108036182e540051045040d44d5403601403007041c910030005408520200c14003403010550b084145800d655150b4811410700a0510074060300200105050081e41c89030880040c5009040c2040805010601410a8041d2034546135020344d9409030818813 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 885951366 1250 885950116 885950159
    0x306021804110a0e09130219050301090308220803011a04031b0e0f3d090605030f03131a1c14090304120602130504140901060b0307080c1e04 62
    0xd03440382e80f04c080c000c0701c0304200c03100583c180c00e2252490061070312080b103140300700300300f2914081603031902c01107170840c1c00011060740801d41070b07410404900c03065600400f600401805041100b0079654400040b40018040c01510080d0030000701c261030012001e44004540210560710041800400904d8018a5006030a02041600001040404800507660041d4030480c084e00100c000703074a80200641d07010403c10030260408080304c049210b05840718000e8135040750000b810501d0071080500c4c002d003000d1642ea075a001804070b070304050f0909200c241110751180105103803d01c1450110898403800041c0a201e2909460500ca1298203a00283c03c0010784841160a03407100403420740c0d02c0c0158401c0503461003800491000041643d00605001038500c40030020b61a02c8030005001d03290802c00f03564100350321101f00820b803442405039200500342c0140d480c0c610b0820840c000e0041c1d00041c03104190500006803421445440e07003e204403090f44a0020341c8550f10f030880c03800d00d07000124405 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 885952616 1250 885951366 885951377
    0x280b1008131b080606300a0204061502011d030702091005090406020c21030115090306050106021f020307141b0106080606030d050f0306040b0a09020301030b070f02160306021804110a 80
    0x21030500b800200d0100000d40b801305039400c10290703040310601e0602c005000301d070780c05076407d03840040e2280d010300390103010391000040d07261900110003800c480240c4081541d644141240b002e41c9440401190708039074050b80e250100340c0c2d40400000020310540c0c400c44d00308036003000704000c4c0102c2e503001e00000020ba200f81c8000c103100d42482000c2c104543c03c80310010804000400031007412958040d61f1001c541442c20701b459490302c5007012980268411405030304221001e03485d0303030070a90001c1344200b4503410845c254205142d000f81403004881c098800210005080f107500303000c0c651318031140c1e01554000e1140c1603c0741c0c0500c0d1119420b681c82c1c0c2c00303480303000c14001d43d003030190043c1c44a0240300524242507038dd031001004090310300030b000140c202d4450358020501040900081d80a94000c2510003207500b80000c005000c811012804000c41d0040120030003d0a0f88480442c1180d810040c0903031510300803c1c1c1600500c03e901503183d80f00b4034108015541d0704103e009418040c9168450 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 885953866 1250 885952616 885952621
    0x304080417060f130b181906050615130e2203031a030106030b06060a0903020d0b01050906040504033905070513021303031b0b280b1008131b0806 64
    0xf641d41c1644880028050100b0400185030310906c01d60b201d00c0c11b00d02c00121409008a82c140c3c4030040b80701181516000d88440802000f07041c0513014007650b400011503940303084a1100f031124444441d00890414103c8000031039186001c100200c20010202903c284d4801d406181c0500181402e80c50744c056041d254010b08210311b03061103040e04a9410100102c03003903903a1010420154888544c403001d20071180c60120243e2034903040100014451550720109506003010811a544010407551049060a0030800060f6000046020307244489124520703100d40340003c2510042d0450301c0b502406c0c1020220b6041c45400194181103d03419240d112842e5600804c50059209240d0b8581001c113080e0782c00c00c0028880c1d4038083d10862840a0034580d00d00581c1d0303031000d14100b61148455404018256486103450f0803441c40b082210b071200b0403810b5005004500f49288c00300710340c81880034460003d21001c090241408031503901416205091040428980a0305040d001e16255803154600 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 885955116 1250 885953866 885953881
    0x7030f05090d030311070614180307020607060902040e100b010e0402041d041403030703020d0e010608100e0a05060115110619020a110604080901032f0304080417060f 73
    0x8071110361401900c000070300380341d5803001d0713028003210542003031918000c20140c0c0100d6054440e80401c140a14550f4803613080a10040e07140040040b04045543c1003006440e005035106000c0768201603100b80003082c8010319000080041c035209105010b140100301241042d1000d5078000b4070800d0742622a0350b46011001c00b4002280218082c81c500c4011601e2402c042442b40720f401035105114044c440a82c903030703030315072242140c0081d038820000c20340214101d44ea42d0b105000310030304090765a00800c01c01d85000442d9503513240800c01c20f502650313038140002002c1000c1c0001035600b90008211400ca50f5035160303130f51000e4810301781800002c04800c0610a50b40012548a02510b640003061707076050b801e6040300c0c0c0254020f231444d00c103001424114107071385a000d01c107480c480c3e40610314960701c510035a0005030550703a5001642010406046007107203103410380c1c0302002c80003042d80891a1a503840e0f2411903164802e60304071822a00803800210121100040d4140c4200d508001010035900d0328032 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 885956366 1250 885955116 885955127
    0x1f080303100e090d08061309030206151906080a060503010e10060b03010311010f0314040b181203011a2b1d06070c031b031d0a08030f0c010f0f0207030f 67
    0x1282d441c50f981100f00301c2286644140381c840d41208004005c81c20040108078040101d0341d0a880840260b08840d0402c0304007584c40c207203020031801c2515440c02d502041408080c03a00c002c1c4c0940024019440042080c600540c0e01c12005020050001c00c94001d030b1584c0d5a94a050050107600b00c107003080c0001c681c0042d04030580f030490f68410703050405190350f84c006551a80204900c4410140d50f1aa03480c82ca0903442025805940500346100c1603003030848000300071101142c04600702d5071060411300c1d42004400202d9044980e00c286584441e46121000c0071603201c0e410052a07920241e0350070304144920f0050300712007490103100401c0440184850b800b0030040020b4040701c1074002c0c200007906140100000c00582d0720070b2800c0d421031080c1005020030525150015800201c11610204845225042c000741074601190811007aa140440990790784c842c0c0140740001110100ba41d00703452030250420b00550418020901010100c52204c00003500201d009400084110a0500c138140c080c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 885957616 1250 885956366 885956371
    0x803070b06031c050d1a0d03081e0610050c100203010f170a020105030112150f0207020f0405010b19110105070e01180b4f0605120f1f080303100e 64
    0x54844c103082044403841d540042c218020307601c2d0203644405454201d5550380e407186e903030f0510a4032015561b00340420000d480d01d8283c540c1c2d00a24500006128080c0d54042c0b20591905413481d00c20782d00c942c80c20750a42040300401d15812040d001000202d950300c0300c0070783c03002501c002600080b0803c01041d15540c2c0c0e088004c0010b80420701c104010310490640420101440d800b03084052250968200f0b01401c0310000c075180f0200c154003180c43c40461078242da40c0c10b096402202c0600c1954100300f00002c080c4212940f407032182ca00e480810700e02c0c40c015401501c00c601030000030084d0b481e001002409100c4652004d41c0000da84a044140301064100010103603003080850b10300b80b9039060181594010740a018110140c40b141e8000e00b030f0499014001001c034040c142030304480c0100c6004500c4085690006410f2000c148406481412107021140e40000240c90010302603c85003c66502c100c0300c40080c504482c909a0045540b5100000441c0200005010240005c0c0d5500074091007000a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 885958866 1250 885957616 885957673
    0x60213050907030c140901050724110c0c01360306060905090a030f050c0102071a09030403080d150503030a030c140f071214030103050609070e07080601080903040803070b0603 77
    0xe248107440105c130702c001e086d0448060412a2800000d13403190035010120461101009400c0640d41d0071b150320718040c1c041120b11a03c280c90511a40700800e07502d480c0300e821080c2c1002900040c107142030391011080d44220088459204012644514440b400c10040c001641c0c41410080c001034042080d1194903c02c159001c040c00c1c0c1c2d40a281e070100d50654005c01d82c5010014203204880d466602840245000c2d88078170185810400e00740c00000d500c060040614029400600042021031b003044112140ca25000c40b0004e41000506034048036039821b40c01c805e03058440401d58080550301a40180d10118050701d4810440d000c1e8007082d5000d206d00a100c1e001c4000c14000940001c2c403880441c8048540750925006404002e00c412449410907441510785500500a02143c42d80038800c40b00070340302c203000700e400700c1c6807015010f006007201802c09410040024001100c0706401d10030340d03000d00208000d0700e50b5040721f0f05110410321000d41d04c007407190003500c02c108091a56007062079510401d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 885960116 1250 885958866 885958877
    0x8060d0515070908010e072102130b0414072607050f0f0408030c030a0f020d0518030a080a0c030e1c15060302102c0a090c030207060213050907030c 65
    0x15060a0790184401410200c28884101c0b00070035440004c1c041d226044248600901c6140d1402c04040e031407841484070090f00d4030300d0719562800350f218010f8030300c400481c8940c081045601403011400070403401a00e0001c028070801403002c81035100c2403107206c140d0340a80380c1181424071303481c401c66514256482408100e0400421303448662550280c8070081016020a08090703030b502b0324074290b03804200d0f5440150400100280301582060460b4403404030341c402040048a40340025002e03200b4440960100c20210381002c815640821420100030713071102c01036031241904c840280c101d071a00f1a0443c081004a0a01407a5042c5201f10810100760142411640d05054840545040d0402c40000300907440358008400342e12446c0c0d01040c1c030f600716038400408801d400d90840d514070307591480c1c05c4025144c503c00d02d500e580b07007007034101900d00700c0384001100380c02440164020b2094601c000d1019001003501c4001081d041c0221040360340035220543e407a41c0e16481101160100f00d2600c0200d035 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 885961366 1250 885960116 885960133
    0x10b0a021c0309300c0c030210050405090906070e01030b0f030a060230070e01140301120317060d020603070207180204030201090e0f040605040c0e0f1815060f0a0f09090308060d05 79
    0xc0c402d0b121000c844d401b13918038002150b1a034012071003102c00b841d64034010034000030701004030b400c050400c9640110508003500250070310401c0284520b400c0003000d410142c032000320058560f1820110340745494010708a488442d0103192401c0030390442c20340080d03041090510034003410009401c00064540307018442d50140d441b04000e8075012644082c2e541000010040302d2a0564007000941c041c1c03080b15000c071103800503880c0082104017055500500313100c210b0140070140c5c0326141c031090a240c0c11140251281d5480c03e08a00d0150035610914540c590298410b858141c41e5004105881c000e0341c40080c0b19454148074101064181e070240b107208182800a0042100d0f40d1109070001d1240d0f00e0420a03a642d001003030324185c01030303a18a94450140050000e9481003e400702c00e4071550740003808244d0044c03082c85802090003080c2500480c08242d84968996032000280003a0402400d802001a1a603100b1801442c550200704c01007840c01022400d2850268142c01134031703621100502c2c1d1039 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 885962616 1250 885961366 885961463
    0x1020a09061407050705040f0612031107090b240d15090e060103080f0901030f0c1d01020c0109180e010e280803041212020301080115050402040806010b0a021c0309 72
    0x48c1040c1c000d030004c40741d86600100c0e07002c00d407a40c140716244c000e5590758001c00303e400b2494180591503000324241d51810038400c0c981e0729601c1100700c0020608401502d41022802002d9007485803914502d2540c2c03601e840390a841c0b4181c0f030340400f586c040481c01c02c170100e240e8054549e0303041c0a000180c240b88040c0b1003040c20841000c010084040c0602d00820119602290a01074408801452012440000c0301260303007081d14811041c0781000348010224001d020002030940c0c41c00c1d0042222078a80641000c409203010380280512020400c02000400d40c0c4140b002e8503560440c000400d01c2c0d6050580c40310604044502c50142c941100c05c442c9140c4490343c400300100f003000044024080c0d003c107840c00c03043d4644050b60090440c1400442c02c181c0d120041000100d0503000705201d5481440140401400021082e0548407071450740d6566000341034042e1301e0403600c410403090441c0303d0003440708410b078142c04c50301155205204130100201e09a44945016400010004c40b0050401030b13030300c1c070 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 885963866 1250 885962616 885962621
    0x1b0601060e22060303110c010906120f230f0f01030203030a05160c0b03010924030609140610050a06030905060c03070c08040b03090607050304050606101101020a0906140705070504 79
    0x40c111144108494081040c00d02c0659619500941c00b20303000c001080100326050104103181034003440c0040d40c0e942064400782c19461480302070340c0c442d0744d1200420076001c46a4084814001c40c84601c00080039503020380341440c10216843d50610a101c00800c48800b1450002810780754010051400d02c2c0c400c1c030b400c5907641c200014140351488550b002e40c2c00f00c3c14000c50280034101c074406140e50380d030604c0442c909607000603450034500c0409403000c600110b11043c07a1400d0b2a07100d0404241c0705054101a41c4840b030748803414074540904c1d0103102811800b6650a01210000e8450b040f03034070b0741e47c00b09078102c82001d280a4801c2e001940001d0841055a0045600c20f20700d080601c1ea00d0000c1d20b51428540040d04091300750703000007060142d4440d0801c8415804105840c0191035850305a848940b14030001d804a8050054510081e15140c007039900700200310013a10085440c0d9504190051000305140b01e00c401180d0841c02403206c2c0e084600440d00344a42020042c46218905410b0000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 885965116 1250 885963866 885963889
    0x2006040605040c0e071d061305151e0304030905010806061b0106080706020609120c12030712180c0801050115080c130b030414010504030912050a171b0601060e 70
    0x3000420840089081c000e04c10741c1d01d020b00c92954900042051038040c1d207034002c224081c0c0c0741c8141014401c420140e44541d001c4c00640b603040c0c0c0c88900f47d580340e43d0018042d00440016840060035480c4001041513100c1c059403145000e42e48030b0840380c1d641c0d401550840420f4800d640c11180c05c109400494800c0176400454038404000020a00da55804442c28088542c00030001170300010140202c2800411080407034408000c5590f03e000460b5140e195034000d0318810040f0010080300040066010341314032140e44603202c5c4240022160000f10048448084004442070042c4a00216101300144607607810703520b0308159410042d04204090300d0148000f850301c00b041c0c901300b2601035440c15420f0302500501048030015200d041a290282507205104805d0449030b1424082202180e4440c4d000344c02c450200703080d187c41044a080140c1824181d60002d420200b00030150025a040000107255400c000c641101c120a581581180c488000384074000c0010044800302c501c03407510303289814 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 885966366 1250 885965116 885965123
    0x3020901270b03070f0210020c07050d030201020409140402010f1d04110f180a060e060f07081e0a0f0201021206090c04091e180b0c1c0e030a200604060504 68
    0x894190340e0b44207110749510884040000071488106034416036010070100c0c90b4140342560660402350300025550307480c801c9101d200d11415400d10518285070007907044a002e060011420711510060303052030202c0c91015201280003035620358079070441c40d21a203610000c007012112408951030040381008003511141c0050318009104125907422044500300a005a03400c0800a0109030415030400001c1855980024140300d030340010642c00e90f0f60541201c1501218001860b210801404c1c200b400380610080c003560101c0b02c0d454144c229562001415101328655148150b42d400d00f0012801c0c4c1c000c80481e2500b034840a03001c42c10900d13001500550081c42282254206035841070003005681c0100d02c881c2003d120b40000c0d500ba0117140c020040382c0002c4070114040e50700c00b80d483e003911110040c541c032285c1d0804604242c4484441c043c81c10b0b4610032134424003d400b228418544c682e0701020303061021401c2c1000a04084500c4c0e00d41120803042200a4046a03807103844102c05000c0080088 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 885967616 1250 885966366 885966437
    0x3040f0b070912140d1b150207060207062424020a080a0f0f1e0c0501020c0d02030d14010806010e04020d0c0308120702160b30041203020901 62
    0x104681068450200780a8000c80040209000f0f1315807450401c1680c102580c20016403880c0c803240741005441c01c680c0a9806441c41c80c0c04521700c00010028010340c00f00501c05800007070420140b0545401101e55084286803404500d51810034030007000c0803e114042040041e00104d061260000210380941c402900603503030440c0ca680d880c20030980c07180c020840407450401d0001da92950004500e2031581c1103050150791080e0254058940c1d01c0380030407003420031007100c1e600d0381084401c0d01a15101001142210302a0004130382c060344941000300c03094000c6141008a0042c500c001045a04880140024007080d07428400414102c9400800c10390301300a11440301400a850707001190021402a451162910000d080032040c0c941c001d0700c0202194890610001a00007894115080701c09000045965507048400000c0d5510040000da8180c880b80d82446072078590842e0707207481a840b904217040d41a40d041015000c0b03000301c40e1a01e0000f0464214444032041c0424001e6100f155a07114 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 885968866 1250 885967616 885967619
    0x61c0506031204030f0b070305060a1502070806070e0102010506030a0b13140706030c0806030c1f030f02121008032a10110d18080706051b19080c03040f0b0709 70
    0x51000543c081d5104540317488010b2501c1c0e00344904400000d401030507600d4180400d0400d08005010354005000c0c0480705101b0002031185140200869001800d0b0041581c5992400d001c01515200140707540394095401e15001500915011511030090b40c4c1c41490440c10fa100c200000405000c040e50071265104a01e020300b00000f02004031100824242d81c000c2222040c0f00740040c402e0401500c2580170b50300031101c0590561303d17024810100885110001144015000120054003408040540e041d10000e4520341d900d500b0a0540d00c140040d54030406207560314907180d035683c89121007640d9005035403c05501e44d0f69200c202402694002021100c0c5c0345203144041c0200c0d402101140f030301b01c2000078080c210201030b001d500b04140c2d02c0d1294405080d42500c80300020320030880000c00e801c2d52a03001640740c40c8140034055007520f5007a060303130319402512404c0039800c40980502000c0307180d9500003103604100c2c0d0100e070300c1103a0120f0001c0c039800d426950000c41110150108080c411003580 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 885970116 1250 885968866 885968893
    0x1d09070e22020a140c0a110105091905030f030309121605012d0c05121806130c30020f060f03040b010609080a1103070308031e06061c050603 62
    0x8908060340c5a101c0c006956030718242c0080c00740d4030700305070000302c1a01c00d100c4500310000100f0040c00c4250448203020395100c403400101c40c507200b100c10440d80651411402d100503413008447d4003d494064088828120b05000140d960b80000c07290340442d9800094140c01c55080c001c003130700110440038080307811441260b43e400d0035103221403002c146e41611800d02c5851840e20f03291903082c1c0341070f048040080c0014480d009000b031080358244d0b0801324841c40420508a0920145041100b425007520310604184210080058845400380c40511141c400402c01d01103030200408901d00e010a40c61401c2840304000c92000caa250083e6401910740c2c02020846c0c4900c00140110031608078900d641e454140f40500000c031068021004111700a40700380f186200010f00c07040c4483e04980285240021200001d1408106800091101801000b80309000740c80250300f60b0302156500c0403001c1c039550442481800e0040110711444110021031080c1190116408290407400103000c0d900c0b03c020504 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 885971223 1107 885970116 885970159
    0x14100606093615060201050705031005011209060509070305010f020723010204090218031507080c071b0b071a04020112110903100c1d09070e 62
    0x10b142480400855144180e210342d0001071091281215072042c10307500c0c0744242d0001d1360810700070691582c020310a0b00c0c030078003507181c40750f00c0c80385400011110740d0142e49110003540d550b01406030124085005080c030035001e0710003c2c00001e04d585841030844031220072540d030151051069034009451215565107140c04000651203a006d10301007540240308a03804020100c0c400601284180c2002c1240d482180d800c038141d07007050f00200040e42c3c90040803541c0b14000703a00680004d180038550f00180811600440c440c450030311000d8940352425140b50820440c0d201c0c0480d40c407007003000190041000b00c2c080d04100c3c0040c10b05500191002021600c5940c8450301e50b84280014800d1038180da07500a0024100c80303032150422613140050401603400c5001412850402100c0c258403540d0006568018200600070745e20524103c0e007402c0f0501c095680000d10740544d101d00040700 = true := by decide +kernel

theorem cover : BRFrame.Cov 885791366 885971223 := by
  have h0 := BRFrame.cov_init 885791366
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885791366 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 885791366 ≤ n) (h2 : n < 885971223) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
