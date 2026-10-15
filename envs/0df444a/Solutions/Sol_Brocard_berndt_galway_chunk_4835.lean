-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4835
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:53:29.984136+00:00
-- url     : https://prove2.me/submissions/91c01e7b-4f75-4426-8053-20985e8b8ab2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 869424460 ≤ n < 869604316 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 869425710 1250 869424460 869424469
    0x3040b13020d29040804060323190b131d03271503161d011e090902120f01050d020a090902031005070e1e01020706032007390b09 57
    0x518004441d01d810383c00d40b03458030303207494a03a02501138800000d01340f01105003909158802d8400c24035600480341d01503a202e40c0503d100719092682c0084058541c1140310315034407100d40300840c205152002080d402c07500d00d0610340e10b40d00d44078003c5140c0d00c10841d51203042c00b40ca2105240c100b0410000d038442c150000040d000480f94500750201d00301c00400d0040b407615607460f0840d008000c1d04c45004071900c02841018005803c0303980d50129070b24020001d09589403203100d520b0400306084c42c100a07510b40614074200c1c0c0000c4440c20304d510925041c0301c861005513006900401d01215201c0d5400ca00d5404039490b08254807a4031141c17912104203008550b0280130031300d00d9540c8d4200412642c6020703c80105040300c038040030341c0201405138a40c03100078480d248000b09610113030010840103140c001c0c12401804e00d8a42d0001c3c0c500503074210440d613106140100200341c014801c42d03d115000f900130b021015141801c8822a40d044000c0c2520040300d11400c0c400c940500854948444607030010a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 869426960 1250 869425710 869425763
    0x3150a0603020306010e0f22020d0c0e18120a14030414010c030605010314090d111c050a1407050606060307170f150a08060a1508030c0303040b13020d 66
    0x2d62501130b140c0085902554002010321034101c02d844203440b5240c2c00030840c1400400c2250b0103089500c4011180036041030b07941d400c480c610802d8405450382e928800703040020303416144000d0326562050071442090f81080452400340c43c1402c0d851621035440400790201d01500c10701105200c0120010b02448803c3c001c0c0f00c001c90300a002030007421001c14006000301142d000c5c040c0440e14001141c04240c10700000588504bc990005104130614404144d0b005402220718800c68401e814030381d40062140120300d8109103c9450745030302e51941643c05092004405001040802c0a2100d50085240007850075088281035a5250352600c0e1490119150581700d4000d05086203200306005400c0c85402c41140300f60b400c2000584500c02420410151088620803200158451408140800b60036130181a110f0304116040901640d19081a030440d0080c500c1307200541c0010007004248507580e509594800100c04464009091590004002446440010b000041c0300d0f0000c8c08505e1440e49813 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 869428210 1250 869426960 869426963
    0x20f01061401091d042a180f020304030f1d0303130905010803030c0a0309030c0f140f010b0d3207090b010519030518150603100b0307060c0507030c0e0a1a03150a0603 73
    0xa40050ba0740700c04c8440c030881250000780304080e148c1392520054084d03078426240900d515550302d0307200c1c9034010021550500b80c841c0c289038250110f80400700d00d030b404100501c1c3d00c100100701c007800d080ca0082a0b4040f1031059100c504c99420070000c00165440d8141210301c4d040780e03414000392410003810102c500061b40000240b901c050080d55100380030000742070000306030100c422500b610511290705400d07034240648280d00300202c51440c00000702d4903a03582d0420340284040c0c1a4240307044001c01c840c15030450514241e60811681880140c0d40340c0035101a4103800e083c028641052550720f4660301e625854503804155a44002c102d100c0d0f611110603d044c100c48088418016030310040340c1036085d0076a80c852080c42100d000079910105401030600804008015000c990701d016400d4030000c2007100201d42c1c50180f070b10702000003a18100441d000d8101c55903081e405140c850182c1c01142d020044141040c101e0701415030841c2d0380050baa4180c0b4001d000060700b940c41d505a52005002d09800 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 869429460 1250 869428210 869428283
    0x12304020c1c021f0b04020723060c0f040605090d081b011406031c0c050a11281214010f0506090f06061603020f01061401091d04 57
    0x40d0260040d00010b01c5a07000100300031551804440200142d03950080303042c940e600500811000c0e184a09142e00060241c600503201500d88100740d5100100c08038150000303004c0c03850090341450304030010041070b030744003980c4807003545080449a035075046801140701e44030410100207903001e4543c07268800500280c1d1300042e070b40d890f0600650360700030342080e18810341c99075880e1070b5480c070b904400701c50007500a94000d400342603d0340d452601d4800c0760b03914000640a004400403a00300040341007004080305800f4884100b020740e011810000d4201c40c2150306190150703580348240e0281156445001290603034595050110040d00d89060413180d0040d02504552030f00c9803060807060303a504601d204590440300310105541d04132004800410075140150011420f0100303540c803013071001014962501900469001d0000c00401c01c0c00e464081e0000d24204002c440c2100c0a940c02c1001d00f00a0a0354015802c01400302002985240d100200061b0804698541c155100300d07800d00403510030f008002 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 869430710 1250 869429460 869429467
    0x7080f0727080c06070c0302121615090608270a06050c0306040c050f070f060e030706271a04060e060906040c050405040320011e0f05070c030801230402 67
    0x70320481840a52064401902408810300703c0c5141c22021612080d03480300106041c0350854090095558000500741c0c1180314900c040c407989143c4201c2403005050f400038030312094a559031300402810a60b8050f81c14812030409120300d040c0f00100310009080140c0d03403000c0291a0520742854400d05003405040b4528201c1400a00800039004500c251800d4800348244820a24211003c0c469801051200a001d01c811000107100105030940d03540a00e102042003c40150110b045071b1054900301c800e641e03603c1344030901d02c182c5d400c00320400442c1030101541089580750a01615844038000180c1078a5000240800c00554040304140300003000315980c514241c810141d03101f10942d000c1d10034039040013001032145002d00455200d0b0754199a10340f0600c501c0341141440c08444404100f4554803400751a0440d03030040c1c0d10741d1201130b9801c80032401407082e4542400300c0d240503003040100f001118030038001c83d8014074440d0440f498132150180d4982118038000341c1c0c0e040e14500130361003070000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 869431960 1250 869430710 869430767
    0xa121403160b04050c010806030a140a1202030d050615040306022a060f06040c120b13050c09011202070c0509092a09150109062d081006030507080f07 66
    0x1002c031902c62881001101c4040100c1d000540744424200c40007a859440f688141001a5804d0700d0180d0101140301140c0b0b41c2000c95650742c3c40749144c903041c1c1005a0001c10702841d41c141d60b000c0d1640000e4241c80c0c042660a502074100711900c100c1c0805000107400190703481e08200100c400c049002002443c482440d800000001c2d107914041d500d9104c0c620320ba1005c00d40914241c0314100c4400e003d0748500d41400d144005000141c03519418503039004595610590f071480b101c0c05040e104503008060350f030343c4284100014012903160790026000d40e1050080500158000360a0410b4403000c540b140d103141d94008131580f84c002089014120500d1840c20030741000e00c1600b4078010894101c840c41501d91310300316851a0240c0f49421107001600490040106074080c0107280f518120b080c4090a400140305801c1c01144042c98107000003415040410404441d2281c41078050a050b00c1d040c446070410740c0d402494204054200300040c0d0301213001c07a1120340946076140c00c078000d40001a03000c841c1d4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 869433210 1250 869431960 869431973
    0x1d0901030f0209250f0e090a020d1a03030307030506060c0a061a011b030f034101060206010303030b0d1a060a15080f07111b01020c0a12140316 63
    0x501c1c003203018a5460b00451100d060900c1d444141541d000301c0e060390005150000c9421010042c0040d040c0000ea20a02e8500d0704d0302d068241c41400d800e040542e55080011401c8110b540c400480c20202045076040315850780c003c0b04507508040c4502e00410141c45a600050542c86921250000f500c1441215000c1041c9a00304034842a01c810300070080203005401501c0b169601c4412401c0c61129400080009000c0c00c0202060140b07071500107200074078801321000d01e00c268020103184600c0e500f854820a801035545801096501c0003038025540341c0301c8080e60341c01e0103001c002d06141d2140d41c0c048050300c580d0007104042e07801c413440603040301d05807202c00400d91041e00c420340a01000c0e580400c092540380da86008212890392803540580d62001c62031107103840a01107100300803005140b001039034000c1001c070000c500c840060980452031240003a15104c0ba10020500900c101c0d2000c1203550321403d9090117868114102c040c0141d40c1c59103c50540c807441b064090030144000480051002 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 869434460 1250 869433210 869433233
    0x212090303041406131d070908060f0a020d090b0114010309030912081e09120f1b030a1703100f06050d0b040b060f1b1c0c030207120b190902101d090103 67
    0x46241e003620580c480400403072309252240070f801c0c03075a0302080228200001d035032145688003802010050030000856000d00541f000760800741d48000c00b0360700604c0141d9404041c441c0b0070b0800d0804200c3e82d4503d580c0500b43d001380d0711845050104442c002030503c00f2030412a18640401280480c0040700305182440741d41198030502d016401da042103080748207000691102e4034040b0401030484150054030540344501900019800d0302801c018800050501c1e001000e40702d035107140445d124500394a044162810079480303d000208410801c11180b6042806c44020080c810320124241800802040242040809040e00000001099909010584094403600350701e1104079062450654005586203002c00d42810804c030302075500e80c0c00c40d0040011201c0b680c4640180e0b410180c0d90040e0511040c10301400703a54004040702041400305419040421b03091482408001000013a000300301700c400c03042c00c0202440098450f51100259444ac1c5000054008003100d201e5078491500d10040710 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 869435710 1250 869434460 869434499
    0x100f0c020a3206180612040b0403020d020313030206030c0c0f010507110105010b12180307080306010f111509030c0601030f02030c0a030f0807081c0b01021209030304140613 76
    0x1510180b410416000350101d1485000000b00041c0c10440210304000030b181c203070003d03264414820040c0d1408007104801041c4a14000d008a120a00d058100079017054032016045003190010808020f51004d0a0050700c117498055807000d88039038178500d0f20092440307480190716191180c3c01464002c0901500319510403041580d5011491000e000d040c0e01b80c820078056508400024459145841544c01317005502804801107800310115020101e410341d44044015510998000708110781542c221103100803240452070010881402105510345400c032081184010400d48400300d0405402082034484181062080d1070041d6940c1c9001c540c20f620b02d035400c900901070101c10403a14500200d05400f125040b4a122000c0281a03440400651098504840354581030050b1400102111200040e0840c000800a101044100068130f40706a09800c0b01e4600d00030000d03544a9200882920112026207002600050721500068140d005603c03402c030781e035039a0b1800041d10f03a144082c01000365 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 869436960 1250 869435710 869435759
    0x60e191e0308060f03071a031b040b16023006151e010c060c0503091501050607020603090f0a081b0705010f0c0c0e1e0a0b100f0c020a 59
    0x8603006100c400c1440492014000c01c2040d8000754040c104411000440000102650fa0054035040319110192103550700e40344240000c000c1143c6500c0202035000b007408003134a1941002d01d0329100c00e8541c8a19540d82850020780c6084c1402c54a482000c10500c445d0503811505070302000e1801490182d407907000303240d58820180420110a01750035840100200544854100c02c11840c04115003401d1006280c100b080c1040880080b42d0f80c2e11601203006041c0c0c1e00d80340d4034104004414501a807425040660615020040140d030f0344283c1181c00711a4142da41c80c6cec03a41e50350405141051100000da0240c0d01403800c081e020040307044020501c2c031034a003841d10141080300c0000d17070740d07480c0c64028036012540040c4d11061940c015038512024900c603d0894610544034196240400c00a48901e01d01e510344110040c14040c142c80202d50061103c0c8080200d0815403000030410005800d80c00180040d81040c0c10806110700303407015400d0303000b82141040e6a81c404010700990004510803005 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 869438210 1250 869436960 869436983
    0xc03090b06040c0e06160803010906140301050123030a060e03031009050f0f04050c0a060e0103060e0f150a0e070e12030a140904150807060201180507060c060e19 71
    0x440c0741c5441040501002030b551003112004c41024006503600c14200035036400210958131001542c0400198040c2c04941d1010412601d8080e820864455020302c0c0391003641002d0051019000114401c03040c101106810301c05984844042806c0842c040300142c8258100920301085040010085014060003044600c1644e5640c403003404803902a5010500c910405000ca81410b036440714594000b80198203480b00d02e03090400140d141c103000d5110314003064a00009200568252103000c3c0107012002460324589800051030903081d400a1015400c50043d2410320415113607000180081c00d0600c140b01803508008002600801040031102c0c402d01e02c08048020003400441603441c0b00700c064460041c100c01c03441c801c4da8160004400c0d0ba410036520f0340300eaa10103030003559040050030740310b01404007642440e100a0948500702074842d0030f589481c0d031084c0082c400007101800c90740319142607028101186804406054040206161031152580c1000c0b0b100c3c15422160b801403240b41240030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 869439460 1250 869438210 869438221
    0x705090a0e160e120703110402091c12021902040207031106010b0414010e01080f06040e0706081009060b0a05161401020307080106020f0c041505220c0203040b2b0c03090b 75
    0x14045102008072100d40102200f0070008084c4447c000d0401c00003030015040c04c1410000c0303000b041540200900b1041c00d104254140b000c0c80d842c1c5140d08003980f01410110440240400003413070020720007802260f000880c1d005042c450105141e003903c1610580d8000d5944041070b48031604280a030052407054065560311541c090b104030216414180c444d6201c40e45c481881d038880c01c034000c22454025417030302000030400400340000d90103415a501ca1295605164200ea403108101b078000d29905071615505221140c3c00c01d05840013051949000d07a07075090315a03d21103200c1580d40000b480740005000510610307070706402031481900c081d501c00c0c04903a6180022039a07400c4207064130a040c0c100c9901e10b01d160906401050540e80d008030000c94032540d803400304113038034500b035a40e0340d16455000c681c01c5082201d0190804c91510781c4000c42c00c280c10b10041c4000361151100d8088090b010544100105420b400d0141141c40c0c040b4003045508140c0da00900a444006411641c480807000040c6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 869440710 1250 869439460 869439469
    0x10170a15080d020c0414070c060b1c0506130506060d03020313031505060d0308271e1203070801140d060903030614060705030406080402060c0303040f030e060a02060705090a0e160e 79
    0x160000030280103090544417004103a618144808041e89c05c99104c000f044d8050301c0b4400f0a0a4a101415981c0d4010710141005070600c01c000c0c040c0c203080c0b100500b11a000c9000052070580018080382e00d6810080b183c80c041e4a10b2084441c0210b00b607055a800200f440403004540c0c0701e0a400803428011a501c1c4070030010320003031030b4030000c020446400229501e441e01c0b00c1400801050800d080c501c2e0b010501c0c0c6a0b02d040c848880c1006000504000b0b2041d035442408160341804980034030302d0540c1440c2c0000b8007440c0050183c02c140c41401e17507011003296100c101c000b5050350408801c005072019424010045c10060003841070034010507480c0f240c903081ca0811200002e400c0b10241d4201824100200c1d0710b00009002030b45d10241c103100c140da082c10103200131b40c0a03610502824007009036a15000e03004403604c10b0722a100748d805001409082da00451a180d11621170b01d07000341e540c500c142c0007a0381d00e03540703410828101401e801084181400400850b401507220b8507184404c426200801 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 869441960 1250 869440710 869440721
    0x130203060d140309060f0742062c06030f1203101805010e0112020607063201080105090c013002030403051810170a15080d020c04 57
    0x8a420103803241140c80442c1c08034510346050314410007520300e8184000d000400a40104550076036034000015000108860350030300d0b0305205200c0b5083c90000d10414005204641c130754240b1514000e641c0b0b40e00101858550060011700840c1e143c0c20011040e90004080b0903801c40ca0749a40317000140c010500c41e103030025180c10f822003124000c00d07404004500f403040a4102a109a00703004000401054034000c00c550183c80650082d0001819854a440c12004000680c40526580309144903080580c407640e04031142250003071404600002d460154842c0520102042501403070321510320120440f4180c205c5048500c408024803840d03c400180030340310640180400d01080c0c2e4038840380042502c100c890100120b615103682e1801c00000340c110244d0f402150700f00c0020340c000540c4201080820401e00441400307a075940c1e03030f0203446040030b0074444019641640d20707015100040c48905d05500a1500315980848444006969040c019900c80100c0088005805418001f03505414184560f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 869443210 1250 869441960 869441971
    0x50a06020307121416050f0a140706031a04020a3b0a0501050a11190b0f13051f090501021812010207080d0b03010b040c0e0a120c1715040b0105130203 66
    0x25a40780c62205c14100444031a050f41c11107660007038140c400b05103c0140140300b032603030068440310704a002c880703503050130700e05650401c40a051a211809140458100008116040a41d001641d0f80012002510104960a28001c20003800e48007044046a00711800c40c0306040d0700c44541a1a04140800407070254500886000071801d00502949500c01d0342002c00881c0c42d01c069415111100d407a8084444011001b9070f0701c1d0054100780062410311001c0d041e449442c0c80c83c1c910715481203079501da0700c4d941d41160b641008080d1742e80f0051050015404621fa00b41d000000319500c06513503019240251480304002d00c1180600610506604103008039080d650f1b121040030310b4083d81070b41c07d6008051140c602d6030950350f1001c00c0441b42c0c650b03108000c001404d40e1101102100c1c0c85041110002d103942014a418200d205c011001030b038500c84100c29901c0c20b1110001c0030010f07038001d500d4402603030f80b2580c80d40f0002c07041c002401344081341103040c0c40c020f0b6210b0a1a0003040c600c0c10982c4802d640 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 869444460 1250 869443210 869443247
    0x90b060702040b0114030c130504020306030c040c200f192a05090a05150f03060136020301090f090b071404170c0307063006050a0602030712 62
    0x352030051400354411209544141403d02030f0044900070403800e900116a620380082c400100503d10000c0036101800502d0112001e515520382640403e817255002c4030307014003503507d607014590350720b00442200c2c006d8800b44003018003418418110556411014020052601a0203c2d401220b038200142d001600e0f0015000c06a80c8440e40c0141c00454010545559640c120b2401256030b47e18041c181e07000710f016a8011a1034213002440c6440e405241400512505c85099a0425a180807440d181102d14100911402d1409112800ca44a1101d4070100428000600c1030040e84080c2d40507605a0b40c0f0102c041103584e08100034803084561076803001d450040444000b0f200548103442029003c2c140a4a26060560b90001e4805450b03a4a003010700d2600000c4400100741030802c082c070010901c03458803104d181c9119001d071004184282103102c507006d2100001c1e110420340c2c0c201c0d0703004040181400d00c100b40d550368025100e400c0f00600f2140d00b074156480d65078031403180c00c94400e220050034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 869445710 1250 869444460 869444467
    0xf02011b18120314090a090e0105060306090303270304050607080408012702040513080415020f15010e040f0c0e0a1a011b020409020306010b1c1119020a050d05090a090b06 75
    0x1804d00000d81011661a50116510390040340560007406005141c900010000c05d450412004050601000802c0e000c00303a4001e1041000000440030b11200035600c81d00108030702d69039240a9400e502c519003200350064400100501000701000090041f54550300080211260b0f0b489505105a0b090381000e000a0152110b0005441c05500c6030fa00120044a40802000076580e03c10943c0c00c20340c854001425a582c2c070990040d0140002188500564040c1688200035aa0106442c0d81030103035074440d502040010b01080400c0450300400c0382c22650100c40c06540390352801e041d00d4120381c1c1c281e0940c101500b054200e1030640b41e02103103440584507940030351070400c4285401c07900d119090340d0140d140c1468801684042c0101c90103000c1c858541540e40d145985650980042c000c2d90301101860442480108000310341503440c900c0351a03039551465180014121301d001a40c00f8064000d01850041020180d08030740140b510240c19101c500b103499031100407000701d406490382c03260004002c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 869446960 1250 869445710 869445737
    0x211606032009031501091b0212070b0619030c051e0102070b030c070f080705010e19020f01170f0103110f01023703030209040b040506100f02011b181203 67
    0x108040c219440002d82240c403400b5110501c004c14020a034444801c081c1c1d1046010416001c0865075005401c241c0000c01c5100131880301e8402c40c1c8601480601511036a101242041d65041c1140d80080401080b0400d000c0d220305102d800918240700380f078801e8007000d80928110100d080c200840145c142c014044152a0070600c07000d50388018510300024030100018000945041202d04003e400754489507119102440e00500f11030b41d01a11030003950003061052481c0e03440e00c0c50b19101c5030b8182c40148a041c41c90b030040c3d405180100b01c0c0d0b81100500010000307000240705485049031b024001002e01c0b000702009104000c2d6034015094010f030480c81003210103039114000c4503500100007207281103600f080c3c0c1060030800d04c940b800714002a0006030700b00480c0703024000e41801d0ba00455082000342441070000d4000d490140f0300b0805c0c09161030749400d029000390701011881030344c4503d14071484071410b0010400400146e01c4ca083d0780030b600020038000c0450f0303003011405515031180c11000a85 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 869448210 1250 869446960 869447021
    0xc011e0503342601180b0402070804030b04050709020a09091508030c07061428030b032508010b01090630050405150613090221160603 59
    0x9a06100c4158100d007001400349154004440040010a41d2281c100d26585072841010f04180c038408140848424018048161000600c4402d010b5682d00010780c1e075141c80c0070801a00940101400342c0d240824000240086008000e00c00c911840076544025221101f04049008520908002440411741408410402d600c00540714298002c080d82190361108410300d5603210608403c92030f00803140c200b203415004001780d1070070b000c000c0d425810142ea1141c1540c0441c546400b10210955000c0d042c0b88050190b4800c841042c00a001e84034034200c414040171415045905048540d1407500c00096003107018801d54403040c005070368170440d8902e01030301190042a00c0f101181511201c038450702302c1d10580c02d601c00c141c4c540c442003c940c0703181c2070400a09052102016103100000d91040240c1781c1e03a006d18860040e0f40c80200020340d2542800411502e030f40e64013024131403011950411409a40000f501140704428003004c0d518503494010413016607038443d111025a041c6940403d100400d03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 869449460 1250 869448210 869448241
    0x609050c041b0c0804030503210a0c0c11120115050f010206093004150e010c0b0703051003050a050303151203070209150402031504052a030901020c0a050c011e0503 72
    0x14544445c03c1c0f07610780e200d50741950300012005c604401da034181c1780041e00c89110415404091100204960311044001410500d91140300400070303018034202d40800d035184801c20a43c0c0c24804001c00002c00c031801520b01c0c0d0000b902449104100a41d1056050361000409a10480400014202c400500c0c036150a154011458400d103449081491080c9a9a08800382c402001c02031181c178400540100003501a81c442ea5601e410010b40d40d6130000030401c02c12855404c003c00e468005111369400480c004400c4003a040145580140b00040e010701500001541c0602120314044003070a60701c2c0204500d0040d00521070100790020301c80480035180c11410540d05c4030302d4088840310000032100043c126881200c0c0b460030340554400803000d50801d40f04255000408403d914042c691460079144050114a41140113000000000e1455002901079980c500040c000311080c8503031a15009848000b41d05c0c28a0000f62100d40c1c210100c1d2102c01c0c1004221020b8550602d942c5404915110402 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 869450710 1250 869449460 869449463
    0x509130f48020a02060304030f14030408220b0703030917030105090106120228082202040e0106080303040308090d140912010b03060c04060306050f0f091902070609050c041b0c 77
    0x50f811645002d40c0b01c180045205030b100340d076880001288000c0290080d0b18041e5000c03045103050080200103014001201c09141c0314080403000e0f40c2d12440b080034100c95075000705110381d41c08261324040641680000900354407503036480c1400b071a55002494103020034032902d584000341c140100301d468040c40a01401a80d003100151504d40822030a05241102d000f0b001e120305003500031110110b6018030f43c1900121a84540341d0a250440e4503d0391240d9070840107480780e41e8883d0200e0728246c00350f00c40c0004041510941c1d4a901e420308018203400000c80d420041d500801440120542c422409600c0181044c2a070500701901c080a0041405001c01c3f112900e6583d1540d4413001e680070032200f48075040000c01940d44505002d0f0003001e407420350744030300d00401d4600c0504210f035441c42803004210009a80c03204945e0f403189085450403040d0030a64122510001c1d4400a11000350461410980110101c039006124001800203c61800b04102044005050030389103652198243c4000035 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 869451960 1250 869450710 869450713
    0xb13060503130f030801050112050103121815020c01170402092809150b090609070f0516050d11030313111311071b030c060509130f4802 60
    0x1090780f540ca10750031503480f038001e602040c1c0c60f10041000c0d41e80700c04040c2080e1403250041c0140d500d10b03500c8001d259804489202881041c01820812210210440c8014412016070380a400c0c00c043e400f0f500d41558010550004100f140320546185044d90000c1c0100c0d40600301c00b1940c0d8030000c0401b8000701403040b00e002d100701e80300b85030f807100c0c3d06020300c80e90503006441112200710103a01400885004080703450184245900b00011aa2001c0b2000d5124015081020b419211600c0c22140d501c148090480c40e104014601020b000c400103251091040548940c1c2c076502040c56415540d010449070360070b001c840d0b4042d01c000504010760303d0380d0603130028242c200c0c3c28110039060000d80c2e50754030a400c94000046910020701c148074a43d00c0c580841c106c0f828100324110f880701e009a03003090060740e00340b243c001002c00580d00c079950308100792070803074601b007001d2400b10140f1406804001030750302d03152000803d0340c011034810398203012000f2801d1200c110300c82d02004403501c01010a105841c20f5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 869453210 1250 869451960 869451991
    0xf03050601140a17060a1809060e0d0206010602070b0301082d0a08090f090106050a052a030304060606050c030a14070803010b03040b01120f1b080718060b13060503 72
    0x20011009010f8005503a1100b01c1c003000010b000b1641d03104010181ca214100400c400c010342c6110540e0f444030515550000304050f100f60800d80c001d0503030700c101003e803886501810214243c2c04641d080c180c0e101c541c240c89074190b4030281c409181c0402c0c0158030090f000000e8407001e503100e03801402076104e07c6c001c8400d1140c12031a00d2a0030401120b10a80b006171000900200358075024840706501c1c2400c0307469650310f50401c840108030340560000701c000c1c0f00c8002000d00c108400c100078901c403032407002c10b401d00d040302c1c2681d410b0300c0b5041034a044a11504000010985c24024400e407985820040d00542c00d0601c001d8048030000c090a4000303800721420010903000c01d0b10311000718040c069030a04141c1e00e04040ca00780d00ca01c0c005034081361100c41210034490000315111200c624641d080322150800303951110150382203004070b5111300807511a54000180d00642c14070a9070151851150400089984640248140c411482ca1071000014948103124480c014400f668000d01d035200350766134 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 869454460 1250 869453210 869453237
    0x30712020a03080c0c011407020a05011409060f040f02041a180628081209130204051809030c0f070801060806042303070c0b030604270305090312031305120a0f03050601 74
    0x60194050340c48d000103030840b1440790203110090280c884050340200000a09140c05202e0396105c01000e411007200113818400720382840b9071144018442900200100000620303000c0004070464255044c03030048aa0a0154043e9640c80701143c0c41460040c0c8100740d01108001161103101180040c03c01c1c08401d0000030510340020007502000201ca68100c907500e205001c10442c0a04000c03114000c56401007001703124030344480440303c1c1070411190403403001c1e03214030300302c01d0443c090060490500d21036110f0001d0320220019141e4219002c1000801000e41c17a042220386900c02101e001d004004881c2450200c402008a07500c4280d10b80420340381407564540d2841d02c14621940705500c10344000c0240030051902c7c1c400c3c1281c90a905412603138101c03a040b2014003603506218054248030002c5030080442d2018050507000d0540418081d035030340b4015000711188501103100751500c0c40382c100c0303e280b08004002155030b2800700d511114203050039003508038060b210041c4030a0410991030002c03003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 869455710 1250 869454460 869454491
    0x8061210050c1b0309042913020d0c180828020f0901030b0a0501060806010c020d110d08184009081b010b011403130b0108030712020a03080c0c01 64
    0x200d010310f910019680e1403400508110544402e50703c0b01c415810907140c0d2048000c070440c4602d804510036202d502d4002852a0140001d0080b218400a000e0400714000c007425404000c1110010803040401302242d210060244d0302c0c11181c0d41d02c0410700c01c400080c120740c4030356076000803254030041c280700300c40c1c12203004a00aa64280d100321050f40036801401040d40030303030140d28050202e0780343c0001c0c94648000001c0148014a038080d0103044403510040a200248003407080d003003000b80483c10300010070710f001a40d5501c00400450b04d100c200d040340303020b840d1120485980c1c0540b4000f0524080d16100c105038002e80e551844941c182c0c6441650069240c42d00603542c0082c040e0341000c1c0c444241b500750304030b00c0124680c40340342c5034581810143c0507a08040d40803902c4680c0304c2c010752a9502c50b01944104411400064501c2080c100000f410000c00401408000c0c4290100c1082d41c124500a80c6e407803454a5000300842c1403e40043c1000e807041c806800d1040c0354500115150343c201c03228a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 869456960 1250 869455710 869455747
    0x9020705031b0604030807020a030e010309050c06041203140406050702090919080706050f07142a250810110706060609080c031501090b0105070b0c07020108061210050c 74
    0x408040c3c010b10200020716401441e4982e1140c8580041c042500719698000c00842c00119400c0c180359952041c0410b00108010b0120890344c00740030030340c0e1180c460313450010a480c204800c80001d00c1c003282c3c600c402410101900c0441c1c402e034031618244040e90b400c000c52800000c1c0f41400300c3c400d80031404031403079240585962190003680410b03a51041130900c3d07410b8070300c01040c1d00d172070702a43d0061100f660b038400070b02580c00d60b4148140791910b0f0115000210b45950702805014001c14001458208001180700301400890b94030800d2075400d0000080114070395482a8039964010003404120f440d1580c201d16011520003403001c1c036015280c0d4070704080b1011500081e000420941062100100402c12400c1c00f0b082103004000d02d109507520079100d00014003494051039116910a0161703401402a101482c0c0d10450002c211301e080010151640c1100000760300207141c550115206041090f422109031049101070001080000040d80c0508406480d200d0100d004000c481c2507a215503144 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 869458210 1250 869456960 869457007
    0x120c06090602030a05060d03080c0a0905120304090c09080c041107080d0b04050901112d1908060a0e0f07090b0c071703030618130b010e0702120c03040902070503 71
    0x60f22810700c0c00d0a54126440149418040c00c00b010b280004642c1205205d039205c203642c800d05942d6081c0308002c80f00c144165003c0358100c0140402c0ba441c402012003d4010754407464810051a408400308550340d80b00da11036030340241c00c002d12208450516400400a824550300158905201990780f10060341c00007a2001c1481d030365240341d40d00c80c43e040c0603540d04420381c60024450076031011112210740c842c650311001000c80c09107203030000030311244a80d600d011310303a12402e0b102c11043c40300f504c41c4048180c010000902000016810f450100340c410265110380380c40340c2450369485401080c51102038416000d000440d02c00107000c410070130083c030b2801c0c0b14030041d051031880c0c12100140c1041040007a0400d42060003007040303907101c0d004007043c00510720004100a13242d002d14961407451290018088442400c004600039070b01c2e5080c58090a11542214002d5100c5c1c1080c01060280107140341070340d08104420406984580c010b041140d01800070780c0d01d041da010303c0300910041803045 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 869459460 1250 869458210 869458223
    0xe01061815020d02070e190218031e060f10060513030203011d070f1a0a0e0904032007030c09090201110601140a0806160c0809040518010f0216120c0609 67
    0x56a0480d810310041004208a0100c1b40c031504101d01c1d10400762601d8803e03000890f0f40800d1040d881c085e00d2210701041c01c0080c00ba00c1980c10450300c8061003602c61032044240344a800702141078030340700340d900b01c0c45032045041300710103142000c2045500768070592001480710800c00303012025035003e11031240030307a07607088800e55400b040b0b009403420b0801c1948121601d142c00d81040107644059201c9500300c4070800320040c0d0700c64110380141e415035801d44140b908a21814100002c254024842184a441c00d070000046100d01d074169941d83c801c1400020300c40e2000e40000c0003a254980c10900b4070610506000c0265040c9080c00c516100c803d03030241042c1c265002c040004c9007001d803c1075002d09000c00180440d031411804020b011035410103e14100140c00c0e180c8414455003005507160440000c1c0184440c1c248110341c4083c121080f031504c0c19035440c003012101e02070240e00c00c0340d440050401100101c0b00060b21602c0d1040300a011580c18402c9000020001075001e100340081c061291720f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 869460710 1250 869459460 869459473
    0xc140115230301020c1e210a08010b070201022107051b010801050612010b090d2003060709080703020f03150a0e0c0109050d0b060a1d06040509070e0106181502 70
    0xca018045009599503503001c2e034410010b07001c0fa0000841d6042810f0451004441b05918100e172140c5407036148003080345108881c60f804280c0c40004d000422030a10540d85203500d503601c0740002d5400740f040090090242c0d00802c1400050040d040c00d208000c04009400350915943da1103850400d2407041001c83c0c0500551445035440d80c012907060b01424081d00e1140c00d02185111200c10a02e06020345ca4500c85c0102c2c1c103110a81c1c2c0c2c20110040e09900810150070701001c11110030b150001103904074031a014050004184a10800490381160410401440c90a00d95003c1c08142214449041d03010f020714a102100c95203036616407400b82e002500300242002c0b0901c42c96041031100c2040c5410800009001c00040e034800c12218220764100c681000c95403200800159001081c0e0b03c0040342085d5130744c550038840314a40c5424400d100a0303d041c0150b03035400e0000e070b860301c07814005c404a40e2030301c900610140d0f210741500641d0000c480c1407412440e0720780c2c01c10030101e01c042c64107000680c440c8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 869461960 1250 869460710 869460749
    0x30d08041a0118180c08010506010306090e03180324070f14030115030b030d200304030c030b071b0c18050c030a0902040209180907060806010c140115 66
    0x102101c82001c0d07150160408a504103090007200c90b01c18080500c0c19a1110300c140800103c64900005040e4842203401010703666010143c0a090700b101c0c040d01003803400c0000505441c5c035000d4079a0244406026528200003850040c0b21030100c1c11a5580510680b42800d60351151001c04e051030742e900c0b00290010b8a400003000b8181c1d40c01e001e04a042001708807102032240902015a070646e0724802250303c1000303010328110000e00310185219818070800605000054000d40b65581c8040000d408041550746c0000c019a00e100351300c1b00401c00003050008002061014050640180b92450924481e450300c0c0001d070788040003007909448003c000c0c28100090300c11151452010b142d00c40083c452403803d590000380600006084290035a03e0303543c5d003011952964111600314500030000d00318002c0071064480300301d03011616082c00703215100300825440e000f681c10921600c0140e58141e00101596608000a50f9084d00b403a03c0d5900e8861005102440816200287c5424903110b00c141100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 869463210 1250 869461960 869461973
    0x14130e0f040210020a05030307031e060e01080d1701060e0111150a0f050f0417041a0a110f0a110d140109060f09020319080f0706020702040f05070e040c0905030d0804 73
    0x1c0000d203d09540c0720b1a0b00c0c10000f1004010340ea8410480e06002821650844140e81103010001182c46010b14104012494031040d02106050f54100700c100c0b02451003254042d41c80c1c0303448c84d03120400ca40c2d02c8001000f4252186241c096004410b01d046200500d003065864544031712480d8000300b10740c0960810100840c144900d440c031268070382d0180901d0600c0c122060341e5240142c0f0141620501140b9000ca004009003140c00920050b04041d60505e085e01420703465401859807070000481182004c0c3e80c4010020b0100d500c1c3d9920000741441190f1a41c0720361082441d0003616401202582d2402c000c40c46030060347e1108440c036030001c910386080340750810131282e6403a00145203501d802100005a24001900c44001c19100300b4030f00c0e43c040a06000515006001c1c2d1030300e5441c000180a800c0290a4000d010194405e540c248841501d110580080d100221682c1001074011507402c03080b80b50036080260109401e0400402c201d40724004281820030760000c440120301e0003020b020030880c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 869464460 1250 869463210 869463229
    0xd0b12060106032d090618031707030e03042907111504061b080d090f15020313110a0312170f010803070201050c1903080a0b03010504020114130e0f0402 67
    0x40024000c40da003000e5184d0305401100300307902c008100d42e03824a007000c01000c0d13400703402210030000d5050000001c03454010268a0b1740b1710700740303003440ca0500403d8009000c0e0180d148540920070145003468100024000e11b61010b20352000d1800b040074000040c085181c0090603500d020b115225180c40541091101d9208041040c0002910070042046a40c0d4400704507400c0d80d00c0078bc4500e100605d1403c01c0c00041c0251ba022803080ba2624030858108884010404502c2d40300f000001c2d540503050200104900085854038604400c800c1d19a0009070703606a450000580146401d407040d48940b2040c10544c1d000301480046140c2da854048002c909075440343e4480c1c20050200d0880d0306148000c0c4e00d9009882c40281480320206142181d500c041c00304000100c40103d0780c8a18421a0400420b090390540e6001003142c50300b0403201c0701d803c060294900c150b8045e1580e0001071000780440600383d0005028004800e5003400200340c04101b80c400e68010b050352403130210542050300400c00001c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 869465710 1250 869464460 869464481
    0x603050703150b0901050d0902040c170c03040f0201050c030c070803030a0f05090c191701050a0f05040b042909010204030309080316060506011710060207050f0102060c0d0b1206010603 81
    0x1ca03600403c41c40824100f00c9040c16403c0c42c0c15510383d015040000c0140c062240020f605c28201101050b0040c2d12403000500b80648101401e0300c0d45031056031901c507100548002e012180801d041c0303c05540541c0090414034080c0b0308891521240449403030a00c0c140d42c000d05a20b4100209105001076240030300c2c400400003240410060515020f036542e1500300c003083ea80a01c21a81a400c0003051194904005000380c40901110340200761840740200002c44460700e03201e240400210100c00701b413040320311880c2d210568034030a89030784e12010901c2c03044000c03025110304111190420081e020b550710380140700070400541c4660542c80d0160501482d9000440180d1050003096660380c000c994480c80e103908010002019290b0400417105081d9600031211000302e09424003a000c03400c1001401152265804d543c600d41d00d5000300055841500c203064016401000403a55824a510080680c02007002d00025240350030004200c03480100700080c0b8407504140010400c0035014081c40d90b202 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 869466960 1250 869465710 869465741
    0x61d01142508010e0c0702221109060a030b064f03061107020d0f120e010e1c020d1a0702070b0415200a05120c030306090705040308040603050703 64
    0x18030003108001d194102c1445014000c50070b0101180741c442e66413044401a075000740c0751031060380145000c0c44201c0245101c16070400d10f030101d80d00c030020814080c0c440500e0014209460140c1d1500101c010b0100f0b03040c0950300030003c00604c40c00158a0150500c1801c5800070b512120710b044200c0c1c0c2c69504992090800d2002c400c2d180c243d18a120f12001c000c1d203500400005411001d0f42c08500315000d0600000d4020020301003080c10321400c9400c0801701031003180240398510384100210b032100240320015000c01c045031031180c82c84c9010540615a6000300c1c100807101005500014144141001c2c113603008031440740b4040c8400703c0c180d0b80c903900055900003407002c58a003040c03010181c401e502c62460304e60800c40c3c00c40b11ba10301c00d0011010300e540c4011040104203686610301d4444c0b90ba00000c0301c05100f00711031a20503068180c1a038051201a0700070b90300f1540da010500c501c1240082441041210405c030210015110002500c090410fa076030010300c501e801d41d4054112010401164a031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 869468210 1250 869466960 869467021
    0xf0203101409071407030507051f0e1b060d090b040b090d030606140c150103050106050126160516060507170f0c09011b0506091e060103061d0114 64
    0x5850300041c42c00200042900b2083d0b40712511b0070122628064000300a00c18020b1144000c04202c0400b02c01050310020034080007c03104803c40f1aa41b0322540b502c11440280c0d00300c807c050341c500140684001b5075015808900e0603011743c1d40c04040e8500b2141141d016070b0b91418011000d1080189243c0e0380600d084c01c2001d03a0400d00050b009102d0b02d1100d540c256030005074240e043d10103000404843e1691104e0b5102542c49241c07040c0644103a02405d80010500388171021241f803d0204003a000d0120841d0f0f8545450300c2c910000c0c540c1c0d054015809100c2d04000c110541305c0d286079001303042402004c002407182080078006101d940c0522842d1920100310041c00303481c203034024042d5001b029a03044e076569000e41c0310050f9080c1182646600f40c0b06241c0b82400d040c0800850b59030b00c69030607101690703014000c841c18070382c041011503401c0d905076001e2401072000940d140c0c0200c40d802d000c000c1d440e018540c56401c02d400d4039500c212a1500b280c1c0c00e02841541e0045070300d6600d02d013500c0c1a20552 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 869469460 1250 869468210 869468221
    0x90303200f03100e090c130606140a0e0901030c0311060f0d0b12030418050f04050a06090303020708030a0e0c0603091914030a0f08100b04050103090201030f0203101409 74
    0x100c0e000300c000304412000008003154841d009500e6060081c43c10304c0307090540340340881c035081d16240011030039405a0f0a100d03000540a8040c42000281c41d001c0d10713210580354003484400c00903007025881130103004940005c03000035590078100d00e0007140f01da48003103022425403510390302152081c8d0038140100824001303a0510003a11040e00c0004000c8040007814103103060004801070115002042c6c1800700181c00704400840e0f412401c5609041075060010741c980002c240800e42044801518680215003100300150140e005010300d03030f029280260500055845181e1698002c0d19902001a2b07a071480c0540c01c0c0d000c0c04940c51240044513000c1c00c501c0c089070034540b9907038002d20004071a451103614000f0000c40f200745142e2160040110b0391030b040204005400d0001002c030303010129074903200240286103941c1005043c0c41981d034440d41400d03c0c0c040150054000004124181625260103440c08911440614130a09400c98082d1300300785020200042866048440c0b4042e000703032801c000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 869470710 1250 869469460 869469521
    0x801021804051302040c0c050c030f03041206060504050115110705062a06040506010618081e010e0a03020c180103020306040314121e090615061615090303 68
    0x35106034040c0d50114141d5035800e040034810b00140d80081d840f520300904001da46506c10214500303140328108540240354551300b015610890410441641e500030042801001d1410403200801c03846010702060705515031000406444003600150031140c0600c481c00c0304607500000521100003000042c0c007000b07040001045c002d125088900d920303941e52103400c01c18041010000380084485070140c41c03803402c0a281594a4000071f118100c0040c103a001c840c2c050304080b0700300e042100d00440050170103a5000c0b44081e90f03960709000d20001550b8035080b00300c00200c240892480301d482a40606a40021101000040440c80890340c03842c0c041000180010380700000d6a035002601030070840c10f03030b42c10b0908140341803056118103115920000c09000c812280000da040c00b0b0300c0182c000d20059035880301c010741d41d2a0105d40eaa0032240c40e075410180e0504001c0c0c0149461414940714101c0181d15440343c1d8480300724002600d50702551006650107165141c400c4c2c0c5440b294907409241c25800629450 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 869471960 1250 869470710 869470747
    0x150f0306061d010e0a0f1410021c230a03090302060c2b06050d0804090b010c030c06051b040e091b0a09020d18080a030f0b4e07080102 59
    0x280c1880001d0390504d40942d00c0c1d80000e0010038826000807540740d16580c00d01640c0c4410010180a0701e000504401d1050000c2094201e20328245c2c81032200f42501d8200301c41c0c0c0d00200c920500205420b64a400b50105100c00034030306074201d902c01007040000751800a28201c00100a41c007510410301880c450102100755000454024008584000844615010080140341d009542c401d8401856a08100740800070708220b402c041410002c40030f0010041d140704100140060014242d09042c034002030303040e4041608156041200040101800000380003a40141c1001c0102c000745c40801c04c2e4450b003044418030340707803100d00d00110740c1c1a0303400416420801d40c02121102c54021038003405c03648142d801504c6100005644005d607540c02d00701020203501000c2590000703400c0c040d2485150901d4020304008110140c07054245688900b038190407804004480700c10005015112422207070b00c0145011490340c95105c500550b0443c1c1811031600340c03958003500e0070341d005010103044900100400d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 869473210 1250 869471960 869472017
    0xf07090e060f0a11040b190f02030f0d0b100f08070201090b041212050705041703040605190c02060703050406020c120d030f0902030102220911090f03101b0311030c0d090507150f030606 81
    0x107a40c40c0c0d0720780d0b05501c01070018a40402cee000741030035403084c10380303030340440280d196500a07101c40c0007603158504101e007078528065003d450f048491002c1000175070034084036000e5018519040e0a01000c11584c0b00a48109a40c00400500d0200d0248000c10100000026006840005601d001d25228001e807150203040c4006041a1030f190f51010168090071904a1980d030051041e40d481d0424680900180c005000300740040c4a401d4120000741051a400001c08203020000c142d020600f140440140c4a000c13040b1010710340f91462940180c84c00d0000e0f0507071807801120004403850789034225044074080c0c3d0000102c1410040440c0c64425070f0750845d1100c82d01a24651103034982000803904e00024504400520351500b510340700e000b140500b4070b01c1c40d548150743c18041c26800940c501c0003408282c40381c01030400c1c01c20000382440c1d0b80307038422541188100155140150384021280f10361203403144e0800851804203100249680c14401c00340640a03500b0051420400c41c80c040d080e41e140d1500 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 869474460 1250 869473210 869473237
    0xc0e120102161b0308070507260c09062805040b10092c07200109020a180e07080f0c011e0c02030709020c0f07090e060f0a11040b190f0203 61
    0xe02c02800d01c3c0000b040c030285401509441e074440140c50b0055a03a1043c0c8142c040303d50200d0810b103203100c0118041100302540d003008260824180003000156040031746416800007649000345500710700302c2d00108980c00c044562000741d0341f8000902c004e403812810414428005030342c030303a40142e800082075401d90f4680c030490003c02002e10340400d40244c2e401c4101c2d020002c681d040002d607907441030015420300045194000154240201c40d820b0301c124850003940100c0d040c105111490400c2c641101c5101e02074000b03e010200301d040c083c140030194004c01429041003c2242d6002c1080211f480c801c0c03800e00e41480f1030074422001281d081120080c240411800000e00c03070646d90100001806000100821940c600251311039036980d400c4104900e0141c0a01100052a24140d00c10b1545e05200305001c1e100954030120203410b42c0c2002001d01c8105030b541d4840107018103110000d440030f8855260040d541da004a203200840d4400c41c00840c1c01c210800300341001c0540d010041c4e50a5404144 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 869475710 1250 869474460 869474483
    0x8070b03012c15040614130b041d1b18070c020127030b0a020c070e1b031005091003030e150421170910050a0e03010c0e12010216 57
    0x1490410101d5101c0320b80e485482d000c00348202c001c001000088034080071a01000101d5807a4440c21000c1c141442d42c0e03600010019105681d04000c0d040303130038030000c0103000081c8408034070351204041c24040214540ca41c032042240c00d55460208a01d868040121008000c2c0700001240e90b500d81c4000700090100085e1184480441e40a6604829801c221b500c0c43c0f114540078206144d58940b03e03200c1660081090004107a11220910803617850380050340190017041e04041c40402c4000d40130b8840f400800f01800c918074146802c0002d140105406100e117480700d0300d0407081181c403880c054050801000100001c20000c1e0700714000c9021010191031131f403100d60100307070080114080c039807001141d03c00140c03101a440d004a40c0b102e10b254422510408c03912010540382c82c550050b42e04046e0095a070102c590380c4e4074040c0c801342a1609261400700301d68500100030038255084049035401050030300820006502d05404420546641c0b40003c506084442c1000307968441131120290031400b104 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 869476960 1250 869475710 869475749
    0x30c180b1302071a0f160c0c060c17030403020618010b030604110a17010203061801030c120804090e0a170a051209070305071e06091512022505010608070b0301 70
    0x815401c846800c040c080c1342052070040d041c1c48201408480f0300080b0740d030b050050011280221ba0005c4010303041130541e80324605001c42620340c00c010b40d1b401c1d20f01c0b50380d00c0e401200f4a82140f0003140724600c00c2d805046181000404403030365074404c91980e44c4690500c00310100c40c1c1c40004515501541000d485101d501084011448a1000c0c2c3c00070307160b98a411480c151548015001180504025036440d0032141c0b13142596442110700b800001d082d103400d960f040045c80803248510780e03a14066003005251039517551040044418000342031001d41c00c0782c1c0641c400c0c003e0320500c0203000d42500d140c0074070300f60840300010200c0c49110340c40080039444078089410403801308840005160f0060490305a1525076140c5002406400702410b803018403540042149841040144110341c08111070104c5082402030599421880c4449008816400c2c02840d00f42400c0d0018911000c540084d82000c0b40d000d410071500395440340e040b01d504d03a407080c4010040c0350601801c482c1101c40000601c00d031000007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 869478210 1250 869476960 869476973
    0x60f07082404060b0301050906040216170f0408160602010203150409050703120c061802060d09020f09010f05130e1f060e0106110c03121b0f07030c180b130207 70
    0x150035499401c28a42000404d4075408840190f040c0c680896031a400d42c1c1d640c4041209038130851030001c0301960224030a1000401c04072a040c11840036261650820007030344081c2509800076804500c2c03a501511562414115182c40b0801030141440258914a0031182c070800c405e200020490085a035140c41c83c013840024132107640a164000840000b00e40c0d000c01c02011500e9801c410ba403660302d446d881c1c404002d600c451640d00c10394081d02580c1843e1034a50800010810003070140c2e044407a40c0200a055513681610078085e0503c0a082c0640038100001c0c40880b000401010504a2400822a006a40000d107002070750540803c0c10032009800c0048201501e526840810fa0854000011491540148203694658480d02c00c980c03038003500c0c008042c1d03201900c40f054100d01c1000c003c102c1105002034461102a0380c0c11045420000f0b450030070524008266005552a42d1000380c02d01007010711100340c8002c540181d10901c20070a912000a41e40d51b0011915070045900080702c0040102 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 869479460 1250 869478210 869478271
    0x30906030705270d020f04090b04080a1701080c0f0316180e0319030b030309031902040606020a1122050a0b0307060212041205070e090f060f0708 64
    0x10060125034032801e2040700034010360481684408441c1d4a00c1071001c28480201654281d2400200b200d103410480b40c00348500181c100c807056030010344800051002c9100d40c602e1a000c0d42c40760014030f0b541d00c50524020901c185c07004ca14412000024010040d0540024405020290071a8007030304551190300003d2400003400300d5180d041d08016000501c010100c22241c400f03c1405000b0300022000d0b00c0110f80701c1c855400c5050b400c0d00c0003141c0c14030300c503c607910a02083c86c0140c100c900d030401c403800023031514800041071103001c10b40b003a0410031820b003130080200801ba240003c1c219050b45981d0507030440c21542056020300051f9412000310745982d104c4d6050090401010402d5080c0303401f561000d00321130703555640030788112240060001e200203103209415030f842032003505042c02d000301d140d20340100980c282c81d40c0c800e00d41c011500c001d108803107601603101040144400c003481c0d01d15a0070500c4c01094402004c1a0404003e91160010180c9501c200000d10301e43c100c000c040f0404504d01e0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 869480710 1250 869479460 869479477
    0x12031b073e151908041104111812030d05010f120512031003140604030305090c0a09090f08040f150206150105030417130e090102030402010c14210a03050a09020a120503 74
    0x3d00d4203883c000442e07000301c4443d0107640650b4110007004092070500c01a648189003103d0407160400010340c00d41e80d4040f1008022000030846c071100c04110340124550703040b209040740c3c0b080ea103100401c4960074003041e81f070003800100c020914104c500e440c0c1c151204038501241c4004a0004005201000a1046100699444043c000400c514082c5856842a00310307001c5000c01e103020042844c6080c0014110301380d0f02e00030701c451080c83c103060007180580100601181c0c1c1603080c1040c2d01c00201198050030203000304642c658500b40ca00f400c50000d00507a03107203200543d0404403d00440c2e0788948011040781d81d003800c10f00ea80f525603140031300600241c8002d0b4200108081a0702c0c04161641c0b0080c02100d0701001e1445c85038455062035402c07480300f5203000f804604442c220200195402100491651211007034455070b20422400c29040141e910541ea510040064409803481e0144520758001c4e002d14020010052240e011821090160051110b1241920440c1d420098100122004807 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 869481960 1250 869480710 869480737
    0x14031f060b0a0305041407030b0105060703110d052104030503060d2108090d0306120b1008060108031b0d140309032701020d1112031b073e15 62
    0x2d0684103002401130100b81c0d81190311210300301480992801c005014010380350865034902581c2d01e4041080b10759030108804805004608065080c440d5080c410483c1180c81d41c0c0703c0546c1c1d08403006140c0400c8180e0064032411440741c000f40404640d0200650b64481c0c07043c3d0f03c162207a40b95003444c0e040d004100d201030700303803080c90000f900b01c0c07950016519020b0030054046034501a200003041c1c058030713104d0143c80030b008115449a07000c11084c0701081e030006410b5030810143c81e125100b450030550240c016400036440024820605049071551020081071f0070050500c82c500020010302e070462000440f6003240010001c10341807007050080f1040000b581c280c0c0182d100440704103244415200860700e001d8004d006c00d103488a4014040749101c3d14400c8050003ca40d80304440c407416800192a0006441409900b005402c0e041c00081c8045030090104201480030901c0012100803030a054044038010700034902610b0300e101181501035482141d0f030048842818244852034042d0404500e0b01 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 869483210 1250 869481960 869481967
    0x170d020f0316152309010204030314070c170303270309040b0109051008090c0a12032a0602131a070305030603030909040f0309060201051311120706031514031f060b 72
    0x4071885045442c1030130901501c0d08146603943c11006080780102d1102a01003000c0294a10100d0b000038000d000705071041c0e0011805a840b01c240c0c0d8008031700080b0b01d040661000050100000f0030704401c622403048081c040b02c100c0b1903030614640341c0c007a5800c9103014980750100c0305100d0317002d0020301025100c040c0a40b500c45a644800505244055607001d91fa40100305000100e030601c3d01e000820364041c6c08508040c1c0b42c455a04a03170120000c074260404507007100008180940440050400900983d0096240d03454038004045420480d8045840b1210345860070340034610610589641c1030b014207080b600d82d42c44e00042403e5205070b51405074041ca504080004101d003c51100d1f222501941d071706403103075031101026070807600c054800c541e4002400640d01c0005450313103000002c65002920010824800201d41890040b841d0041c00100340c80b004885030007403442c00c00c0c00c01003441c0c1041c1400800d00002098444601c043c16010001e000e41003401d5240c02504000020152f8103400e556 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 869484460 1250 869483210 869483231
    0x30803090a08031501090e1303110304081e0105070c020a050d080d0e0706110102161103100c050a020f0c0612070915020606150712030c021501170d020f031615 70
    0x7050030589421400700310121b4011500b5103540d55580e10071404102404600100c50f201601d00100710140b00300e00d0702c0200000715114400b03000d07039114210412892004c072906402410b003590801407002040058068001c400340e5201c0c44085c04540e400d0300d460749015440c0c00c140c0c91b140b0404038010440c9051030911455890001840b4048a1060360b0f2260000345440303216090344589002c0c501054017920302d820220302903100405004000404641080d11141c80203010381c4c41d80c00710038020800119103523128580500408140c002250301802c0c103100140001440d901400c3d00e04240c1092040000e40038038010b00500c001742040d0f400c0c0d0036500fa02071100039035810088840502404090502c1c1a03c0304c1c01c0c07402d469440d0b9001600c0b58460042d21300c22001042610941802c5200d50700980b0800309142c60a140680003819101300790b100800d0340702e80b0b01b00c041107403c02150b00101c86141112004000e5591804000009100903085810a42c840d101400f1078500d006141108614 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 869485710 1250 869484460 869484481
    0x30102041d010306151404020a050d0915150819050114040f050c0d02130c0224010e180d030506060918070201150605070303050402040f06150e0307050a030803090a0803 74
    0x24101c1e40300c1c1c130051144400007030a00c103c500080c4204640034481085004852405030041c0c5100f42c52460400c4c01d01c60766800307500aa81c0e0050040d60181114516580420707010300419402c03400300306040712480d01e02a83d4075610074824903140c104052000c0c20341c0c1004000c0d00002d12072580d840082549061600b810174401e62580c8080b41c3c5c91107807041421850410030443c550f0f440d001004008402c60703c61008003c1c0203283c10400440c014000960008a010b50078003170aa0b0340707180b40e140c0641c14403d07440140c10001c1d103076140d581c00380d81ca070000c8441e0004094040c0f03500d0b0300d00402c1e0f54540402141780b501400c0e140e142d114400c02ca140c0030070b00043c2c5075540300d030609178000d11014040520f407400d4442a4002d203030002c0d50401c401d1001c0383c040d40145070010310240001608218040c14441101c0042e00087c40c20040e43c602c207143e5643c03040c1f1010b4601412030141000620b0100000d02a56052100a05021011000442450b0140480000c5540180401d80e4a1402e200b018 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 869486960 1250 869485710 869485769
    0x606030b0f060103061404020307020709110a080a02092b0827010c0b010603110403021e01080a0213030609050a020a0f060909021e03090304030503130f140d03050903010204 76
    0x1c1c0d20007004040040d0066120740100f01c1140c4001100e418a10225030611002e540300030900402d500c500d0340e0010381010503200b061401011150030396128014410001c0581030003030818405107006100d03940190740d4400303030f40400101654100140c80a8030b0621617848032014001351403000f020545079802c41c62a40a80300a00c544054810034102c0000156451140d10901802c1108040018400710f4002d034002c0c0030310030340001d003542086e64a60000301000700d03915120111601b4540c15000c1c5580000b00c25400c002400c03404c0d4209511b01600030b2071011144006000e0940300c656000601a00780f10885d45503070080c3c03400d008662520400a08201d96101e92400541c4c401000286008036100b610151104600340c001d000d40d000c002e00c10745400140043c0c140340010400040060300c04c0000703000700010b0f901c46507040c6250441c2d40800c02c0841c0c0c88403101802440d42909540d1741e03001480c001c10340c94200180c0f10245180402d009009603040010201c0c0c1103044400451501c200c2d1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 869488210 1250 869486960 869486971
    0x80108280b0f0609400813060e011b120c06090b0610030213030609140a03181401051909081002091e09013803040c060503060a050607050a0606030b 65
    0x10001680c070b91000722514140524030880078119400c0e104160032080c0c05c0e081c4100c8060204020b80c0b044075071540d0840781d1080031180004401038404014864104111038445102401c00e0300c16101c0d20301d00d001740301012140c0103002c42c02509403010b605010703800c98220140c111000b004095014a401503500000384c5180f80b19032900752420030418442d008403024500e11100b90952079207199243d40c060a240c1c40202c45650300e1513800c8806060401c48258024029039a0518004032020010a0218580c2001c00d83d40040041400707070342d030070008888986440e8017140e1429504020110340c1d140311604040c209000b0b00718200d14078101174014242a030012030f140c11802d1001800809011503445000741c00c403480303d00420500300e188c0860084500007503e5070f88400c4000c4000c4c0125007007044040c44048010041c40180416410f5440c060070950030003d155003000350004200c0045880340c01d02c02e410010f0171101b080810b111901c3c4640e40705c40300780200da469103007000812404a41 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 869489460 1250 869488210 869488219
    0x110316030609020a1407050309150d05061c083f060d0c030803131203061707180b0a030c060e012703060b120615010f080108280b0f06 59
    0x2000700d4a110140300321803103501c0607110078611400c5c0d548601290f070040101581d2600003031080001d40e4544807000300b000412038445a50f2841d81145079000c45001604150095078107044076142401d800703501d000e05541028205481d0401c080d070480e007101114441e40201d4040340c4901103401d0791000c00d8401b00e03281c608072126a588980501046840702213014240c8400b0700d07010000304881000031038200310000d16407e0103100a03200c2c0700d00c0040e40c000c00000290740350b44c10046148080d4120700c000300c48030013400c0401d1030300041c0c01c582c905d03c4104100740c03070362008840c40390f50703d6080460045521031300700221150f894030003514204090f291a40400e0050100d1001004c0342040c901840040d40182004903042d078860070002e0187d0b00051307401c01083c0e54840b40c410820000c80f4401e00c03901d184003440c1554040018106000c440341d0400b4010182e006000c46440451203071628000c014040c90000800703c040c20074806c5a007401f6107a1450b280600505c80c1c12918154403d080c142c8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 869490710 1250 869489460 869489471
    0x9020d020d061a01022413060501030b01051806010806010305060a0f140103061a03130201030209191806080a02190e0901020408150103080702010c0203010f0204060e09090f0613030311031603 84
    0x1401681c89004042d401ba41403219030001c000c445807002465034004008200c00381800b141e035500c850444000384c02c00c1c0c8590506100400451510054440480780c00340445082401d1500020b0a28000600240c0c140760f107901c0069440c0e110002070b640100840050b15680d582e80341c80305601c19040056090011b8200071000c01c2c40002640c1030a400031b03006075610b01c1c5503181d0015482c9010b441074221304140d020002d941c05a074800300c40105110324907000140c0e82c1d14080300c51852029020303120f2080c1e03046c07602c00c00c5200c074081078400440e0740549203030741c444020880303d2880b600983c00a03240c203d9981c0074010340090550190003994025030848a800100f0040d00ca0810824032004003250400c000c0440194410316100389058405000801c1d90b070107810041050340c202e03800150010b4007865a0070034a02c0d01308402508141284068041c854aa080b420384a10004000f924070b550170003950b204161003503010801f150b1003244410303124107200daa0400405442c480880009042c030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 869491960 1250 869490710 869490761
    0x10020309010c05070f1e060f1406191403160312080109200a090b0307031a04020a080c0f0c120306031507081909150e10140a09020d020d06 61
    0x100102c8007203e41000076102502e60175901c0d0205c03010b81c2c000c0036071b480c00050380f507130b0008000f40940075101111b02c10100300b001425145510f1b0000040c4828810b000c0c0d80c00b000b21903482042480252a4600c030500d112000701c0010174501030002c0d101e001e01c04541d100000038858410300d515280169a913450040e82daa942070b0724241c0300040c28000030703403418440424140d420b40c0001c3c0300c04022410145800c6a942211104680088030444040317500c4030306c00808005a045a18601a800c480450404000f100014030300c0c00000c0090440c0c2d08005030050164140c031003580c040f481100219600c0c0c141a030380b8030075031380c000b6a00d40303000740301e0100d0040051150303c030a07600c46c1003596180b152550f24101020030a651240f42200340c00e941da01c070400481c0040780a02d5030700c0e800301070200300d00041d0f01c81145480391890007017800b00d20342010000c081d403800c00925001030243c4804940054907000003444440b40140095004503004503210411000350042c1140d030311410081000f4900d007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 869493210 1250 869491960 869491967
    0x1213030b09010203240d2102010e1b060f0c0a060c11030a140a17010e09070e100e04060e0d271d0c042303060c040308030f150310020309010c 62
    0x251041001654048840e00c1017003104100c03640000c0c0c1c024414803541d00c41d929480541c65030000400d40401941c041506500d809006039094001ca13a802065111405007000785010004030a041c804c9800040300c3c001c0340d510a0540398895a0038080c1c0f400c4d201176207031040040481e940341c480480c040c010014900e0001105a07248041551100c10b040040d800c0004920340c41010901c052040c4109032a03580c20820100768007901c009081481c207400e148030703003601d0070700d196004008803d42001000519041400c11000b221039000c84242941c4807850030402a0152041003491881010401207000d540440c45142d0350500502c01050b803540069400502400c078001d1406a03034440030f0009000d1445811240d0001c403002105003825101c2e1115200300c1103281303100c1584030005400c1012450280400d07600301e09281c0403603240c1342c070b9642c8400d0a4040140402260740c02a07000428040c03c8182c50355483e000201910040441528810000c0d003065034815101d6180c190841031301d501 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 869494460 1250 869493210 869493217
    0x2030304170c06060f130906060f050307030804120809060c160b3f0906010905070912020f0d06050705130f080a0f0303091a19060b0415021213030b090102 68
    0x20b19002e0f0086940300b8041c00409200400c2c06504903080da4420340c20342200d84220040d543c071480c0e0208245140c07801c140e164120907008070f40b081e00f180c00f00304002004003040758102d500d0303087c0a40100302d060038201c56a014a45074940c10040000d100e00c102500401c501c06000c00700c02070240b080d9214110248240103040310201c1a202440311107011540701102c00c84500103000c400072524440c90906180c038442039580c28141e03403000d0b0050200c07000e00d00072540c4c04040344c9080c1000d54070705040a06c040d4960f5402034003807150a43d08101d07030344551031462640b5030080014041c03030808180040195008140300b40054452403000305840003200b1500e01111700d0800140210700964482051075107001901303e0926a503034080800061000f48218a00f000504003140c0c1803a18003004c41c40020122140c011491400c8814044803403d0029101510003618109001404260f800c0c1d2408440d11114183c0c120042180c24140b00c0b20a4218181d03841504a18a5074544200c0b16081c0e02 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 869495710 1250 869494460 869494477
    0x27090702070602070b072402072a05012105190f020f090402090a0e040303022a0d0807120203100503190818040615020c150f120703060302100203030417 67
    0xb04001410801c2040b00c2016090842c003c0950947c2154502206400c4040f000c002803046600444d401050103540701d0511092030312196480803403081c070484001c1001540c0292414040e0380c0d9440d40f801104030340003001000c40084100003504007242040310283c0300003c87c2505605000c02c0043c004190300a4441c5007444050003824124210b0402000c3c2d0000c040054024012030b9000644640c81c0b80081d0180e8025140141da4203c02c001546404082c03e0266164082c040b00f40141440001881d110f003055600d021410381d1070f1880100e6031600c4441c0c651996030f00110500c03100021301d8004c034084072404ca0440303030a211640946030315104041c1e400b900e072081c1402031401c1e07c50ba9050351030b20402c2c000c000196064a0b020500d4544441c00303aa140143d000302d5150519050800d614800c494004039802d00349185c140b2514802c4c801c100c04001e041604202182401d0f00a4000710040c40d4000e110305008054840000d660360030859003076460300c2c20382c000f01e070140398101c00301c90700b15 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 869496960 1250 869495710 869495713
    0xf031416032f1c02031210030c1d1801021b0609010e0607080403050904060509070c05100501081902120f15010e150d0f080d0e011a010c0b04030527090702070602 71
    0x40002811400c0d81c800400f1208103500003000500c01407102081c0d907031b1040020300304d4038580300c0c1542412204081d0b03940040c942060044400240c030316070900c645034030901c00502a440c034079040711114064022810071211108481e4105440400c0114031103101c1e007e024000c10803914454102540c403902a607040011541101c007040109101c1c20041c01c008502030004181c490b910408038072260800c548020000385181004001c0080038008200c41c000000c0701800b16504040011b40c5078000746031100364524004034500c0841d20355100807035200d002801030b1803100d03101000c0d403a1106140040340e10302c07010243c00451202d2410580354010602c550117100190381070342c184103200044000907900c241d01c0400010004041c440184031619030064085040c94615101d242542c80b40e5a51144201500003084842c0e41d0158400318469006039205000d600c07503044c280c807144208800d03c00c00f50451440882c40c50020310341000f24840a4070981e405580e007a03c1244c1ba09424013528005 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 869498210 1250 869496960 869496973
    0x3040627031a0406090506010e060f01080705031f0503060901020a0f030509060705030a021315020712150b0a1706101d150604050303040801060f0e040f031416032f 72
    0x40319040c511503907200e442410001030b81c170400d484840ca0140e099000702e03440c0103c401000800c0c28003030a603415095080c01d00341641d0030420350103000342c003004091400c00ca038038070410004480c171143c03820010b24024050300c1d41c900300300c541d00e801f039804401003a010a0703103107a060ba0b03410b00c07070710500e4031910f5490050310320341d1101a821a41544064511280b1907000d0103043c00c10ad006c2400a0003e10100c12890803c020010f0061700304407169000290118165003040d010030100701451013030341682c0c8070028441c4250000901e0210b070310b40040c00c6c50441c0300c5120b1403d000000b407070f0740034500d000146c0381c7c041e90f00c10320005500202914420761200100100b280181425914034900900401d05401e185d25000440c1c5150000c6d40147c00580d10340c44208044d01000440c00c1c090548008028541c2c9429100d10b04148112003005080004140000300c05d00042400e480d880d041442848240c0310140c00d00400b00044443c0c10040d00305c801c001400695105007a14020610b030601610a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 869499460 1250 869498210 869498243
    0x2105011428060c03050405031c090918080708300a061512110706021801030605031b0103020403171201050316050906060c06091f060b090d060603050304062703 70
    0x246111004002c03420b000003441b010031b003540d0a1100300303143c0c2a20b0a40f449143c0c2d5005008065054030703403000b07041c1032504c2d042100c03c5100c1c545115070310381c0084060750360700c80d10328104c0160710462000c43c3e4034014060b0001d000081080404c04d400e814041c20804079100d40c4449000c840e4a4440d03071a41403c11801c200b00309004d0401a42c800700803c0c800500e514031000e9403030182d4001c4034220380895001422081844038113483c83c0750960b0032302c0c0c108a41800c1001003640c40742000001c00c2e8050540301e1040c1b1580c803e404560107958044103903401c0c014003d000c44441d400c5200502055110310001107101d0400045001c2203041d070440f6400154a0082404140398025003d20f403c210304000c0c290441c401004002d019041c1c03a4000e02010000048a9800800507600b80f803d45051400030800c5800000075a0300102d400c40e8101d50a0103549021b00c004d0805a00081260001080004030036030003a09210344d85900c50202c1e504030022100010030504140402482c04009503071800 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 869500710 1250 869499460 869499467
    0xc010b01090b1c0f0c0203090301140903120907050d12020d1403180a0f030801050907110709020c10060f080114161112161101020d0f210501142806 65
    0x71030307450303c0c41001444044004052003990100000003000d80d10000710a06942400d00c6480203544001d031408050b414007502d841c0d1688500c903e10b550030400d200101d40300030814403515000f40401008240e0654252170031540c090852600c41015008400710128454051250b03c5400c0100708541e5180d40c2d260440f0050b2004174070b405840794828202c10700009a00c41c00d4990604e070294503507003070961504041203074124008007038004008240c1c00c400d02090300060003c1c00c1e106440400340e103c103030b18009a40b4010480030302c00c60490404000050003502e200403070054132205e000074812064045480c95850000780c40c00703140c100036207280000e62480703542c40350020f42850054901800c80d066090341c0390b400040d420036000120710b4084081008030156503607940000c0c0003820381c2c900b0120001c7d084d52003c0641d075060200c04207101044d040c0b0811110007503900042c04205950f129040190041916100107014981e20b2150300c03c59100c0c2040c04007070400c422600c5a4840c28540c044 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 869501960 1250 869500710 869500747
    0x90c0901020715030b03030715110f0304030e0d08030a0f0516050d09020415031110080c03070f0513030305180102010b032a0a081f1503030e030708120c010b01090b 72
    0x9104240e0b0f680c501840d06d642c244010a17405001e09150002940186c40d200700b1a00794400080460004202d0382c10001c0c040010369038425014204071811814440c0401d204081d0040000d101c400700108001e5040410340c000540c6441c551401c1140e279580342c5e01c9200503007000d88032801094041c4050300140f41241c1050081a1000e440030aa11425034014081c0e440d031a0001c0b0780106120034043c2560030001ca5440310300e211843d20481c1424951051040391202074030b6031040121703084a40f4031440c000c10840d90741c6103031012606900c0f031366400d00601c0d503000702e4050f04084400403200701c1207610501030f800c02030300014050103240d01189070744010a08080d80d502e07100b240300e850314211aa60118104002d26820000d0b107080c0a107402e49a45003002c17070740c0d500f000e54a00300f0080c20074290032003800c00741d031380c10f04150326413858010019140401e980d01000c150b1051560740b1110018200152000c1050f4400034081181100d0040d2050015401603450440302400284112044000807 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 869503210 1250 869501960 869501999
    0x50f13170904050103080a11061023120f0c06040e0c030711100506191809050c060706060303020610030510051f060201060501110718050414011a090c09010207 70
    0x2041d140007074070004142610400d0f40300303480705070700800c1a85205800c20072a0140e0121500a41418501042c4007981100c0318081d855203008410900c40c0c451800e4085940408030003040810b69410300b084180d0780754540b44a07094280a01c0c000386070035080000aa03400d07690210415000c1303175509080c0b400e850304010100300c1006a13030714500e17001c0d400c14442c2c1c0116510016011441d0f1a0900511501c0710700121a104003010286041290300040c600d002c0408280c0640414291010704109152281c21340080d50710003000611030003009460742c402c00c201c030310035002d80e545036460b40c0b0f0001054219100c090600d400807000e510b80c00c2507c1d07008590095442e1403100d81180311001c0f84031190510340180000d40c0d51150300303005030342c1c00c140c28000400015000b0206242854152071022410b806000781d500e84a1001c038040001d00040b102e1042c40300710003000358520441c44644521002c4c0310b10750003101804042044846d07001c080341d041101c103800802c41c80d4602104407000c0405600c4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 869504460 1250 869503210 869503253
    0x406020723030d1409102310091107051b0112020a090602060a020a09030609032c01080717070804321501030f11030c0a1206050f13 58
    0x1022010502007800c01240c80d60480021a1903040c1410020203c0300e10102908401032a80100031a81c100003903510710303e05600c400440e00c1c2c0756215010f442c2107584800d0030400e00e00300c02000004e02c0a1402841118154202440340c00440e0400340307000c3c0b0440131f0181c00c64200680c0c00810710380c54220500d100a061600d00c1c4511b10f1028141c00701e8000040003000074080311820032010b0740c100729a1760412100c0c071084bc50410300400240103144c051200601c0d29403202103240503d805040003800c50f4030315501e44da011000141c42c1d4284a031002c40624041660f000116903028403520040c0c1e0b07184484032001030303141c68020003620403d000500c201d6200620980f01d980c001c01085140500014100c1a500218051900141044008142051140c450301c0041010416141448112a0f041810302100807524404030303080c50304e403403009900405034020000d21443c1102034110120300410042000b078541130222009841c0030b48a510140740c0071010100810314032070f200c001080c407010 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 869505710 1250 869504460 869504483
    0x604091a06060f030916050a0518100b070c06090f030c03300c050c0907050f0d020c031204030e030705031f0608160f17030a050a180b041401051204060207 68
    0x190000076034030417a40c04426400001161900700c20520942d00030b04011100b6440041c18003004c070302c00502c0d41001100d8294084003141c0d40d0300951160348050000e03070300c66542d42d00c4182424070118440707104040014482c581c000511001d80b040f4403040d250310101103155903145d502c40071300e0622401c0c1c0b806500d68000c0d8605078041001c020b031b00c490500640f07520241740b032a41009410300e03400f01c2034940070300a0030041012040d03000302221604280f610a50342c699180030f5940c8000d00904d45441940d110005e85204018400e90460348900c1c8a80d6405208001007418143c403000d0512806426038420355440c03415001d0510180c2c3c8003010480c0c001003a9a40c0d043c5146014036a401304084a54026014052000d15905050123000c6980751710725040d244031900c5940b44100403480d420040041b407050410f5101d100300c43d80c010b031041c0d820b447e0140c542801d44919407091192240001c03a10040403e1075008000355a5468686018103a444e99207864030006540505400c481c9c1c1f11f141e4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 869506960 1250 869505710 869505727
    0x30209040518010e0c090109090f061a0a051905010e040e07030f02010e0303070c0b030c191d01020c060403151107080a0305010f03020906010f0201021e0903060604091a0606 76
    0x148100c5218a00b01ca10034001004030100190840303101c401c4400303407901709640d4003080f51210300d03150f411105c8691001a9520440c04d1111910b0b00c8000001d1003103080c02032000c908504241045c02c0004211405050707240c0d210b04009414010342c000d48840c41240c1c100b0040c0358020502e0b00c102141c09071012807100003144102c0d04021b02c642080328400e007400707a0081907591000440000700d02c01c0d0f005502e440c1064481c00c91003402485a46081030002000410361140442a240005c0311015104102c440c40b0201400814141181c61040301ca4484148110341c40040d02c401c1800020740114601410b544440d91415000c2d80d15010560310f92444d015101c1d02da90081110720300400b015900c901c0c4507940241500d006a002c0037442c124101d0500240e51041d1044e90802d8090801403a00014848103034003a006150308050540d40190904c062a60b042c40241101b071012000d50303615075038200c00c02c803c903042c518014009010400c0b03281c21081d000716242d6040710000340600d0070b01c10503 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 869508210 1250 869506960 869506969
    0x60109081204031205031b0a020c061b0f0601260a050610030605010806010e070804021201051005090a0507051b03090a09061508061e010c020a0b0703021203010503030d020a030209 79
    0xa210501d401038001001c105002c2035403000301c0704070414034055140d800c0040782c08900404c0341c440041130000005403004414000c01110310f1414000d00050b403100001c04148000b070b480c1c07440540702d0340a00b810401d50b81d000454140d050324141c9680c4142203c0040d11480c0180e140701c000300304c41c0302c1e40200760046482080003134400e0700001e08000c9a24214a8003506840c410790010000354014401801750f4030111220036401a1280341c41d1409541c0c0e80005008103010a4035500f9a5103040144000301c2c0c02c24490106850003561003a04507114411460101c51045801074009003050000c12801c5001c580b00394410100b440489081a038060002201d0801c542d0060901e903a0755038040080484842407052031180d1802c10110524050b004900c001d8294081c90390005918501e01c8481ea010302c20721051641c000c0c3c040d012858a551690402c3c1d8000c0c0000d40161045082405e451040340b030480741a1280500907500b0a181c802c003540180d00044400d10515409100045080c0c55 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 869509460 1250 869508210 869508223
    0xf0a050a141602160807050307080106230d020d0507150c0f170712020105061c0b04022403040f03110a030e1909020c011a1005040b031812030106090608040302100506010908 76
    0x1790340c0181480902d00002c05241c010590302c444110f90500000300280c01343d5072000074803030701c03100b0f11140640d000300005010180e2110ac002c0d40981c4003480c01041c8900020840140e4074860042c3c0340700f8800300015110302d5203580000340014026000540010074600d0000303040b0041c41d24003424007000e6624840503040040070b03400141c0d034400810000b843e04041482000e4454001590019425103550a00c3e46c00140046c0c0904504001d40c043c0036800321108034070007003450138039843c0d08181c5404031030250401015000030340d4075000e03003628807004101c1c03803250b40d0301da10ba60030501500024020b10110601c3c40f0080c81543c1d640c0024140385c0c0740010001900b20000012700002d89074046440c0214183c043d6009440886031207240d541c20004a4064030b20318100103803680d0307900328537407605025640300104500503100506041c00c4401c004d541611001c1c1c80b080061501c0e86070445100310112005001030f840300c0207a030410b41d5241d01581c0c018006140c445d09554580020310b15010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 869510710 1250 869509460 869509469
    0xf09051b010c02130b130c050a32070b060303040f140d0605011d160c031103071a0a06050414270d02100f15060809070e0f0a050a14160216 61
    0x5481ea2030862003490110140c501d40c20f080d8504000304401a0001449800742d0194042480ba8074004510b031a618103081d400710070082c0d854409800c0070032b8208001c2e900410400c075111501c0310003040d028500442918142d40c20100a42c0003203150840c001e0b620404810b80300d4005005100c040c0c00b0400707034041c09001e010303445a00d2080e184080104949000d0041488100402013041c0c210b03481d51240070030306419018a807070340305444c0c0059690305501c0303000801401101c00201c40c401183d054580503100310710f02401000708550710424031040d01c14403041c9003122b14072400003406009425900d8495214146003000c02c050100b1f00e0b580c584600c1c1a485005644403d10112400900b0b00848580103010071090204142e610000e000c500e119014050a000000e0f000a1701544200710240062072041400301c15403c00e2480324100842c2070f113406d41c026003040e000416203c20313401404800c4880c00e0071821507648155141e000d20b1600f48001e0118060514604a0b00d64411101400350 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 869511960 1250 869510710 869510749
    0xc1e0527090a0905061611030409092009010b0f070b0a15050411030406091a07030204050108241509041a0111061312030b03030705010b040f09051b010c02 68
    0x3456964108081007030028800a002e50510140f540011008952036400550038001d80c05122075a1a00303640d500d040c0ca000020320b220204000a07040303425000141a00c0c011503440b00c00303202c0c0307941c9503044414407039609400c044140010800e20315407400800e01413107410441810b1280558540752485004d40d44048050784960f105c1080428044120b001842c00300d0f0104000b0701e002c07a0704140ca0000401c06000e880c2c1d41d0001c001440800c009100c14441101d1042c0b9076032415403400780084d0041e0240a0010f908000051520800c3c00c2540020b01d0602000c05520780c6444104141d0401d03001d0503800b0448240071600b980c1d200d9014021607651a00e1409011488800004220b0030307640c1c0300824158002c1007440410248030000d59030950b040114809405034001080d400b5100340d04049416200010301101400707410b6011124410088409000201c46214900155240c0c080043c0c00c40c0c016102800310801582c000c038049440c1030400301444900d43d00001c0e01803920040e0135004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 869513210 1250 869511960 869512027
    0xb04090309030c1205070311011b050706080a1103130203030c10020414060f0a0503040203120301091b1e0804060612050a0c061704022107080304090b040c1e05 70
    0x1c2001c250415000f134480c41000407403070350b51501c1e01c079912951417002804e50003003d00710080b140d10881400c07043c403800408121403e440c41c548140e844100384100703000100f860000ca8000046030148603d08204144110f055480b034100c00c009100003084100d070b0510082282904299041c440c440c1c03130a141c40b100584440c0707400140350442c0c1542c65030a1040360204035010028043c1025905960703403a2070610385980e201e10109141503a80c40329991501c0010000040d50880c1ea00861010a00c0445000b070380c4140001c161000480448550103000c8501d0081140a204e01c002640c858002e1101003902559070750042072040401d00300b620aa0460701e41c180521000c182c3c1480241807928080d0040c00004884684104020b80002c4c0719009103070411440d9030341026030040c0c20880c00d0544034026920000d46980b41d000d48201c05555041c014480440c4c50203103c0d4030042c0e281d0f034495107000c1050030b100a103410800840003003440000e10009000c1058001004810410507220100c03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 869514460 1250 869513210 869513213
    0x12060f0906140607080406052d0903010b15161110020c10090f030f050c12010c0e061303061e060b1222060506010e0d0606030b0705040e0c030a0b0409030903 69
    0xc16640d1580c02c1400341c1c00420402c00000c00b070800b12021984c081c94815200d01003c88038610488070040381c0c00ea58420201c900f1810510070000f46900c00341107000b085116001420300584e140d070326414005441c41400b06441d4032601030803401101d449030444a0300800c002d00040d00c11010808910010380c07111100c83c80780c2c00e01c034008032920a291300340382013402d1419508800e900207501008100d6100c07003907802c04000c0c0401c0b10180b01d080c001c0015040344100d855850027401c8201c049000a11511344c0d1107642d0030b21004545040310151044210300d41552200c0c4040c20842c490300c0c0d280320680000b0003551055100d0b01e000380c2040c40804c3e6440958941031062604d016144401c0303070100c1c0232018003910400074403490803a0b1041000c5683d90700c079001a1021100d14030b60704d81003c1103c2110003000311076400071095038854401210360307407038040b02242d00b8000c034000c0c69101004071020600c84054407000d180c0c040d500560201d000003d040119064400e045800c4010441c1c1000520 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 869515710 1250 869514460 869514479
    0x1d090a1a19031b0f06030c120203071d0f01120b0a0e090a06050f07050706091b08010912050f03070c15020c060a06081b040f06080106170114100612060f0906 69
    0x2800f00c0100d68194002c0d0616103004145121031161605047c1d03500015041036028041d060425181034074115141c1c501110090302c45104054007112001a46140071561315000b00748605000044e960340c14440c3c1c07094180c20040580e9083d007944200310201c0050700011a442c0c02d80300b204020082c040042175894001c0c00c0e5000544070070914000c1a04112055500c40c054400094211901203090318650410000f28003003c0e217001031031594404045600d28054000114152260311640021849182c04680501900b42500c0d84044200049624148200d00b4016a80d0140c0d50b28225402c0c6ca010f03000c1280c0c0082e9040c811500321404100c8500210311601c80180b52041c080c25440504040d5010520780020400f1710603a6118100d04c0316440c44c1d88207078045c2c040b40b002049119101c8100100181714175000c10495824950628540c1c10b120782114010040344000c40c40e800d04200003580d0304104942c4110b6460303600d0700700003200c0424100c090000c00300400005000d50800b403a01 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 869516960 1250 869515710 869515733
    0x1060f0e0103060302010804021e1914030a020603011a16030f020d08161818060e071e0311160b01170a0b060d0516080c011d090a1a1903 60
    0x340c1410300e07041003080943d0704042c0556019904231070a03501d42d5010f203440066800400d0407940c20060101a50011400e0301c1020301c1680c0c000e1081d43d00103100e030010140e4030043c00300002d40000040c0010044071840080e1683c2b0f807880c40f0340e60b9060540c2d0b02e22098103250041030032713000103910340c203a50b141c43c2d010f00c0206e0f850070113458000d83c0383c908039000800b0140311001050030003501074980c12003104500e0303004001d404190300648208600d110711300302805950051000ba90107110110300c805000e071550703d500226299002403110039180c000c1d00101201190700c0400402003001e4101005810010210036218000b402c90950504440c1d002103483e21803a41080d500a40e1040007052040344194ae108004591350b01e403100892405a0030104480031182c103850800d035021403d403401080d0306001403403c1ea55902d40e2800d00030311075055240020810381002e01500460b001d526075402561494209a0703000c8041d000d04c0002c00e00564406c0e01101c40459500c0c014002c0041c40b8009 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 869518210 1250 869516960 869516987
    0x1507030617010e0d0f0c02130540032a030e030a081209161403060610080a0504020118080f0111040f1502070b040608091203070c06111201060f 63
    0xc20282d5040c0c28004d641c1c400c03480c10a814002070301d4010100d50b10800344c05200540c0900b04440504401c44440d02600c8152a417580c180e92520f401c0c00480c031100f50508410040010b60f001c5459510000046140000300c144c04000002d13450b00f00032094030103100b08441c00300540018141660400034000140658241c0c07003504070340c11040100750f00c0710030346840f80401248404603456a4a60038906070b01c4900460f1071018440c0c000850540104002181d008290196170042e924542001f0b115100d03a038201e008a1400790115010244541c0a16401417041c1402210706648a076202c1041009501040750303a80840428041202c080c0140166225070043c05410282004d00240c1c43c40c2043c0101c010b049904504c0e000401e20030000840106818185241e445459031402011001c0443e0310420311300c1407004a610184460080300d10681e80e0795502c030b000c0280ca5070b40c500903000140d0a0960044244101a140c0034508129802010303152540035140c0b09640f0050903d03400b9014 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 869519460 1250 869518210 869518213
    0x901080c0f0913080d0204120c2903220204110d140609160203160b0402010e03070e011203050c07090504031107060801050d150e0d14040b0a0c051507030617 69
    0x1d11181854614030807005941c04044a03846900c200013210081c01f907a070160608041240d440c5040c03013650b0604001340c41c8801550b01070295004081c40e000700d004404c0c005a0042000056844002409501d548503220095010495819000242904c40c500060200d44600250b103003100710281c4980c0b1810700d40740d41d045201d8a0007100080d94003100420203010300750994820309290b48284110740359103400d407140081401c0241041c001a1100700c40880c0400d01e0300d140411180740001e00300302201c3ca82d030f003110051703824425120540802424203d0921030180b02505554500340810405420300884c000303002c0c5040e00b4007d00780061104c103420580c2003c07805000c1103030300040d058103662041d240781034a10010700c3c01d5080750410510300700e4250300d003601d00c0d656807801196141444480e56202c1c0a0110301c40c010420510032482202e0050b0020040801558054044230307051501540590320600c025002d004000c00f4200e0b00e040c0041d0380d880341408160703881030059404258407130 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 869520710 1250 869519460 869519479
    0x3030e1501030809060f04030615031406330d1a2d07050d0c0804020f03010612021908031819030f15020f071118060d030503040c050901080c0f 63
    0x860380040c5114070130007140101000504400202c05100c00c0300c00440e441542004907104d1100d02c0840124a800103e6288441004d1034107032040c00030ba881e005400310f562110f56424804010005800088158032100d2890301031084269200c2410001c071034082d190080f050618402903000c1c54100906948004910502400800e454140940400c1146071040c040588a42e0f10654160096540f15805181414104440d00f540034040d02c3c02980300b5604420502000300806098510741e014170000484100030280251070445c1051002c41c0d018042c1c24641c68880714030341d0965000b02a0300740c8002921401210505040d12150031640410012880d654115940c85000d480c110102408404500f88101958a0990f0451b240c0c0030b03203038134080ea4402d40c0c1d1900d04030780c0011400491090500c0c441d28400c0c14188404035203c2e050040803040c420609a80130746050700050310680c1d590b10400e20115003500d40c0411140602040030003408200608010402d02042890069020b5143c45 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 869521960 1250 869520710 869520713
    0x1e270109150b1b071502010c021005010b070b1302031507020616050306010503060f0a12030e060304330903112e0c0e060d0504150b0d020105030603011803030e150103 73
    0xb0039103c00741c050700b105514001d2410803962820701c3c5038000c01e03a4001e2940b080c405064056001601f00407280e002d03903c0000e6880d41100403100c0034800c4c400000c504201c8000020700c42d0b0307000c6902183c0d65000d4900490b003600844d03c0d00881d41c401181d9440c1c854180411242c0401c0303c658007075501840314a003170b0420340008056000260203a4103010012012400c0c81e40d40c02d010902069015201c05101a44c030314102c86410302650b0141d0105404c040018000e04014003100d01c038603004800900d99540440c0e142503110f480403040c0895021081c9610141100c2d070140c461175034003c0c4c0d00c0c4000b03400c0700c608031800c10f030300070f43c81030b003040700b0b4500503142c10f00e0210413006411542100040c90f607100c020151055404800344541c001000103040c2400b4020343e0185004502030603d0441c04002c407603c100880d60300303101495100a00755003400056100380e0086a01001c003400116003200c20102078122542240e00c02c501280d1240705540c501d800030418020f500c07184100c0c000895145 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 869523210 1250 869521960 869521979
    0xb0120070608130203101b0306210f05030c0102030106030b040209102015070207080307110603041118180d090902070c0b0d27021e27010915 62
    0x1407088506016501e0000b070111680540000b8140b41c002d01503a92200c80401079100a000480124080d80c00d07201c550300002e0305c64852881541d40c070b02030f482d144600e4005828951421034608032500e0110203490800200c09201902c8050040000541c41b94180040035080d511000407460080b803040c800d2071220307600c4040c410001015070512401c2d0002c816462900e0540c1c58040e01034600c01c041c40280400801d05410740301b858517a00362280a1340b2909220b84900c141c400182c055443c0c0c0f04500304c58500100150380240c07081d01202c4400b91070501107034124801c04c030100b402d11440700401800d01445480cac0d004207400d0b24041c000303042840c000500740c4d0581b4010a0146913001c40c00030300700300541701c40f01c4c094180721466944400c1c1031803040700a0400b0022400e000407031660301803410005102e584258a42c01004846000303a05014a1071440b100790019074412001c60090380200c511459442140d110640c00c038100390304140900c0700350f42d80d008109250003032500040001c003c8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 869524460 1250 869523210 869523223
    0x212013140916271a0c03040b09031504030806040b030c03100509010207020a03080319020406080c130308221a16050f0601180b040c050f2109010b0120 66
    0xb80d5900050b00070105000b1610f94001c0500400701d00403408201c1c0150249060120440e8504042019049855160302c801401401520000e0f980140418030404c28928050058010054100c40a05d0142d2107441c02c03190003a00c0580c0440c04c3c0d803050202604180c001d040c08080c003980100904c0700f801d00466515480007a10280f02aa10008650960801e4046885480d001080d02080e0fa4403030605902661040d11a0303012040442d02d00d100c4e00c046802545c0880d16192203001c801c1d90740c03980703280b19907000344182d140e1180041e0001c800980e141015000d00000506d50b0000960154020401c041c80c070b8100c9800f9a2000c0c2c0b511103c0f1b55610101d450089103c1108190000350346001498102c0000030102603014001c004a12060f1008003002510b00d560b10078001d00c20402c00344400c0719000c00c0c0460001c2c1081184c80d0070030103540005c0070080d44440c0d6140340030800c1d101d2040740d80410380b91745081765140d00c0d5580903580d21558022202c02188920251100e01d03480090307660a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 869525710 1250 869524460 869524471
    0x70813090e2b110d02070501110609190609061a010207050a0e0705090a0803030f100e07090e07050405130608010b03121c0b040905060403030509070302012120131409 73
    0x190001c2c40c08a407031040303030b1401d03040d0460011034580070340089000c1d403219002d000d42400545421880803031003c00240040c001c2c03800001030610b400b03500d9050f10310092880410765240f038032078040d000020120721940149059905901000380c41e03c07400203042c44116841648500103c110a11143c1102139140f6000501070030002c0e40e69000300d020138092846e81d8003594403404040304001e00d00c0c0c60440154428800485005090740e161211034541d55800c0d20944001030754440281300d4011100500307034210619040850911340d4410024070078082c0300b911100d070180c6524081190320000d0088008108085028150f003000c0c036000d2004c0e0f40181e4600d0200300010300e54859040300158002120010060403d0003424154249555103102c1940d040380044d01d884c0010705500d101080d54001d8a0341691202c40510019030740c01070345c06110072280c4030541d07241a100d40701511113500b003607090003806a160b2284c000c0c1d541c0140307213040b9074445440380d5545500c14034255903284030640d111 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 869526960 1250 869525710 869525773
    0x20c03091003060803033103050a120e0f10050901060501050d1e0203070507020a0b09130921090e07050f070b070e0a0801060509010512060714070813090e 68
    0x1c070803644085025001c02c0d40455000e000002c1401a500884849003080c1a070144900401c040204850744011445010140c0040c00500000b142148514640d0880c95005080800c030081817603042410000c5203407003800598000b00c04042e480d4050300071380364481c84090003000400d14000010b046842030b641180c10041d07a81003018000341c80700345c4c20740704802d100c00219240d10b40742c08054119403028005900c139080550000800c80d1241089031200000a80b2410341401d9120f03c95020345910181291900700c552444d0f442e030f1012100014050802e0f80d200c1880c80e160452174500c230719010700180c0c01c00c14100440103da40002d02102e00e811380c404400180c40e03883c0c540481e0440100e0139101d40c44406d8140c0040c00322015044030301600c038200e1b1000a542d036102e04020200185460300382135500040000348105000e1002c441158600c5012545031a01aa9910540c0c0e03002030380c0301604010014043c02260802e01c10750300c1c0c100d094001400032a00041e52600c1c89071071280e070b8a48a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 869528210 1250 869526960 869526979
    0x1b0c09010e131401060b041d280902040c0807081807030201110f060a020406020c0103090f0b100b0d02040306060b070507170f070902040302180c0301060f030b0d05150a020c0309 78
    0x420400500d408001d0f0070003c000c0007003039196071070224941e0040c418910b007509110000c0740f2079114019998040c0161102e14884608909209841d2980d01035400b04c030b050b580d032400c20258403907005002141000d0b554a8525103001c590241c18030f507011708100060768a01c0703660503007503c0020b040000c3d2074090926814103640c511a4034540000449085c0140c014841403086121168010303005513070064094843c2511058011021900800740c0031700400300111101c4003154084041e16000804074a040030100d03160304030200d9560100c034400e103416134000303020020b000c124442c0c0340203050f003001000d00d040300b15140e030b0341e442d40d25000310001620003501b8119440380800030341051808050947d455160381d1001c0c1e00094000748402d03402a2a485000c0820240800e5004d1203006045080c60035070b42450000c451154240400c1c20a01d40e40b0b8542040b01d5455200030414144190018103500300d0b141480c04c4180300241081d000c140c018446800810000b02c1903a40b00841502c44218 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 869529460 1250 869528210 869528213
    0xc190317071b0602071b150f0519020705030303040b0402090a111909050d051c0e03121e22080c06090118050409150e210703090b1b0c09010e13 63
    0x240300b20b0780300404007900e86c050301c44180001d0010070304485150b000400c0ba2401c689041c2d54800f095034005000901c100700c0c40c8500ca1006071207210900c80762045070411600c4001192071503005442c00c1e02c000c00c003842084114036060000e1640044010000d000c1a4001c41ca0041c207809500c00300c1c00c0401030142c0c401c00c210f01c1403242900628004150300303090b00d450705229896170000001030001d00c0304031031600902c501031100700350f00d4039015008000501c50040462103640041e030703c40c40513118550075030100611600c0a8160303d00346c1800c6c250061894009186241460343c018030b540d0300001010348840d52480c0a40c4d2800c174080c20304041203944041d1418076600140c014030b81c461311302000c2e4401d2081c00c441100707904090003000c101c03c07030f141d401507a61401c10400342455409401450705010101e000900f802c144030f410095001901d035a60f240264205e02194803044011142d42c0c00300200400c01101c5411060b90321100a5040140041e103001c001402151400d504800400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 869530710 1250 869529460 869529473
    0x80301050f03211201051c02011404080a03260c091903120302270a091805012a0504050907080417040f05090a1a040c050c190317071b 59
    0x2025403002e0780d40c102c4440c10411040f1441d0f0082d69160040c02d41e004000304441c1480d8814440c03000007038210294844403070f03004444444603030074204030381c4505000000c0d889804201110307445d0700c00d8850700b444010700d1041c03800d48174100013910b100d44454000c3c8000b4080f00c400b02c9040f120162400c40c00954109100c2c2004680c03580000d11500751040c4d985501c0d5810ba028255210a43c0c42c0284100104000c1b089140382618203103622002d82c07903041061040a911010718040e0070041d50748400642e41760389084a0a0052402c000407039000910220480005201d00071040c07410580d003000d0a007000300758082c0c00101280207115012003c81e0901c42c040c111030b0800103401010340d968940364214007120030607034810301e13005017180000301b024466076003d1507000341d1401e000111078840c06410032002d802110040b9051100030131211400101c144141d2000c514118494000300c4041d18008168070f02c4041c1030703c1e02c00141010f120740f040c1d11002c069141c5240d010000b518501505000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 869531960 1250 869530710 869530723
    0x1101021c0e0f160906121104020307030912030c0801050a1d060f06210a020a05030a0902010e130204080d0e130f0f050403020a05010e0c180a150f03050d0c080301050f03 74
    0x42d1014070a6030780d000c1c03a480c107140504007990b40381102802280d50b680b400034005024048001d1040441c5d1b000c011490900d80d02641c1d210b8002e02c1c012039010541c1d2582c50a086c3c1009030300c00003a0701c0b0503a4000072500100c1079030040c8800d0750088801490030300711004080c842507820b800f08440300c01040e1941e491b01d441d520100c02c0200301c079980d041c3c016003080030702c0c8045244000e2945c80304006190107026200b540c48004031074580d0351865454000c00307401845030110403414400000c80102d442d40310302a000c2c0744907003403642c0160756604108209140484140d80300040000c10072519440d03482d91070541a1225101c480403503420040c07000c8501410040e458400f143e8945010001891760008900418074083d400802c0940c601389030381f5172607030301c8116100c0d0401032003045100c0682d50b0090f03056006074112030000715000001a66030030840302e40e00041d420704444000380140801808034003076030681414440f103000501c0da00d44161b03010500c0f07017905c28102c4e2120003140341c40a0280 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 869533210 1250 869531960 869531983
    0x90603071401050d151212032a02070b0a200c22060305120d050f090606010c030c0c062303011508040212160911130902030c04081b011101021c0e 64
    0x21105961b13269180105500103501d003d948400300c501440c64074601900ca20780e1314942c07507101d203980125107041042410040c0e00301131b001c510850780c00107081d003408400b801c3d0b00520742d61124900e441092000c01180b441c2401c0e04001d800c85104808169104090810501650100c180c000c2100320f444c94010709103a440544140a0105d9050908500070b009000300c00e1a0282001a0385560b0000000c00074200d4420745154004d401242c05980501012044039100f4034204076102d9090751201c0c40f90f9010303800000410400007102c40301c00d0001c181c00302d403109607001d407a0540d1701d0090203000d040034590034842072110180c041415503d40a000c40d80280c4103100320b80340c0740c0d8640c56484100f1608d116208e800d40c80c1c0a000300482c0310040449100340f050302101e00001341000e100320002e500c00f4101901e0798808010005015105100d40f02448188800329941d910f121400034090151901405581d40d00c1003000114214500042400242ca4590b000030350511200c580d034034050841e00e8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 869534460 1250 869533210 869533241
    0x9040f0b040b01450f0e0106030e070303120b06040f08070512070e0711150a0c0207030305072a060809060a062304150b0702100c03021f1803020309090603071401050d 73
    0x800c1c01ca005c550b864040314000340c44034249a9032120101c04030340e40c07a001004c03160401c80007000841d104940c0c0034910030b0f00390400101b02841000007402503000b075000d00004c1548101c100007490302803110200512013601c109801d0078080031441e8981c042c900954400c07620a001181600c0d128010410035150b407102100c07500607420000c040202c0f170071200c0c0c1c0780d403a0134684a4800907101040405c11a64107032175083c1054065560a1003c04c503000701014a02da003520240d4400c103c1260107002040141c89403e15414091145818403100070250480c0a044c1b01c1c007049281c004ca5840f07a045291020519801e100000005c0c020789480041412072101030000494854030040041820130710845112010455910742a03460185017503014016030045c1c007041d0400010040006601403100030001802c4800300c4451900702640d40e02900140d1004c10100c1aa007450f40381181c1145080707008003012882d080b19810011102000340381000004243c6840310041c5400c490201c030001003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 869535710 1250 869534460 869534597
    0x1080f040510020a050304021207060c0809030c040c0503070e1f0c02040f06060216051e060703030221061c0c05060f120f0405061b0412020609040f0b040b01 69
    0x9134001c00d81c1e00107a41c10380c811242c101964000140c001090340403503003962100300504056880f0611030390484240c45805010380d1101c1030066480c0c1c45500c40411040d12130303503100d0801c02030082281c9a88540e5038028481840f84000030b40d042e021007040711881d890280381500e039a1000c14007904002a0b00c00103241801d0f004581d858000c100e5044100014501501843d0788908000c5444d0038003120042e03940101e040469142403800080c5013980c040d00b405880c01c0e4122078050b0318460602591303502540c0810501980307240100d10085515208048034007485240c0c0c40fa83e81d006081d2240c50312a90f00094903030340780003a0000765003c0c07500c0c10100f0781191500410364518403030111000c880031f0107140c1c0018425903150140044190740340b541941030908004000c49089000c030806d0b603000d00140040031943e90703a07008000407414680b00c0451841008000e01080d240c0312000c2506000100070104044c40c0c0704258a6200380031135100307140504500801c2c2c040c0e442c0d11a6107418245114 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 869536960 1250 869535710 869535727
    0x20d05091e04050f06040e01140f09150a020a08093f040b0301240815150a0e04150e0c07080708180102100b060304260409060e0109020901080f04051002 67
    0x1010000d10583c000d40d1706001500c1c2c1348803103900304d68403030341000c802caa000341c080ac041014802c465580205041c0441d403914440301314600030800b0442e10026001d40004a4686040e4482012070300060140003c007183c0480702420009101b1220320180b0130420b103031029002e600e01d12201c002d02d00010ad2107582d915100e00194a0b0350b8000d0090a00340310084510b16101d200940c010724039141c0359940c24005407074050601c103003800c02c1c280b031755032010200c4440440400c1b03400003458420140c0d118220b044800009000c1520028124000e51342c1480d81c04200e65010020007980c403180c84c5600590310506882d14000c24010050041c2038250046100d1010000c284145045600241c003126081c505c00b0700080b0a8900040b030640c0c01000a102081c0050841da1104400e4140080c0c0c1c0c070103200c60310681d120550031a501a080701500d5035001c00c6140da901c06928050304020606518003005440041c00e0b002d005406071031103103c884000b40500005011072801e0000d0900f0643d40d81030380d0f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 869538210 1250 869536960 869536981
    0x30f030e04112d0403050601060e0103290a06021b15071b210206120618160801091b0507110405041505070c052d0a0c0312020d05091e0405 61
    0x2084180b40b20191882e88910f00d142c02000e0b50103e135800b00003055182e003007050440b031800303440e00d00c2418952540950241510b100039400b090701801454440f280316000208410084a503001c44103541019051400c1e5504820041f510300d94152003550500201e081e00b800e08d44101c1e24040c00d02e011030b00c60348200010050400c2e04503104444007101e00d00001649044295240400035031144040020740c20f200c034400c01240d88444000d20104c0038800c840001d02104108172220f1840b5142ca01e001425990064880b901400c0f0004040103c07880130291001e103200c082184105000300403603400108007120080209034240a0418410390400d45045d404074081208404059410080046c59651068403440740d12504980101300d023103100e15003442c4030071039942c26110350444940d1007003180720700300032a04090748103901c00c640741c0e459424410203100e14842d00c80115000301c9a280b800590040503500309800071141c1014030f41c032900d42c641044920a0b400e0f504030b4141803c02034131004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 869539460 1250 869538210 869538247
    0x601060305180c010c022206030804061202090a050f1f020a0201091202130e100e0a290a05071b06140c0a350a2004030f030e0411 57
    0x20b40340c0c500401904000b10442d01d400301c003904103000680e00b280c207001502d84854030b13070f056031030002c4c12605420388203d80034291100d030b4000b41d80242c0005070030040154441010b40c1003401c0c141c02141822181c20014107002443c0c4100e0f440f4002109540040d940c17480ca2103162408a190010706480115101175200c040781c1e601a400314028007030004c0c10140c0a282440300390340c014140305495a54500c01070007485500c0340500c1c584541803201102c06c206101c4c4001009051f4014a0300516902c0d18a298401505201004c410200d0403111014030310a6003580288401e2004140c40e540d00c2c0044070101001300385000750000340e143c00000e0041c0341c0e0294039080c006850503c243e42d211024501c0502c0340c82d19150000d0780d0f00103010450240c45281e40f20803c00a954001d501a03904a480400c080c19100145030b113a9400d1a100b10354105c0201105c040e0100300d00c1803e291031500c9218440c0354880004d024403103415090794031684d5907800401001c1001183c580c5540e0000c0e045107140d003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 869540710 1250 869539460 869539471
    0x40b06070f120807020c1905030f06010906081c080403031821050a1211040f060908010f09030e09070915030c0201051302030d0507050a02040614011d0603011a0c0601060305 76
    0x1050940b00340070036445003101c1c03445100075400800001210000784031800500f28050400328140f00c00105840da000c1c0540090010f600e002040e542d410601c000080311080c1d4850050b60703018040d00c101d40c180c0750310141d100110b03506001155580304c2c10f007030307014150404005400f00104500c5400300098488400c1395030003054601c0e91141090001598148109100000416102e04a1004d10401c541101c1c584400241d9801d0605a0b240c12000c08c1031071a40002c804240301010038030202200b4071601040040000c400d00520583e510f0107825000180b4166000b16840d4001903895805006032500410030507100941e02c2903003c0c0024010402001c0fa0310040d400d2070f02003aa04c11841070040c4000c0d8005029040e58203c4080c00c4d641c56011030f40458040c0155030110003d680c0b1032041c0740050900000341107003050301c1400140180d0b5002000d00c1c2e0850000035500b0036031511000d80e410348810400c0b0020b098001c611070120340c02a50f082ca940c5d403007400004101c2592603040207000d0b4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 869541960 1250 869540710 869540723
    0x4030e04050c0a180602280c081e010218041d0609031b010608030a2706090302040f18080c0c030a0515010b0f0f13030501091103060a1a090402040b06070f 68
    0x880a50098005013401440b64500503841528440104041c65041c00480c0b4000b460140108505989031040710400307502c004080d4110303d13442036070f00c0c9420f500d82001200da0002107280a440c0c158919404031000e96180c09503a5408540d21000700104441e200c100e116800c03699646031444070980c4e203034461702080084075048140b0070054501405a80261502e80c03001e141000d144400448a10084224028070700600b44461a8104603c0d42210050310055548a94060442c010f01c8103440c140e0345003010341031030a60030300004021422405920f6a0202440d030b640c000c41ca45091804e550703928001d500d4054110b0300c01c20002d00069400e0fa509400b51013450580c8e943e1002c1c00280100d840078031071302c0780c1000803501071980d0074010680341281c5c5e403240307248507100e403503060031200f01e0310302251180740c603506109140c601044400d5126100000a01c01c9801e50785020088806810000780180c3e1468046011991035070000e03401ea4802609198840820f802c11413520307031050070f01b607415 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 869543210 1250 869541960 869541977
    0x120a1103030c0303011a0702100806101e0c03020709060b0d0c020c0616030306180504060b0306070e090606071a07080901021201030f111e190e0103020904030e04050c0a 74
    0x490601000b920041440c84014608580c0f0300240c11008129010001d50f54803803c1086c400140d80344104130422055590b1395450300d15254043c0400d00c4001c240f920140b00c10b603c4d03030240c11080f8050080480300c040c900781500908615050780f510520750400c2d441a828030300041780040d00100a03100c0d0500c2a6424040c00002800c183c2e26050149445500a40200000b5030102a6850580d40007880313440c00140450346e07000c01d56503c168840d01306000d42e0300c3c0c034148820310a02e40101d00049030110702900050500c00c101900700c0c20f202103410702a2060400082c1583e490300265184035410200f0f0540c03590041003100b0100301c0449284000c10503410109400c500148240c80004040166002283e400c644880d80d0702400004221440942c0704511245a05c0c0c01e807a00050010000404884100309820030240e51524100e410a410008801308440300038000b2a90440360151008501c0e629582000c5a01407900c0d100d039a041401d010a0002c03070054000200b10440c42e9070344079200f = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 869544460 1250 869543210 869543243
    0x1b07240906060515071e0b07050c0c0103060b0306010c0510020412030908010b06090603190f0f060b120c09010c120815221107021f020601080a05100209040b120a 71
    0x1c00109100211014810500102001070f1b820714403018007a05c00800c44000f00c0381640c4c0c456001600b00c4504d40003030404609100004c40810054100500c2400c060000710f00741000d1058501000b405107040040c03003514042401000e01c003c1d8040490158195616921031140000702a05042d044000a90709180001e4400c03041c440d452030140c004201d035103410840001c06c65590405801c01501000c800207800d41401244a4641c80100c0800c0100302110000111400c50300b10303a20000e15100c041243ca2a51045c813112a540001060001502c4030810700c01210b442c42c0e8854014584180003070000c40740c94200004074440c40845e040034030000d04100602c10520760f1155000402c3e844048a550040c5243e0440c14940078511101400d10045400180901c84020526540c414141c3c00310000301c0e0381800324a002d00042c00c001c0022069940d41d441d40c4242c86204000d1031980468074060682e80c2d500138414084004020003d5070729a00741c010303142c0e40e541c4012502d075000b8004068 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 869545710 1250 869544460 869544469
    0x4030f0206010b030105150408010c2d05030c16080708030108120a023f03060a0806091c0207030804080c030610050d0602091f08070f02061b072409060605 68
    0x103041c0c80f40d501400d400d5918107003c0c0400315842c442c4a410400e0240000b00e42480f0034071a040b45503020f80d070340075403040d415038100503681d0b6400c0f07a544803284e0340b9080007440c41d0030100f01d03030700302d48502505541c5400e40303d02559100c1841000901000c000a0503c1c20300001102850507140e070001542c5540c10643c050611a228083e50800035030003000c0c03010700566501e8504d003404019127610341c4d140700da6000e15080c4000c0041081003001004800d0290724200800c14078050030b03500c4018081400c1440f00d03141e40c4d141d01803500d6654540109145444e80c400d00c030761001543d01205094136580c0300c81c1031940303860680b811135020307101d242c0000c0d03031010080070402c0803104054141406004070340c4428000c3d6115402082d0031024075841c5440b04940b030522984072100a649030a01d60a240c034004000640e4010b14404540c000c07014415414440c0800002c0381040d8003040d9a10300082c90001c100d02119100300d00621460f162445d41320740e298001080603403103014104641600c980811 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 869546960 1250 869545710 869545723
    0x40803040533090f030309011d0c0a1203030b03060f04053a0507080a05030906070503221b170c010c050d0e01110715080114092e0e04030f02 62
    0x10422044000703030002d048000e0181960304400c2c080c0a56825003000e075603c61541d4001d56120016a42d203043c28081c0040013021075850b22514000380c808450300c00c0010301c23600a540100600c0c47e884103074590030940682c0c008000c1c014058203544440c5025004c5010001c0100c8040d6054018009031000d40d205849103407010070400c80d42c400800301c2d2409080c041000c01e2402406000081003160049840c842c003401000302190307202d50343d03072034a450518107112025102d001440801d00600000543d00c0d0388000c208509c4010313a00c0610414203084280925100110345c542010020100f8070716104440043ea0310f51800484907000d01443c01140c01d01c507072106c05420340d00589a0445001e20030040c482c200c0405150059404250041c5541000b040350300c00c03291a6492942c6900c1c56401c140c40c1801001107011500f8400c5110f40400c41e1024020710642c45007002d646086083e191030040e0000d5004542254102540c640b03051030f03000300090300d00f5808070340380b18140f0031405c0c400030b1003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 869548210 1250 869546960 869547013
    0x20304021e030f2d030703120507031d0c0102012d110c032d040302010507111c050705040b0301090f14120a0f030605010201021305010c020a0506030408030405 70
    0x2110126000140c08091403498500c0580c0341c01101046200014200072035518100b0f0740c1490410551884d5841c9550b4554071400400c1d50400c0c04807802294101500c2c4038031901004010032326986000c070407002840d0b0841c0000108000d41001c24070003900084113511194280c00030007032503594030014072140c04070f0000200b80c0c01d4804069080c000840d0010a1303100c0040d410507047c074520005031401c5800c00030802c40c00c4840f902c0840740c010b2628410303070780301c0c1400400d60b8030301829900001d00380d01c00d07000083c28962103608803c0e502d0301d414030b03141010b100c0d0305e40c1d07000020b94920b00251a19003030710400380f0543c14075460108501d01846400c001a0f4000350364564000b2603900c1070312440082620411600401c000d1307224103219040201000415580c1d080c0014024030000f070120b8840e90441c13070443e0300c1440006800c002c104c40d4079094580034203004081f55045e200207003948050707030000d0341c01000100500040011003070280d40514403540580e140036001a1041c8103009030a1030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 869549460 1250 869548210 869548219
    0x90307081f0e03160828140a0207030210020a0512030c0a1407120e01080a060e191805010510080606010203030403050307052a28020103020a090e190f02030402 70
    0x1c800034525070a0340040c0049100e4000d8a04142c1c0380d50596041c103a0344841619034010005240342072040c00c02d28825200c0760200ea2140c805090b040003451065070301e044514000300014113403822802000010b008550040c050103011100890080d254800000111080c0c86982c41c4a882d080c08101900d21881d61046228100b410301103088402c442c0c048120090b80c0300070441200403406145041c0760f04810b0340c071a1040356009000042c0000001030501d02000e29018080c045503801ca0328103900300c0c0070210300a0848071903500d400b004282042030300700c045400ca4241402c00c901074204600c1280079070642c4850903a2840180c2d00c030f1204882d1240160400c00c00507001034011005180c1024251600f5803c16501c02d0300f0782070710768080076148a01e03c0c4001008040007820429000000644603d02c0190416010b044061050300ea07402030615402040301e00c1c07500e10403480e00c0000c000c6600d2000050500e1001011041108052400c206082c000c2e02d0a000c00e15008490003241d002d031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 869550710 1250 869549460 869549503
    0x6090b0a1b0203040357080a120e0a05090a0b090711070303121b0905040b030f0c10031e05070e01140d09061b0522081905160b09030708 60
    0x3610200302c2c94040c00e2460180701503446c207040881603808075400403210801507020140e8446180c01255007075000d00b059500040d500c1d0001200f8254000c0110740c1810403d030081650400105005507640150380c04c44000410004485000e030081d40b24154150341458079070f1038551045a52100f80220094130386c0c413155041000a00c40c615050000c5112040024490400e1a44480c160190a00100010101c0030244100d1426100d0008403060880041c02c21104035817000d502c84e001d9501c0c062042c0400c94684044902036005044600000301c5070f210010084400500148070a50703031500054100b80345e0280950040c400303281c00007245003425052152a151920240500490813920162103a400240d04114424000703050303501500c2c1d90f80c070b90321540302200c50818003080604c40110402e0f010801e112020840c2c5502034680c0d0a82c502002e581d082c074031b282c00c206603010381008488240c0016041704000c06801140d408034141c85580d47da5400f0640c1d43e203494409480d081caa0795 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 869551960 1250 869550710 869550743
    0x2101802180702030403060219080f091906110703080f010b03041a15030105090304030201140f030610051e0901030f1b030b040605030118020a0f0305060c0706090b0a1b02030403 78
    0x1c01c000c950028280c0b04507468561680d90707420981c0c01c205c044101000d1000c0c0c0130340703d043d04807441c150b02c10314920751910f0f6468401461966000c104010744030344c4850b03c0041c0d05012894214890440c194800c4556400d014500144214011108050321191190000c10418440d6040328010794010321001c20b15018103540d000701c10000781044000c80c50504000425440a00600c0c0c4200000c00c080e507141c0b485c6000140500a00040032051581d0411103040c1414884080c2c80d0801d10a0714003542a4001404c207885c241300e10001d905003540307040c182201154007a001000340c41c2c0c0170b0380c040c0000301e1039100c0307241950900903036050554444c08040c06464420b500561241e01d0082c00030a203155950086400c6a1100150102001c01c9100c010f042d8100303904018000e01c90790f5440001a46941c039910b490702d02c0070f0100d040e424030018203107041c440c0c250003035620580c00008a1181d0305040c000f0a00a100071900010080c0740e480c14040700ca40088150380032030f908000600050900e5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 869553210 1250 869551960 869551999
    0x807020a0b180106030803090f031c18060603120e09040f021005070c09051510080a05060d0221071d060405220302070303090e13021201020c010c02101802 68
    0x108070940280e1008103042d0484424004d120045018202d100d0703582c1403205a0301d04000c99a540040f095001300116022070082039002d00165503803680000318101c03441c0208504400003280074000354201140030052242100681c4007119032511a00c5456115109202074070000b1100074001d4001e140003030000d03007020190441c2843c4680380480c50a60555120540305400d5040001e1041c0c2d41e0040004ca5a0301ca811220141012950312003040c001840090050000400e01185107480c0d0000c075859848412020360303025801400002907402c1c00c811128040b0040501c84040e106d00c0d0400036400704003900741c04101c0c0c0aa46444259500c0c6024031015040140621088005200c94010f49003160301d00c070402d0901c41d50142c0190361843c2001050f02400da0414283d200301107050186080540d070505103820b80c107440c03ea82c020f00d64004140280150200c40c04507509056032000303c0356021a4400c986001220704104540d07080b46100c0d0001d52490009401c12413410079407040034507 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 869554460 1250 869553210 869553233
    0x1f02030f0a06051f181d070c0b071103040e13020406050f18040f1b15030b28050306010609090e0a0f0201051612050c061320061b030304120807020a 65
    0x6490174a48a07510140991800c20700c3d89a0018501000360b1158480307030001050982d8018030a498850340821113500c913142c41031006098401480030b06807405035a40801d1080e41c00030300319114451080d203070686c86080740c0c00744034200700c7c416844e06070045071502d800c4621894030071740603085030300503580e0f140b0b502040c46000e0802d480541b03840001e000044d190707a459001860041c2d0f1081c1034035140180d0703910f030b51031744911000c00e042c24040c0f00c810176202c1081c2ca1044900b01d02d4809107030905120b40b03900306200e54101c00d805000707110001c9031142d08100588200e8900715420070003100c6100d1120b44800303100138001c0c4090f10900341c45000d0b6100d14003030507400843c0c800e203003030a500560b1200e40061071040d054011031000701b8901c5103143c00744041c661021010f01c84081c4581c0c0d698440d00c101d04854101c2d04840ba100a0424094a403402501c11074420700880700c080d9030003001d040d0f50321b400031034084a803c00180c0c9080002031017501c50078050902c6030000c10201c401d5a41d0349600f00d1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 869555710 1250 869554460 869554519
    0x40308281202160f0309080d0305010305061b0712030203061203040f3006091103010510030210050d0e030c210906071e0b0403090b04061d031f02030f0a0605 69
    0x1c3c8800c0210011510760030403d05518800e448001c1d40600d0240303030b5070511003401c03900b20074185084010404540c000c54040d901040d07084501e2602503482e81d0740841d601554602030515680100384080c0c042d019801180600c00454001c5505d80d0000c140c1030b0b5900c00c0340070740111450590b00c01c01003c04c4119580405074030145034002541c003600036000c01c0014022302600c00c44c0c5c40700448002c1c00f603000c110b0440d003070f000c0d00240054549100382d007000011070f2100a014000c0724601d644018810010785508259295051100a09061803290383ea00035510082e924040d40b61000103440c500f2a40241031818600d5103404c22485608016960308027038030648a0003004c2c006081d081108598a014a91040d4201c02050500d420010b1201c1466000079070703000c034200700c24040a504214019680040c4144400000100e140424141180c1c1c07101c5c100c1035030307241840d11103500a540285100b842802d12031f9111b40e451094840036202a03100da50341110b030308a070400f8a044862880c42911 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 869556960 1250 869555710 869555737
    0x1206010207051306030215030403080f18191a25020715110c0109064b32160c0803070201030f020909010e07090b040308281202 56
    0x181d542000c5014103807001210109656188130910031407400303404400c016502d108a07c0d0440c44c1987d0054081e0402034041c083c078002020029084000d50144251960040c01c00d45854414150b05080b114040a0341190b9400b10000c4c0b03404400075103c030942c81b800c20300f4100d9065178012131010b529088545141000c40c05803c1c4042000301c45070900071912200b9544101115880c26105404e01b00f07414009030410a5841c010030007154058441c281d03042c0b04007285001450041000407401c80e42800e00c0d010122202071040d200c0100003400216031403191500410381000342c0da0b0a0030b01c0914071100c600707103015112071000300c40c4a10140116100450500840206640300c0b070310800119402203c0c10740c40094044110350f80740c0034190107042c21410030341c20b00e001000024003100050190b014201d02190014208500c13480428005129400d00c00391341c0d40d202d04181da0507600c8034407188034501c9450b130002d00c4081c031420140030000c1c950ba80c4003c6180c203000c1d0040654000ca400070480b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 869558210 1250 869556960 869556973
    0x303110a030c03052d0d15290c06090a0b0702010e0601090c022b020708060f060d05030d0e0a0606140112021e040906090506010c08030112140a0308010e090703050312060102 76
    0x42c0740f042070310499100903075100d40d116144481e100c020341d41880e03916107100c40d80c034408100b100706844c07181c0084414001c1e4236071040700021021415014031624a811482190140f11a001003c160719141c14040c1c02c40c00303590f81e1342d124142c0c00d94a90600720342e5030f5440300004011102440c0d0005807110b050f441a200c0140301c40e190805040d0202c4030a0100446040241110503010440b00e030050260340301411161404000c5046070302d0000301900d000d5015090f140013001411b2040b00d0801c107100804112060310b00a030b42e0754454464500b26102d525205001c600001c440d03d28156034030050b0745801800b0400707403180001e904144072000ca500c189c2c81001450030b038804003400c003514500c0000142103141c0315504054400141c0660b0500c200342000c100800c6148044a046d04c00c0c2513120034581d1950314140081b50f602136045a014040c0c018000308240d0302000e440e0490f054541c41202c1c03900c41c1d4007583d0310340c03c1c2c0380700084c8a0760080258a41d0090114400741d800031050040d95907 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 869559460 1250 869558210 869558257
    0x41e03050a03170a06050303040b1b1207020a060309050d0f031803030203190b030307110a0504050a380d1401050403120f02040608011e05030f070303110a030c0305 72
    0x582507003480110301081405000e18500a044a402540002c0a410601580745000003107611392045019024805400040503543c810100307110044806010040f2142c10408000406150b00401d40c2244683c61855002078a28443d014801d40e254104015050180c0b001500780d403449180d0014000303240c2c541b20529000e0004c41e503003000e25402610302580d01e19003480740501c0514000e0703000810a180880d0060a0744001054910046c1d0050303e0601c1d8800001c001a80000503a1125078458241020012440b0703041d00400916450b15816003081c1a0a01c1031410140744081b009028002080204500e841c100000304a00b60242c010300b260548220016070035550304a078240d0224044007074141150a40b4400c40c1100d16609a0031414503080c0a0002c0008006108118482d416000761950a005402131038009010041c129402d003241c00eaa07030382c3c803144284070580c04544008140c2c1000c3e82c01003507e9082e50351507910b0042c41141c590f02030300e90350403024200b4914281260440d1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 869560710 1250 869559460 869559463
    0x41d1605070b0a1805070603020a091502070b0703050d0207030c0201110c0112090f02031b01091a120601030216030e03160b040b0307020a06090b0f06190506160f0c06110f03041e0305 80
    0x1b002c1c01c00c1d5580540d4a508808024264408550007090b104c078000420705041907000c503061040c1c030032034501d0319590384403401c0031150303402142c0c840ca98140c03000504404058004100000841c400c2e280e0389008003030781b40302c10348a50700d0302d01850102d03a40d09604440b00c0030b01d61104010a103d090b120351601040c1c0c010a1170a4019211540e44042d40300700d0020668112080300010300d000700b4071035005801011460000d02814401c050710b4010381c0d02180150f8001c0d019a920010100000300c1c0480c00c604009040f4810048082d000b80070380e60303441d4085045c1680c3c0c03905485221001c40e2a261801e8107071640c2c3d90009060700110702503400780b10009000c6003c0c0d40c0c6850700508440b4805c0c10701c2d008101c56424064069407051542004500e00541d4600b985d108803101101c0003078490710700c4207034a4590100300d2001030101c141b2012007010090380c0036040c0181d44080c0d888200143c095650256140c81014802440b9070050000308003121403401500c83c1c1380a0420060003241e41c969416 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 869561960 1250 869560710 869560723
    0x81209130e33012c1e131a010f0b04050f0d03020c12061e0609040b072001050a06050406080703080a030b0909010e121914041d1605070b0a1805 63
    0x620200c48140981c0449101e0b05104c810b0b02a01c030a442c5090b050025051460344014200c1c80c42820020000401209103401103600349a000100c10612844072220128240d009003d1b0014079181020045640c0726800141e9043d164050031003106440300104000c0c0008000a088003144103091105045450b184010210f68803103000078207180c20b01c0c1b14a070340c203031260305441c00d8a19012410000f959440701d4285410030f42022514805031115030302150805001540c10101d414a030145a4081805600a40c400c50203070900304a2162150204000e41c1d0080c4103200050380310941c103101145022005000135045030400140c1c00340680085a01c82070308445100b417a941d2110209821030083c0300403520005082c2c1098903100448038043e1010100305c5145040104044660302c4071410142100e0140c000b1150409030440c5102d044144140704035003c190f140700c2c0c004d030a4a01d0740500281c40f11180d00016400b01c3c4c0d900e160350400144072600c6980d461104086503640403071800d2101 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 869563210 1250 869561960 869561969
    0x150603030f0c072408010b0a120506040912170108070305060403050a0e1306050f0406081c050903060a24450213050d0503180a081209130e3301 63
    0x1440b901c0741200c40160055005902482030402d040019823070b1180d000c01e602c20321010a1200042039151500840c0c000d00f0000c00c0100004034282009a0b1140c00c02029400c0d2031080c00166103503a01c40039100d4542c0e00d140710003403280e88239002007400a80100098400c2080314604444922002c0c00090454980b01c100d58210070707a2600103101030300b0204803071b04644000b954184001d9251030384150b0380705000080c190044040042c101c2089100d0f50482c0e0091070014200c580c41d00703040000300003c204061110743c104102c5100300c9494025241003004442a241c010006440c24040c83e0b1410b06005480303000189580d83d8003a4516460820306012050504d0011b0301c411807025082210038950f000b062060711450b88400c0010000000c503001900f403402465440d909200108582043d540c106101a0203809008400c4800040c0a080146401c40d5869402c155003452401123508150302409a40c01c84424202908a480046070303101c1116140c1d4071022800b11403061842200303801 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 869564460 1250 869563210 869563259
    0xc05070905040c091505060c01060b07060506010305060d051b0112020c0c010e03070807051309080a08061c1214130e1906080303130804120b09150603030f0c07 70
    0x34002880703640f03000392004c1c0031500b0040003000040e800418815625101782c9205400c0018084044d000a402940050640701c8050f44c4802403440c10b400074203011158240000d180c0000603899251000c1000c2d51241c0080242240c0d0003c3d8224403034650ba950711941c140840b1039161040302c49180300030012140920050030f80070f8100c0000410420060860a100341d000d5082403010303850108016040301c00444d507200c00d5500307400303401c4041c140c2100c001e4589040442c030710001541000000e481b0703120888540f40c8844501048814000581d10050700350052105585085801105903d61140030141c1c12814554800920700780f0f4452074218201440811041c000c01c005140151008082d014800f072044600303010880741e0b04d000c001c00040004c2059408541407203c1034041760041e04020741610a2810641070503a081c102c10b0b50000d682d032103020880f28042c3c045800807401014010302940c5030607003038000402c254110190a031081e0240105c0095901d000c1c04c0303015a081001074 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 869565710 1250 869564460 869564471
    0x2060304050a0212120a03020d060b0c0307031205040b04020d060b12010c08090304030b060112060905102d1403030d15060f11070302060a05070b07050c0c010504080a0f030c050709 79
    0x10500200300400d501244a42d841141c41c200c000170b03207806880720a1100c0c900161140e0448c124080a000c83e5440050400c200044030045104080700628901d40a0f46804440040b441c000004988046601070700d00074130100847d0040c6030100e055070701c8a0158501060704075450300000c084000d83d5621043c0c9030354504036141959044040c55900214040c0514202480c54803603d0400100825440c10001640040d004102c800c0d486100a0302e40359204022500d400655501c001c6040e0140002000c0f074050003e000c40550381400300d028213090404442c0b00c2c07600c25614041c140350700c0d415070b16010a0140d00300d42e80c800d10442c1295080c49007102c11051a1400252004984050300c0742080a826000c00c9941c50018800d01203982c19264580e40d5000004200c032940504bd000030100e082500074005640d034004080c11103a4086019900d03d0742000c001900c071446140301d41041c94000c2401d40c4085100e060560604074040c1c100150400c2c038a0b90341d9400c0c0728040d00b0840c42203a903038 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 869566960 1250 869565710 869565713
    0x90a15030f090f0b06030a08040914090307020109140a0e090105180d270801020d09120f120b0604170d02060703142a07051c081009110702060304050a 66
    0x14003604400e0000580200001003036903c1d103030455200c6580c098080c0801201058080c1c8041248400140c0c0045005460b26214000340d4003809290700b40585020540d000301c3d084002c0403084901c0958141c42d542c070038a01d810703090000c601d0900c003900c1e4013070440c0c200098030210452001d4841c031015800000d45150900c120546841c2c20118400d20380d02603102c0c00000c981101911310711544510081e0900403180302c00920088850b000b0140c1e6500104030b0004008254011401d201e00c2200400308211800e0412038a10250240e0680050707012069907440304d506912031703145144060f000b14601600c0d40480a0b40c44e480b82c1c0302c08195400000a00304456040c070040745c02485910341440710b40c0303004650070f4602c080030f0140e08510b600e0030100c0300782d000200307050203c1000b6820309a4035400141081d43d04c40b018013040f915070307243c00d40007101c5462040d0940b51040744031b801800241800c01030058014880c1c050105521641000014096901c08010714840e5110300c0041003002c889 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 869568210 1250 869566960 869566967
    0x60305060c120a093e09071409040e010c050a0e040912031a09100812040e161101020d090614240f0d0305130b07080703050708090a15 59
    0x51103040044000d115491510303101d100e4854100582c075101155180041c1040c0300c02d44c15017a490404e0341e103030842c40c0144c3d560510703500e1154040349608013201e503081c000740b00ca407200844003803000803410b12428000d070004c0e1015140080c3e0280c80062080094601c407400c560b03142c6680c801054020038000c0f80154001e00c0409400c41c2960140018103c1e60388180300391403400d10240074141c035010320820311200f00640b6100a44024500354035400d00903440d05480d02140200c0c0006d026000d44170003008086000c070740c21907056030080c1405607503414400c0384c60100d006400b020040190404075400c6030900141a0443c16414001404100c1d072900303504803012600c0401030313000101d04200c030700300c1e0342c58507807101550781ca012104580d07080000454440c110048941d109500e640c005091690003006842000c15680041c441d00d611060351112030301500341c0080000804000c80e5002034850380150400c0c0e80328160960408040a00284030300d04903422103444010350700c9800ca40c2660 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 869569460 1250 869568210 869568223
    0x1f08010203010b2212080d0f1a03010c021522060204261b04020c03040824130b0112060608031b070b04050117040201050c0f01060302030706050306090f090f010f060305 74
    0x2480400f80010b240b400c07017481010b02003c1405403a4030300116540e0f40135074541c0c01110003044038072410401c08820001c292580400008114025882c0190301d00c0d00500000c0c59189400c14002f6880c51341d503940c0344e500100020813191000c405a0344d10b00f83e00103050740c001741001e4288140054440c00303440d03000c1031480000600002081d4012080c00584200d104a4081c03000310a580c056601d035031052280d0f00d03501c50b0303a100340b1240c498900c40c1c404217a2100b03000d9281541050303021520703442da00a4000d00307860015010f44000c180700010090021000000145140300f802c000c1101660f40c0c4206040d60000c100d440d107003040c0703140c00801c06d000620030140500f031074071519030419080000007031030500000c0000454401082c042015603000d41c1c181d0380c0810848084a8601081c2c0740f0450190406200484c06031023010004280c0d24024410b032442424044c01d0004c148d0b8681001e0324450388083c0110140e40280c00500704003a0080c051910418003001000c51842e20790300e07000389000c0c03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 869570710 1250 869569460 869569507
    0x30f0a02030624120f0a0627120e0f1f0f0915030e010219051c0506061206010c020a06050414060403020a0605211015080f1f08010203010b 61
    0x4608904502089241c444410586402614102145544d43c003e0900d00760260301c80142c1441920030382403c10285412043c0969046040c01c1c10822aa03c006a05100e01010007030044400003404090746120310100740078100001c00c81c120b1005d100010502050b0385150082e000c0052a0429403890340150902c0b00340c2e200d51502e41c40035450604143c80b141c400300708000400d0b8a548403107003491000d4064880607144003060441040c641080a0120b5101c3d0b08502d481da0711422031420050341922406100b84400703484540b5080c0e44241000341424014940d9062012008032035025848160815020300110b840d0603580700c1c1800b1409103400c2007541901d1249204120610050b10f6400c450342c110b400b42e0820603103a140301c1060140e40410303000a040b0003117264040020301c0b42c0d4070440c0422034080104e2140451820a0100c52007038049950f04c0144594201161400554a4004d01700385003e96052424580725030280f030076a482a0311001801f00040f500c034101c070b10780d410005c4201 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 869571960 1250 869570710 869570731
    0x2090c0706091514010521030f181e010215090f06040b101a0703030e0f0115050906240a03020c06040501020901090605030403090306020d020c15242b02030f0a020306 73
    0x56150000040b40b0b041903400d107c0c80300015400070000c2003000c0040d50442c1c800e410302962a0326020480e02c10105002d55068421a4100e6404044403007010142d484544107a0240400c51040c0303040403564540a016181188500710f051148100280182405036224007902255070900801c1c5040215058202d12414141003a158503c08069021910140d5044c14007050340c9450b02d540038184142803030040329650a103c0c5c841e80411403500f0711403e031748089440402c0364071188184902c00142c5060294841d54410724036043c10b0800d4050084d00d031562801503d083c01310385245051907002d903407c45083e03401141011841d0303000103100001d410a480d03c02c3c110315290700c004250445510010341016400580500c0400c060340484041000308412079a00c92a9181d01510340c5204803102e98035a070401581800f0002d0000c0701c510079950041c443d084081c651306c10000344c48101244041c100050625000060710203002c129490200c0c1c5000d1b0404880340d00605040481c010500e1148 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 869573210 1250 869571960 869572001
    0xf0e06060f1c2f071b030c080f06013204060909030e100c0506131a090607090b03010602100b0a09050f1504020f04090b030a1506290702090c07060915 66
    0x50300f032040a0311480c5401c140e042d02c880750105c09040b0042020341018210040510021840020003d10b4100c801700c0c02c411515903a0703881008443e120030041000e4420301e10400503540c001d0303081010f4601501d0041002402c0b40c1e580340c0d4a41240e080391030441c040b83c44681c201c3e1942c80d20949034100000641892031480041d40d0f82d40f526030740018003508550342d46624040c2400140d000000c4a0700241c540c8800c141481c0b10f10b01d544910031140e01c80041d515402c080b60b0154001c0c2524100c80e1f041c1c0040001101c403920360409402902c15883d04032a13402c0d400a0741d1400340c000c01c2e0080c0610200d603003007401e00d2040410350210440400703001d01e00400c00c00c844840e51204440448900940000b100342030400041e050007140803000d0a0707401f810020b01c0c0c210455600203c221102c401654403411410384480003941d400a244240c20841480301c4000340c2400d941e0341e54403000d100f002e0f5103003544543d100c100700c40e440b40e001c3e55107021966941c0d031892014405d40146a0a01444444 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 869574460 1250 869573210 869573291
    0x30a15120521071b08071202030d020a0503030a02340201080c040501120f0b0409060204090b1c1403071208041a06030705130207080d0b0a0f0e06060f1c 67
    0x1003d2003492001803002c0142000401c910021a15200c0500b420100340d800b595641c800c10f00701d90100880c2a80700f405900300312140c02d03000042e81501030f41c0c010007442c20740e6124406070000b0340090181401c41002502419109a803040c0565041c01000c16030345944440c500004120401c0100701d40743c0c860080105001684c0c02ca000701c805140501c00100b82004011103c1000c1c0245840301d64000e800c20403036908002041d00544165040700400b000307502482c60400600d0350920303026201c1600d85890140200e038101108108001c0f560741101e20305201d6540b01da4400341c1c1101c6000008036900244003c2044500b03003080c41e961141d80411503410404002074960a036403040b60702c62454019108502244c2e501900c0401e900144065180d400c0345120780c0140c07004c0e1170450b200300040600440e4400f00c0342c612800340c44c07007200c221150365100014044654000f0602c07040e0780f207042c4034200440039400740b0300c500848107541c04244481b110440d85000304100d20b01410325040c1c0c0c1001d0382d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 869575710 1250 869574460 869574523
    0x1707080f1b01090503010504031d06070b13020a03080403030f090e01060219060617011a0d050318010e150c0105010f060f0e040b3304050a0605030a151205 68
    0x200c1c803640c18200c10881404070310058a100c0c0c09944942d825509240c00c21041c940c002010613402100c6e0000020038018041c100b1409200304003000701901ba0001c08a0300a07640700f0080d008045c8094964550a03449449188030790300198000c800044130310904229080c0e02202603c02011141d46200940d410040082d4584145002907617100590300550018006983c120000410402c0c1c10b101c000030107284018041c1032135a41c240201590301003006120304004c000c10b00387c1a0408061400c04000c007418100d08454140b40710304101d180c901c5000031380c3c0c48200d112500040e001c1220740d6415649020703420341f08141e0003113240350384105040080a03000101c65880f030800740390501c010a00c041c0064003d182034114182c06c080c100484101000b544004460643e40b002d0000b0340b0301c0e050045010131403069005440d0060503420080046600a40255811001401c1b012402d40800950080c40114031f901c000704003250043c01d40207128042c408910015001800c441c8620019041076 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 869576960 1250 869575710 869575723
    0x11070606050d172a0c18040b130302120d0e060601080c030a021605030f030105011d180415091b0617070e030a0605040f0b0f13020f01020102040801061707080f 70
    0x5041450005440e010940015184004813a100e00820340084212034000c2e99034000400010b000d5510500d20040026526422520450744000802907595a43ca045051100c44200450a45c440d4010181c45901c3c1e40010f42406e41d0040400611280d403d0412480c1c4030000c1c2401c0e051180c100284211103c4071012664880c1c0c4090025039101c4002046081d64070070a0000707401400041603048600503800001c604a5600740e84909620070b18045800101445608195100c506620130408c8109a9111035501030301401e540400600640702d0201036070f004e02012186241500401154103441a07200f001600c590b123001d1035000110310403206412000340c44142405982400041961380400c5168000d550043c420b0020382800e107000e508261180c2422554440701c500060f103099440b40c00705211300700c14140e031007020072141c090012002801c804903045540800001c00d010000b40103900040901c5280e8080ca600388803401c600b03184664003d103589812003003008a0446001959 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 869578210 1250 869576960 869576993
    0x10806010318050723090c0d0c26010e090a1e21030204090513151e1503053c070e0f391303050111070606050d 49
    0x5105800e0b21680c001c800c0781008000d05a00c2254400b04106048034040340f0b050032107032071001c1040c0c03c800400c284444204d546401c500000d1002d011005003c2d00001981c1c281824400340d15901e40130030f122802010705286034170900380d000400042c072a0240e5175070b00110359000b500415032a0307541c003548000e0800b8401080940040d0070014440c11160391071100d80201000c030180b0b00c803440d010340030350090300c02d49219514210000d42a4003000020b07080c40ca40c0480485010040400c0a400030503210040c0008122465400200c0b030038944940e40358100075110410440d8514503100c0d16040e113070100e410450100e115840e904011140d140740641c4920030b00c5452189a2101032458006503520501c5c81341c0c0e280080c40030241c4142089801641e0f007111061602d03079031035481c20340c484054074000c540d03481140300200c0b000310440103800c20800407494100310940e41c1e15140e0940c0d041820b4003100d8440004c0000401c5114800e01005000035101004c07884082c4d103c002d9407420004c01c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 869579460 1250 869578210 869578217
    0x1a0109060614072a140303040509270d0221070b06100513060c02031e0709090303020702090906010e0108010902060f09060d050708100f0f0506090117040303051b0901080601 76
    0x150b290070016403d00764003250350350058801c00211001050a0544e019100e01024207000c491014400d04020040b101a600040c0200343c00f03860b03081c44078031421340c0c1071829181903518540b071207241e0000340954013001e4800d600401c0100c40000b26181e0783c1c0480d5405c06400d140801c0120001002ca0b46150b030700000031a0400d420425550303040c1d81318880c80c0080c03200751070740007000720b107031500002c04041e23281c025801c0343c0c251920908800300b40c10001c10001c000741c0c0b2600c01046406d0260b0000c4001c144079190140c24a8031541c04200c107031034251001d045a4010720010301034031722840581d0340180003800c0280065501ca4000c28020b119081c0d4081102400050400251700c0d41011600e2450184804020f10f250803640200081020384812061000302407000806c143c0b081040015161170300c001071000303498002003101c10751011040506005843c4a0a07180d0b0400b250390620680c000c1d00c002c9420700e010800c81040440c40c02100010381e00c03e000c030301e8103179030310050441d4400802e09 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 869580710 1250 869579460 869579467
    0x60f0114190303050913020309070e0c121501091805090d0203040e1f12050d03181e020a1a0309010f050411120c100e100206060d080a1404031a0109060614 68
    0x717010034403104001a180b91641e0000051100e1000c0000e000021168040805500b81c1c803441031448262103440310b00c500c0f009045010880050102e007141c0c12072041410304481ea1640c6070f0902002042040d0411070140e500e8080121508040c0020300034820184041c45c9000d04103d181043c1c090050329601c03038440008104404404030285d00c101400602c8200c0c5050300540c41c10a6481c002c540b034a40c0000d0070403a54860300324401644611283d806040702400450084107004001420002039a108800d00400902c8000383c580b03c4170180318500d650f55403450070800280c2511588851000121310308810840400c400804d00c0e124400f007110480364203040c803412186030500e0000d1450f807000442d440d0000d5290050035459507454143d1706214590407421050381c890340300312200386e00b08090301c103900d000030301500c01001210107508241c014402c0600301d80c2040c2e00aa001201c220390390200c0841c030314501500280c0184401da0341405194288500107045644001c101d006010300817 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 869581960 1250 869580710 869580727
    0x705131a1308030306011829090904050703030908030f09060d0608030a0201062c0402092a12160f180513021209010612030f020f060f011419030305 65
    0x300495850594001c0703580c14180d201d14415880c0d134000c0e220f1070f0214140d07100700f4500c900c0540141c01204c0c0366280d408000d04004a0001c20050000034121a06101b0040e07142541c0d528a01e5900076070040e4002d260190543c034015288851035001070726a54000d0241d400301449840071140a028103903161a08e451000074064040d020780d03040040980004920415510342c154420300441d8540200001541d92001ca4a4200d103000b941400e104505000001d0150030301e1303000c0c144c02c8117201e1034103004800044112101c0c0c403141802038980840020380c009842c544030b450282c20507250a2207030300003404204068074804e01c030402039080c0b0085003c0d80d005810500d403203600400024000484100c0c05100e110001d5000c0d0544111800348030b40400c50031300051242e41d06680d0b44103140064079001e62025603941100780044000c510611245400055040c0201c0340540d10b0150804803550601c2da0260601d00c0001c426805150a242c0c0001c081103500d03411000c40740c241c01c01d5035440100 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 869583210 1250 869581960 869582009
    0x417120304051e0c03010509330106051b120406030c0e010e1002011416030e0307080418020903010f090209070f080f04080928142202041206060806070513 68
    0x41880b5260726510300405c122280c035009c99100c200000700c3c0145020b00d0141002c040c0c00301486052600f081c1d13000b074018082a070241009014001050800d61101032a0b10215842c06c61089464102d000011030308108c91030305402803501c000c49500f1b01c0e43c0c1ca0116180024010800340315420f2090410b80c10041c100c90007035001201d12480c8603840042c40ca800c0310081c1c0000100c40550000910f00241e1a08260020068405140d4030031000b9160500d0030a0388185004242c1264030301300d608104203402a0340c00d210f03e00c1c00001202e808030308001140100326003104020701210a000c0c0d25010b846145620281041e80226400d208400646031030510190303d000b03091850360021b01107660a009850000f91410080b4080600c603980e8507182da003018900115400c86e2600010681e220210000e0814419030742e4542d04a001030401d81e541c9141c0704c56210346242655400d640c0c5c0f00c2800030110501826602c04418103159240040012a142542c500c0e07220b01d800c40b0030b2000104072003165 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 869584460 1250 869583210 869583223
    0x60c03020c070e041104050f010b07021302030910050c0a02030f0d020c060108030318150103080d0e07140909060609040f060902091006030c02011e021e0417120304051e 74
    0x10a00c12520b540703440c1c001c11044900f068800352031902002410030340610b4a4090b05108240e07144c0c4010090746000c01c2100d01b504004412a405006c451a881400025101462151a0800041084101c00c01d024003c640000e0480408800304200d60404241c0000440c0c0400342c62031020350352003c801003003200a014420070150207014000002400c1034000024500030ba920701d001d505082030f65050183c3e281d004141d81c010709d1080034010408101204060444209d1021022950110070306180c0d0074032000e900010300707010200b01d0700e030f00078103140505680c444450002400b25050101c00180019002440244003000101c0784004102ca9030f00070304080b541c050600340c12401d003008032560040080c0241070010b4580000d030700c0507074414003e001024101c408802c08110b08420074401030342c007100c5100040094644000294a14640100014203807009401500c1e12420949800c00e00b119601580040d814801d000210700301059a40040d075049024030110b10250440d0380c2400d4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 869585710 1250 869584460 869584477
    0x170d09050304031a0f100302090402040213081e0a1e1506090906050f070e090a0b06040b1e0a12020901090e090d030c050403080d0209220e010606110307060c0302 71
    0x1c04070b000020000b180c1030700b40214121080840c041c0d92003089030001c6850803581ca401204229800b0405410700c9050340342c0041c0060009860b0038071040a44151a07901ea02400180d03008000c5806a200d00051410b03404c8040c5010f0048024180c6451254003520101413100c0c0002014601c10001e1646051410030116141440142c1c2e41c3e40040005040104041d5041420600040c441200704481e0341e101e0f44035034603101c000320100024080342000080c00942c0040d500d000c2c044040e41c0c2c1001503c000e0506000c50756031072148501da50b109901c05075020100300382c20b00807601d8050300001c42d0700c1030b40039034800143c5642a01004031182c400c0c0b503106110712001001840740507080421482003215403501c09108000400c00200c078a4803c40c8000303415620141b00c1600801c3c42a0000e00000ca40180203518600050700310030188000c0c0503020110036130724094814041c90078091080240060304000721184809a03900c3e0b142e00c0341d48002440159194614020036029506603094034 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 869586960 1250 869585710 869585713
    0xf03071e020a060f0c0f030506030316080d06060e0102030f0703021f09210e040f061a120a050615030603070e161409030a0320060f22170d0905 63
    0x440003900301945031980c05a00740c54944c102210311141341164044e00070540819500e1940760300807114120f00900002d880030f60303d070100f00554480c1c0b5445e144408001401074030101c0c1e4810310030000f542150005d43c0300805000780ca0b4060500c43c0e030044140c4da81c40c80c04020a956400c041d250490401d0380400d4100d544c6032020803481d000c450701d94001e030203951140e114402030304001c00128401e0b410961440d40010020851581c407800c01f038025503a4401d8508000c900903444004070501e854450a401704110350205028188840c02e400340c58100a920b1020440b81c1052004144c2e40810048448440440000271480640f020841b074801420030706581c82c82800c110300e90a500030840300d00003000502d0101221000c03039101c0110350580d00010700820080d01c89640c1541c80c080507510b10004c4030110308140786261020310402c1e01c00c0607201e6280885280c0740d01484a50140081000b03010341d00c0c941c001000801080c2d2985600f070041c21499124011100003e018040505005106 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 869588210 1250 869586960 869587007
    0xc122001061409040c0b131e0e0a0b03010f0207050a0510061a0a050d0603151109130e030415052503090308090d0c12060b06030903041401030e150621030f0307 70
    0x609100c039800e0545250f541231803e081503050405801d00b519001d0174010300c4880002c101c0301c070702540c070801c0300351800b40c00803602640314a00041240c2185034203580c2900414448400c01a0500088100b150090b000708265410325070408401445800400003000c0300240c0036218178014800e03610064203603007081c050031392039182000c408481c050302c40c887e89003000e0780007000341401c81c00c5e99880038002e02480380c07807000420070030080c140404841e80c050008000100304111100078850400c0150380305c850344c500490301000020304e20207440207400d10f02d1408040001e03900014200c222604000c18070345880310400001c4039003a0fa80030041680784008000598001c400001c410b0540c00384404120252a400a04c01548400c480c0d40c02140c1040006010851022000e19250f50b01031400107401a482024285080c4404102d4003000340d0600c10031030340345810021b042090310340e1660180a40461940305541c0e00481403252010000800021892889501002c034071140403886d4800 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 869589460 1250 869588210 869588227
    0x10e030d0c02330f04050d0b010302090a091e020a3f02031c05090603010905040b09010b060a03110721080105030712120c122001061409040c0b 63
    0x11107040504101d014186940418940451aa5034500403c255507404000000c1d020f0122001c1c1d8480d18032101d00e04010b0001040300d490300c00c5a0120a4071945000401e9411401000306504000b0100380d0704a041c82c490800040f4118a0221880c2640f11f954440390b019100203010705080303800164107554291550f101c2a0700300c0b41c51030001c05100d440001201070f814030f100040010202e000c0d415902241d11345a0490300c0714003509410800345840c604055070b0a00082c0954020b0380a1000c0c0350b158030500050007a03480c50036401c643c03007070001c221076000080400c01c0b80c050201c032001490795518480513140b41d000100c0e44582e502a20814200030345400c028003030440c42c45d400c0001404c3c500041000e00b40007900009481e01d04000f1340d5012019034035050070400c100c40310300421110b0603800340000c8400041c0549816144c0b201841c0e004c00d80008840d9880400e201d0310b40f60b0525008001c10582e544e01e00018401c241e0703444069070780b01d0500390500c071040c1d4007500900400160403107 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 869590710 1250 869589460 869589467
    0x36031c03061401080117070906031505090c24040314070e0c0705071a0c070f080c0a12021c120216050405040b0105011b0b0a0c080c041a09010e030d 65
    0x924614280e00c0400509844103410b501d00007095200300d0104000000500c00c40c10485005200c0040e0582280d400c00e8440142d40c043d604944e00c1110742c8101d4005900903c22a1b000d201e52150500000305842c0b154800002c050b1142c130740b20b5503109403100c4207036003071401810112800742d90070070089005481c00c03140207551500c20348180d0300d540720380c5800300d80c000449000303c4918540100081820380e080c250750400e5100c015a4094030a101048011041c01c0309002140c000c0c80c44581e600c000e2440c1428003070500c1400d80b0468415040524180b002c3c0c8190620f501e0040d40641c0d64200e10072030040359000c0000144000f50891850403a11240c1e158005440004007000240e5660200d0f40d4905100913120203480080607c0804c40051083c4e52103180711038060020070344044d01d424502c1d2200c81c420f060a40b11550b00949030011010081c0d04841819040708900380f00c18030303051a0201c40514201c004120f450f01c000e0000d041c0082c0e078840e20f0420040340d00241581c0f1401403203007014 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 869591960 1250 869590710 869590753
    0x41a04030203010c08010605090603130210030e0607050c0a0b0604180f1a0c1605030d0f020405150909070c030e04020d0b01082508040c080f1e01023603 67
    0x102c0c880c3d030030004540d4030b00d480f81203800d040b00c825840e01400c04100c00108001038000400a44906881c0220351000d0707542d0128844258007030f0b0b10000390380824407083c1420450020b000c4010b1001c04c0056003540d20340040d940c100705810000389041519020002005402c4188803210305500241401c01400710304018844040c1c0300d82e0b82c000c028241006982070814003150b14954915003440445007000c8170200a626040c4940c041e64540075540309000b08840b000140743c00900d41c00300c0d080c003c034185020341c0c5200c40030b001109414190701000040d005c602c0100810200f2145005240815015a80f00c00a00c83c0081055407141110440c02d4005d200c99101140024001000704030125200790440b05111614a0a054004002c1c0000c5c2e917403500140046401d100e60010000340c00d4401c0c880010807030854409042070741c6201c00c03902d034090030890301d01d091644104141c1d00006d902032900c480ea18178200302e484480b00c1410505216201c0b205041e6098003d09001c2e64149032540070a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 869593210 1250 869591960 869591963
    0x4110f070507080d03060b12070903050f010f0b060903031912061d0601080c09010507050f0d020d020f07080601090c03150305100e03030c03150d060c021f022805041a0403 75
    0x1c9803e031013042c0f1012404d88105200f003209503541080086d003a51010100360341e10003101e00340980c05a980780c2d610b038a0007000c80349107140f59566541d08000c4600600500414a2084400c02d04024030b0341e000139100d211789400c0701003450002084c00e5100f80242810182d000000a007041641c0e9074507142c6c0d4038a6241100c2c8202d42e00c04100054496010329502c50280071100030503401e115800d00151040d610400d415a01e80c0b042e00300d0700c003181104100484440d00d071980586404501c071034000e49046010004010a600a01c3e8248484800060f0f00c1c1e04541d42c40c02d002c02c000184000030b90040a00f0302000c0c4c06004030510100901400282d0070b448880201020000f414041d00103a4807408143d5016209440810224030101481404904000800ec1a24000700d41d240c1d600d40071078444100d002c0160f00b00300c2041403d030711031005409503403607902019440d008000400b182d00300c05110103205440401c261003c0700c0f40c0700e0700035100a060703026606c00169503120544800e41d0440e210 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 869594460 1250 869593210 869593213
    0x70306090606050324100906080102041a0f090d0c120c080d030b0105120a0e060115030b06030114010c080426070515030403210513050c01020609030904110f07050708 73
    0x200250905000450300626001d001c0605c1030103c4040a6000449024040c5111449100130200e0315a00e80e22810008161040006980300d18000700d21506034089065200c8240d0140140c0421443c200102ca2020000303c03041d00050542d0b00e482c15030414640c214040880c000f103e03040820202d1a03500701501c4540c42100d4801041300d00450603108404001c900040007407001020300c03500d008a154000008001c04100c1c0c0402011040c0341c1842644405a0545a070080008003905485040c4201d042543c1152441d8180044aa0003c580c404141c0c108200100590140301c23001e003d881c007410715480703c1d031800b69541c0016080c598004001802c6c500599000042a1401c485180030000ea41480341e42907944688041e51040040b05210a8004990240343c111180a10480c2c1c0b29107014001180301c00c1c0641041850718641d1440607041d0b40c0040d05021407504000151143c0401c00c46001ca003000310711071420007038020301004402d0364a001c5211b1041001c0811b0318805d50b1070040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 869595710 1250 869594460 869594471
    0x131202031b030a021b060c12030a0b0607020a06111501150912050d11030c0a0b010e241c020a2705100303030b0303131410110d0507050f0703060906 65
    0x41c40301c2e45a20500c14268050380c40402c4007603010b03011582540317511344000c00c61810714405040d080d0030580c6400b02c25034102400020045090030a01c91035070940c0d400e0307522504040e0356a021800c01d80007800f818050080082c0d103100d080c2010003040e0304c0881440d882d02900d5035182000e07140f50700211540e00200f1044c13000070030705841400304807070816000401804d10142e00d800503188940c0507108040700e40000c200c002c481c0c2e0820400081c80038816081e48a00f90f1510403400d181202c0078050a1040c0c1540006081028400c1e039080455542140c11800c0104405840d4011020000000303401c8481032400007122080e41e040403804000e10090740c00d40764143e560000441c2d004981e2440ba030340301c42c403062010a1199010280202d00079045a1900c0700c0b610758914802001d41c0900f84014890303600840c00d08102003004010b03403940c00c14001e034644205505486411442c1c1400421101144136810310200304220910441c50605451032580c40c2e081c000090500f600080d6401420007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 869596960 1250 869595710 869595757
    0x605010503070b0c0a060b1804030e1e130c050c0f0106080c10140f2203050d03020a0e0d0501110703050d060e010e041202030f040609031a040803010e13120203 70
    0x180200c544c09082d060207095020341d0303030380c40c0001000c141c14495080264081600400f610141c0444e0085019841e02c070291140c031802c01104c070584041ca090018020b0802802c641c480c440341d00034030010b03038002203002c0305007a1080310280501440c03240306116070010f580030a281944010151a000c0007912101031040040c0b09040b4100c5e50040700099050b034058095a8460000e0003085504803080d5207065055904896100c82142c003826041615203402c004125081000000013902400e09505090516034040c10407801e0020107406004181241020880203500c038000841c00620030300d484001500b80205035800004040e99810b2070030202003021005e004c2120704a41c8001c0c50791030507650300e07640c0c8010603148a01c250154401842409031290268014102030311080c0e4405403840e1035410705e0207800050a42c04101d1104c001c0600002c280c0e51801c82e8190342c020303000d00c0555215003005030040701070f0780d00282020010054410f100d0b580800200b0804140c03040c50903400048 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 869598210 1250 869596960 869596979
    0x603060e010b0405030303010b09031f0b102c0402090307080604030e0a0f0b1809070c06060b16020d050f03040f05040e06090c010c03020c090901140703090f020d050102070f060501050307 82
    0x807130243ca51305a00a10042103090b8840c4e00806e60324002030306035480c0d84101c040000403008102c100002c4643c0794941c1c0b040d18105822005c005109901c2d10001d800000190150080084682e507500c1c510604900c0545889980444605c90409002c0b0307002a9904e070020b43e281d450079602100000d1a200120384d003490001c619800b42d928013610041400c0c0b81040c00d280d00c2d40500490300300a48116414101c0d9075886541c4c520070030840c0c40e0100c1d403240340e1522034100c3d0040d402c941b522013014095004403005c4054881c00090303043e2201444118241002d503e000490f2506400740c0c0710000b4040b0b01e803000342d00b060301241c4085c0c0e4148080042c0d0f0000710b4941d00d080720a012254003400e0520301c00c0d8071413543c904809000e40182c40c0480300e13010210340b1841c0201c0e48030700b5030b039180d5244544007450316a500e94000914641000307004c2c038542d0780514240c25443c002c0e2040c090741d40c80034288202075044640c19540038841200801c024501440506802d210302846800344c0000054020803 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 869599460 1250 869598210 869598217
    0x109170f0d0f110d121a19051c1110182301020a0f0215070602040306270f0605071b0c0609050406030c120606030209070305040618030f0e0103150603060e010b 70
    0xc1c0c030780481c540101034141004006e181c0102c2020701400504000300c0c2c449004411020700f00b41d081c003111500300424081540001090044407203035500021010907024140741c260f54008a0740d021035020741f200203d8125410503005128600317542800030303002d238000800201c41d0050560100a1a00a000581c1c881034000c1014100b0081c4c14034141c014688840b205406403100b034052818005251640c0040b600300e6041207484030703a82c40c1d500f14a8580d4a1182d000382d1610006803d0389070690f5a031001c414800b13040200342d141c0300c902050059000c0c223203c03020245405844a807502e101d0601030400c0520f8800d400c04a554480c02040742d051034082d400c1542e4000101c040084c0c038201d80d04480400d00c00066801076034441c1c0110061381d440780144c0c010b03955a54045042d06007414140d0480340c4c4070381e03a90001d00c4024844070019030045c2a003000b080050400e4801868086c0050f00a484902e000c0050b0403881c040220b95141c040d8002e009039610700414090700d83e00c0d101c1d00c004a20 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 869600710 1250 869599460 869599483
    0x1203230720100b01050d020a0201090b0606040b04031407090c020c010f08100b13050603040b040c0605030402180402030708070f0906292b0209010e0f0109170f0d0f11 73
    0x100000b401c190340c412035400c4268001410702d0700c81d103006100402c00c0100d0300500c1c20303180141d4442d105a000e20400721072403600000d049800381d140c40c1c60246960030b144100d00c4001c1c05d000040108007280c90003400400020402d0304018030a905c41480c0094907540e45408803800300da14580d0400003288529034092083c1200d5080e40714803400c00e01c0c010215040340d211124201c401000101d6030fa00c03103401540c09540703d801d410800781800d15004800d1145c0742c11440410209000b04409a555854040500e02080110540d103403160b00100341000d1031a001060540315040d400604d90800c91000e6040350705400040143e191202034841640802502c0020420500d400c059200d51184005001035101c400e40342e4440000e50140b90315010009210190459020800107030558210080c540c501e03000700c64a004a00c0c03240e001030718000050044440c584c42e08445841e40c8002040b0004d502d4012101703c2d920240407100003040e0500307017036454000035290f50201d007141e5070009094400d00c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 869601960 1250 869600710 869600713
    0x120c02090117100e010204050109090509030f030901150605090f01020a0f02040c050c011a010306060323091e0d021608031903022101141203071203230720 68
    0x1646440c080c0089401210ba16003054090007110900c0c90281e0310412078481212000540c44e9494140058803151066000d03d4105003804100510060007004981100164a40c040d84a807585052035004042503812079210b00007040c0049005a00400640b45841c0100e800720360b00586480120b03141c00f0389030001040c02007281c400300f005282581060499081c2450f00758100b9821a080a0075201080501c4400d0201d100013203901b5641802500d010b00203600f81400b1111944001c3c00030802d000c4500000540520080395001005000b00c01c219030050419410700301a105180307480703070201e050920141c441d0321081011a071288695004540c42500618104000382c9003426041c0d5100c0b4000040503401c00060411100c203a00040d81080c4401e80c0b15080d604001d207000702c0c0a4003002c00c612400c02c141d4000c41c038043c00000c64070015400300b03941c4445602240c0550103002030355071703082200d1001c1d0001c0f40c0030420944424801c22581c5d507081c1e100c00403c020341603000060052030010703 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 869603210 1250 869601960 869601979
    0xb070b10080d0e0f0f0d0c03060f0b130b0109051e100311030a02131d0403080612100e1908030f1b12071e02030406020f010608030304020904110d0f120c02 68
    0x49152000d000c0700070b00e202421204405a01d540020248132224000b00c7c0c0c1c85114600900500545114012500f0140c80c402c0219200600006444c04005030908855a0b141c3c3d0340343c001644200c8408000749400b4002840304035800c60110780403401051428025480e60038a8050384d4400e001d00194800c031803002c145991104050800658851807601c8c41124080c200004d9013400700007020325010700903481c1c108030300741890028542c25002d00054420b581c403590070913003410003244c0230070b620050880c0028003070b1054050505000036000a42081c8158402d99000d110040e001140b0178051040300107074035a100c1c0710281014540c507131307516100c6100f40101ca20403050010303095003100d51030a00700c42c851080304e0890400c5c09400b80328070041c2c1000c10100700842e01001042580004c04000348842400c0c02d20b1280da80c000240b000c0d101d0181800484e01788030381c0003800c07052554040c0c244441c0341d446040003003114010010407200324184c040600800e0f40704071190344180740c0c0240407162 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 869604316 1106 869603210 869603237
    0x1e0405030718150605160501110706060302100903080301030f050a060c2c37030302010506101b02010f050d020414030d0c0503040911040b070b10080d 66
    0x30031403d01400d2051030f41010a42d641c14145014119100381641049400b50040c80c2850410980024070007080c4801c5800107020390b4001d03201c1001581000b0400c9034104141e01c4042d016140070b000500008401c03601c0c45003001d01540c00c407107501001c1d0700c520049840c05042500402c004c0e1032076031081d031844840301644010852401d2072102540010540e0440341040207a8490300300342080403860107200c800640e80c1c0c484003100300e0180e224a4043d0081500b591502d1040c0c0c403d800d041102d030703c04d8428400b405901180f050035100c1a034010f456105030300c00040c052100c18000c6020f404000d1010f00010002000d0400100c48048140340c2400c44040c203c0d0108070b801c1c2c10560125400004840484550b0340b000651802440c0c0b010440d406181c201c040700c00000618401400200c4140d40e0240350f030000001d40080d0b54500d191b130b031a40401d100b44041000442e0908 = true := by decide +kernel

theorem cover : BRFrame.Cov 869424460 869604316 := by
  have h0 := BRFrame.cov_init 869424460
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869424460 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 869424460 ≤ n) (h2 : n < 869604316) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
